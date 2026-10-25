"""LoL 敵スキルCD一覧ツール

ピック画面では LoL クライアントの LCU API、試合中は Riot 公式の Live Client Data API から
敵チームのチャンピオンを取得し、Data Dragon のデータを元に Q/W/E/R の基本クールダウンを一覧表示する。

使い方:
    python lol_cd_tool.py                      # 普通に起動
    pythonw lol_cd_tool.py --resident          # 常駐（ピック画面で自動表示）
    python lol_cd_tool.py --install-startup    # Windows ログイン時に常駐起動するよう登録
                                               # （ウィンドウのチェックボックスからも可）
    python lol_cd_tool.py --uninstall-startup  # 登録解除
    python lol_cd_tool.py --mock sample_allgamedata.json   # 試合外での表示確認
"""

import argparse
import base64
import html
import json
import os
import queue
import socket
import ssl
import subprocess
import sys
import threading
import re
import time
import tkinter as tk
import tkinter.font as tkfont
import urllib.parse
import urllib.request
from pathlib import Path

VERSION = "dev"  # リリース時に GitHub Actions がタグ名（v1.2.3 → 1.2.3）で書き換える
GITHUB_REPO = "katakarapape/LoL_CT_Tool"
EXE_ASSET = "LoL_CT_Tool.exe"
# 更新確認の間隔（日）。設定 update_days で変更でき、0 なら確認しない
UPDATE_DAY_CHOICES = [(1, "毎日"), (3, "3日ごと"), (7, "1週間ごと"), (14, "2週間ごと"),
                      (30, "30日ごと"), (0, "確認しない")]
LIVE_URL = "https://127.0.0.1:2999/liveclientdata/allgamedata"
DDRAGON = "https://ddragon.leagueoflegends.com"
LOCALE = "ja_JP"
FROZEN = getattr(sys, "frozen", False)  # PyInstaller で exe 化されているか
APP_DIR = Path(sys.executable if FROZEN else __file__).resolve().parent
CACHE_DIR = Path(os.environ.get("LOCALAPPDATA", APP_DIR)) / "LoL_CT_Tool" / "cache"
NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
SETTINGS_PATH = CACHE_DIR.parent / "settings.json"
LAST_UPDATE_CHECK_PATH = CACHE_DIR.parent / "last_update_check"  # 最後に更新を確認した UNIX 時刻
# show_on: 常駐時に表示するタイミング "champselect"=ピック画面から / "client"=クライアント起動時から
# update_days: 何日ごとに GitHub の新バージョンを確認するか（0=確認しない）
# spell_layout: スキルCDの並び "grid"=Q W / E R の2×2 / "row"=横4列 / "column"=縦4行
# timer_voice: 試合時間の節目（VOICE_TIMES）を音声で知らせるか
# voice_advance: タイマー音声を節目より何秒早く読み上げるか（0.0〜VOICE_ADVANCE_MAX）
DEFAULT_SETTINGS = {"show_on": "champselect", "update_days": 7, "spell_layout": "grid",
                    "timer_voice": False, "voice_advance": 0.0}
DEFAULT_LOL_DIR = Path(r"C:\Riot Games\League of Legends")
STARTUP_LINK = (Path(os.environ.get("APPDATA", "")) / "Microsoft/Windows/Start Menu/Programs/Startup"
                / "LoL 敵スキルCD一覧.lnk")
SINGLE_INSTANCE_PORT = 47555
POLL_MS = 2000

# ピック画面以降、ウィンドウを表示しておくクライアントのフェーズ
SHOW_PHASES = {"ChampSelect", "GameStart", "InProgress", "Reconnect"}

POSITION_ORDER = ["TOP", "JUNGLE", "MIDDLE", "BOTTOM", "UTILITY"]
POSITION_LABEL = {
    "TOP": "TOP", "JUNGLE": "JG", "MIDDLE": "MID", "BOTTOM": "ADC", "UTILITY": "SUP",
}
# LCU の assignedPosition は小文字・呼び名が異なる
LCU_POSITION = {"top": "TOP", "jungle": "JUNGLE", "middle": "MIDDLE", "bottom": "BOTTOM",
                "utility": "UTILITY"}
SPELL_KEYS = ["Q", "W", "E", "R"]
# スキルCDの並び: (設定値, ツールチップ, アイコンのマス (列, 行) の一覧)
SPELL_LAYOUTS = [("grid", "2×2（Q W / E R）", [(0, 0), (1, 0), (0, 1), (1, 1)]),
                 ("row", "横4列（Q W E R）", [(0, 0), (1, 0), (2, 0), (3, 0)]),
                 ("column", "縦4行（Q / W / E / R）", [(0, 0), (0, 1), (0, 2), (0, 3)])]

BG = "#10141c"
CARD_BG = "#1a2130"
CARD_HL = "#2a2a12"
FG = "#e6e6e6"
SUB = "#8a93a6"
GOLD = "#f0c040"
KEY_FG = "#6fb6ff"
PASSIVE_FG = "#c8cdd8"

# Live Client / LCU API は自己署名証明書なので検証を無効にする（localhost 専用）
_LOCAL_SSL = ssl.create_default_context()
_LOCAL_SSL.check_hostname = False
_LOCAL_SSL.verify_mode = ssl.CERT_NONE


def http_json(url, timeout=5, context=None, headers=None):
    req = urllib.request.Request(url, headers=headers or {})
    with urllib.request.urlopen(req, timeout=timeout, context=context) as r:
        return json.loads(r.read().decode("utf-8"))


def _version_tuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", v)[:3])


_UPDATE_LOCK = threading.Lock()  # 自動確認と「今すぐ確認」が同時に差し替えないように
_updated_to = None  # この起動中に差し替え済みのバージョン


def apply_update():
    """GitHub の最新リリースが今の exe より新しければダウンロードして差し替える。

    実行中の exe は上書きできないが名前変更はできるので、今の exe を .old に退避して
    新しい exe を同じ名前で置く（次回起動から新版。.old は次回起動時に削除）。
    """
    global _updated_to
    if not FROZEN or VERSION == "dev":
        return None
    with _UPDATE_LOCK:
        if _updated_to is None:
            _updated_to = _download_update()
        return _updated_to


def _download_update():
    headers = {"User-Agent": f"LoL_CT_Tool/{VERSION}", "Accept": "application/vnd.github+json"}
    rel = http_json(f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest",
                    timeout=10, headers=headers)
    latest = rel.get("tag_name", "")
    if _version_tuple(latest) <= _version_tuple(VERSION):
        return None
    asset = next((a for a in rel.get("assets", []) if a["name"] == EXE_ASSET), None)
    if asset is None:
        return None
    exe = Path(sys.executable)
    tmp = exe.with_name(exe.name + ".download")
    req = urllib.request.Request(asset["browser_download_url"], headers={"User-Agent": headers["User-Agent"]})
    with urllib.request.urlopen(req, timeout=60) as r:
        tmp.write_bytes(r.read())
    if tmp.stat().st_size != asset["size"]:
        tmp.unlink()
        raise OSError("ダウンロードしたファイルのサイズが一致しません")
    old = exe.with_name(exe.name + ".old")
    old.unlink(missing_ok=True)
    exe.rename(old)
    try:
        tmp.rename(exe)
    except OSError:
        old.rename(exe)  # 失敗したら元に戻す
        raise
    return latest


def update_worker(on_updated):
    """前回の確認から設定日数（update_days）が経っていれば更新を確認する（バックグラウンド）。

    起動時と、常駐中は1時間ごとに「確認する時期か」を見る。設定は毎回読み直すので、
    ウィンドウで間隔を変えると常駐側にも反映される。
    """
    if not FROZEN:
        return
    exe = Path(sys.executable)
    try:
        exe.with_name(exe.name + ".old").unlink(missing_ok=True)  # 前回更新の残骸
    except OSError:
        pass
    while True:
        days = load_settings()["update_days"]
        try:
            last = float(LAST_UPDATE_CHECK_PATH.read_text())
        except (OSError, ValueError):
            last = 0
        if days > 0 and time.time() - last >= days * 86400:
            try:
                latest = apply_update()
                LAST_UPDATE_CHECK_PATH.parent.mkdir(parents=True, exist_ok=True)
                LAST_UPDATE_CHECK_PATH.write_text(str(time.time()))
                if latest:
                    on_updated(latest)
                    return  # 差し替え済み。以降は次回起動の新版に任せる
            except Exception:
                pass  # オフライン等は1時間後に再試行
        time.sleep(3600)


def load_champion_data():
    """最新パッチの championFull.json を取得（cache/ に保存し同パッチなら再利用）。"""
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    try:
        version = http_json(f"{DDRAGON}/api/versions.json")[0]
    except Exception:
        cached = sorted(CACHE_DIR.glob(f"championFull_*_{LOCALE}.json"))
        if not cached:
            raise
        path = cached[-1]
        version = path.stem.split("_")[1]
        return version, json.loads(path.read_text(encoding="utf-8"))["data"]

    path = CACHE_DIR / f"championFull_{version}_{LOCALE}.json"
    if path.exists():
        data = json.loads(path.read_text(encoding="utf-8"))
    else:
        data = http_json(f"{DDRAGON}/cdn/{version}/data/{LOCALE}/championFull.json", timeout=30)
        path.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
        for old in CACHE_DIR.glob(f"championFull_*_{LOCALE}.json"):
            if old != path:
                old.unlink()
    return version, data["data"]


# --- サモナースペル -----------------------------------------------------------
# 表示順（Data Dragon のID）。真TP・クエストTPは Data Dragon に無いので下で別途定義
SUMMONER_ORDER = ["SummonerFlash", "SummonerDot", "SummonerTeleport", "UnleashedTeleport",
                  "QuestTeleport", "SummonerHaste", "SummonerHeal", "SummonerBarrier",
                  "SummonerExhaust", "SummonerBoost", "SummonerSmite"]
UNLEASHED_TP_ICON = ("https://raw.communitydragon.org/latest/game/data/spells/icons2d/"
                     "unleashed_teleport_new.png")
# LoL Wiki の Teleport 記事より（2026-10 / パッチ 16.20 時点）。変わったらここを書き換える
EXTRA_SUMMONERS = {
    "UnleashedTeleport": {"name": "真TP", "cd": "330→240", "sub": "10分〜\nLv1→10"},
    "QuestTeleport": {"name": "クエストTP", "cd": "390", "sub": "TP持ちは\n300→210"},
}
SUMMONER_SUB = {"SummonerTeleport": "10分で\n真TPに", "SummonerSmite": "チャージ式\n最大2・間隔15"}
# Data Dragon の cooldownBurn がチャージ時間でないスペルの上書き（スマイトの 15 は連続使用の間隔）。
# LoL Wiki の Smite 記事より（2026-10 / パッチ 16.20 時点）。変わったらここを書き換える
SUMMONER_CD_OVERRIDE = {"SummonerSmite": "90"}


def load_summoners(version):
    """[(id, 名前, CD表示, 補足, アイコンのローカルパス)] を表示順で返す。"""
    icon_dir = CACHE_DIR / "icons" / version
    icon_dir.mkdir(parents=True, exist_ok=True)
    for old in (CACHE_DIR / "icons").iterdir():
        if old.is_dir() and old != icon_dir:
            for f in old.iterdir():
                f.unlink()
            old.rmdir()

    def icon(name, url):
        path = icon_dir / name
        if not path.exists():
            req = urllib.request.Request(url, headers={"User-Agent": "LoL_CT_Tool/1.0"})
            with urllib.request.urlopen(req, timeout=20) as r:
                path.write_bytes(r.read())
        return path

    data = http_json(f"{DDRAGON}/cdn/{version}/data/{LOCALE}/summoner.json")["data"]
    result = []
    for sid in SUMMONER_ORDER:
        try:
            if sid in EXTRA_SUMMONERS:
                e = EXTRA_SUMMONERS[sid]
                path = icon("UnleashedTeleport.png", UNLEASHED_TP_ICON)
                result.append((sid, e["name"], e["cd"], e["sub"], path))
            elif sid in data:
                s = data[sid]
                path = icon(s["image"]["full"],
                            f"{DDRAGON}/cdn/{version}/img/spell/{s['image']['full']}")
                cd = SUMMONER_CD_OVERRIDE.get(sid) or cd_range(s["cooldownBurn"])
                result.append((sid, s["name"], cd,
                               SUMMONER_SUB.get(sid, ""), path))
        except Exception:
            continue  # アイコン取得に失敗したスペルだけ飛ばす
    return result


# --- オブジェクト・アイテムのタイマー -------------------------------------------
# (名前, 時間, 補足)。Data Dragon に無いので固定値。
# LoL Wiki の各記事より（2026-10 / パッチ 16.20 時点）。変わったらここを書き換える
TIMERS = [
    ("カニ", "2:55", "川の両側\n再出現 2:30"),
    ("ドラゴン", "5:00", "再出現 5:00"),
    ("エルダー", "6:00", "ソウル後\n再出現 6:00"),
    ("ヴォイドクラブ", "8:00", "14:45 消滅\n再出現なし"),
    ("ヘラルド", "15:00", "19:45 消滅"),
    ("バロン", "20:00", "再出現 6:00"),
    ("バロンバフ", "180", "効果時間(秒)"),
    ("エルダーバフ", "150", "効果時間(秒)"),
    ("ゾーニャ", "120", "アクティブCD"),
    ("GA", "300", "復活CD"),
]

# 試合時間の音声案内の節目（試合開始からの秒数）。
# 主なオブジェクトの初出現（カニ・ドラゴン・ヴォイドクラブ・ヘラルド・バロン）と25/30分
VOICE_MARKS = [175, 300, 480, 900, 1200, 1500, 1800]
VOICE_LEAD_SEC = 90  # 各節目のこの秒数前（1分半前）にも、その時点の経過時間を読み上げる


def elapsed_text(sec):
    """175 → '2分55秒経過'、300 → '5分経過'。"""
    m, s = divmod(sec, 60)
    return f"{m}分{s}秒経過" if s else f"{m}分経過"


# (試合開始からの秒数, 読み上げる文) を時刻順に
VOICE_TIMES = sorted((t, elapsed_text(t)) for t in
                     {*VOICE_MARKS, *(m - VOICE_LEAD_SEC for m in VOICE_MARKS)})
# 途中参加・再接続（前回の試合時間が無い）とき、節目からこれ以上過ぎていたら読まない（一斉に読まない）
VOICE_LATE_SEC = 10
VOICE_ADVANCE_MAX = 60.0


def speak(text):
    """Windows 標準の音声合成（System.Speech）で読み上げる。終わるまで戻らないので別スレッドで呼ぶ。"""
    ps = ("Add-Type -AssemblyName System.Speech;"
          "(New-Object System.Speech.Synthesis.SpeechSynthesizer).Speak($env:SPEAK_TEXT)")
    subprocess.run(["powershell", "-NoProfile", "-Command", ps],
                   env=dict(os.environ, SPEAK_TEXT=text), creationflags=NO_WINDOW)


def due_voice_lines(prev_time, now, announced):
    """前回の試合時間 prev_time から now までに来た節目のうち、まだ読んでいないもの。

    試合を追えている間は、練習ツールの早送りで飛び越えた節目も読む（一度に複数越えたら最後の1つだけ）。
    途中参加・再接続（prev_time < 0）では遅すぎる節目は読まない。
    """
    due = [(sec, text) for sec, text in VOICE_TIMES
           if sec not in announced and prev_time < sec <= now
           and (prev_time >= 0 or now - sec < VOICE_LATE_SEC)]
    return due[-1:]


# --- 通常攻撃の射程 -------------------------------------------------------------
# Data Dragon の attackrange は Lv1 の値のみ。レベルで射程が伸びるチャンピオンは最大値を固定で持つ。
# LoL Wiki の各記事より（2026-10 / パッチ 16.20 時点）。変わったらここを書き換える
# チャンピオンID → (Lv1の射程, 最大射程, 最大になるLv)
RANGE_SCALING = {
    "Tristana": (550, 718, 18),  # パッシブ: 0〜167.65（レベル比例）
    "Kayle": (175, 625, 16),     # Lv6 で 525、Lv16 で 625
    "Gnar": (400, 500, 18),      # ミニナー: 175 + 225〜325（レベル比例）。メガナーは 175
}


# 形態が変わるチャンピオン。Data Dragon のスキル名は「A/B」と両形態を併記しているが、
# 射程は片方（A）の形態の値しか無いので、もう一方（B）の形態の射程を固定で持つ。
# LoL Wiki の各記事より（2026-10 時点）。'' は射程なし（自身対象など）
# チャンピオンID → (もう一方の形態名, その形態の通常攻撃射程, {スキルキー: 射程})
ALT_FORMS = {
    "Jayce": ("キャノン", 500, {"Q": "1050", "W": "", "E": "650"}),
    "Elise": ("蜘蛛", 125, {"Q": "475", "W": "", "E": "825"}),
    "Nidalee": ("クーガー", 125, {"Q": "", "W": "375", "E": ""}),
    "Gnar": ("メガ", 175, {"Q": "1150", "W": "550", "E": "675"}),
}


def attack_range_text(champ):
    """'射程 550' / レベルで伸びる場合は '射程 550→718 (Lv18)'。
    形態が変わる場合はもう一方の形態の射程を ' / 蜘蛛 125' のように添える。"""
    scaling = RANGE_SCALING.get(champ["id"])
    if scaling:
        lv1, top, lv = scaling
        text = f"射程 {lv1}→{top} (Lv{lv})"
    else:
        text = f"射程 {round(champ['stats']['attackrange'])}"
    alt = ALT_FORMS.get(champ["id"])
    if alt:
        text += f" / {alt[0]} {alt[1]}"
    return text


def champ_spell_range_text(champ, key, spell):
    """スキルの射程。形態が変わる場合はスキル名の『A/B』に合わせて '600/1050' と並べる（無い側は '—'）。"""
    own = spell_range_text(spell.get("rangeBurn", ""))
    alt = ALT_FORMS.get(champ["id"])
    if not alt or key not in alt[2]:
        return own
    other = spell_range_text(alt[2][key])
    return f"{own or '—'}/{other or '—'}" if own or other else ""


# --- パッシブ説明 (LoL JP Wiki) ------------------------------------------------
# パッシブだけは LoL 日本語 Wiki のチャンピオンページから説明文をそのまま表示する。
# 敵として出てきたチャンピオンのページだけを取りに行き、パッチごとにキャッシュする。
JPWIKI = "https://www.loljp-wiki.jp/wiki/"
JPWIKI_UA = {"User-Agent": "LoL_CT_Tool/1.0 (personal cooldown viewer)"}
_PASSIVE_RE = re.compile(
    r'<dl class="[^"]*\bpassive\b[^"]*">\s*<dt>(.*?)</dt>\s*<dd>(.*?)</dd>\s*</dl>', re.S)


def _norm(name):
    return re.sub(r"[^a-z0-9]", "", name.lower())


def html_to_text(s):
    s = re.sub(r"<br[^>]*>", "\n", s)
    s = re.sub(r"</p>\s*", "\n", s)
    s = re.sub(r"<[^>]+>", "", s)
    lines = [line.strip() for line in html.unescape(s).splitlines()]
    return "\n".join(line for line in lines if line)


def cd_range(burn):
    """'8/7.5/7/6.5/6' → '8→6'、'6' → '6'、CD無し → '—'。"""
    vals = [v for v in burn.split("/") if v]
    if not vals or vals == ["0"]:
        return "—"
    return vals[0] if len(set(vals)) == 1 else f"{vals[0]}→{vals[-1]}"


def spell_range_text(burn):
    """'1150' → '1150'、'1000/1100/1200' → '1000→1200'、5000以上 → '全域'。
    25000 は自身対象にも全域にも使われていて区別できないので、0・self と同じく '' を返す。"""
    vals = [v for v in burn.split("/") if v]
    try:
        nums = [float(v) for v in vals]
    except ValueError:
        return ""
    if not nums or max(nums) <= 0 or max(nums) >= 25000:
        return ""
    if min(nums) >= 5000:
        return "全域"
    return cd_range("/".join(vals))


def passive_cd_summary(text):
    """JP Wiki の説明文から最初の『CD: …』『固定CD: …』を拾って要約（無ければ ''）。"""
    m = re.search(r"^(?:固定)?CD\s*[:：]\s*([\d./]+)", text, re.M)
    return cd_range(m.group(1).strip("/")) + "s" if m else ""


def _http_text(url, timeout=20, headers=None):
    req = urllib.request.Request(url, headers=headers or {})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", errors="replace")


class JpWikiPassives:
    """チャンピオンID → {"name", "text", "url"} を JP Wiki から取得（失敗時は None）。"""

    def __init__(self, version):
        self.version = version
        self.dir = CACHE_DIR / "jpwiki" / version
        self._pages = None  # 正規化名 → Wiki のページ名
        self._en_names = None  # チャンピオンID → 英語名

    def _load_index(self):
        if self._pages is not None:
            return
        self.dir.mkdir(parents=True, exist_ok=True)
        old_root = CACHE_DIR / "jpwiki"
        for old in old_root.iterdir():
            if old.is_dir() and old != self.dir:
                for f in old.iterdir():
                    f.unlink()
                old.rmdir()
        index = self.dir / "_index.json"
        if index.exists():
            data = json.loads(index.read_text(encoding="utf-8"))
        else:
            listing = _http_text(f"{JPWIKI}?Champion", headers=JPWIKI_UA)
            pages = sorted({urllib.parse.unquote_plus(html.unescape(p)) for p in
                            re.findall(r'href="[^"]*\?Champion/([^"#&]+)"', listing)})
            en = http_json(f"{DDRAGON}/cdn/{self.version}/data/en_US/champion.json")["data"]
            data = {"pages": pages, "en_names": {cid: c["name"] for cid, c in en.items()}}
            index.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
        self._pages = {_norm(p): p for p in data["pages"]}
        self._en_names = data["en_names"]

    def _page_for(self, champ_id):
        for key in (self._en_names.get(champ_id, ""), champ_id):
            page = self._pages.get(_norm(key))
            if page:
                return page
        return None

    def get(self, champ_id):
        path = self.dir / f"{champ_id}.json"
        if path.exists():
            return json.loads(path.read_text(encoding="utf-8"))
        self._load_index()
        page = self._page_for(champ_id)
        if not page:
            return None
        url = JPWIKI + "?" + urllib.parse.quote(f"Champion/{page}", safe="/")
        m = _PASSIVE_RE.search(_http_text(url, headers=JPWIKI_UA))
        if not m:
            return None
        info = {"name": html_to_text(m.group(1)).replace("\n", " "),
                "text": html_to_text(m.group(2)), "url": url}
        path.write_text(json.dumps(info, ensure_ascii=False), encoding="utf-8")
        return info


# --- LCU (LoL クライアント) ---------------------------------------------------
class Lcu:
    """lockfile から接続情報を読み、クライアントの API を叩く。"""

    def __init__(self):
        self.lol_dir = DEFAULT_LOL_DIR
        self._last_lookup = 0.0

    def _find_lol_dir(self):
        # 既定パス以外にインストールされている場合、起動中プロセスから探す（重いので30秒に1回）
        if time.time() - self._last_lookup < 30:
            return
        self._last_lookup = time.time()
        try:
            out = subprocess.run(
                ["powershell", "-NoProfile", "-Command",
                 "(Get-CimInstance Win32_Process -Filter \"name='LeagueClientUx.exe'\").ExecutablePath"],
                capture_output=True, text=True, timeout=10,
                creationflags=NO_WINDOW).stdout.strip()
            if out:
                self.lol_dir = Path(out.splitlines()[0]).parent
        except Exception:
            pass

    def _credentials(self):
        lockfile = self.lol_dir / "lockfile"
        if not lockfile.exists():
            self._find_lol_dir()
            lockfile = self.lol_dir / "lockfile"
            if not lockfile.exists():
                return None
        parts = lockfile.read_text().split(":")
        return parts[2], parts[3]

    def get(self, path):
        """クライアント未起動なら None。"""
        cred = self._credentials()
        if not cred:
            return None
        port, password = cred
        auth = base64.b64encode(f"riot:{password}".encode()).decode()
        return http_json(f"https://127.0.0.1:{port}{path}", timeout=2, context=_LOCAL_SSL,
                         headers={"Authorization": f"Basic {auth}"})


# --- 敵リストの抽出 -----------------------------------------------------------
def resolve_champion(player, by_id_lower, by_name):
    raw = player.get("rawChampionName", "")
    prefix = "game_character_displayname_"
    if raw.startswith(prefix):
        c = by_id_lower.get(raw[len(prefix):].lower())
        if c:
            return c
    name = player.get("championName", "")
    return by_name.get(name) or by_id_lower.get(name.lower().replace(" ", "").replace("'", ""))


def player_id(p):
    return p.get("riotId") or p.get("summonerName") or ""


def sort_enemies(enemies, my_pos):
    """enemies: [(champ or None, position, fallback_name)]。対面→ロール順に並べる。"""
    def key(e):
        pos = e[1]
        lane = 0 if my_pos and pos == my_pos else 1
        order = POSITION_ORDER.index(pos) if pos in POSITION_ORDER else len(POSITION_ORDER)
        return (lane, order)
    return sorted(enemies, key=key)


def enemies_from_game(game, by_id_lower, by_name):
    """Live Client の allgamedata から (自分のposition, 敵リスト)。"""
    players = game.get("allPlayers", [])
    active = game.get("activePlayer", {})
    me_ids = {active.get("riotId"), active.get("summonerName")} - {None, ""}
    me = next((p for p in players if player_id(p) in me_ids or p.get("summonerName") in me_ids), None)
    my_team = me["team"] if me else "ORDER"
    my_pos = (me or {}).get("position", "")
    enemies = [(resolve_champion(p, by_id_lower, by_name), p.get("position", ""),
                p.get("championName", "?"))
               for p in players if p.get("team") != my_team]
    return my_pos, sort_enemies(enemies, my_pos)


def enemies_from_champ_select(session, by_key):
    """LCU の champ-select session から (自分のposition, 公開済みの敵リスト, 敵の人数)。"""
    me = next((p for p in session.get("myTeam", [])
               if p.get("cellId") == session.get("localPlayerCellId")), {})
    my_pos = LCU_POSITION.get(me.get("assignedPosition", ""), "")
    their = session.get("theirTeam", [])
    enemies = []
    for p in their:
        champ = by_key.get(str(p.get("championId", 0)))
        if champ:
            enemies.append((champ, LCU_POSITION.get(p.get("assignedPosition", ""), ""), champ["name"]))
    return my_pos, sort_enemies(enemies, my_pos), len(their)


# --- 常駐・スタートアップ登録 ---------------------------------------------------
def acquire_single_instance():
    """常駐の二重起動防止。取得できたソケットを返す（プロセス終了まで保持）。"""
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.bind(("127.0.0.1", SINGLE_INSTANCE_PORT))
        s.listen(1)
        return s
    except OSError:
        s.close()
        return None


def load_settings():
    try:
        return {**DEFAULT_SETTINGS, **json.loads(SETTINGS_PATH.read_text(encoding="utf-8"))}
    except Exception:
        return dict(DEFAULT_SETTINGS)


def save_settings(settings):
    SETTINGS_PATH.parent.mkdir(parents=True, exist_ok=True)
    SETTINGS_PATH.write_text(json.dumps(settings, ensure_ascii=False), encoding="utf-8")


def resident_command():
    """常駐モードで起動するための (実行ファイル, 引数文字列)。"""
    if FROZEN:
        return Path(sys.executable), "--resident"
    pythonw = Path(sys.executable).with_name("pythonw.exe")
    if not pythonw.exists():
        pythonw = Path(sys.executable)
    return pythonw, f'"{Path(__file__).resolve()}" --resident'


def is_startup_registered():
    return STARTUP_LINK.exists()


def is_resident_running():
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.settimeout(0.3)
        return s.connect_ex(("127.0.0.1", SINGLE_INSTANCE_PORT)) == 0


def start_resident():
    if is_resident_running():
        return
    exe, args = resident_command()
    subprocess.Popen(f'"{exe}" {args}', cwd=APP_DIR, creationflags=NO_WINDOW,
                     close_fds=True)


def install_startup():
    exe, args = resident_command()
    ps = (
        "$s = (New-Object -ComObject WScript.Shell).CreateShortcut($env:LINK);"
        "$s.TargetPath = $env:TARGET; $s.Arguments = $env:ARGS;"
        "$s.WorkingDirectory = $env:WORKDIR; $s.Save()"
    )
    env = dict(os.environ, LINK=str(STARTUP_LINK), TARGET=str(exe), ARGS=args,
               WORKDIR=str(APP_DIR))
    subprocess.run(["powershell", "-NoProfile", "-Command", ps], env=env, check=True,
                   creationflags=NO_WINDOW)
    return f"スタートアップに登録しました: {STARTUP_LINK}"


def uninstall_startup():
    if STARTUP_LINK.exists():
        STARTUP_LINK.unlink()
        return "スタートアップ登録を解除しました。"
    return "スタートアップには登録されていません。"


# --- UI -----------------------------------------------------------------------
class App:
    def __init__(self, root, mock_path=None, resident=False):
        self.root = root
        self.mock_path = mock_path
        self.resident = resident
        self.settings = load_settings()
        self.lcu = Lcu()
        self.champs = None
        self.by_id_lower = {}
        self.by_name = {}
        self.by_key = {}
        self.jpwiki = None
        self.passives = {}  # チャンピオンID → JP Wiki のパッシブ情報（取得失敗は None）
        self.passive_requests = queue.Queue()
        self.passive_pending = set()
        self.version = "?"
        self.last_signature = None
        self.last_render = None  # (enemies, my_pos) パッシブ取得後の再描画用
        self.collapsed_cards = set()  # 折りたたんだチャンピオンID（既定は展開）
        self.expanded_passives = set()  # 説明文を開いたパッシブ（既定は折りたたみ）
        self.defaults_applied = set()  # 対面判明時の既定（対面以外は閉じる）を適用済みのID
        self.results = queue.Queue()
        self.polling = False
        self.visible = True
        self.dismissed = False  # 常駐時、ユーザーが閉じたら次の試合まで出さない
        self.updated_to = None  # 更新済みのバージョン（同じ起動中に二重に差し替えない）
        self.game_time = -1  # 前回ポーリング時の試合時間（秒）。試合外は -1
        self.announced = set()  # この試合で読み上げ済みの節目（VOICE_TIMES の秒数）
        self.voice_gen = 0  # 試合が変わるたびに増やす（前の試合で予約した読み上げを無効にする）
        self.voice_queue = queue.Queue()  # 読み上げ待ちの文（重ならないよう1件ずつ読む）

        root.title(f"LoL 敵スキルCD一覧 v{VERSION}")
        # 画面に収まる高さにする（タスクバー分を空ける）
        height = min(780, root.winfo_screenheight() - 90)
        root.geometry(f"720x{height}")
        root.configure(bg=BG)
        root.protocol("WM_DELETE_WINDOW", self._on_close)

        top = tk.Frame(root, bg=BG)
        top.pack(fill="x", padx=10, pady=(8, 2))
        self.status = tk.Label(top, text="データ読み込み中…", bg=BG, fg=SUB,
                               anchor="w", font=("Yu Gothic UI", 10))
        self.status.pack(side="left", fill="x", expand=True)
        if resident:
            tk.Button(top, text="終了", command=self._quit, bg=CARD_BG, fg=FG, relief="flat",
                      activebackground=CARD_HL, activeforeground=FG).pack(side="right")
        bar = tk.Frame(root, bg=BG)
        bar.pack(fill="x", padx=10)
        tk.Label(bar, text="※ 秒・ランク順の基本CD（ヘイスト等は未反映）",
                 bg=BG, fg=SUB, anchor="w", font=("Yu Gothic UI", 9)).pack(side="left")
        # スキルの並びの切り替え（並び方を図にしたアイコン）
        tk.Label(bar, text="並び:", bg=BG, fg=SUB,
                 font=("Yu Gothic UI", 9)).pack(side="left", padx=(8, 2))
        self.layout_icons = {}
        for layout, tip, cells in SPELL_LAYOUTS:
            icon = tk.Canvas(bar, width=26, height=22, bg=CARD_BG, highlightthickness=1,
                             cursor="hand2")
            icon.pack(side="left", padx=1)
            icon.bind("<Button-1>", lambda e, l=layout: self._set_layout(l))
            icon.bind("<Enter>", lambda e, t=tip: self._flash(f"スキルの並び: {t}"))
            self.layout_icons[layout] = (icon, cells)
        self._draw_layout_icons()
        btn = dict(bg=CARD_BG, fg=FG, relief="flat", activebackground=CARD_HL,
                   activeforeground=FG, font=("Yu Gothic UI", 9), padx=5, pady=0)
        # 右から順に並ぶので逆順で追加
        for text, kwargs in [("P説明を閉じる", {"passives": False}), ("P説明を開く", {"passives": True}),
                             ("全員たたむ", {"cards": False}), ("全員ひらく", {"cards": True})]:
            tk.Button(bar, text=text, command=lambda k=kwargs: self._set_all(**k),
                      **btn).pack(side="right", padx=(4, 0))

        opts = tk.Frame(root, bg=BG)
        opts.pack(fill="x", padx=6)
        check = dict(bg=BG, fg=FG, selectcolor=CARD_BG, activebackground=BG,
                     activeforeground=FG, font=("Yu Gothic UI", 9))
        self.autostart_var = tk.BooleanVar(value=is_startup_registered())
        tk.Checkbutton(opts, text="Windows起動時に自動で常駐", variable=self.autostart_var,
                       command=self._toggle_autostart, **check).pack(side="left")
        self.client_var = tk.BooleanVar(value=self.settings["show_on"] == "client")
        tk.Checkbutton(opts, text="クライアント起動時から表示（常駐時）", variable=self.client_var,
                       command=self._toggle_show_on, **check).pack(side="left")
        # 2段目: タイマー音声（左）と更新の確認（右）。1段に並べると幅に収まらない
        opts = tk.Frame(root, bg=BG)
        opts.pack(fill="x", padx=6)
        self.voice_var = tk.BooleanVar(value=self.settings["timer_voice"])
        tk.Checkbutton(opts, text="タイマー音声", variable=self.voice_var,
                       command=self._toggle_voice, **check).pack(side="left")
        self.advance_var = tk.StringVar(value=f"{self.settings['voice_advance']:.1f}")
        advance = tk.Spinbox(opts, from_=0.0, to=VOICE_ADVANCE_MAX, increment=0.1, format="%.1f",
                             width=4, textvariable=self.advance_var, command=self._set_voice_advance,
                             bg=CARD_BG, fg=FG, buttonbackground=CARD_BG, insertbackground=FG,
                             relief="flat", font=("Consolas", 9))
        advance.pack(side="left")
        advance.bind("<Return>", lambda e: self._set_voice_advance())
        advance.bind("<FocusOut>", lambda e: self._set_voice_advance())
        tk.Label(opts, text="秒早く", bg=BG, fg=SUB,
                 font=("Yu Gothic UI", 9)).pack(side="left", padx=(2, 0))
        labels = dict(UPDATE_DAY_CHOICES)
        self.update_var = tk.StringVar(
            value=labels.get(self.settings["update_days"], f"{self.settings['update_days']}日ごと"))
        menu = tk.OptionMenu(opts, self.update_var, *labels.values(),
                             command=self._set_update_days)
        menu.configure(bg=CARD_BG, fg=FG, activebackground=CARD_HL, activeforeground=FG,
                       relief="flat", highlightthickness=0, font=("Yu Gothic UI", 9), pady=0)
        menu["menu"].configure(bg=CARD_BG, fg=FG, font=("Yu Gothic UI", 9))
        self.check_btn = tk.Button(opts, text="今すぐ確認", command=self._check_update_now,
                                   bg=CARD_BG, fg=FG, relief="flat", activebackground=CARD_HL,
                                   activeforeground=FG, font=("Yu Gothic UI", 9), padx=5, pady=0)
        self.check_btn.pack(side="right", padx=(4, 0))
        menu.pack(side="right")
        tk.Label(opts, text="更新の確認:", bg=BG, fg=SUB,
                 font=("Yu Gothic UI", 9)).pack(side="right")

        # サモナースペルCD一覧（スクロールしない固定表示）
        self.summ_frame = tk.Frame(root, bg=CARD_BG)
        self.summ_frame.pack(fill="x", padx=10, pady=(4, 0))
        self.summ_icons = []  # PhotoImage の参照を保持（GC で消えないように）
        self._build_timer_bar()

        container = tk.Frame(root, bg=BG)
        container.pack(fill="both", expand=True, padx=6, pady=6)
        self.canvas = tk.Canvas(container, bg=BG, highlightthickness=0)
        sb = tk.Scrollbar(container, orient="vertical", command=self.canvas.yview)
        self.inner = tk.Frame(self.canvas, bg=BG)
        self.inner.bind("<Configure>",
                        lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.inner_id = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.canvas.bind("<Configure>",
                         lambda e: self.canvas.itemconfigure(self.inner_id, width=e.width))
        self.canvas.configure(yscrollcommand=sb.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        root.bind_all("<MouseWheel>",
                      lambda e: self.canvas.yview_scroll(int(-e.delta / 120), "units"))

        if resident:
            self._set_visible(False)

        threading.Thread(target=self._load_data, daemon=True).start()
        threading.Thread(target=self._voice_worker, daemon=True).start()
        threading.Thread(target=update_worker, daemon=True,
                         args=(lambda v: self.results.put(("updated", v)),)).start()
        self.root.after(100, self._drain)

    # --- window control --------------------------------------------------
    def _set_visible(self, visible):
        if visible == self.visible:
            return
        self.visible = visible
        if visible:
            self.root.deiconify()
            self.root.lift()
        else:
            self.root.withdraw()

    def _on_close(self):
        if self.resident:
            self.dismissed = True
            self._set_visible(False)
        else:
            self._quit()

    def _quit(self):
        self.root.destroy()

    def _toggle_autostart(self):
        try:
            if self.autostart_var.get():
                install_startup()
                start_resident()  # 登録したらすぐ常駐も開始
                self._flash("自動起動を有効にしました（常駐を開始）")
            else:
                uninstall_startup()
                self._flash("自動起動を解除しました")
        except Exception as e:
            self.autostart_var.set(is_startup_registered())
            self._flash(f"設定に失敗しました: {e}")

    def _set_update_days(self, label):
        days = next(d for d, l in UPDATE_DAY_CHOICES if l == label)
        self.settings = {**load_settings(), "update_days": days}
        save_settings(self.settings)
        self._flash(f"更新の確認: {label}")

    def _check_update_now(self):
        if not FROZEN or VERSION == "dev":
            self._flash("開発版（exe 以外）のため更新の確認はできません")
            return
        if self.updated_to:
            self._flash(f"{self.updated_to} に更新済みです（次回起動から反映）")
            return
        self.check_btn.configure(state="disabled")
        self._flash("更新を確認中…")

        def work():
            try:
                latest = apply_update()
                LAST_UPDATE_CHECK_PATH.parent.mkdir(parents=True, exist_ok=True)
                LAST_UPDATE_CHECK_PATH.write_text(str(time.time()))
                self.results.put(("check_done", latest))
            except Exception as e:
                self.results.put(("check_error", str(e)))
        threading.Thread(target=work, daemon=True).start()

    def _toggle_show_on(self):
        self.settings["show_on"] = "client" if self.client_var.get() else "champselect"
        save_settings(self.settings)

    def _toggle_voice(self):
        self.settings = {**load_settings(), "timer_voice": self.voice_var.get()}
        save_settings(self.settings)
        self._flash("タイマー音声: " + ("オン（" + "・".join(elapsed_text(m).replace("経過", "") for m in VOICE_MARKS)
                                       + " と、その1分半前に読み上げ）" if self.voice_var.get() else "オフ"))

    def _set_voice_advance(self):
        """入力された秒数を 0.0〜VOICE_ADVANCE_MAX に収めて保存（数値でなければ元に戻す）。"""
        try:
            sec = min(max(round(float(self.advance_var.get()), 1), 0.0), VOICE_ADVANCE_MAX)
        except ValueError:
            sec = load_settings()["voice_advance"]
        self.advance_var.set(f"{sec:.1f}")
        if sec != load_settings()["voice_advance"]:
            self.settings = {**load_settings(), "voice_advance": sec}
            save_settings(self.settings)
            self._flash(f"タイマー音声: 節目の {sec:.1f} 秒前に読み上げ")

    def _voice_worker(self):
        while True:
            text = self.voice_queue.get()
            try:
                speak(text)
            except Exception:
                pass  # 音声合成が使えない環境でも本体は動かす

    def _announce_time(self, game):
        """試合時間が節目を越えたら読み上げる（タイマー音声がオンのときだけ）。

        設定の秒数（voice_advance）だけ早めた時刻で判定する。ポーリング間隔（POLL_MS）より
        細かく合わせるため、次のポーリングまでに来る節目はその時刻に予約して読む。
        """
        now = (game.get("gameData") or {}).get("gameTime")
        if now is None:
            return
        if now < self.game_time:  # 時間が戻った = 別の試合
            self.announced.clear()
            self.voice_gen += 1
        # 設定はファイルから読み直す（別プロセスのウィンドウでの変更を常駐側にも反映）
        advance = load_settings()["voice_advance"]
        prev = self.game_time + advance if self.game_time >= 0 else -1
        self.game_time = now
        now += advance
        self._speak_lines(due_voice_lines(prev, now, self.announced))
        gen = self.voice_gen
        for sec, text in VOICE_TIMES:
            if sec not in self.announced and now < sec <= now + POLL_MS / 1000:
                self.root.after(int((sec - now) * 1000),
                                lambda s=sec, t=text: gen == self.voice_gen
                                and s not in self.announced and self._speak_lines([(s, t)]))

    def _speak_lines(self, lines):
        if not lines:
            return
        self.announced.update(sec for sec, _ in lines)
        # 常駐と手動起動のウィンドウが同時に動いているときは常駐側だけが読む（二重に鳴らさない）
        if not load_settings()["timer_voice"] or (not self.resident and is_resident_running()):
            return
        for _, text in lines:
            self.voice_queue.put(text)

    def _draw_layout_icons(self):
        """各アイコンにマスの並びを描き、選択中のものを金色で強調する。"""
        for layout, (icon, cells) in self.layout_icons.items():
            selected = layout == self.settings["spell_layout"]
            color = GOLD if selected else SUB
            icon.configure(highlightbackground=GOLD if selected else CARD_BG,
                           highlightcolor=GOLD if selected else CARD_BG)
            icon.delete("all")
            cols = max(c for c, _ in cells) + 1
            rows = max(r for _, r in cells) + 1
            cw, ch = 20 / cols, 16 / rows  # 余白を除いた描画領域 20×16 を等分
            for c, r in cells:
                x, y = 4 + c * cw, 4 + r * ch
                icon.create_rectangle(x, y, x + cw - 2, y + ch - 2, fill=color, outline="")

    def _set_layout(self, layout):
        self.settings = {**load_settings(), "spell_layout": layout}
        save_settings(self.settings)
        self._draw_layout_icons()
        self._rerender()

    def _flash(self, msg):
        self.status.configure(text=msg)

    # --- background work -------------------------------------------------
    def _load_data(self):
        try:
            version, champs = load_champion_data()
            self.results.put(("data", (version, champs)))
        except Exception as e:
            self.results.put(("data_error", str(e)))
            return
        try:
            self.results.put(("summoners", load_summoners(version)))
        except Exception:
            pass  # 取れなくても本体は動かす

    def _build_summoner_bar(self, spells):
        for w in self.summ_frame.winfo_children():
            w.destroy()
        self.summ_icons = []
        for col, (sid, name, cd, sub, icon_path) in enumerate(spells):
            self.summ_frame.columnconfigure(col, weight=1, uniform="summ")
            cell = tk.Frame(self.summ_frame, bg=CARD_BG)
            cell.grid(row=0, column=col, sticky="n", pady=4)
            try:
                img = tk.PhotoImage(file=str(icon_path)).subsample(2)  # 64px → 32px
                self.summ_icons.append(img)
                tk.Label(cell, image=img, bg=CARD_BG).pack()
            except tk.TclError:
                pass
            tk.Label(cell, text=name, bg=CARD_BG, fg=FG, font=("Yu Gothic UI", 8)).pack()
            tk.Label(cell, text=cd, bg=CARD_BG, fg=GOLD, pady=0,
                     font=("Consolas", 10, "bold")).pack()
            if sub:
                tk.Label(cell, text=sub, bg=CARD_BG, fg=SUB, pady=0,
                         font=("Yu Gothic UI", 7)).pack()

    def _build_timer_bar(self):
        frame = tk.Frame(self.root, bg=CARD_BG)
        frame.pack(fill="x", padx=10, pady=(4, 0))
        for col, (name, value, sub) in enumerate(TIMERS):
            frame.columnconfigure(col, weight=1, uniform="timer")
            cell = tk.Frame(frame, bg=CARD_BG)
            cell.grid(row=0, column=col, sticky="n", pady=4)
            tk.Label(cell, text=name, bg=CARD_BG, fg=FG, font=("Yu Gothic UI", 8)).pack()
            tk.Label(cell, text=value, bg=CARD_BG, fg=GOLD, pady=0,
                     font=("Consolas", 10, "bold")).pack()
            tk.Label(cell, text=sub, bg=CARD_BG, fg=SUB, pady=0,
                     font=("Yu Gothic UI", 7)).pack()

    def _passive_worker(self):
        """敵チャンピオンのパッシブを1件ずつ JP Wiki から取得（サイトに負荷をかけないよう直列）。"""
        while True:
            champ_id = self.passive_requests.get()
            try:
                info = self.jpwiki.get(champ_id)
            except Exception:
                info = None  # Wiki に繋がらなくても本体は動かす（公式の説明文で代替）
            self.results.put(("passive", (champ_id, info)))
            time.sleep(0.5)

    def _fetch_state(self):
        """('game', allgamedata) / ('champselect', session) / ('client', phase) / ('none', None)"""
        try:
            if self.mock_path:
                game = json.loads(Path(self.mock_path).read_text(encoding="utf-8"))
                self.results.put(("state", ("game", game)))
                return
            try:
                self.results.put(("state", ("game", http_json(LIVE_URL, timeout=2,
                                                               context=_LOCAL_SSL))))
                return
            except Exception:
                pass
            phase = self.lcu.get("/lol-gameflow/v1/gameflow-phase")
            if phase is None:
                self.results.put(("state", ("none", None)))
            elif phase == "ChampSelect":
                session = self.lcu.get("/lol-champ-select/v1/session")
                self.results.put(("state", ("champselect", session)))
            else:
                self.results.put(("state", ("client", phase)))
        except Exception:
            self.results.put(("state", ("none", None)))

    def _schedule_poll(self):
        if not self.polling:
            self.polling = True
            threading.Thread(target=self._fetch_state, daemon=True).start()

    # --- UI thread -------------------------------------------------------
    def _drain(self):
        try:
            while True:
                kind, payload = self.results.get_nowait()
                if kind == "data":
                    self.version, self.champs = payload
                    self.by_id_lower = {k.lower(): c for k, c in self.champs.items()}
                    self.by_name = {c["name"]: c for c in self.champs.values()}
                    self.by_key = {c["key"]: c for c in self.champs.values()}
                    if self.jpwiki is None:
                        self.jpwiki = JpWikiPassives(self.version)
                        threading.Thread(target=self._passive_worker, daemon=True).start()
                    self._set_status("試合待機中…")
                    self._schedule_poll()
                elif kind == "summoners":
                    self._build_summoner_bar(payload)
                elif kind == "updated":
                    self.updated_to = payload
                    self.root.title(f"LoL 敵スキルCD一覧 v{VERSION}（{payload} に更新済み・次回起動から反映）")
                elif kind == "check_done":
                    self.check_btn.configure(state="normal")
                    if payload:
                        self.results.put(("updated", payload))
                        self._flash(f"{payload} に更新しました（次回起動から反映）")
                    else:
                        self._flash(f"最新版です（v{VERSION}）")
                elif kind == "check_error":
                    self.check_btn.configure(state="normal")
                    self._flash(f"更新の確認に失敗しました: {payload}")
                elif kind == "passive":
                    champ_id, info = payload
                    self.passive_pending.discard(champ_id)
                    self.passives[champ_id] = info
                    if self.last_render:  # 表示中のカードに反映
                        self.last_signature = None
                        self._render(*self.last_render)
                elif kind == "data_error":
                    self._set_status(f"Data Dragon の取得に失敗: {payload}（10秒後に再試行）")
                    self.root.after(10000, lambda: threading.Thread(
                        target=self._load_data, daemon=True).start())
                elif kind == "state":
                    self.polling = False
                    self._apply_state(*payload)
                    self.root.after(POLL_MS, self._schedule_poll)
        except queue.Empty:
            pass
        self.root.after(100, self._drain)

    def _apply_state(self, kind, payload):
        if kind == "game":
            self._announce_time(payload)
            my_pos, enemies = enemies_from_game(payload, self.by_id_lower, self.by_name)
            if not enemies:
                self._set_status("試合中（敵プレイヤー情報なし）")
            else:
                self._set_status(f"試合中  |  敵 {len(enemies)} 人")
                self._render(enemies, my_pos)
            active = True
        elif kind == "champselect":
            my_pos, enemies, total = enemies_from_champ_select(payload or {}, self.by_key)
            self._set_status(f"ピック画面  |  敵 {len(enemies)}/{total} 人公開"
                             + ("（試合開始時に全員表示）" if len(enemies) < total else ""))
            self._render(enemies, my_pos)
            active = True
        else:
            self.game_time = -1
            self.announced.clear()
            self.voice_gen += 1
            if self.last_signature is not None:
                self.last_signature = None
                self.last_render = None
                # 試合が終わったら開閉状態をリセット
                self.collapsed_cards.clear()
                self.expanded_passives.clear()
                self.defaults_applied.clear()
                self._clear()
            if kind == "client":
                self._set_status(f"クライアント起動中（{payload}）…ピック画面で敵を表示します")
            else:
                self._set_status("LoL 未起動 / 試合待機中…")
            if self.resident:
                self.settings = load_settings()  # 通常ウィンドウ側での設定変更を反映
            active = kind == "client" and (self.settings["show_on"] == "client"
                                           or payload in SHOW_PHASES)

        if self.resident:
            if not active:
                self.dismissed = False  # 試合が終わったらリセット
            self._set_visible(active and not self.dismissed)

    def _set_status(self, msg):
        self.status.configure(text=f"パッチ {self.version}  |  {msg}")

    def _clear(self):
        for w in self.inner.winfo_children():
            w.destroy()

    def _render(self, enemies, my_pos):
        signature = (my_pos, tuple((c["id"] if c else name, pos) for c, pos, name in enemies))
        if signature == self.last_signature:
            return
        self.last_signature = signature
        self.last_render = (enemies, my_pos)
        # 対面が分かっていれば対面だけ開き、他は閉じる（各チャンピオン初回のみ。手動の開閉は尊重）
        if my_pos and any(pos == my_pos for _, pos, _ in enemies):
            for champ, pos, _ in enemies:
                if champ and champ["id"] not in self.defaults_applied:
                    self.defaults_applied.add(champ["id"])
                    if pos != my_pos:
                        self.collapsed_cards.add(champ["id"])
        for champ, _, _ in enemies:
            if champ and champ["id"] not in self.passives and champ["id"] not in self.passive_pending:
                self.passive_pending.add(champ["id"])
                self.passive_requests.put(champ["id"])
        self._clear()
        for champ, pos, name in enemies:
            self._add_card(champ, pos, name, bool(my_pos) and pos == my_pos)

    def _rerender(self):
        if self.last_render:
            self.last_signature = None
            self._render(*self.last_render)

    def _toggle(self, ids, cid):
        ids.symmetric_difference_update({cid})
        self._rerender()

    def _set_all(self, cards=None, passives=None):
        """表示中の全チャンピオンについて、カード/パッシブの開閉をまとめて切り替える。"""
        ids = {c["id"] for c, _, _ in (self.last_render or ([], None))[0] if c}
        if cards is not None:
            self.collapsed_cards = set() if cards else set(ids)
        if passives is not None:
            self.expanded_passives = set(ids) if passives else set()
        self._rerender()

    def _add_card(self, champ, position, fallback_name, is_lane):
        bg = CARD_HL if is_lane else CARD_BG
        card = tk.Frame(self.inner, bg=bg, highlightthickness=2 if is_lane else 0,
                        highlightbackground=GOLD)
        card.pack(fill="x", padx=4, pady=2)

        pos = POSITION_LABEL.get(position, "")
        name = champ["name"] if champ else fallback_name
        cid = champ["id"] if champ else None
        card_open = cid not in self.collapsed_cards
        header = f"{'▼' if card_open else '▶'} {name}"
        if pos:
            header += f"  [{pos}]"
        if is_lane:
            header += "  ★対面"
        head_row = tk.Frame(card, bg=bg)
        head_row.pack(fill="x", padx=8, pady=(2, 0))
        head = tk.Label(head_row, text=header, bg=bg, fg=GOLD if is_lane else FG, anchor="w",
                        cursor="hand2", font=("Yu Gothic UI", 11, "bold"))
        head.pack(side="left", fill="x", expand=True)

        if not champ:
            tk.Label(card, text="チャンピオンデータが見つかりません", bg=bg, fg=SUB,
                     anchor="w").pack(fill="x", padx=8, pady=(0, 6))
            return
        head.bind("<Button-1>", lambda e: self._toggle(self.collapsed_cards, cid))
        tk.Label(head_row, text=attack_range_text(champ), bg=bg, fg=SUB,
                 font=("Yu Gothic UI", 9)).pack(side="right")

        # P: JP Wiki の説明文をそのまま表示（取得できなければ Data Dragon の公式説明文）
        if cid not in self.passives:
            passive_name, passive_text = champ["passive"]["name"], "JP Wiki から取得中…"
        elif self.passives[cid]:
            passive_name, passive_text = self.passives[cid]["name"], self.passives[cid]["text"]
        else:
            passive_name = champ["passive"]["name"]
            passive_text = html_to_text(champ["passive"]["description"]) + "\n（公式の説明文）"
        passive_cd = passive_cd_summary(passive_text)

        if not card_open:
            # 折りたたみ時は全スキルのCDを1行に要約（ランク1→最大ランク）。射程があれば括弧で添える
            parts = [f"P {passive_cd}"] if passive_cd else []
            for key, spell in zip(SPELL_KEYS, champ["spells"]):
                part = f"{key} {cd_range(spell.get('cooldownBurn', ''))}"
                spell_range = champ_spell_range_text(champ, key, spell)
                parts.append(f"{part}({spell_range})" if spell_range else part)
            summary = tk.Label(card, text="   ".join(parts), bg=bg, fg=PASSIVE_FG, anchor="w",
                               cursor="hand2", font=("Consolas", 10))
            summary.pack(fill="x", padx=(28, 8), pady=(0, 4))
            summary.bind("<Button-1>", lambda e: self._toggle(self.collapsed_cards, cid))
            return

        grid = tk.Frame(card, bg=bg)
        grid.pack(fill="x", padx=8, pady=(0, 3))
        layout = self.settings["spell_layout"]
        if layout == "row":
            # 列: [キー, 名前/CD] × 4（Q W E R を横一列。CDは名前の下）
            for c in (1, 3, 5, 7):
                grid.columnconfigure(c, weight=1, uniform="name")
            last_col = 7
        elif layout == "column":
            # 列: [キー, 名前, CD]（Q / W / E / R を縦に1行ずつ）
            grid.columnconfigure(1, weight=1)
            last_col = 2
        else:
            # 列: [キー, 名前, CD] × 2（Q W / E R の2×2配置）。名前列を伸ばしてCDを右寄せ
            # CD列は最長の値に合わせた固定幅、名前列は均等にして、全カードで列位置を揃える
            cd_width = tkfont.Font(family="Consolas", size=10).measure("0" * 21)
            for c in (1, 4):
                grid.columnconfigure(c, weight=1, uniform="name")
            for c in (2, 5):
                grid.columnconfigure(c, minsize=cd_width)
            last_col = 5

        passive_open = cid in self.expanded_passives
        tk.Label(grid, text="P", bg=bg, fg=KEY_FG, width=2, pady=0,
                 font=("Consolas", 10, "bold")).grid(row=0, column=0, sticky="nw")
        p_name = tk.Label(grid, text=f"{passive_name}  {'▼' if passive_open else '▶ 説明を表示'}",
                          bg=bg, fg=FG, anchor="w", cursor="hand2", pady=0,
                          font=("Yu Gothic UI", 9))
        p_name.grid(row=0, column=1, columnspan=last_col - 1, sticky="w", padx=(2, 8))
        p_name.bind("<Button-1>", lambda e: self._toggle(self.expanded_passives, cid))
        tk.Label(grid, text=passive_cd or "", bg=bg, fg=FG, anchor="e", pady=0,
                 font=("Consolas", 10)).grid(row=0, column=last_col, sticky="e")
        if passive_open:
            # Tk は半角スペースで優先的に改行するため、日本語文中では折り返しが不自然になる
            tk.Label(grid, text=passive_text.replace(" ", " "), bg=bg, fg=PASSIVE_FG,
                     anchor="w", justify="left",
                     wraplength=600, font=("Yu Gothic UI", 9)
                     ).grid(row=1, column=1, columnspan=last_col, sticky="w", padx=(2, 8), pady=(0, 4))

        for i, (key, spell) in enumerate(zip(SPELL_KEYS, champ["spells"])):
            cd = spell.get("cooldownBurn", "")
            cd_text = cd if cd and cd != "0" else "—"
            key_label = tk.Label(grid, text=key, bg=bg, fg=KEY_FG, width=2, pady=0,
                                 font=("Consolas", 10, "bold"))
            spell_range = champ_spell_range_text(champ, key, spell)
            name_text = f"{spell['name']}  {spell_range}" if spell_range else spell["name"]
            name_label = tk.Label(grid, text=name_text, bg=bg, fg=FG, anchor="w", pady=0,
                                  font=("Yu Gothic UI", 9))
            cd_label = tk.Label(grid, text=cd_text, bg=bg, fg=FG, anchor="w" if layout == "row" else "e",
                                pady=0, font=("Consolas", 10))
            if layout == "row":
                col = i * 2
                key_label.grid(row=2, column=col, sticky="w")
                name_label.grid(row=2, column=col + 1, sticky="w", padx=(2, 6))
                cd_label.grid(row=3, column=col + 1, sticky="w", padx=(2, 6))
            elif layout == "column":
                key_label.grid(row=2 + i, column=0, sticky="w")
                name_label.grid(row=2 + i, column=1, sticky="w", padx=(2, 6))
                cd_label.grid(row=2 + i, column=2, sticky="e")
            else:
                row, col = 2 + i // 2, (i % 2) * 3
                key_label.grid(row=row, column=col, sticky="w")
                name_label.grid(row=row, column=col + 1, sticky="w", padx=(2, 6))
                cd_label.grid(row=row, column=col + 2, sticky="e",
                              padx=(0, 14 if col == 0 else 0))


def main():
    ap = argparse.ArgumentParser(description="LoL 敵スキルCD一覧ツール")
    ap.add_argument("--mock", help="allgamedata 形式のJSONファイルを読み込んで表示（テスト用）")
    ap.add_argument("--resident", action="store_true",
                    help="常駐モード: 普段は非表示、ピック画面/試合中に自動表示")
    ap.add_argument("--show-on", choices=["champselect", "client"],
                    help="常駐時に表示するタイミングを設定して保存（champselect=ピック画面から）")
    ap.add_argument("--update-days", type=int, metavar="N",
                    help="N日ごとに新バージョンを確認するよう設定して保存（0=確認しない、既定7）")
    ap.add_argument("--install-startup", action="store_true",
                    help="Windows ログイン時に常駐モードで起動するよう登録")
    ap.add_argument("--uninstall-startup", action="store_true", help="スタートアップ登録を解除")
    args = ap.parse_args()

    if args.show_on:
        save_settings({**load_settings(), "show_on": args.show_on})
    if args.update_days is not None:
        save_settings({**load_settings(), "update_days": max(0, args.update_days)})
    if args.install_startup:
        print(install_startup())
        return
    if args.uninstall_startup:
        print(uninstall_startup())
        return

    lock = None
    if args.resident:
        lock = acquire_single_instance()
        if lock is None:
            return  # 既に常駐中
    root = tk.Tk()
    App(root, mock_path=args.mock, resident=args.resident)
    root.mainloop()


if __name__ == "__main__":
    main()

# exe をビルドする: powershell -ExecutionPolicy Bypass -File build.ps1
# 出力: dist\LoL_CT_Tool.exe
Set-Location $PSScriptRoot
if (-not (Test-Path .venv)) {
    python -m venv .venv
    .\.venv\Scripts\python -m pip install -q pyinstaller
}
.\.venv\Scripts\pyinstaller --noconfirm --onefile --noconsole --name LoL_CT_Tool `
    --distpath dist --workpath build lol_cd_tool.py

@echo off
REM Builds StratMonitor.exe (single file) into the "dist" folder.
cd /d "%~dp0"
python -m PyInstaller --noconfirm --clean --onefile --windowed ^
  --name StratMonitor ^
  --add-data "strat_guide.html;." ^
  --collect-data tzdata ^
  --collect-all curl_cffi ^
  --collect-all yfinance ^
  strat_monitor.py
if errorlevel 1 (
  echo Build failed.
  pause
  exit /b 1
)
if exist settings.json if not exist dist\settings.json copy settings.json dist\settings.json >nul
echo.
echo Done: dist\StratMonitor.exe
pause

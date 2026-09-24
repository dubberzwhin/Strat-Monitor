# Strat Monitor

A multi-timeframe monitor and playbook for The Strat. Uses Yahoo Finance data,
no account or API key needed.

## Download and run (Windows)
1. Go to Releases (right side of this page) and download `StratMonitor.exe`.
2. Put it in its own folder, for example `Documents\StratMonitor`.
   It saves your watchlist to `settings.json` in that same folder.
3. Double-click to run. The first launch takes a few seconds.
4. If Windows shows "Windows protected your PC", click **More info**, then **Run anyway**.
   This appears because the exe isn't code-signed.

## Run from source (Windows / Mac / Linux)
Requires Python 3.12+.
    pip install -r requirements.txt
    python strat_monitor.py

## Build the exe yourself
    pip install -r requirements.txt pyinstaller
    build_exe.bat
The exe is created in `dist\`.

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

## How to use

### The main screen
Each row is one stock. The four columns show the last three candles on the
1 Hour, 1 Day, 1 Week and 1 Month charts, labeled using Strat numbers:

| Label | Meaning | Color |
|---|---|---|
| `1` | Inside bar (inside the previous candle's range) | Yellow |
| `2u` | Took out the previous high | Green |
| `2d` | Took out the previous low | Red |
| `3` | Outside bar (took out both the high and the low) | Purple |

For example, `2d-1-2u` reads oldest to newest: a 2-Down, then an Inside bar,
then a 2-Up. The line under the labels shows the high and low of the most
recent candle. The hourly column only counts finished hours, so the candle
that's still forming is left out.

A **★** and a cyan ticker name mean the hourly or daily chart has a setup worth
watching: the latest candle is an inside bar, or the recent candles contain a
`1-1` or `3-1`.

### Opening a playbook
Click any row to open that stock's playbook. It shows an hourly candle chart,
active Strat patterns, trigger levels, timeframe continuity and more.
- **⬅ Back to Main Monitor** returns to the table.
- **⬇ Export as HTML** saves the playbook as a file you can open in a browser
  or share.

### Adding a stock
1. Type the symbol in the **Stock** box (for example `AMD`).
2. Optional: type an ETF in the **ETF Home** box (for example `SMH`). This is
   the sector or industry ETF the playbook compares the stock against. Leave it
   blank and the app picks one based on the stock's industry.
3. Click **Add Pair** or press Enter.

Futures work too: `/ES`, `/NQ` and `/YM`. You can also type `SPX`, `NDX` or
`DJI`, which the app tracks using SPY, QQQ and DIA.

### Changing a stock's ETF
Click the row, click **Back**, type the new ETF in the **ETF Home** box, then
click **Set ETF**. Click **Set ETF** with the box empty to go back to the
automatic choice.

### Removing a stock
Click the row, click **Back**, then click **Remove Selected**.

### How often it updates
Pick a **Pull Rate** from the dropdown:
- **1 / 5 / 15 / 30 Minutes**: refreshes on that interval.
- **46m Past Hour** (default): refreshes once an hour, at 46 minutes past.

Click **🔄 Refresh Now** to update immediately.

### Strat Guide
**📖 Strat Guide** opens a study guide to The Strat inside the app. Use
**↗ Open in Browser** to view it in your web browser instead.

## Your settings
Everything saves automatically: your watchlist, ETF choices and pull rate.
There's no Save button. They're stored in a `settings.json` file in the same
folder as `StratMonitor.exe`.

- **Updating to a new version:** replace only the exe and keep `settings.json`.
  Your watchlist carries over.
- **Moving to another PC or backing up:** copy `settings.json` along with the exe.
- **Starting fresh:** close the app and delete `settings.json`. It comes back
  with the default watchlist.
- **Sharing a watchlist:** send someone your `settings.json` and have them put
  it next to their exe.

Keep the exe in its own folder, not loose on your Desktop or in Downloads, so
`settings.json` stays with it.

## Troubleshooting
- **A row stays on "Awaiting Data..."**: the symbol may be wrong, or Yahoo
  Finance doesn't have data for it. Check the symbol on finance.yahoo.com.
- **"Data for X is still loading"** when you click a row: wait for the first
  refresh to finish (the status line under the title shows progress).
- **The first launch is slow**: the app unpacks itself each time it starts.
  This is normal and takes a few seconds.

## Disclaimer
This tool is for education and research only. It is not financial advice.
Market data comes from Yahoo Finance and may be delayed or inaccurate.

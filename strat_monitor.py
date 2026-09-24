import sys
import math
import datetime
import time
from zoneinfo import ZoneInfo
import json
import os
import threading
import webbrowser
from concurrent.futures import ThreadPoolExecutor, as_completed
import yfinance as yf
import pandas as pd
from PySide6.QtCore import Qt, QTimer, Slot, Signal, QObject, QRectF, QUrl
from PySide6.QtGui import (
    QFont, QColor, QBrush, QTextCharFormat, QTextCursor,
    QPainter, QPen, QFontMetricsF
)
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QTableWidget, QTableWidgetItem, QLabel, QHeaderView, QPushButton,
    QLineEdit, QComboBox, QMessageBox, QStackedWidget, QTextEdit,
    QTextBrowser, QFileDialog
)
# QtWebEngine renders the full HTML/CSS/SVG Strat guide in-app. Optional: if the
# module is unavailable we fall back to opening the guide in the system browser.
try:
    from PySide6.QtWebEngineWidgets import QWebEngineView
    HAS_WEBENGINE = True
except Exception:
    QWebEngineView = None
    HAS_WEBENGINE = False

# When frozen into an exe (PyInstaller), settings live next to the exe so they persist,
# while bundled read-only files are unpacked to sys._MEIPASS.
if getattr(sys, "frozen", False):
    APP_DIR = os.path.dirname(os.path.abspath(sys.executable))
    BUNDLE_DIR = getattr(sys, "_MEIPASS", APP_DIR)
else:
    APP_DIR = os.path.dirname(os.path.abspath(__file__))
    BUNDLE_DIR = APP_DIR

SETTINGS_FILE = os.path.join(APP_DIR, "settings.json")
# The Strat study guide ships next to the script and opens in the default browser
# (it's a full HTML/CSS/SVG page that QTextBrowser can't render). A copy next to the
# exe overrides the bundled one.
GUIDE_FILE = os.path.join(APP_DIR, "strat_guide.html")
if not os.path.exists(GUIDE_FILE):
    GUIDE_FILE = os.path.join(BUNDLE_DIR, "strat_guide.html")

DEFAULT_WATCHLIST = [
    {"ticker": "/ES", "etf": "SPY"},
    {"ticker": "/NQ", "etf": "QQQ"},
    {"ticker": "/YM", "etf": "DIA"},
    {"ticker": "AAPL", "etf": "XLK"},
    {"ticker": "AMZN", "etf": "XLY"},
    {"ticker": "GOOGL", "etf": "XLC"},
    {"ticker": "META", "etf": "XLC"},
    {"ticker": "MSFT", "etf": "XLK"},
    {"ticker": "NVDA", "etf": "SMH"},
    {"ticker": "TSLA", "etf": "XLY"}
]

TICKER_MAP = {
    "/ES": "ES=F", "/NQ": "NQ=F", "/YM": "YM=F",
    "SPX": "SPY", "XSP": "SPY", "NDX": "QQQ", "DJI": "DIA"
}

STRAT_COLORS = {
    "1": "#ffbc42",
    "2u": "#5fdd8e",
    "2d": "#ff6b6b",
    "3": "#cc88ff",
    "N/A": "#FFFFFF"
}

# ── risk / reward ────────────────────────────────────────────────────────────
OPT_RR_DRAWDOWN = 0.50                       # options R/R risk = this fraction of the entry premium
STOP_RULE = f"option −{OPT_RR_DRAWDOWN:.0%} or losing the trigger level in force"
OPT_HOLD_DAYS  = {'daily': 1, 'swing': 3}    # trading days of theta charged before the target prints
RISK_FREE_RATE = 0.04


def _norm_cdf(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def _bs_d1(S, K, T, sigma, r):
    return (math.log(S / K) + (r + 0.5 * sigma * sigma) * T) / (sigma * math.sqrt(T))


def bs_price(S, K, T, sigma, is_call, r=RISK_FREE_RATE):
    """Black-Scholes value of a European option; intrinsic at/after expiry."""
    if S <= 0 or K <= 0:
        return 0.0
    if T <= 0 or sigma <= 0:
        return max(0.0, S - K) if is_call else max(0.0, K - S)
    d1 = _bs_d1(S, K, T, sigma, r)
    d2 = d1 - sigma * math.sqrt(T)
    disc = K * math.exp(-r * T)
    if is_call:
        return S * _norm_cdf(d1) - disc * _norm_cdf(d2)
    return disc * _norm_cdf(-d2) - S * _norm_cdf(-d1)


def bs_delta(S, K, T, sigma, is_call, r=RISK_FREE_RATE):
    if S <= 0 or K <= 0 or T <= 0 or sigma <= 0:
        itm = S > K if is_call else S < K
        return (1.0 if is_call else -1.0) if itm else 0.0
    n = _norm_cdf(_bs_d1(S, K, T, sigma, r))
    return n if is_call else n - 1.0


def implied_vol(price, S, K, T, is_call):
    """Volatility that reprices `price` under Black-Scholes, or None when the
    quote sits outside what any volatility in 1%-500% can produce."""
    if price <= 0 or T <= 0 or S <= 0 or K <= 0:
        return None
    lo, hi = 0.01, 5.0
    if not (bs_price(S, K, T, lo, is_call) < price < bs_price(S, K, T, hi, is_call)):
        return None
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if bs_price(S, K, T, mid, is_call) < price:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def _add_trading_days(dt, n):
    """Step forward n weekdays (market holidays are not skipped)."""
    while n > 0:
        dt += datetime.timedelta(days=1)
        if dt.weekday() < 5:
            n -= 1
    return dt


# ── breadth: cap-weight vs equal-weight ETF mapping ──────────────────────────
# GICS sector (as reported by yfinance .info['sector']) → (cap-weight SPDR,
# Invesco S&P 500 Equal Weight). Used to auto-derive a stock's SECTOR breadth
# pair so the user no longer has to assign it manually. Edit a ticker here if a
# breadth row shows "data unavailable" — Invesco renamed this series in 2024.
SECTOR_ETF_MAP = {
    "Technology":             ("XLK",  "RSPT"),
    "Financial Services":     ("XLF",  "RSPF"),
    "Healthcare":             ("XLV",  "RSPH"),
    "Consumer Cyclical":      ("XLY",  "RSPD"),
    "Consumer Defensive":     ("XLP",  "RSPS"),
    "Energy":                 ("XLE",  "RSPG"),
    "Industrials":            ("XLI",  "RSPN"),
    "Basic Materials":        ("XLB",  "RSPM"),
    "Utilities":              ("XLU",  "RSPU"),
    "Real Estate":            ("XLRE", "RSPR"),
    "Communication Services": ("XLC",  "RSPC"),
}

# yfinance .info['industry'] → cap-weight theme/industry ETF (the "ETF Home").
# Used to AUTO-assign a tighter home than the broad sector. Falls back to the
# sector cap ETF (then SPY) when unmapped. The cap ETF is the most representative
# instrument (iShares US / VanEck / Invesco KBW); its equal-weight twin — for the
# Industry breadth ratio — is resolved via ETF_EQUAL_WEIGHT_MAP below. Industries
# with a genuine cap-vs-equal pair get a real breadth row; the rest still get a
# sharper confirmation ETF but no breadth ratio.
INDUSTRY_ETF_MAP = {
    # Technology
    "Semiconductors":                           "SMH",
    "Semiconductor Equipment & Materials":      "SMH",
    "Software - Infrastructure":                "IGV",   # no equal twin
    "Software - Application":                   "IGV",   # no equal twin
    "Solar":                                    "TAN",   # no equal twin
    # Healthcare
    "Biotechnology":                            "IBB",
    "Drug Manufacturers - General":             "PPH",
    "Drug Manufacturers - Specialty & Generic": "PPH",
    "Medical Devices":                          "IHI",
    "Medical Instruments & Supplies":           "IHI",
    "Health Information Services":              "IHF",
    "Medical Care Facilities":                  "IHF",
    "Healthcare Plans":                         "IHF",
    # Industrials
    "Aerospace & Defense":                      "ITA",
    "Airlines":                                 "JETS",  # no equal twin
    "Railroads":                                "IYT",
    "Trucking":                                 "IYT",
    "Integrated Freight & Logistics":           "IYT",
    "Marine Shipping":                          "IYT",
    "Residential Construction":                 "ITB",
    "Building Products & Equipment":            "ITB",
    # Energy
    "Oil & Gas E&P":                            "IEO",
    "Oil & Gas Exploration & Production":       "IEO",
    "Oil & Gas Equipment & Services":           "OIH",
    # Financials
    "Banks - Diversified":                      "KBWB",
    "Banks - Regional":                         "KBWR",
    "Insurance - Diversified":                  "IAK",
    "Insurance - Property & Casualty":          "IAK",
    "Insurance - Life":                         "IAK",
    "Insurance - Specialty":                    "IAK",
    "Capital Markets":                          "IAI",
    "Asset Management":                         "IAI",
    "Financial Data & Stock Exchanges":         "IAI",
    # Basic Materials
    "Other Industrial Metals & Mining":         "PICK",
    "Steel":                                    "PICK",
    "Aluminum":                                 "PICK",
    "Copper":                                   "PICK",
    "Gold":                                     "GDX",   # no equal twin
    "Other Precious Metals & Mining":           "GDX",   # no equal twin
    # Consumer Cyclical
    "Internet Retail":                          "RTH",
    "Specialty Retail":                         "RTH",
    "Discount Stores":                          "RTH",
    "Department Stores":                        "RTH",
    "Apparel Retail":                           "RTH",
    "Auto Manufacturers":                       "CARZ",  # no equal twin
    # Communication
    "Communication Equipment":                  "IYZ",
    "Telecom Services":                         "IYZ",
}

# Cap-weight ETF → its equal-weight counterpart. Pairs the "ETF Home" (manual or
# auto-assigned) with an equal-weight twin for the Industry/Theme breadth ratio.
# SPDR "S&P" (X-series / KBE / KRE / KCE / KIE) ETFs are equal-weight; their cap
# counterparts are iShares "US", VanEck, or Invesco KBW. Map to "" when no clean
# equal-weight product exists: the ETF still drives sector-confirmation, but the
# breadth ratio row is skipped (honest — there's nothing to ratio against).
ETF_EQUAL_WEIGHT_MAP = {
    # market + GICS sectors
    "SPY": "RSP",  "QQQ": "QQQE", "DIA": "",
    "XLK": "RSPT", "XLF": "RSPF", "XLV": "RSPH", "XLY": "RSPD",
    "XLP": "RSPS", "XLE": "RSPG", "XLI": "RSPN", "XLB": "RSPM",
    "XLU": "RSPU", "XLRE": "RSPR", "XLC": "RSPC",
    # industry pairs (cap → equal)
    "SMH": "XSD",  "SOXX": "XSD", "IBB": "XBI", "PPH": "XPH",
    "IHI": "XHE",  "IHF": "XHS",  "ITA": "XAR",
    "IYT": "XTN",  "ITB": "XHB",  "IEO": "XOP", "OIH": "XES",
    "KBWB": "KBE", "KBWR": "KRE", "IAK": "KIE", "IAI": "KCE",
    "PICK": "XME", "RTH": "XRT",  "IYZ": "XTL",
    # theme ETFs with no clean equal-weight twin (breadth ratio skipped):
    "JETS": "", "GDX": "", "TAN": "", "IGV": "", "CARZ": "",
}

# Market layer is constant: cap-weight S&P 500 vs equal-weight S&P 500.
MARKET_BREADTH_PAIR = ("SPY", "RSP")

# (label, trailing trading-day lookback, "in line" threshold on the cap-eq spread)
BREADTH_TIMEFRAMES = [
    ("Daily",     1, 0.0010),
    ("Weekly",    5, 0.0025),
    ("Monthly",  21, 0.0050),
    ("Quarterly", 63, 0.0075),
]

# A stock at/above this market cap is treated as a mega-cap leader, for which
# cap-weight outperformance is *confirming* rather than a breadth warning.
MEGA_CAP_THRESHOLD = 500e9


class WorkerSignals(QObject):
    data_ready = Signal(dict)
    status_update = Signal(str)
    playbook_ready = Signal(str, int)


class CandleChartWidget(QWidget):
    """Interactive 1h candlestick chart. Price on the Y axis, time on the X axis
    labelled in New York time. On hover it draws a crosshair (vertical line
    snapped to the candle under the cursor), a date/time flyout on the X axis, a
    price flyout on the Y axis, and an O/H/L/C flyout for that candle."""
    BG, GRID, TXT = QColor("#0d0f12"), QColor("#1e2530"), QColor("#8a9ab0")
    UP, DN, CROSS = QColor("#5fdd8e"), QColor("#ff6b6b"), QColor("#6b7a8d")

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMouseTracking(True)
        self.setFixedHeight(380)
        self.setCursor(Qt.CursorShape.CrossCursor)
        self._t = []                                   # NY-time timestamps
        self._o = self._h = self._l = self._c = []     # OHLC arrays
        self._v = []                                   # volume
        self._geo = None
        self._mx = self._my = None                     # last mouse pos (or None)

    @staticmethod
    def _fmt_vol(v):
        if v >= 1e9: return f"{v / 1e9:.2f}B"
        if v >= 1e6: return f"{v / 1e6:.2f}M"
        if v >= 1e3: return f"{v / 1e3:.1f}K"
        return f"{v:.0f}"

    def set_data(self, df, n_bars=120):
        self._geo = None
        self._mx = self._my = None
        self._t = []
        self._o = self._h = self._l = self._c = self._v = []
        if df is not None and not getattr(df, "empty", True) and len(df) >= 2:
            try:
                d = df.tail(n_bars)
                self._o = d["Open"].to_numpy(dtype=float)
                self._h = d["High"].to_numpy(dtype=float)
                self._l = d["Low"].to_numpy(dtype=float)
                self._c = d["Close"].to_numpy(dtype=float)
                self._v = (d["Volume"].to_numpy(dtype=float)
                           if "Volume" in d.columns else [0.0] * len(d))
                # Cached index is naive UTC -> re-attach UTC, convert to New York.
                idx = pd.to_datetime(d.index)
                try:
                    self._t = list(idx.tz_localize("UTC").tz_convert("America/New_York"))
                except TypeError:
                    self._t = list(idx.tz_convert("America/New_York"))
            except Exception:
                self._t = []
        self.update()

    # ── geometry helpers ──────────────────────────────────────────────────
    def _compute_geo(self):
        n = len(self._t)
        if n < 1:
            return None
        W, H = self.width(), self.height()
        left, right, top, bottom = 58, 14, 12, 42
        gap = 10
        plot_w = W - left - right
        avail = H - top - bottom            # split between price pane and volume pane
        if plot_w <= 20 or avail <= 50:
            return None
        vol_h = max(40, avail * 0.22)
        price_h = avail - vol_h - gap
        pmin, pmax = float(self._l.min()), float(self._h.max())
        if pmax <= pmin:
            pmax = pmin + 1.0
        pad = (pmax - pmin) * 0.06
        pmin -= pad; pmax += pad
        try:
            vmax = float(max(self._v)) if len(self._v) else 0.0
        except Exception:
            vmax = 0.0
        return dict(n=n, W=W, H=H, left=left, top=top, plot_w=plot_w,
                    price_h=price_h, vol_top=top + price_h + gap, vol_h=vol_h,
                    pmin=pmin, pmax=pmax, span=pmax - pmin, slot=plot_w / n,
                    vmax=vmax if vmax > 0 else 1.0)

    def _y_of(self, g, price):
        return g["top"] + g["price_h"] * (1.0 - (price - g["pmin"]) / g["span"])

    def _x_of(self, g, i):
        return g["left"] + g["slot"] * (i + 0.5)

    def _idx_at(self, g, x):
        return max(0, min(g["n"] - 1, int((x - g["left"]) / g["slot"])))

    # ── painting ──────────────────────────────────────────────────────────
    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.fillRect(self.rect(), self.BG)
        g = self._geo = self._compute_geo()
        f = QFont("Arial"); f.setPixelSize(11); p.setFont(f)
        if g is None:
            p.setPen(self.TXT)
            p.drawText(self.rect(), int(Qt.AlignCenter), "No hourly data")
            return

        # horizontal gridlines + price labels
        for k in range(6):
            price = g["pmin"] + g["span"] * k / 5
            y = self._y_of(g, price)
            p.setPen(QPen(self.GRID, 1))
            p.drawLine(int(g["left"]), int(y), int(g["left"] + g["plot_w"]), int(y))
            p.setPen(self.TXT)
            p.drawText(QRectF(0, y - 8, g["left"] - 6, 16),
                       int(Qt.AlignRight | Qt.AlignVCenter), f"{price:.2f}")

        # candles + volume bars (volume pane shares the candle's up/down colour)
        body = max(1.0, g["slot"] * 0.6)
        vbase = g["vol_top"] + g["vol_h"]
        for i in range(g["n"]):
            o, h, l, c = self._o[i], self._h[i], self._l[i], self._c[i]
            cx = self._x_of(g, i)
            col = self.UP if c >= o else self.DN
            p.setPen(QPen(col, 1))
            p.drawLine(int(cx), int(self._y_of(g, h)), int(cx), int(self._y_of(g, l)))
            yo, yc = self._y_of(g, o), self._y_of(g, c)
            p.fillRect(QRectF(cx - body / 2, min(yo, yc), body, max(1.0, abs(yc - yo))), col)
            vh = g["vol_h"] * (self._v[i] / g["vmax"]) if len(self._v) else 0.0
            if vh > 0:
                p.fillRect(QRectF(cx - body / 2, vbase - vh, body, vh),
                           QColor(col.red(), col.green(), col.blue(), 140))

        # "Vol" tag in the volume pane
        p.setPen(self.TXT)
        p.drawText(QRectF(g["left"] + 4, g["vol_top"] + 2, 60, 14),
                   int(Qt.AlignLeft | Qt.AlignTop), "Vol")

        # x-axis time labels in New York time (below the volume pane)
        p.setPen(self.TXT)
        step = max(1, g["n"] // min(7, g["n"]))
        y_lab = vbase + 6
        for i in range(0, g["n"], step):
            cx = self._x_of(g, i)
            lx = min(max(cx - 44, 0.0), g["W"] - 88)
            p.drawText(QRectF(lx, y_lab, 88, 16),
                       int(Qt.AlignHCenter | Qt.AlignTop), self._t[i].strftime("%m/%d %H:%M"))

        if self._mx is not None and self._my is not None:
            self._draw_crosshair(p, g, f)

    def _draw_crosshair(self, p, g, f):
        mx, my = self._mx, self._my
        if mx < g["left"] or mx > g["left"] + g["plot_w"]:
            return
        i = self._idx_at(g, mx)
        cx = self._x_of(g, i)
        price_top, price_bot = g["top"], g["top"] + g["price_h"]
        vol_bot = g["vol_top"] + g["vol_h"]
        cy = min(max(my, price_top), price_bot)        # horizontal line stays in price pane
        p.setPen(QPen(self.CROSS, 1, Qt.PenStyle.DashLine))
        p.drawLine(int(cx), int(price_top), int(cx), int(vol_bot))     # snapped, spans both panes
        p.drawLine(int(g["left"]), int(cy), int(g["left"] + g["plot_w"]), int(cy))

        # date/time flyout on the X axis (below the volume pane)
        self._tag(p, f, self._t[i].strftime("%a %m/%d  %H:%M"),
                  cx, vol_bot + 3, anchor="bottom")
        # price flyout on the Y axis (left), at the cursor height
        price = g["pmin"] + (1.0 - (cy - g["top"]) / g["price_h"]) * g["span"]
        self._tag(p, f, f"{price:.2f}", g["left"] - 2, cy, anchor="left")
        # O/H/L/C/V flyout for the hovered candle
        o, h, l, c = self._o[i], self._h[i], self._l[i], self._c[i]
        up = c >= o
        lines = [self._t[i].strftime("%a %m/%d  %H:%M NY"),
                 f"O  {o:.2f}", f"H  {h:.2f}", f"L  {l:.2f}", f"C  {c:.2f}",
                 f"V  {self._fmt_vol(self._v[i]) if len(self._v) else 'n/a'}"]
        self._ohlc_box(p, f, lines, up, g, cx)

    def _tag(self, p, f, text, ax, ay, anchor):
        """Filled label. anchor 'bottom' = centered horizontally, top edge at ay;
        'left' = right edge at ax, centered vertically at ay."""
        fm = QFontMetricsF(f)
        tw, th = fm.horizontalAdvance(text) + 12, fm.height() + 6
        if anchor == "bottom":
            x, y = ax - tw / 2, ay
        else:  # left
            x, y = ax - tw, ay - th / 2
        x = min(max(x, 0), self.width() - tw)
        y = min(max(y, 0), self.height() - th)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#2b323c"))
        p.drawRoundedRect(QRectF(x, y, tw, th), 3, 3)
        p.setPen(QColor("#e6edf3"))
        p.drawText(QRectF(x, y, tw, th), int(Qt.AlignCenter), text)

    def _ohlc_box(self, p, f, lines, up, g, near_x):
        fm = QFontMetricsF(f)
        tw = max(fm.horizontalAdvance(s) for s in lines) + 18
        lh = fm.height() + 2
        th = lh * len(lines) + 10
        x = near_x + 14                      # prefer right of cursor; flip if it'd overflow
        if x + tw > g["left"] + g["plot_w"]:
            x = near_x - 14 - tw
        x = min(max(x, g["left"]), self.width() - tw)
        y = g["top"] + 6
        p.setPen(QPen(QColor("#2e3540"), 1))
        p.setBrush(QColor(18, 22, 28, 235))
        p.drawRoundedRect(QRectF(x, y, tw, th), 4, 4)
        ty = y + 5
        for k, s in enumerate(lines):
            p.setPen(QColor("#e6edf3") if k == 0 else (self.UP if up else self.DN))
            p.drawText(QRectF(x + 9, ty, tw - 14, lh), int(Qt.AlignLeft | Qt.AlignVCenter), s)
            ty += lh

    # ── mouse ─────────────────────────────────────────────────────────────
    def mouseMoveEvent(self, e):
        pos = e.position()
        self._mx, self._my = pos.x(), pos.y()
        self.update()

    def leaveEvent(self, _e):
        self._mx = self._my = None
        self.update()


class StratMonitorApp(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("THE STRAT MULTI-TIMEFRAME MONITOR & PLAYBOOK")
        self.resize(1250, 900)
        self.setStyleSheet("background-color: #0d0f12; color: #f0f0f0;")

        self.is_fetching = False
        self.raw_df_cache = {}
        self.current_playbook_row = None
        self.selected_expiry = None
        self.current_playbook_html = ""
        self.load_settings()

        self.signals = WorkerSignals()
        self.signals.data_ready.connect(self.update_table_data)
        self.signals.status_update.connect(self.set_status_text)
        self.signals.playbook_ready.connect(self._on_playbook_ready)

        self.stacked_widget = QStackedWidget()
        self.setCentralWidget(self.stacked_widget)

        self.guide_view = None          # QWebEngineView, built lazily on first open
        self.guide_page_index = None
        self.init_monitor_ui()
        self.init_playbook_ui()
        # NOTE: the guide page (QtWebEngine/Chromium) is built on first click, not
        # here — constructing it eagerly spins up Chromium and slows app startup.

        self.stacked_widget.setCurrentIndex(0)
        self.start_data_thread()

        self.master_timer = QTimer()
        self.master_timer.timeout.connect(self.handle_timing_engine)
        self.master_timer.start(5000)
        self.last_run_hour = -1

        # Warm up the guide page in the background a few seconds after launch, so
        # the first click is instant — without the eager-build startup penalty.
        # The window is already shown and the data fetch already running by then.
        QTimer.singleShot(4000, self._warm_guide)

    # ─────────────────────────────────────────────────────────── settings ──

    def load_settings(self):
        if os.path.exists(SETTINGS_FILE):
            try:
                with open(SETTINGS_FILE, "r") as f:
                    config = json.load(f)
                    self.watchlist = config.get("watchlist", DEFAULT_WATCHLIST)
                    self.refresh_mode = config.get("refresh_mode", "46m Past Hour")
            except Exception:
                self.watchlist = json.loads(json.dumps(DEFAULT_WATCHLIST))
                self.refresh_mode = "46m Past Hour"
        else:
            self.watchlist = json.loads(json.dumps(DEFAULT_WATCHLIST))
            self.refresh_mode = "46m Past Hour"
        self.last_interval_sync = time.time()

    def save_settings(self):
        try:
            with open(SETTINGS_FILE, "w") as f:
                json.dump({"watchlist": self.watchlist, "refresh_mode": self.refresh_mode}, f, indent=4)
        except Exception as e:
            print(f"Error saving config: {e}")

    # ─────────────────────────────────────────────────── sector resolution ──

    def resolve_sector_info(self, ticker):
        """Look up a ticker's GICS sector, industry and mega-cap status.
        Returns (sector_or_None, industry_or_None, is_mega_bool).
        One network call via .info."""
        yf_symbol = TICKER_MAP.get(ticker, ticker)
        try:
            info = yf.Ticker(yf_symbol).info
            sector = info.get("sector")
            industry = info.get("industry")
            market_cap = info.get("marketCap") or 0
            return sector, industry, (market_cap >= MEGA_CAP_THRESHOLD)
        except Exception:
            return None, None, False

    def fetch_earnings_info(self, obj):
        """Pull the most-recent (reported) and next (scheduled) earnings dates for
        a ticker via yfinance. Returns a dict with last/next dates, the reported
        vs estimated EPS for the last print, the surprise %, and the estimate for
        the next print. All keys may be None (futures/ETFs have no earnings, or the
        feed is empty). One network call; failures degrade silently to None."""
        out = {'last_date': None, 'last_actual': None, 'last_estimate': None,
               'last_surprise': None, 'next_date': None, 'next_estimate': None}
        try:
            df = obj.get_earnings_dates(limit=24)
        except Exception:
            df = None
        if df is None or getattr(df, "empty", True):
            return out
        try:
            df = df.sort_index()
            idx = df.index
            try:
                now = pd.Timestamp.now(tz=idx.tz)
            except Exception:
                now = pd.Timestamp.now()

            def _col(row, name):
                if name in row and pd.notna(row[name]):
                    return float(row[name])
                return None

            past = df[idx <= now]
            future = df[idx > now]
            if not past.empty:
                ts, r = past.index[-1], past.iloc[-1]
                out['last_date']     = ts.to_pydatetime()
                out['last_actual']   = _col(r, 'Reported EPS')
                out['last_estimate'] = _col(r, 'EPS Estimate')
                out['last_surprise'] = _col(r, 'Surprise(%)')
            if not future.empty:
                ts, r = future.index[0], future.iloc[0]
                out['next_date']     = ts.to_pydatetime()
                out['next_estimate'] = _col(r, 'EPS Estimate')
        except Exception:
            pass
        return out

    def _auto_theme_etf(self, item):
        """Best theme/industry ETF for a stock: its industry ETF if mapped,
        else the sector cap ETF, else SPY."""
        industry = item.get("industry")
        if industry and industry in INDUSTRY_ETF_MAP:
            return INDUSTRY_ETF_MAP[industry]
        sec_cap, _ = SECTOR_ETF_MAP.get(item.get("sector") or "", (None, None))
        return sec_cap or "SPY"

    def ensure_sectors_resolved(self, watchlist):
        """Fill in 'sector' / 'industry' / 'mega_cap' for any item missing them,
        and auto-assign a theme ETF when the user left the ETF box blank.
        Runs inside the fetch thread (.info is slow) and persists once resolved
        so each ticker is only looked up a single time."""
        changed = False
        for item in watchlist:
            if "sector" in item and "industry" in item:
                continue
            self.signals.status_update.emit(f"Resolving sector: {item['ticker']}...")
            sector, industry, is_mega = self.resolve_sector_info(item["ticker"])
            item["sector"] = sector            # may be None (e.g. index futures)
            item["industry"] = industry
            item["mega_cap"] = is_mega
            # Auto-assign theme ETF only when the user did not specify one.
            if not item.get("etf"):
                item["etf"] = self._auto_theme_etf(item)
            changed = True
        if changed:
            self.save_settings()

    # ──────────────────────────────────────────────────────────── UI init ──

    def init_monitor_ui(self):
        page = QWidget()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(15, 15, 15, 15)

        control_layout = QHBoxLayout()
        control_layout.setSpacing(8)

        self.add_input = QLineEdit()
        self.add_input.setPlaceholderText("Stock (e.g. AMD)...")
        self.add_input.setStyleSheet(
            "background-color: #1a1e24; border: 1px solid #2e3540; padding: 6px; color: white; font-weight: bold;")
        control_layout.addWidget(self.add_input, 2)

        self.etf_input = QLineEdit()
        self.etf_input.setPlaceholderText("ETF Home (blank = auto)...")
        self.etf_input.setStyleSheet(
            "background-color: #1a1e24; border: 1px solid #2e3540; padding: 6px; color: #00FFFF; font-weight: bold;")
        self.etf_input.returnPressed.connect(self.add_ticker)
        control_layout.addWidget(self.etf_input, 2)

        add_btn = QPushButton("Add Pair")
        add_btn.setStyleSheet(
            "background-color: #007ACC; color: white; padding: 7px 12px; font-weight: bold; border: none;")
        add_btn.clicked.connect(self.add_ticker)
        control_layout.addWidget(add_btn)

        set_etf_btn = QPushButton("Set ETF")
        set_etf_btn.setToolTip("Apply the ETF box to the selected row "
                               "(blank = re-run automatic industry/sector assignment)")
        set_etf_btn.setStyleSheet(
            "background-color: #0E7490; color: white; padding: 7px 12px; font-weight: bold; border: none;")
        set_etf_btn.clicked.connect(self.set_etf_on_selected)
        control_layout.addWidget(set_etf_btn)

        remove_btn = QPushButton("Remove Selected")
        remove_btn.setStyleSheet(
            "background-color: #A82020; color: white; padding: 7px 12px; font-weight: bold; border: none;")
        remove_btn.clicked.connect(self.remove_ticker)
        control_layout.addWidget(remove_btn)

        control_layout.addWidget(QLabel("Pull Rate:"))
        self.rate_combo = QComboBox()
        self.rate_combo.addItems(["1 Minute", "5 Minutes", "15 Minutes", "30 Minutes", "46m Past Hour"])
        self.rate_combo.setCurrentText(self.refresh_mode)
        self.rate_combo.setStyleSheet(
            "background-color: #1a1e24; border: 1px solid #2e3540; padding: 5px; color: white;")
        self.rate_combo.currentTextChanged.connect(self.change_refresh_rate)
        control_layout.addWidget(self.rate_combo, 2)

        self.force_btn = QPushButton("🔄 Refresh Now")
        self.force_btn.setStyleSheet(
            "background-color: #2E7D32; color: white; padding: 7px 15px; font-weight: bold; border: none;")
        self.force_btn.clicked.connect(self.start_data_thread)
        control_layout.addWidget(self.force_btn)

        self.guide_btn = QPushButton("📖 Strat Guide")
        self.guide_btn.setToolTip("Open The Strat study guide in your browser")
        self.guide_btn.setStyleSheet(
            "background-color: #40207a; color: #d8a0ff; padding: 7px 15px; font-weight: bold; border: none;")
        self.guide_btn.clicked.connect(self.open_strat_guide)
        control_layout.addWidget(self.guide_btn)

        layout.addLayout(control_layout)

        self.title_label = QLabel("THE STRAT MULTI-TIMEFRAME MONITOR")
        self.title_label.setFont(QFont("Arial", 15, QFont.Weight.Bold))
        self.title_label.setStyleSheet("color: #ffffff; margin-top: 10px;")
        self.title_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(self.title_label)

        self.status_label = QLabel("Initializing monitor pipeline...")
        self.status_label.setFont(QFont("Arial", 10))
        self.status_label.setStyleSheet("color: #8a9ab0; margin-bottom: 8px;")
        self.status_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(self.status_label)

        self.table = QTableWidget()
        self.table.setColumnCount(5)
        self.table.setHorizontalHeaderLabels(["TICKER (ETF)", "1 HOUR", "1 DAY", "1 WEEK", "1 MONTH"])
        self.table.setStyleSheet("""
            QTableWidget { background-color: #16191f; gridline-color: #2e3540; border: 1px solid #2e3540; font-size: 13px; }
            QHeaderView::section { background-color: #1a1e24; color: #8a9ab0; padding: 8px; font-weight: bold; border: 1px solid #2e3540; }
        """)
        self.table.verticalHeader().setVisible(False)
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        self.table.cellClicked.connect(self.handle_row_clicked)
        layout.addWidget(self.table)

        self.stacked_widget.addWidget(page)
        self.rebuild_table_structure()

    def init_playbook_ui(self):
        page = QWidget()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(10, 10, 10, 10)

        nav_layout = QHBoxLayout()
        back_btn = QPushButton("⬅ Back to Main Monitor")
        back_btn.setStyleSheet("""
            QPushButton { background-color: #1a1e24; color: #ffffff; padding: 6px 14px;
                          font-weight: bold; border: 1px solid #2e3540; border-radius: 4px; }
            QPushButton:hover { background-color: #252b33; }
        """)
        back_btn.clicked.connect(lambda: self.stacked_widget.setCurrentIndex(0))
        nav_layout.addWidget(back_btn)
        nav_layout.addStretch()

        export_btn = QPushButton("⬇ Export as HTML")
        export_btn.setStyleSheet("""
            QPushButton { background-color: #1a3a5f; color: #7eb8ff; padding: 6px 14px;
                          font-weight: bold; border: 1px solid #2e5d9e; border-radius: 4px; }
            QPushButton:hover { background-color: #1e4a7a; }
        """)
        export_btn.clicked.connect(self.export_playbook_html)
        nav_layout.addWidget(export_btn)

        layout.addLayout(nav_layout)

        self.candle_chart = CandleChartWidget()
        layout.addWidget(self.candle_chart)

        self.playbook_text = QTextBrowser()
        self.playbook_text.setOpenLinks(False)
        self.playbook_text.setStyleSheet("QTextBrowser { background-color: #0d0f12; border: none; }")
        self.playbook_text.anchorClicked.connect(self.handle_playbook_link)
        layout.addWidget(self.playbook_text)

        self.stacked_widget.addWidget(page)

    def _ensure_guide_page(self):
        """Build the in-app guide page (QtWebEngine) on first use and return its
        stacked-widget index. Returns None when QtWebEngine is unavailable.
        Built lazily so launching Chromium never delays app startup."""
        if not HAS_WEBENGINE:
            return None
        if self.guide_page_index is not None:
            return self.guide_page_index
        page = QWidget()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(10, 10, 10, 10)

        nav_layout = QHBoxLayout()
        back_btn = QPushButton("⬅ Back to Main Monitor")
        back_btn.setStyleSheet("""
            QPushButton { background-color: #1a1e24; color: #ffffff; padding: 6px 14px;
                          font-weight: bold; border: 1px solid #2e3540; border-radius: 4px; }
            QPushButton:hover { background-color: #252b33; }
        """)
        back_btn.clicked.connect(lambda: self.stacked_widget.setCurrentIndex(0))
        nav_layout.addWidget(back_btn)
        nav_layout.addStretch()

        open_ext_btn = QPushButton("↗ Open in Browser")
        open_ext_btn.setToolTip("Open the guide in your default web browser instead")
        open_ext_btn.setStyleSheet("""
            QPushButton { background-color: #40207a; color: #d8a0ff; padding: 6px 14px;
                          font-weight: bold; border: 1px solid #5a3a8a; border-radius: 4px; }
            QPushButton:hover { background-color: #4e2a92; }
        """)
        open_ext_btn.clicked.connect(self._open_guide_in_browser)
        nav_layout.addWidget(open_ext_btn)
        layout.addLayout(nav_layout)

        self.guide_view = QWebEngineView()
        self.guide_view.setStyleSheet("background-color: #0a0d0f;")
        layout.addWidget(self.guide_view)

        self.guide_page_index = self.stacked_widget.addWidget(page)
        return self.guide_page_index

    def _warm_guide(self):
        """Pre-build the guide page and load its HTML once, in the background after
        startup, so the first user click switches to it instantly. Idempotent:
        _ensure_guide_page caches the page and the URL only loads when empty."""
        if not HAS_WEBENGINE or not os.path.exists(GUIDE_FILE):
            return
        self._ensure_guide_page()
        if self.guide_view is not None and self.guide_view.url().isEmpty():
            self.guide_view.load(QUrl.fromLocalFile(os.path.abspath(GUIDE_FILE)))

    def open_strat_guide(self):
        """Show the Strat study guide. Renders in-app via QtWebEngine when available,
        otherwise falls back to the system browser. The web view is created on this
        first click (lazy) so it never adds to startup time."""
        if not os.path.exists(GUIDE_FILE):
            QMessageBox.information(
                self, "Strat Guide Not Found",
                f"Couldn't find the guide at:\n{GUIDE_FILE}\n\n"
                "Place 'strat_guide.html' next to strat_monitor.py and try again.")
            return
        idx = self._ensure_guide_page()
        if idx is not None and self.guide_view is not None:
            # Load once on first open, then just switch to the page.
            if self.guide_view.url().isEmpty():
                self.guide_view.load(QUrl.fromLocalFile(os.path.abspath(GUIDE_FILE)))
            self.stacked_widget.setCurrentIndex(idx)
        else:
            self._open_guide_in_browser()

    def _open_guide_in_browser(self):
        url = "file:///" + os.path.abspath(GUIDE_FILE).replace("\\", "/")
        webbrowser.open(url)

    def export_playbook_html(self):
        if not self.current_playbook_html:
            QMessageBox.information(self, "Nothing to Export", "Open a playbook first.")
            return
        path, _ = QFileDialog.getSaveFileName(
            self, "Export Playbook as HTML", "", "HTML Files (*.html);;All Files (*)"
        )
        if not path:
            return
        if not path.lower().endswith(".html"):
            path += ".html"
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(self.current_playbook_html)
        except Exception as e:
            QMessageBox.warning(self, "Export Failed", str(e))

    # ───────────────────────────────────────────────────── table helpers ──

    def _row_display_name(self, item_dict):
        ticker = item_dict["ticker"]
        etf = item_dict.get("etf", "")
        if not etf:
            return f"{ticker} (auto…)"      # ETF resolving on next sync
        return f"{ticker} ({etf})" if ticker != etf else ticker

    def rebuild_table_structure(self):
        self.table.setRowCount(len(self.watchlist))
        for row, item_dict in enumerate(self.watchlist):
            display_name = self._row_display_name(item_dict)
            item = QTableWidgetItem(display_name)
            item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            item.setFont(QFont("Arial", 11, QFont.Weight.Bold))
            item.setForeground(QBrush(QColor("#FFFFFF")))
            self.table.setItem(row, 0, item)
            for col in range(1, 5):
                empty_item = QTableWidgetItem("Awaiting Data...")
                empty_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
                self.table.setItem(row, col, empty_item)
        self.table.resizeRowsToContents()

    def add_ticker(self):
        ticker = self.add_input.text().strip().upper()
        etf = self.etf_input.text().strip().upper()   # blank → auto-detect on sync
        if not ticker:
            return
        if any(d["ticker"] == ticker for d in self.watchlist):
            QMessageBox.information(self, "Duplicate", f"{ticker} is already being monitored.")
            return
        # Empty etf is intentional: ensure_sectors_resolved() will look up the
        # stock's industry/sector and auto-assign the best theme ETF.
        self.watchlist.append({"ticker": ticker, "etf": etf})
        self.save_settings()
        self.rebuild_table_structure()
        self.add_input.clear()
        self.etf_input.clear()
        self.start_data_thread()

    def set_etf_on_selected(self):
        """Override (or re-auto) the theme ETF for the selected row. Typing a
        value in the ETF box and clicking sets it; leaving it blank re-runs the
        automatic industry/sector assignment."""
        selected_ranges = self.table.selectedRanges()
        if not selected_ranges:
            QMessageBox.warning(self, "Selection Required", "Click a row first.")
            return
        row = selected_ranges[0].topRow()
        if not (0 <= row < len(self.watchlist)):
            return
        item = self.watchlist[row]
        etf = self.etf_input.text().strip().upper()
        if etf:
            item["etf"] = etf
            msg = f"{item['ticker']} ETF set to {etf}."
        elif "industry" in item:           # already resolved → re-auto immediately
            item["etf"] = self._auto_theme_etf(item)
            msg = f"{item['ticker']} ETF auto-set to {item['etf']}."
        else:                              # not resolved yet → blank triggers auto on sync
            item["etf"] = ""
            msg = f"{item['ticker']} ETF will be auto-detected on next sync."
        self.save_settings()
        self.rebuild_table_structure()
        self.etf_input.clear()
        self.status_label.setText(msg)
        self.start_data_thread()

    def remove_ticker(self):
        selected_ranges = self.table.selectedRanges()
        if not selected_ranges:
            QMessageBox.warning(self, "Selection Required", "Click a row first.")
            return
        row = selected_ranges[0].topRow()
        if 0 <= row < len(self.watchlist):
            removed = self.watchlist.pop(row)
            self.save_settings()
            self.rebuild_table_structure()
            self.status_label.setText(f"Removed {removed['ticker']}.")

    def change_refresh_rate(self, text):
        self.refresh_mode = text
        self.save_settings()
        self.last_interval_sync = time.time()
        self.status_label.setText(f"Pull rate: {self.refresh_mode}")

    @Slot(str)
    def set_status_text(self, text):
        self.status_label.setText(text)

    # ───────────────────────────────────────────────── strat bar labeling ──

    def get_strat_label(self, current, previous):
        if pd.isna(current['High']) or pd.isna(previous['High']):
            return "N/A"
        ch, cl = current['High'], current['Low']
        ph, pl = previous['High'], previous['Low']
        if ch <= ph and cl >= pl:
            return "1"
        if ch > ph and cl < pl:
            return "3"
        if ch > ph:
            return "2u"
        if cl < pl:
            return "2d"
        return "2"

    def process_timeframe_sequence(self, df, is_hourly=False):
        if df is None or len(df) < 5:
            return "Data Error", "H 0.00 L 0.00", False, []
        working_df = df.copy()
        if is_hourly and not working_df.empty:
            # Compare last bar's UTC timestamp to current UTC.
            # yfinance 1h bars are stamped at the START of the hour in UTC.
            # If fewer than 3600 s have elapsed since that stamp, the bar is still forming.
            try:
                last_ts = pd.Timestamp(working_df.index[-1]).tz_localize(None)
                now_utc = pd.Timestamp.now(tz='UTC').tz_convert(None)
                if 0 < (now_utc - last_ts).total_seconds() < 3600:
                    working_df = working_df.iloc[:-1]
            except Exception:
                pass
        candles = [self.get_strat_label(working_df.iloc[i], working_df.iloc[i - 1])
                   for i in range(-3, 0)]
        joined = "-".join(candles)
        is_alert = "1-1" in joined or "3-1" in joined or joined.endswith("1")
        last = working_df.iloc[-1]
        return (f"{candles[0]}-{candles[1]}-{candles[2]}",
                f"H {last['High']:.2f} L {last['Low']:.2f}",
                is_alert, candles)

    # ──────────────────────────────────────────── strat pattern analysis ──

    def analyze_strat_setups(self, cache):
        d1 = cache.get('d1_list', [])
        m1 = cache.get('m1_list', [])
        h1 = cache.get('h1_list', [])

        close            = cache.get('last_close', 0.0)
        bull_trigger     = cache.get('bull_trigger', cache.get('last_high', 0.0))
        bear_trigger     = cache.get('bear_trigger', cache.get('last_low',  0.0))
        prev_weekly_high = cache.get('prev_weekly_high', 0.0)
        prev_weekly_low  = cache.get('prev_weekly_low', 0.0)
        monthly_open     = cache.get('monthly_open', 0.0)
        prev_monthly_high = cache.get('prev_monthly_high', 0.0)
        prev_monthly_low  = cache.get('prev_monthly_low', 0.0)

        def last(s):  return s[-1]  if s               else "N/A"
        def prev(s):  return s[-2]  if len(s) >= 2     else "N/A"
        def third(s): return s[-3]  if len(s) >= 3     else "N/A"
        def up(b):    return "u" in b
        def dn(b):    return "d" in b
        def ins(b):   return b == "1"
        def out(b):   return b == "3"

        # Full Time Frame Continuity is candle COLOR (close > open = green) lined up
        # across timeframes, per The Strat — NOT the 2u/2d directional label. The
        # 2u/2d direction (prior-bar break) is still carried in m1/w1/d1/h1 and read
        # via up()/dn() below for triggers, patterns and scenarios.
        monthly_green = cache.get('monthly_color_green', False);  monthly_red = cache.get('monthly_color_red', False)
        weekly_green  = cache.get('weekly_color_green',  False);  weekly_red  = cache.get('weekly_color_red',  False)
        daily_green   = cache.get('daily_color_green',   False);  daily_red   = cache.get('daily_color_red',   False)
        hourly_green  = cache.get('hourly_color_green',  False);  hourly_red  = cache.get('hourly_color_red',  False)

        ftfc_bull = monthly_green and weekly_green and daily_green
        ftfc_bear = monthly_red  and weekly_red  and daily_red

        # ── daily bull patterns ──────────────────────────────────────────
        bull_patterns = []
        if dn(prev(d1)) and up(last(d1)):
            bull_patterns.append(("2-2 Reversal",
                "Prior day was 2-Down; today printed 2-Up. Seller exhausted — buyer reclaiming "
                "the range. Classic rev strat. Trigger: break above today's high in force."))
        if dn(third(d1)) and ins(prev(d1)) and up(last(d1)):
            bull_patterns.append(("2-1-2 Reversal",
                "2-Down → Inside day → 2-Up. The inside bar compressed the seller; today's buyer "
                "is breaking out of the coil. Trigger: above today's high. Stop: " + STOP_RULE + "."))
        if up(third(d1)) and ins(prev(d1)) and up(last(d1)):
            bull_patterns.append(("2-1-2 Continuation",
                "2-Up → Inside → 2-Up. Buyer paused in the inside bar and is now resuming. "
                "Add in force above today's high — the seller did not show up during consolidation."))
        if out(third(d1)) and ins(prev(d1)) and up(last(d1)):
            bull_patterns.append(("3-1-2 Breakout",
                "Outside day → Inside compression → 2-Up. High-volatility range set the boundaries; "
                "today's break targets the outside day's upper wick as immediate magnitude."))
        if out(prev(d1)) and up(last(d1)):
            bull_patterns.append(("3-2 Reversal",
                "Outside day immediately followed by 2-Up. Aggressive stop-hunt reversal. "
                "Macro target: the outside bar's high boundary."))
        if up(prev(d1)) and ins(last(d1)):
            bull_patterns.append(("Inside Day After 2-Up (Loading)",
                "Day is consolidating above an up move. Tomorrow's break above today's high "
                "triggers a 2-1-2 continuation — the buyer is simply pausing, not leaving."))

        # ── daily bear patterns ──────────────────────────────────────────
        bear_patterns = []
        if up(prev(d1)) and dn(last(d1)):
            bear_patterns.append(("2-2 Reversal Bear",
                "Prior day was 2-Up; today is 2-Down. Buyer exhausted — seller reclaiming. "
                "Trigger: break below today's low in force with sector/index confirmation."))
        if up(third(d1)) and ins(prev(d1)) and dn(last(d1)):
            bear_patterns.append(("2-1-2 Reversal Bear",
                "2-Up → Inside → 2-Down. Buyer trapped in the inside bar; seller breaking out. "
                "Stop: " + STOP_RULE + ". Target: prior week's low."))
        if dn(third(d1)) and ins(prev(d1)) and dn(last(d1)):
            bear_patterns.append(("2-1-2 Continuation Bear",
                "2-Down → Inside → 2-Down. Seller paused and is resuming. "
                "Add in force below today's low — buyer never showed up during consolidation."))
        if out(third(d1)) and ins(prev(d1)) and dn(last(d1)):
            bear_patterns.append(("3-1-2 Breakdown",
                "Outside day → Inside → 2-Down. Downside resolution of the broadening formation. "
                "Target: outside day's lower wick as immediate magnitude."))
        if out(prev(d1)) and dn(last(d1)):
            bear_patterns.append(("3-2 Bear",
                "Outside day followed by 2-Down. Seller took control after volatility expansion. "
                "Macro target: the outside bar's low boundary."))
        if dn(prev(d1)) and ins(last(d1)):
            bear_patterns.append(("Inside Day After 2-Down (Loading)",
                "Day consolidating below a down move. Break below today's low triggers a "
                "2-1-2 bear continuation — the seller is simply pausing, not done."))

        # ── extended-sequence patterns (guide coverage: PMG, 1-3, 3-1-3, 1-2-2, 3-2-2)
        # d1_list only carries 3 labels; these need 4-6 CLOSED bars, so rebuild a
        # longer label sequence straight from the cached daily frame (closed-aware).
        df_macro_a = cache.get('df_macro')
        day_closed = cache.get('day_closed', True)
        ext = []
        try:
            if df_macro_a is not None and len(df_macro_a) >= 8:
                last_i = len(df_macro_a) - (1 if day_closed else 2)
                for i in range(max(1, last_i - 5), last_i + 1):
                    ext.append(self.get_strat_label(df_macro_a.iloc[i], df_macro_a.iloc[i - 1]))
        except Exception:
            ext = []

        if len(ext) >= 5 and all(dn(b) for b in ext[-5:]):
            bull_patterns.insert(0, ("Pivot Machine Gun (Bull)",
                "Five consecutive 2-Down bars with no consolidation — a linear ladder of "
                "vulnerable stops left above every bar. Entry: $0.01 above the most recent "
                "bar's high; the reversal cuts back through all five pivots in sequence. "
                "Macro target: the high of the first bar of the ladder. Stop: " + STOP_RULE +
                " — if the reclaim doesn't go instantly, it's invalid."))
        if len(ext) >= 5 and all(up(b) for b in ext[-5:]):
            bear_patterns.insert(0, ("Pivot Machine Gun (Bear)",
                "Five consecutive 2-Up bars with no consolidation — stops stacked under every "
                "bar. Entry: $0.01 below the most recent bar's low; the break machine-guns back "
                "through all five pivots. Macro target: the low of the first ladder bar. "
                "Stop: " + STOP_RULE + "."))

        if ins(prev(d1)) and out(last(d1)):
            if daily_green:
                bull_patterns.insert(0, ("1-3 Rev Strat (Bull)",
                    "Inside bar broke down first (false breakout flush, stops swept), then "
                    "reversed and traversed the entire mother-bar range into an outside bar. "
                    "Pure intra-bar liquidity grab. The reclaim of the inside bar's high set "
                    "the macro target at the opposite end of the mother bar structure."))
            elif daily_red:
                bear_patterns.insert(0, ("1-3 Rev Strat (Bear)",
                    "Inside bar broke up first (false breakout, buy-stops swept), then reversed "
                    "through the full range into an outside bar. Macro target: the opposite end "
                    "of the original mother bar structure."))

        if out(third(d1)) and ins(prev(d1)) and out(last(d1)):
            if daily_green:
                bull_patterns.insert(0, ("3-1-3 Bullish Expansion",
                    "Outside bar → inside compression → second outside bar overrunning both prior "
                    "ranges. Secondary institutional expansion sweep cleaning out trapped liquidity. "
                    "Trigger fired at the inside bar's high; stop: " + STOP_RULE + "; macro "
                    "target: the first 3's high extreme. High-velocity stop-run — require FTFC."))
            elif daily_red:
                bear_patterns.insert(0, ("3-1-3 Bearish Expansion",
                    "Outside bar → inside bar → second outside bar through both prior ranges. "
                    "Stop: " + STOP_RULE + "; macro target: the first 3's low extreme. "
                    "Require full bearish FTFC — high-velocity configuration."))

        if len(ext) >= 3 and ext[-3] == '1' and up(ext[-2]) and up(ext[-1]):
            bull_patterns.append(("1-2-2 Momentum (Up & Add)",
                "Inside bar broke up and immediately printed a second consecutive 2-Up with no "
                "pause — institutional force generated follow-through without consolidation. "
                "Add on each new 2 that holds direction; NEVER add on an inside bar or a 3 "
                "mid-sequence. Stop: " + STOP_RULE + " (each add's own trigger)."))
        if len(ext) >= 3 and ext[-3] == '1' and dn(ext[-2]) and dn(ext[-1]):
            bear_patterns.append(("1-2-2 Momentum Bear (Down & Add)",
                "Inside bar broke down then a second consecutive 2-Down with no pause. Add on "
                "each new 2 down; never add on a 1 or 3 mid-sequence. Stop: " + STOP_RULE +
                " (each add's own trigger)."))

        if len(ext) >= 3 and ext[-3] == '3' and dn(ext[-2]) and up(ext[-1]):
            bull_patterns.insert(0, ("3-2-2 Reversal",
                "Outside bar → 2-Down stop-hunt past the 3's boundary → 2-Up snap-back. The "
                "breakdown trapped late shorts deeply offside; the reclaim catches them. "
                "Stop: " + STOP_RULE + ". Macro target: the parent 3 bar's high. "
                "~55% hit rate per the guide but 'goes insane' when it kicks in — small risk."))
        if len(ext) >= 3 and ext[-3] == '3' and up(ext[-2]) and dn(ext[-1]):
            bear_patterns.insert(0, ("3-2-2 Reversal Bear",
                "Outside bar → 2-Up spike past the 3's high → 2-Down snap-back. Late breakout "
                "buyers trapped. Stop: " + STOP_RULE + ". Macro target: the parent "
                "3 bar's low extreme."))

        # ── double inside day: compression on compression ──
        if len(ext) >= 2 and ext[-1] == '1' and ext[-2] == '1':
            _dbl = ("Two consecutive inside days &mdash; compression stacked on compression inside "
                    "the same mother bar. The longer the coil, the bigger the expansion: the break "
                    "of the OUTER inside bar's range is the trigger, and the move tends to run the "
                    "full mother-bar magnitude in one drive. Loaded both directions until it breaks "
                    "&mdash; no bias, just the levels.")
            bull_patterns.append(("Double Inside Day (Coiled)", _dbl))
            bear_patterns.append(("Double Inside Day (Coiled)", _dbl))

        # ── Failed-2 / 50% rule — LIVE check on the still-forming daily bar ──
        # Guide: the prior bar's 50% midpoint is the structural decision boundary.
        # A forming bar that broke one side then reclaimed across the midpoint is a
        # confirming Failed 2 (and a Failed-2-Goes-3 candidate). Read live, never
        # traded as a closed signal — surfaced as an early-warning banner only.
        failed2_bull, failed2_bear = "", ""
        try:
            if not day_closed and df_macro_a is not None and len(df_macro_a) >= 2:
                fb = df_macro_a.iloc[-1]      # forming bar
                pb = df_macro_a.iloc[-2]      # last closed bar
                p_mid = (float(pb['High']) + float(pb['Low'])) / 2.0
                f_h, f_l, f_c = float(fb['High']), float(fb['Low']), float(fb['Close'])
                if f_h > float(pb['High']) and f_c < p_mid:
                    failed2_bear = (
                        f"Today broke above yesterday's high (registered 2-Up) then reclaimed "
                        f"BELOW yesterday's 50% midpoint (${p_mid:.2f}) — a confirming "
                        f"<strong>Failed 2</strong>. Breakout buyers are trapped offside; high "
                        f"probability the bar fails its direction entirely or expands into a "
                        f"<strong>Failed-2-Goes-3</strong> through yesterday's low. Longs: honor the "
                        f"stop ({STOP_RULE}); the break of yesterday's low is the bear conversion.")
                if f_l < float(pb['Low']) and f_c > p_mid:
                    failed2_bull = (
                        f"Today broke below yesterday's low (registered 2-Down) then reclaimed "
                        f"ABOVE yesterday's 50% midpoint (${p_mid:.2f}) — a confirming "
                        f"<strong>Failed 2</strong>. Breakdown sellers are trapped; high probability "
                        f"of a full directional failure or a <strong>Failed-2-Goes-3</strong> through "
                        f"yesterday's high. Shorts: honor the stop ({STOP_RULE}); the break of "
                        f"yesterday's high is the bull conversion.")
        except Exception:
            pass

        # ── weekly context ───────────────────────────────────────────────
        # Closed-aware weekly context: per The Strat a scenario only counts once the
        # bar closes, so read the last two CLOSED weeks (prev_weekly_strat is the last
        # closed week, prev2_weekly_strat the one before — both closed-index-aware) rather
        # than last(w1)/prev(w1), whose tail is the still-forming bar mid-week.
        _pw_strat  = cache.get('prev_weekly_strat',  '')
        _pw2_strat = cache.get('prev2_weekly_strat', '')
        weekly_22_bull = dn(_pw2_strat) and up(_pw_strat)
        weekly_22_bear = up(_pw2_strat) and dn(_pw_strat)
        weekly_inside  = ins(_pw_strat)

        # ── domino analysis: does daily trigger also flip a higher TF? ───
        # A domino is SIMULTANEOUS: the prior-week level must sit BETWEEN current
        # price and the daily trigger, so a single break sweeps through both. If
        # price has already cleared the weekly level (it's beyond the close), the
        # weekly signal already fired — breaking the daily trigger can't "domino"
        # through a level it's already past. (Matches the cascade engine's _classify.)
        # Bull domino: prev week high between close and the bull trigger → weekly 2-Up
        domino_wk_bull = prev_weekly_high > 0 and close <= prev_weekly_high <= bull_trigger
        # Bear domino: prev week low between close and the bear trigger → weekly 2-Down
        domino_wk_bear = prev_weekly_low > 0 and bear_trigger <= prev_weekly_low <= close
        # Monthly domino: weekly already bull AND close has exceeded monthly prior high
        domino_mo_bull = prev_monthly_high > 0 and weekly_green and close > prev_monthly_high
        domino_mo_bear = prev_monthly_low  > 0 and weekly_red  and close < prev_monthly_low

        quarterly_open = cache.get('quarterly_open', 0.0)
        yearly_open    = cache.get('yearly_open',    0.0)

        above_monthly_open   = (close > monthly_open)   if monthly_open   > 0 else None
        above_quarterly_open = (close > quarterly_open) if quarterly_open > 0 else None
        above_yearly_open    = (close > yearly_open)    if yearly_open    > 0 else None

        # Long-term bias: monthly candle (4) + yearly open (3) + quarterly open (2) + monthly open (1)
        # Max 10 points each way — structural position, the "freeway"
        lt_bull = monthly_green * 4
        lt_bear = monthly_red   * 4
        if above_yearly_open    is True:  lt_bull += 3
        elif above_yearly_open  is False: lt_bear += 3
        if above_quarterly_open is True:  lt_bull += 2
        elif above_quarterly_open is False: lt_bear += 2
        if above_monthly_open   is True:  lt_bull += 1
        elif above_monthly_open is False: lt_bear += 1

        if lt_bull > lt_bear:   lt_bias = "BULL"
        elif lt_bear > lt_bull: lt_bias = "BEAR"
        else:                   lt_bias = "NEUTRAL"

        # Short-term bias: weekly candle (3) + daily candle (2) + hourly candle (1)
        # Max 6 points each way — current momentum on the freeway
        st_bull = weekly_green * 3 + daily_green * 2 + hourly_green * 1
        st_bear = weekly_red   * 3 + daily_red   * 2 + hourly_red   * 1

        if st_bull > st_bear:   st_bias = "BULL"
        elif st_bear > st_bull: st_bias = "BEAR"
        else:                   st_bias = "NEUTRAL"

        return {
            "monthly_green": monthly_green, "monthly_red": monthly_red,
            "weekly_green": weekly_green,   "weekly_red": weekly_red,
            "daily_green": daily_green,     "daily_red": daily_red,
            "hourly_green": hourly_green,   "hourly_red": hourly_red,
            "ftfc_bull": ftfc_bull,         "ftfc_bear": ftfc_bear,
            "bull_patterns": bull_patterns, "bear_patterns": bear_patterns,
            "lt_bias": lt_bias,             "st_bias": st_bias,
            "above_monthly_open": above_monthly_open,
            "domino_wk_bull": domino_wk_bull, "domino_wk_bear": domino_wk_bear,
            "domino_mo_bull": domino_mo_bull, "domino_mo_bear": domino_mo_bear,
            "weekly_22_bull": weekly_22_bull, "weekly_22_bear": weekly_22_bear,
            "weekly_inside": weekly_inside,
            "failed2_bull": failed2_bull,     "failed2_bear": failed2_bear,
        }

    # ──────────────────────────────────────────────── options chain HTML ──

    def compute_pivot_targets(self, df, current_price, direction, max_targets=3):
        """
        Use prior daily highs (bull) or daily lows (bear) as targets.
        Scans backwards so nearest levels are found first.
        Skips a level if:
          - it's on the wrong side of current_price
          - price has already crossed back through it since that bar
          - it's within min_gap of a level already selected
        Returns up to max_targets targets, sorted nearest-to-farthest.
        """
        if df is None or len(df) < 3:
            return []

        highs = df['High'].values
        lows  = df['Low'].values
        n     = len(highs)

        # Minimum separation: larger of $1 or 0.25 % of price
        min_gap = max(1.00, current_price * 0.0025)

        targets = []

        # Walk backwards; skip the current (last) bar — it is today's range
        for i in range(n - 2, -1, -1):
            if direction == 'bull':
                level = float(highs[i])
                if level <= current_price:
                    continue
                # Discard if any later bar traded back above this level (already consumed)
                if any(highs[j] >= level for j in range(i + 1, n)):
                    continue
            else:
                level = float(lows[i])
                if level >= current_price:
                    continue
                # Discard if any later bar traded back below this level (already consumed)
                if any(lows[j] <= level for j in range(i + 1, n)):
                    continue

            # Skip if too close to an already-chosen target
            if any(abs(level - t['price']) < min_gap for t in targets):
                continue

            date_str = pd.Timestamp(df.index[i]).strftime('%b %d')
            targets.append({'price': level, 'date': date_str})

            if len(targets) == max_targets:
                break

        return targets

    def handle_playbook_link(self, url):
        expiry = url.toString().removeprefix("expiry://")
        if expiry and self.current_playbook_row is not None:
            self.selected_expiry = expiry
            self.handle_row_clicked(self.current_playbook_row, 0)

    # ── options playbook: contract selection, walls, sizing, premium stops ──

    def _nearest_wall(self, direction, key_levels, price):
        """Nearest options wall in the trade's direction → (strike, label, count).

        Bull longs look UP for call OI/Vol walls above price; bear shorts look
        DOWN for put OI/Vol walls below price. OI is preferred over Vol when both
        qualify (standing institutional gravity vs single-session flow). Returns
        (None, '', 0) when no wall sits in the trade's path."""
        if direction == 'bull':
            order = [('call_oi', 'Call OI wall'), ('call_vol', 'Call Vol wall')]
            in_path = lambda s: s is not None and s > price
            pick = min                       # nearest above = smallest qualifying strike
        else:
            order = [('put_oi', 'Put OI wall'), ('put_vol', 'Put Vol wall')]
            in_path = lambda s: s is not None and s < price
            pick = max                       # nearest below = largest qualifying strike

        cands = []
        for key, label in order:
            strike, count = key_levels.get(key, (None, 0))
            if in_path(strike):
                cands.append((strike, label, count))
        if not cands:
            return None, '', 0

        target = pick(c[0] for c in cands)
        # If both OI and Vol qualify at the same nearest strike, OI label wins (listed first).
        for strike, label, count in cands:
            if strike == target:
                return strike, label, count
        return None, '', 0

    def _select_contract(self, direction, chain, trigger, target, key_levels, scope='daily'):
        """Pick the contract to actually buy for a directional setup. Strikes are
        chosen relative to the TRIGGER (where the trade is entered), never today's
        price — a gap between the two would otherwise land the pick deep ITM.

        scope='daily'  → 1 strike OTM from the trigger (gamma on the break); falls
                         back to ATM when that strike would sit past Target 1.
        scope='swing'  → ATM at the trigger (more delta, less theta bleed while
                         price chops before the weekly magnitude move).
        alt = the strike nearest Target 1, when it lies beyond the primary.
        Returns a dict, or None if the chain side is empty."""
        if not chain or trigger <= 0:
            return None
        df = chain.get('calls') if direction == 'bull' else chain.get('puts')
        if df is None or df.empty:
            return None

        bull = direction == 'bull'
        df = df.sort_values('strike').reset_index(drop=True)
        strikes = df['strike'].astype(float)
        atm_i = int((strikes - trigger).abs().idxmin())
        otm_i = atm_i + 1 if bull else atm_i - 1
        pick = 'atm'
        primary_i = atm_i
        if scope != 'swing' and 0 <= otm_i < len(df):
            otm_k = float(strikes[otm_i])
            past_target = target > 0 and (otm_k > target if bull else otm_k < target)
            if not past_target:
                primary_i, pick = otm_i, 'otm1'
        primary = df.loc[primary_i]

        def _num(row, col):
            a = row.get(col)
            return float(a) if a is not None and not pd.isna(a) and a > 0 else 0.0

        def _ask(row):
            return _num(row, 'ask')

        wall_strike, wall_label, wall_ct = self._nearest_wall(direction, key_levels, trigger)

        out = {
            'strike': float(primary['strike']),
            'ask':    _ask(primary),
            'bid':    _num(primary, 'bid'),
            'last':   _num(primary, 'lastPrice'),
            'iv':     _num(primary, 'impliedVolatility'),
            'expiry': chain.get('expiry'),
            'scope':  scope,
            'pick':   pick,
            'trigger': trigger,
            'wall_strike': wall_strike,
            'wall_label':  wall_label,
            'wall_ct':     wall_ct,
        }

        if target > 0:
            alt = df.loc[int((strikes - target).abs().idxmin())]
            alt_k = float(alt['strike'])
            if (alt_k > out['strike']) if bull else (alt_k < out['strike']):
                out['alt_strike'] = alt_k
                out['alt_ask']    = _ask(alt)
                out['target']     = target

        return out

    def _size_note(self, conviction):
        """Conviction → position-size guidance. Bakes in the documented rule that
        oversizing low-quality signals (and re-entering on a dip that isn't a fresh
        setup) is the primary source of net-negative P&L."""
        # Per the guide: NEVER full size at the first signal. Enter a starter
        # tranche on the trigger and scale in only as successive higher timeframes
        # (15m → 30m → 60m) go in force in the same direction. Conviction tiers
        # are max-allocation CEILINGS for the completed ladder, not entry sizes.
        notes = {
            'high':    ("<strong style='color:#5fdd8e;'>Scale-in ladder, high ceiling.</strong> "
                        "Starter tranche (~1/3) on the in-force tick; add as the 30-min then the "
                        "60-min go in force the same direction. The 35&ndash;45% max-conviction "
                        "ceiling applies ONLY with FTFC + simultaneous sector break + volume "
                        "confirmation + the stop already working in the system. Never the full "
                        "ladder at the first print."),
            'partial': ("<strong style='color:#ffd070;'>Starter tranche only (&le; half ceiling)</strong> "
                        "until the 60-min opens in the trade's direction AND sector + SPY confirm. "
                        "Add the next tranche on each higher-timeframe in-force confirmation &mdash; "
                        "after the tick, never in anticipation of it."),
            'counter': ("<strong style='color:#ffd070;'>Reduced starter, no ladder.</strong> Counter-trend "
                        "to the monthly — extra confirmation required and no adds until FTFC actually "
                        "turns. Boundary/exhaustion fades live on the instant-go rule: no "
                        "follow-through in the SAME session = exit; do not hold for the far side of "
                        "the range while higher timeframes stay against you. A dip after a win is "
                        "NOT a setup; no re-entry without a fresh inside-bar break or a clean 2-1-2."),
            'scout':   ("<strong style='color:#d8a0ff;'>Scout / starter size only.</strong> Stop: "
                        + STOP_RULE + ". Add on the trigger reclaim — never average "
                        "down into the wick."),
        }
        return notes.get(conviction, notes['partial'])

    def _options_rows(self, setup_row, direction, contract, conviction):
        """Build the Contract / Alt strike / Size rows for a setup card.
        `setup_row` is the closure defined inside _compute_playbook_html — pass it in.
        Returns just the Size row when no contract could be selected (chain unavailable)."""
        if not contract:
            return self._size_row(setup_row, conviction)   # still give the size rule

        tc   = "#5fdd8e" if direction == 'bull' else "#ff6b6b"
        kind = "Call" if direction == 'bull' else "Put"
        ask  = contract['ask']
        ask_s = f"ask ${ask:.2f}" if ask > 0 else "ask n/a"

        why = ""
        if contract.get('wall_strike'):
            why = (f" &mdash; targets the {contract['wall_label']} at "
                   f"<strong style='color:{tc};'>${contract['wall_strike']:.2f}</strong> "
                   f"({contract['wall_ct']:,}) as immediate magnitude")

        trig = contract.get('trigger', 0.0)
        if contract.get('pick') == 'otm1':
            scope_note = (f" &mdash; 1 strike OTM from the ${trig:.2f} trigger (daily signal: "
                          f"gamma on the break)")
        elif contract.get('scope') == 'swing':
            scope_note = (f" &mdash; ATM at the ${trig:.2f} trigger (swing signal: more delta, "
                          f"less theta bleed through mother-bar chop)")
        else:
            scope_note = (f" &mdash; ATM at the ${trig:.2f} trigger (Target 1 sits inside the next "
                          f"strike, so 1-OTM would need a move past the target)")
        rows = setup_row("Contract",
            f"<strong style='color:{tc};'>${contract['strike']:.2f} {kind}</strong> ({ask_s}){scope_note}{why}")

        if contract.get('alt_strike'):
            alt_ask = contract.get('alt_ask', 0.0)
            alt_s   = f"ask ${alt_ask:.2f}" if alt_ask > 0 else "ask n/a"
            lotto = ""
            if 0 < alt_ask < 0.35 * ask if ask > 0 else False:
                lotto = (" <strong style='color:#ffd070;'>&#x1F3B0; Lottery pricing</strong> "
                         "&mdash; the chain is pricing this strike as a long shot (guide: don't "
                         "go deep OTM; not enough time). If played at all, size it to zero and "
                         "treat the debit as the full expected loss &mdash; it is not a "
                         "substitute for the primary strike.")
            rows += setup_row("Alt strike",
                f"${contract['alt_strike']:.2f} {kind} ({alt_s}) &mdash; at Target 1 "
                f"(${contract['target']:.2f}): cheaper and more leverage if T1 prints, but it "
                f"needs the full move to get paid.{lotto}")

        rows += setup_row("Size", self._size_note(conviction))
        return rows

    def _size_row(self, setup_row, conviction):
        """Size row only (used when the chain is unavailable so the card still
        carries the sizing discipline)."""
        return setup_row("Size", self._size_note(conviction))

    def _option_rr(self, contract, is_bull, spot, trigger, target):
        """Model the contract at the trigger (entry) and at Target 1 after the hold
        period's theta, rather than quoting today's ask. Risk is an
        OPT_RR_DRAWDOWN loss of the entry premium.
        Volatility is backed out of the live quote at the current spot price.
        Entry pays half the spread over model value; exits give half back.
        Returns None when the chain can't support an estimate."""
        if not contract or not contract.get('expiry') or spot <= 0:
            return None
        et = ZoneInfo("America/New_York")
        now = datetime.datetime.now(et)
        try:
            exp_date = datetime.date.fromisoformat(contract['expiry'])
        except ValueError:
            return None
        expiry = datetime.datetime.combine(exp_date, datetime.time(16, 0), tzinfo=et)
        year = 365.0 * 86400
        T_now = (expiry - now).total_seconds() / year
        if T_now <= 0:
            return None
        # The trigger can't fire while the market is shut, so entry is the next open.
        entry_at = now
        if now.weekday() >= 5 or now.time() >= datetime.time(16, 0):
            entry_at = _add_trading_days(now, 1).replace(hour=9, minute=30, second=0, microsecond=0)
        elif now.time() < datetime.time(9, 30):
            entry_at = now.replace(hour=9, minute=30, second=0, microsecond=0)
        T_entry = (expiry - entry_at).total_seconds() / year
        if T_entry <= 0:
            return None
        hold = OPT_HOLD_DAYS.get(contract.get('scope'), 1)
        exit_at = _add_trading_days(entry_at, hold)
        T_exit = max(0.0, (expiry - exit_at).total_seconds()) / year

        K, is_call = contract['strike'], is_bull
        bid, ask = contract.get('bid', 0.0), contract.get('ask', 0.0)
        has_spread = bid > 0 and ask > bid
        quote = (bid + ask) / 2 if has_spread else (ask or contract.get('last', 0.0))
        iv = implied_vol(quote, spot, K, T_now, is_call)
        if iv is None and contract.get('iv', 0.0) >= 0.05:
            iv = contract['iv']
        if iv is None:
            return None
        half_spread = (ask - bid) / 2 if has_spread else 0.0

        entry     = bs_price(trigger, K, T_entry, iv, is_call) + half_spread
        at_target = max(0.0, bs_price(target, K, T_exit, iv, is_call) - half_spread)
        risk   = entry * OPT_RR_DRAWDOWN
        reward = at_target - entry
        return {
            'entry': entry, 'at_target': at_target,
            'risk': risk, 'reward': reward,
            'rr': reward / risk if risk > 0 else None,
            'theta_cost': bs_price(target, K, T_entry, iv, is_call) - bs_price(target, K, T_exit, iv, is_call),
            'iv': iv, 'hold': hold,
            'delta': bs_delta(trigger, K, T_entry, iv, is_call),
            'spread': (ask - bid) if has_spread else None,
            'expires_first': exit_at >= expiry,
        }

    @staticmethod
    def _classify_candle(o, h, l, c):
        """Hammer / shooting-star classification for one OHLC bar.

        Hammer  = long LOWER wick, tiny upper wick, small body up top  → sellers
                  rejected, demand stepped in (bullish-reversal shape / failed
                  breakdown).
        Shooter = long UPPER wick, tiny lower wick, small body down low → buyers
                  rejected, supply stepped in (bearish-reversal shape / failed
                  breakout).

        Returns None when the bar is neither, else a dict with type/strength/
        colour and the wick fractions used in the narrative."""
        rng = h - l
        if rng <= 0 or o <= 0 or c <= 0:
            return None
        body = abs(c - o)
        top, bot = max(o, c), min(o, c)
        upper = h - top
        lower = bot - l
        body_frac  = body  / rng
        upper_frac = upper / rng
        lower_frac = lower / rng
        green = c >= o

        # A wick dominates when it is >=2x the real body AND the opposite wick is
        # negligible; the small body must sit at the opposite extreme of the range.
        is_hammer  = (lower >= 2 * body and upper_frac <= 0.15
                      and body_frac <= 0.40 and lower_frac >= 0.50)
        is_shooter = (upper >= 2 * body and lower_frac <= 0.15
                      and body_frac <= 0.40 and upper_frac >= 0.50)
        if is_hammer == is_shooter:          # neither, or (degenerate) both
            return None
        ctype = 'hammer' if is_hammer else 'shooter'

        # Strength is graded on how dominant the rejection wick is, NOT on body
        # colour. Per The Strat the textbook hammer is a *red* bar closing near
        # its high and the textbook shooter is a *green* bar closing near its low
        # (the "triangle-they-out" colours), so colour is carried for context but
        # never used to up/downgrade the signal.
        dom = lower_frac if ctype == 'hammer' else upper_frac
        if dom >= 0.66:
            strength = 'strong'        # wick is two-thirds+ of the whole range
        elif dom >= 0.58:
            strength = 'moderate'
        else:
            strength = 'weak'
        return {'type': ctype, 'green': green, 'strength': strength,
                'lower_frac': lower_frac, 'upper_frac': upper_frac,
                'body_frac': body_frac, 'o': o, 'h': h, 'l': l, 'c': c}

    def fetch_live_options_html(self, yf_symbol, current_price, selected_expiry=None, min_dte=0):
        try:
            tk = yf.Ticker(yf_symbol)
            expirations = tk.options
            if not expirations:
                return "<p style='color:#ff6b6b;padding:10px;'>No options chain available.</p>", {}, {}

            # Use caller-chosen expiry if valid; otherwise default to the first
            # expiry with at least min_dte calendar days left (guide: match the
            # expiration to the signal's timeframe — never weekly contracts on a
            # weekly-cascade/monthly signal). min_dte=0 keeps the old nearest-expiry.
            if selected_expiry and selected_expiry in expirations:
                target_expiry = selected_expiry
            else:
                target_expiry = expirations[0]
                if min_dte > 0:
                    today = datetime.date.today()
                    for exp in expirations:
                        try:
                            if (datetime.date.fromisoformat(exp) - today).days >= min_dte:
                                target_expiry = exp
                                break
                        except Exception:
                            continue

            opt_chain = tk.option_chain(target_expiry)
            calls_df = opt_chain.calls.copy().sort_values('strike').reset_index(drop=True)
            puts_df  = opt_chain.puts.copy().sort_values('strike').reset_index(drop=True)

            if calls_df.empty or puts_df.empty:
                return f"<p style='color:#ff6b6b;padding:10px;'>Empty chain for {target_expiry}.</p>", {}, {}

            # Slice to ATM ±3 strikes
            otm_c = calls_df[calls_df['strike'] >= current_price]
            if not otm_c.empty:
                ci = otm_c['strike'].idxmin()
                active_calls = calls_df.iloc[max(0, ci - 1):ci + 4]  # 1 ITM + 4 OTM
            else:
                active_calls = calls_df.tail(5)

            otm_p = puts_df[puts_df['strike'] <= current_price]
            if not otm_p.empty:
                pi = otm_p['strike'].idxmax()
                active_puts = puts_df.iloc[max(0, pi - 3):pi + 2]  # 4 OTM + 1 ITM
            else:
                active_puts = puts_df.head(5)

            max_cv = calls_df['volume'].max() if not calls_df.empty else 0
            max_pv = puts_df['volume'].max()  if not puts_df.empty  else 0

            # ── significance-aware level detection ───────────────────────────
            # A level is only a "wall" if it's a genuine concentration outlier —
            # not merely the max in a thin chain (a 481-OI nominal max is not an
            # institutional level). "Fresh" flags volume >= OI on a strike: new
            # positioning today, which carries more intent than standing OI alone
            # ("gravity comes from volume relative to OI, not OI alone").
            WALL_MULT, WALL_SHARE, FRESH_VOL_FRAC = 2.0, 0.10, 0.40

            def _wall_strike(df, col):
                """Strike with a significant OI/Vol concentration, else (None, 0)."""
                try:
                    d = df[['strike', col]].dropna()
                    d = d[d[col] > 0]
                    if d.empty:
                        return None, 0
                    i = d[col].idxmax()
                    peak  = float(d.loc[i, col])
                    med   = float(d[col].median())
                    total = float(d[col].sum())
                    if med > 0 and peak >= WALL_MULT * med and total > 0 and peak / total >= WALL_SHARE:
                        return float(d.loc[i, 'strike']), int(peak)
                    return None, 0
                except Exception:
                    return None, 0

            def _fresh_strike(df):
                """Strike with the most fresh positioning — volume >= standing OI and
                materially sized vs the side's top volume, else (None, 0, 0)."""
                try:
                    d = df[['strike', 'volume', 'openInterest']].dropna()
                    d = d[d['volume'] > 0]
                    if d.empty:
                        return None, 0, 0
                    vmax = float(d['volume'].max())
                    cand = d[(d['volume'] >= d['openInterest']) & (d['volume'] >= FRESH_VOL_FRAC * vmax)]
                    if cand.empty:
                        return None, 0, 0
                    i = cand['volume'].idxmax()
                    return (float(cand.loc[i, 'strike']),
                            int(cand.loc[i, 'volume']), int(cand.loc[i, 'openInterest']))
                except Exception:
                    return None, 0, 0

            c_oi_strike,  c_oi_count  = _wall_strike(calls_df, 'openInterest')
            c_vol_strike, c_vol_count = _wall_strike(calls_df, 'volume')
            p_oi_strike,  p_oi_count  = _wall_strike(puts_df,  'openInterest')
            p_vol_strike, p_vol_count = _wall_strike(puts_df,  'volume')
            c_fresh_strike, c_fresh_vol, c_fresh_oi = _fresh_strike(calls_df)
            p_fresh_strike, p_fresh_vol, p_fresh_oi = _fresh_strike(puts_df)

            def cell_style(is_atm, is_hv, is_hoi):
                if is_atm: return "background:#141520;"
                if is_hv:  return "background:#0a1e12;"
                if is_hoi: return "background:#2a2000;"
                return ""

            def name_color(is_atm, is_hv, is_hoi):
                if is_atm: return "#c0b0ff"
                if is_hv:  return "#5fdd8e"
                if is_hoi: return "#ffbc42"
                return "#d8e4f0"

            def _badge(bg, col, bord, label):
                return (f"<span style='font-size:9px;font-weight:700;padding:1px 5px;border-radius:3px;"
                        f"margin-left:4px;background:{bg};color:{col};border:1px solid {bord};'>{label}</span>")

            def _hit(strike, ref):
                return ref is not None and abs(strike - ref) < 1e-6

            def tags(strike, vol, max_v, oi_wall, fresh):
                t = ""
                if abs(strike - current_price) <= current_price * 0.005:
                    t += _badge("#141520", "#c0b0ff", "#2e2e5e", "ATM")
                if vol == max_v and vol > 0:
                    t += _badge("#0a1e12", "#5fdd8e", "#2d7a44", "Vol#1")
                if _hit(strike, oi_wall):
                    t += _badge("#2a2000", "#ffd070", "#6b4d00", "OI Wall")
                if _hit(strike, fresh):
                    t += _badge("#0a1a2a", "#7ec8ff", "#1a4d7a", "Fresh")
                return t

            def build_rows(df, max_v, oi_wall, fresh):
                rows = ""
                for _, r in df.iterrows():
                    vol = int(r['volume'])       if not pd.isna(r.get('volume', float('nan'))) else 0
                    oi  = int(r['openInterest']) if 'openInterest' in r and not pd.isna(r['openInterest']) else 0
                    ask = r['ask']               if not pd.isna(r['ask']) else 0.0
                    is_atm = abs(r['strike'] - current_price) <= current_price * 0.005
                    is_hv  = vol == max_v and vol > 0
                    is_hoi = _hit(r['strike'], oi_wall)
                    cs  = cell_style(is_atm, is_hv, is_hoi)
                    nc  = name_color(is_atm, is_hv, is_hoi)
                    tag = tags(r['strike'], vol, max_v, oi_wall, fresh)
                    rows += (f"<tr style='{cs}'>"
                             f"<td style='padding:7px 10px;font-weight:800;color:{nc};border-bottom:1px solid #1e2530;'>${r['strike']:.2f}{tag}</td>"
                             f"<td style='padding:7px 10px;text-align:right;color:#d8e4f0;border-bottom:1px solid #1e2530;'>${ask:.2f}</td>"
                             f"<td style='padding:7px 10px;text-align:right;color:#d8e4f0;border-bottom:1px solid #1e2530;'>{vol:,}</td>"
                             f"<td style='padding:7px 10px;text-align:right;color:#8a9ab0;border-bottom:1px solid #1e2530;'>{oi:,}</td>"
                             f"</tr>")
                return rows

            th = ("background:#1a1e24;color:#8a9ab0;font-size:10px;text-transform:uppercase;"
                  "letter-spacing:0.07em;padding:7px 10px;font-weight:700;border-bottom:1px solid #2e3540;")

            def side_table(title, rows):
                return (f"<div style='font-size:12px;font-weight:700;color:#8a9ab0;padding:8px 10px;"
                        f"background:#151820;border:1px solid #232830;border-bottom:none;'>{title}</div>"
                        f"<table width='100%' style='border-collapse:collapse;border:1px solid #232830;'>"
                        f"<thead><tr>"
                        f"<th style='{th}text-align:left;'>Strike</th>"
                        f"<th style='{th}text-align:right;'>Ask</th>"
                        f"<th style='{th}text-align:right;'>Volume</th>"
                        f"<th style='{th}text-align:right;'>OI</th>"
                        f"</tr></thead><tbody>{rows}</tbody></table>")

            call_rows = build_rows(active_calls, max_cv, c_oi_strike, c_fresh_strike)
            put_rows  = build_rows(active_puts,  max_pv, p_oi_strike, p_fresh_strike)

            # Key levels for target magnets / wall caps. Walls are the
            # significance-filtered concentrations above; 'fresh' carries the
            # vol>=OI new-positioning signal (strike, volume, OI).
            key_levels = {
                'call_vol':   (c_vol_strike, c_vol_count),
                'call_oi':    (c_oi_strike,  c_oi_count),
                'put_vol':    (p_vol_strike, p_vol_count),
                'put_oi':     (p_oi_strike,  p_oi_count),
                'call_fresh': (c_fresh_strike, c_fresh_vol, c_fresh_oi),
                'put_fresh':  (p_fresh_strike, p_fresh_vol, p_fresh_oi),
            }

            # Build clickable expiry selector — show up to 8 nearest dates
            expiry_chips = ""
            for exp in expirations[:8]:
                is_active = (exp == target_expiry)
                if is_active:
                    chip_style = ("padding:4px 10px;border-radius:5px;font-size:11px;font-weight:700;"
                                  "background:#1e3a5f;border:1px solid #2e5d9e;color:#7eb8ff;"
                                  "margin-right:5px;display:inline-block;")
                    expiry_chips += f"<span style='{chip_style}'>{exp} &#x25CF;</span>"
                else:
                    chip_style = ("padding:4px 10px;border-radius:5px;font-size:11px;font-weight:700;"
                                  "background:#1a1e24;border:1px solid #2e3540;color:#8a9ab0;"
                                  "margin-right:5px;display:inline-block;")
                    expiry_chips += (f"<a href='expiry://{exp}' style='text-decoration:none;'>"
                                     f"<span style='{chip_style}'>{exp}</span></a>")

            footer = (f"<div style='padding:8px 10px;background:#151820;border:1px solid #232830;"
                      f"border-radius:0 0 6px 6px;margin-top:-1px;'>"
                      f"<span style='font-size:10px;color:#6b7a8d;text-transform:uppercase;"
                      f"letter-spacing:0.08em;margin-right:8px;'>Select Expiry:</span>"
                      f"{expiry_chips}"
                      f"<span style='font-size:10px;color:#4a5568;margin-left:8px;'>"
                      f"ATM = near price &nbsp;&middot;&nbsp; Vol#1 = highest volume "
                      f"&nbsp;&middot;&nbsp; OI Wall = highest open interest</span>"
                      f"</div>")

            html = (f"<table width='100%' style='border-collapse:collapse;margin-bottom:0;'>"
                    f"<tr>"
                    f"<td width='50%' style='vertical-align:top;padding-right:6px;'>{side_table('CALLS', call_rows)}</td>"
                    f"<td width='50%' style='vertical-align:top;padding-left:6px;'>{side_table('PUTS', put_rows)}</td>"
                    f"</tr></table>"
                    f"{footer}")
            return html, key_levels, {'calls': calls_df, 'puts': puts_df, 'expiry': target_expiry}

        except Exception as e:
            return f"<p style='color:#ff6b6b;padding:10px;'>Options chain error: {e}</p>", {}, {}

    # ──────────────────────────────────────────── playbook click handler ──

    def handle_row_clicked(self, row, col):
        item_dict = self.watchlist[row]
        ticker    = item_dict["ticker"]
        etf_home  = item_dict["etf"]

        cache = self.raw_df_cache.get(ticker)
        if not cache:
            QMessageBox.information(self, "No Data", f"Data for {ticker} is still loading.")
            return

        # Reset selected expiry when the user clicks a different ticker row
        if self.current_playbook_row != row:
            self.selected_expiry = None
        self.current_playbook_row = row

        # Populate the interactive hourly chart immediately (the narrative below
        # loads on a worker thread).
        self.candle_chart.set_data(cache.get("df_hourly"))

        selected_expiry = self.selected_expiry
        spy_cache  = self.raw_df_cache.get("SPY")
        etf_cache  = self.raw_df_cache.get(etf_home)

        breadth_layers, mega_cap, breadth_caches = self.build_breadth_layers(item_dict)

        self.playbook_text.setHtml(
            f"<html><body style='background:#0d0f12;color:#8a9ab0;padding:40px;"
            f"font-family:Arial,sans-serif;font-size:14px;'>"
            f"&#x23F3; Loading playbook for <strong style='color:#ffffff;'>{ticker}</strong>..."
            f"</body></html>")
        self.stacked_widget.setCurrentIndex(1)

        threading.Thread(
            target=self._build_playbook_thread,
            args=(row, ticker, etf_home, cache, spy_cache, etf_cache, selected_expiry,
                  breadth_layers, mega_cap, breadth_caches),
            daemon=True,
        ).start()

    def build_breadth_layers(self, item_dict):
        """Assemble the cap-vs-equal breadth layers for a watchlist item:
        Market (always SPY/RSP), Sector (auto from GICS sector), and
        Industry/Theme (from the manual ETF Home + its equal-weight twin).
        Returns (layers, is_mega, caches) where layers is a list of
        (layer_name, cap_sym, eq_sym, descriptor)."""
        etf_home = item_dict["etf"]
        sector   = item_dict.get("sector")
        is_mega  = item_dict.get("mega_cap", False)

        layers = [("Market", MARKET_BREADTH_PAIR[0], MARKET_BREADTH_PAIR[1], "the broad market")]

        sec_cap, sec_eq = SECTOR_ETF_MAP.get(sector or "", (None, None))
        if sec_cap and sec_eq:
            layers.append(("Sector", sec_cap, sec_eq, f"the {sector} sector"))

        # Include the Industry/Theme layer whenever the home ETF is a genuinely
        # narrower instrument than the market/sector rows already shown. If it has
        # an equal-weight twin we render a true breadth ratio; if not, the section
        # falls back to the ETF's own trend (eq_sym == "" signals absolute mode).
        theme_eq = ETF_EQUAL_WEIGHT_MAP.get(etf_home, "")
        if etf_home and etf_home not in (MARKET_BREADTH_PAIR[0], sec_cap, sec_eq):
            layers.append(("Industry / Theme", etf_home, theme_eq, f"the {etf_home} complex"))

        needed = set()
        for _, cap, eq, _ in layers:
            needed.add(cap)
            if eq:
                needed.add(eq)
        caches = {sym: self.raw_df_cache.get(sym) for sym in needed}
        return layers, is_mega, caches

    def _build_playbook_thread(self, row, ticker, etf_home, cache, spy_cache, etf_cache,
                               selected_expiry, breadth_layers=None, mega_cap=False,
                               breadth_caches=None):
        try:
            html = self._compute_playbook_html(
                ticker, etf_home, cache, spy_cache, etf_cache, selected_expiry,
                breadth_layers, mega_cap, breadth_caches)
        except Exception as e:
            html = (f"<html><body style='background:#0d0f12;color:#ff6b6b;padding:40px;"
                    f"font-family:Arial;'>Error building playbook: {e}</body></html>")
        self.signals.playbook_ready.emit(html, row)

    @Slot(str, int)
    def _on_playbook_ready(self, html, row):
        if self.current_playbook_row == row:
            self.current_playbook_html = html
            self.playbook_text.setHtml(html)

    # ──────────────────────────────────────────────── market breadth layer ──

    def _breadth_returns(self, cache):
        """Trailing % return over each breadth timeframe from a cache's 1y daily
        df_macro. Returns {timeframe_label: float_or_None}."""
        out = {label: None for label, _, _ in BREADTH_TIMEFRAMES}
        df = cache.get("df_macro") if cache else None
        if df is None:
            return out
        try:
            closes = df["Close"].dropna()
        except Exception:
            return out
        for label, lookback, _thr in BREADTH_TIMEFRAMES:
            if len(closes) > lookback:
                try:
                    out[label] = float(closes.iloc[-1] / closes.iloc[-1 - lookback] - 1.0)
                except Exception:
                    out[label] = None
        return out

    def _breadth_narrative(self, ticker, descriptor, weekly_state, daily_state, mega,
                           cap_r=None):
        """Plain-English breadth read, weighted to the weekly (then daily).

        Direction-aware: the SAME cap-vs-equal spread means opposite things on an
        up tape vs a down tape, so the narrative keys on the SIGN of the move, not
        just the spread. Equal-weight 'leading' while the group is falling is
        relative strength on a down tape — not money flowing into the whole group.
        Cap-weight leading on a down tape means the mega-caps are leading the group
        LOWER, which confirms a short, not a long."""
        if weekly_state not in (None, "na"):
            primary, primary_tf = weekly_state, "Weekly"
        else:
            primary, primary_tf = daily_state, "Daily"

        # Tape direction from the cap-weight return at the primary timeframe.
        cap_ret = (cap_r or {}).get(primary_tf)
        up_tape = (cap_ret is None) or (cap_ret >= 0)   # unknown → assume up
        tape_txt = "rising" if up_tape else "falling"

        if primary == "broad":
            # equal-weight outperforming cap-weight (cap return < equal return)
            if up_tape:
                return ("&#x1F4C8;", "#5fdd8e",
                        f"Equal-weight is leading cap-weight across {descriptor} on a {tape_txt} "
                        f"tape &mdash; money is flowing into the whole group, including the smaller "
                        f"names. Broad participation; a mid/small-cap long here has real wind behind it.")
            # down tape: cap-weight fell MORE → the big names led the group lower
            if mega:
                return ("&#x26A0;", "#ff8d6b",
                        f"Cap-weight is falling <em>faster</em> than equal-weight across {descriptor} "
                        f"&mdash; the mega-caps are leading the group <strong>lower</strong> while the "
                        f"broader names hold up better. The giants are the names being sold, so for a "
                        f"mega-cap like {ticker} this <strong>confirms the short</strong>.")
            return ("&#x26A0;", "#ffd070",
                    f"Cap-weight is falling <em>faster</em> than equal-weight across {descriptor} "
                    f"&mdash; the damage is concentrated in the big-cap names while the broader/average "
                    f"name holds up better. The relative strength is in the smaller names, not the "
                    f"heavyweights &mdash; the group as a whole is still down.")
        if primary == "narrow":
            if up_tape:
                if mega:
                    return ("&#x2714;", "#5fdd8e",
                            f"Cap-weight is leading equal-weight on a {tape_txt} tape &mdash; the "
                            f"move in {descriptor} is concentrated in the mega-caps. For a mega-cap "
                            f"leader like {ticker} that is <strong>confirming</strong>: the giants are "
                            f"being bid and {ticker} <em>is</em> the leg driving it.")
                return ("&#x26A0;", "#ffd070",
                        f"Cap-weight is leading equal-weight on a {tape_txt} tape &mdash; the move in "
                        f"{descriptor} is narrow, concentrated in the mega-caps. A non-mega name going "
                        f"up here is more likely an isolated pop (news, squeeze) than sector-wide flow "
                        f"&mdash; exactly the kind of move that fades.")
            # down tape: cap-weight fell LESS → mega-caps relatively defensive
            if mega:
                return ("&#x25CF;", "#8a9ab0",
                        f"Cap-weight is falling <em>less</em> than equal-weight across {descriptor} "
                        f"&mdash; the mega-caps are holding up better than the broad market; the "
                        f"selling is heavier in the smaller names. {ticker}'s cohort is the relatively "
                        f"defensive one here, though the tape is still down.")
            return ("&#x26A0;", "#ffd070",
                    f"Cap-weight is falling <em>less</em> than equal-weight across {descriptor} "
                    f"&mdash; the mega-caps are holding up while the smaller names get sold harder. "
                    f"A non-mega name here sits in the weaker cohort &mdash; broad weakness underneath.")
        if primary == "inline":
            return ("&#x25CF;", "#8a9ab0",
                    f"Cap- and equal-weight are moving in line across {descriptor} (group {tape_txt}) "
                    f"&mdash; no strong breadth signal either way.")
        return ("&#x2014;", "#8a9ab0",
                f"Breadth data for {descriptor} is unavailable (ETF data did not load).")

    def _earnings_section_html(self, cache, ticker):
        """Card showing the most recent earnings (reported vs estimated EPS, with
        beat/miss) and the next scheduled earnings date. Returns "" when there is
        no earnings data (ETFs, futures, or feed empty). Also flags when the next
        report is imminent — an open options position would face IV crush."""
        e = cache.get('earnings')
        if not e:
            return ""
        last_date  = e.get('last_date')
        next_date  = e.get('next_date')
        if not last_date and not next_date:
            return ""

        def fmt_eps(v):
            if v is None:
                return "<span style='color:#6b7a8d;'>n/a</span>"
            return f"-${abs(v):.2f}" if v < 0 else f"${v:.2f}"

        # ── most recent reported earnings ────────────────────────────────────
        if last_date:
            actual, est = e.get('last_actual'), e.get('last_estimate')
            surprise    = e.get('last_surprise')
            if actual is not None and est is not None:
                beat = actual >= est
                vcol = "#5fdd8e" if beat else "#ff6b6b"
                verdict = "BEAT" if beat else "MISS"
            elif surprise is not None:
                vcol = "#5fdd8e" if surprise >= 0 else "#ff6b6b"
                verdict = "BEAT" if surprise >= 0 else "MISS"
            else:
                vcol, verdict = "#8a9ab0", ""
            surprise_txt = (f" &middot; <span style='color:{vcol};'>{surprise:+.1f}% surprise</span>"
                            if surprise is not None else "")
            last_block = (
                f"<td style='padding:12px 16px;vertical-align:top;width:50%;border-right:1px solid #2e3540;'>"
                f"<div style='font-size:10px;color:#6b7a8d;text-transform:uppercase;letter-spacing:0.07em;'>"
                f"Most Recent</div>"
                f"<div style='font-size:15px;font-weight:800;color:#ffffff;margin:4px 0 6px 0;'>"
                f"{last_date.strftime('%b %d, %Y')}"
                + (f" <span style='font-size:12px;font-weight:800;color:{vcol};'>{verdict}</span>" if verdict else "")
                + f"</div>"
                f"<div style='font-size:12px;color:#d0d8e5;line-height:1.6;'>"
                f"Reported <strong style='color:{ '#5fdd8e' if (actual is not None and est is not None and actual >= est) else '#d0d8e5' };'>{fmt_eps(actual)}</strong> "
                f"vs <span style='color:#8a9ab0;'>{fmt_eps(est)}</span> est{surprise_txt}</div>"
                f"</td>")
        else:
            last_block = (
                f"<td style='padding:12px 16px;vertical-align:top;width:50%;border-right:1px solid #2e3540;'>"
                f"<div style='font-size:10px;color:#6b7a8d;text-transform:uppercase;letter-spacing:0.07em;'>"
                f"Most Recent</div>"
                f"<div style='font-size:13px;color:#8a9ab0;margin-top:6px;'>No reported earnings on record.</div>"
                f"</td>")

        # ── post-earnings tape note (repeat morning flow) ────────────────────
        post_earn_note = ""
        try:
            if e.get('last_date'):
                _ld = e['last_date']
                _days = (datetime.datetime.now(tz=getattr(_ld, 'tzinfo', None)) - _ld).days
                if 0 <= _days <= 5:
                    post_earn_note = (
                        f"<div style='font-size:12px;color:#ffd070;margin-top:8px;line-height:1.6;'>"
                        f"&#x1F4E1; <strong>Post-earnings tape (T+{_days}d):</strong> watch the first "
                        f"hour each morning for the REPEAT participant &mdash; the same seller (or "
                        f"buyer) showing up morning after morning is institutional repositioning, not "
                        f"a one-day reaction: trade with that flow, don't fade it. Second-day "
                        f"'afterblow' moves off the earnings gap are common; the gap's reaction "
                        f"extremes are live S/R until fully reclaimed.</div>")
        except Exception:
            post_earn_note = ""

        # ── next scheduled earnings ──────────────────────────────────────────
        if next_date:
            days = (next_date.date() - datetime.date.today()).days
            if days <= 0:
                when = "today / awaiting report"
            elif days == 1:
                when = "in 1 day"
            else:
                when = f"in {days} days"
            imminent = 0 <= days <= 7
            ncol = "#ffd070" if imminent else "#d0d8e5"
            nest = e.get('next_estimate')
            est_txt = (f"<div style='font-size:12px;color:#8a9ab0;margin-top:4px;'>"
                       f"EPS estimate: <span style='color:#d0d8e5;'>{fmt_eps(nest)}</span></div>"
                       if nest is not None else "")
            warn_txt = (f"<div style='font-size:11px;color:#ffd070;margin-top:6px;line-height:1.5;'>"
                        f"&#x26A0; Earnings within a week &mdash; expect elevated IV and a post-report "
                        f"volatility crush on any options held through it.</div>") if imminent else ""
            next_block = (
                f"<td style='padding:12px 16px;vertical-align:top;width:50%;'>"
                f"<div style='font-size:10px;color:#6b7a8d;text-transform:uppercase;letter-spacing:0.07em;'>"
                f"Next Scheduled</div>"
                f"<div style='font-size:15px;font-weight:800;color:{ncol};margin:4px 0 2px 0;'>"
                f"{next_date.strftime('%b %d, %Y')} "
                f"<span style='font-size:12px;font-weight:600;color:#8a9ab0;'>&middot; {when}</span></div>"
                f"{est_txt}{warn_txt}"
                f"</td>")
        else:
            next_block = (
                f"<td style='padding:12px 16px;vertical-align:top;width:50%;'>"
                f"<div style='font-size:10px;color:#6b7a8d;text-transform:uppercase;letter-spacing:0.07em;'>"
                f"Next Scheduled</div>"
                f"<div style='font-size:13px;color:#8a9ab0;margin-top:6px;'>No upcoming date announced.</div>"
                f"</td>")

        return (
            f"<table width='100%' style='background:#1a1e24;border:1px solid #2e3540;"
            f"border-radius:12px;border-collapse:collapse;margin-bottom:16px;'>"
            f"<tr><td colspan='2' style='padding:10px 16px 0 16px;'>"
            f"<div style='font-size:13px;font-weight:800;color:#ffffff;'>&#x1F4C5; Earnings "
            f"<span style='font-size:11px;color:#8a9ab0;font-weight:600;'>&middot; {ticker}</span></div>"
            f"</td></tr>"
            f"<tr>{last_block}{next_block}</tr>"
            + (f"<tr><td colspan='2' style='padding:0 16px 12px 16px;'>{post_earn_note}</td></tr>"
               if post_earn_note else "")
            + "</table>")

    def _breadth_section_html(self, ticker, layers, mega, caches):
        """Build the Market Breadth section: one block per layer (market / sector /
        theme), each a cap-vs-equal-weight read across Daily/Weekly/Monthly/Quarterly."""
        if not layers:
            return ""

        def _pct(r):
            if r is None:
                return "<span style='color:#6b7a8d;'>n/a</span>"
            col = "#5fdd8e" if r >= 0 else "#ff6b6b"
            return f"<span style='color:{col};'>{r * 100:+.2f}%</span>"

        section_label = (
            "<div style='font-size:11px;font-weight:700;color:#6b7a8d;text-transform:uppercase;"
            "letter-spacing:0.1em;margin:6px 0 10px 0;border-bottom:1px solid #232830;"
            "padding-bottom:6px;'>Market Breadth &mdash; Cap-Weight vs Equal-Weight</div>")

        def _cell(tf, verdict, vcol, detail):
            return (
                f"<td style='background:#15181e;border:1px solid #232830;border-radius:8px;"
                f"padding:9px 8px;text-align:center;vertical-align:top;width:25%;'>"
                f"<div style='font-size:10px;color:#6b7a8d;text-transform:uppercase;"
                f"letter-spacing:0.07em;margin-bottom:4px;'>{tf}</div>"
                f"<div style='font-size:13px;font-weight:800;color:{vcol};margin-bottom:4px;'>{verdict}</div>"
                f"<div style='font-size:10px;color:#8a9ab0;line-height:1.5;'>{detail}</div></td>")

        blocks = ""
        for layer_name, cap_sym, eq_sym, descriptor in layers:
            cap_r = self._breadth_returns(caches.get(cap_sym))

            if eq_sym:
                # ── true cap-vs-equal breadth read ──────────────────────────
                eq_r = self._breadth_returns(caches.get(eq_sym))
                cells, states = "", {}
                for tf, _lb, thr in BREADTH_TIMEFRAMES:
                    cr, er = cap_r.get(tf), eq_r.get(tf)
                    if cr is None or er is None:
                        state, verdict, vcol = "na", "N/A", "#8a9ab0"
                    else:
                        spread = cr - er
                        if abs(spread) < thr:
                            state, verdict, vcol = "inline", "IN LINE", "#8a9ab0"
                        elif spread > 0:
                            state, verdict, vcol = "narrow", "NARROW", "#ffd070"
                        else:
                            state, verdict, vcol = "broad", "BROAD", "#5fdd8e"
                    states[tf] = state
                    cells += _cell(tf, verdict, vcol, f"{cap_sym} {_pct(cr)}<br>{eq_sym} {_pct(er)}")
                icon, ncol, narrative = self._breadth_narrative(
                    ticker, descriptor, states.get("Weekly"), states.get("Daily"), mega, cap_r)
                subtitle = f"{cap_sym} (cap) vs {eq_sym} (equal)"
            else:
                # ── no equal-weight twin: show the ETF's own trend instead ──
                cells = ""
                for tf, _lb, _thr in BREADTH_TIMEFRAMES:
                    r = cap_r.get(tf)
                    if r is None:
                        verdict, vcol = "N/A", "#8a9ab0"
                    elif r > 0:
                        verdict, vcol = "UP", "#5fdd8e"
                    elif r < 0:
                        verdict, vcol = "DOWN", "#ff6b6b"
                    else:
                        verdict, vcol = "FLAT", "#8a9ab0"
                    cells += _cell(tf, verdict, vcol, f"{cap_sym} {_pct(r)}")
                icon, ncol = "&#x2139;", "#8a9ab0"
                narrative = (
                    f"No equal-weight counterpart is known for {cap_sym}, so sector-wide "
                    f"breadth can't be measured here &mdash; this row shows {cap_sym}'s own "
                    f"trend only. Read it as niche leadership: is {descriptor} being bid at "
                    f"all, regardless of how broad the participation is underneath.")
                subtitle = f"{cap_sym} trend &middot; no equal-weight twin"

            blocks += (
                f"<table width='100%' style='background:#1a1e24;border:1px solid #2e3540;"
                f"border-radius:10px;border-collapse:collapse;margin-bottom:10px;'>"
                f"<tr><td style='padding:11px 14px;'>"
                f"<div style='font-size:13px;font-weight:800;color:#ffffff;'>{layer_name} Breadth"
                f"<span style='font-size:11px;color:#8a9ab0;font-weight:600;'> &middot; "
                f"{subtitle}</span></div>"
                f"<table width='100%' style='border-collapse:separate;border-spacing:6px;"
                f"margin-top:8px;'><tr>{cells}</tr></table>"
                f"<div style='font-size:12px;color:{ncol};line-height:1.6;margin-top:6px;'>"
                f"{icon} {narrative}</div>"
                "</td></tr></table>")

        return section_label + blocks

    def _compute_playbook_html(self, ticker, etf_home, cache, spy_cache, etf_cache,
                               selected_expiry, breadth_layers=None, mega_cap=False,
                               breadth_caches=None):
        d1_seq = cache['d1_list']
        w1_seq = cache['w1_list']

        current_close     = cache.get('last_close', 0.0)
        daily_atr         = cache.get('daily_atr',  0.0)
        current_high      = cache.get('bull_trigger', cache.get('last_high', 0.0))
        current_low       = cache.get('bear_trigger', cache.get('last_low',  0.0))
        prev_weekly_high  = cache.get('prev_weekly_high',  0.0)
        prev_weekly_low   = cache.get('prev_weekly_low',   0.0)
        prev_monthly_high = cache.get('prev_monthly_high', 0.0)
        prev_monthly_low  = cache.get('prev_monthly_low',  0.0)
        weekly_open       = cache.get('weekly_open',  0.0)
        monthly_open      = cache.get('monthly_open', 0.0)

        prev2_weekly_high = cache.get('prev2_weekly_high', 0.0)
        prev2_weekly_low  = cache.get('prev2_weekly_low',  0.0)

        # df_macro retained for pivot target computation (compute_pivot_targets)
        df_macro_cached  = cache.get('df_macro')
        quarterly_open   = cache.get('quarterly_open', 0.0)
        yearly_open      = cache.get('yearly_open',    0.0)

        now_et       = datetime.datetime.now(ZoneInfo("America/New_York"))
        trading_day  = now_et.weekday()          # 0 = Monday … 4 = Friday
        week_closed  = (trading_day == 4 and now_et.hour >= 16) or trading_day >= 5
        days_to_fri  = 4 if week_closed else (4 - trading_day)   # Mon=4 … Fri(pre-close)=0
        week_label   = "until current weekly expiration"

        # ── data freshness guard ──────────────────────────────────────────
        # The prior-period bins are only as good as the bars behind them. If the
        # daily feed has lagged (e.g. a weekend render whose data stops mid-week),
        # the "prior week/day/month" levels can be built on a partial period.
        # Flag it rather than present stale numbers as final. Threshold of ≥2
        # missing sessions avoids false alarms from a single market holiday.
        stale_banner = ""
        try:
            if df_macro_cached is not None and len(df_macro_cached) > 0:
                _last_bar = pd.Timestamp(df_macro_cached.index[-1]).date()
                _ref = now_et.date() if now_et.hour >= 16 else now_et.date() - datetime.timedelta(days=1)
                while _ref.weekday() >= 5:        # roll Sat/Sun back to Friday
                    _ref -= datetime.timedelta(days=1)
                _gap = max(0, len(pd.bdate_range(_last_bar, _ref)) - 1)
                if _gap >= 2:
                    stale_banner = (
                        f"<table width='100%' style='background:#2a1a00;border:2px solid #8a6d00;"
                        f"border-radius:10px;margin-bottom:16px;border-collapse:collapse;'>"
                        f"<tr><td style='padding:12px 16px;'>"
                        f"<span style='font-size:14px;font-weight:800;color:#ffd070;'>"
                        f"&#x26A0; STALE DATA &mdash; daily feed is {_gap} sessions behind</span><br>"
                        f"<span style='font-size:12px;color:#ffe6b3;line-height:1.6;'>"
                        f"Latest bar {_last_bar:%b %d}, but the last expected session is {_ref:%b %d}. "
                        f"Prior week/day/month levels may be built on a partial period &mdash; "
                        f"refresh data before trading these levels.</span></td></tr></table>")
        except Exception:
            stale_banner = ""

        # ── bar quality: where did the last closed bar finish in its range? ──
        # Streams' "bright green / bright red" read: a green day closing in the top
        # quarter of its range (or red in the bottom quarter) is conviction — the
        # side that won kept the offer/bid into the bell; continuation is favored.
        _rng = current_high - current_low
        _clv = ((current_close - current_low) / _rng) if _rng > 0 else 0.5

        # ── volume confirmation (the guide's "fourth truth") ──────────────
        vol_ratio = 0.0
        try:
            if (df_macro_cached is not None and 'Volume' in df_macro_cached.columns
                    and len(df_macro_cached) >= 21):
                _v = df_macro_cached['Volume']
                _avg20 = float(_v.iloc[-21:-1].mean())
                if _avg20 > 0:
                    vol_ratio = float(_v.iloc[-1]) / _avg20
        except Exception:
            vol_ratio = 0.0

        # ── VIX read (risk-on / risk-off tell from the streams) ───────────
        # "They're not buying the VIX on this dip" = algos not hedging = risk-on.
        vix_state, vix_chg = "", 0.0
        try:
            _vx = yf.Ticker('^VIX').history(period='5d', interval='1d')
            if _vx is not None and len(_vx) >= 1:
                _vc = float(_vx['Close'].iloc[-1]); _vo = float(_vx['Open'].iloc[-1])
                vix_chg = _vc - _vo
                vix_state = 'red' if _vc < _vo else ('green' if _vc > _vo else 'flat')
        except Exception:
            vix_state = ""

        analysis = self.analyze_strat_setups(cache)
        bull_pats = analysis['bull_patterns']
        bear_pats = analysis['bear_patterns']

        # ── session context (day-of-week mechanics from the guide) ─────────
        _dow_lines = {
            0: ("MONDAY &mdash; opens coupled", "#ffd070", "#1a1400", "#6b4d00",
                "The weekly open and daily open are the same print &mdash; the daily group "
                "carries no separate information yet. Weekly swing entries today run on less "
                "evidence; Tuesday's decoupling is the first real daily confirmation."),
            1: ("TUESDAY &mdash; daily decouples from the weekly", "#5fdd8e", "#0a1e12", "#2d7a44",
                "The daily group now prints separately from the weekly. A bright green (or red) "
                "Tuesday confirming Monday's direction is the first real swing evidence &mdash; "
                "'they bought Monday, bought Tuesday: how do you turn that around?'"),
            2: ("WEDNESDAY &mdash; mid-week reversal day", "#cc88ff", "#1a0f2a", "#7a40aa",
                "Wednesday 2-2 reversals are statistically significant &mdash; they set the tone "
                "for Thursday/Friday and still leave days for the move to work. A simultaneous "
                "2-2 today is an institutional mid-week arrival; align swing entries with it."),
            3: ("THURSDAY &mdash; late-week", "#8a9ab0", "#161920", "#2e3540",
                "Simultaneous breaks late in the week carry less weight than early-week ones. "
                "Current-week premium is mostly theta &mdash; check the Expiry row before paying it."),
            4: ("FRIDAY &mdash; expiry pressure", "#8a9ab0", "#161920", "#2e3540",
                "Early-period evidence is gone; weekly bars are closing, not opening. New daily "
                "signals that haven't triggered need next-week contracts and the weekend reset."),
        }
        session_banner = ""
        if trading_day in _dow_lines:
            _t, _c, _bg, _bd, _body = _dow_lines[trading_day]
            if trading_day == 4 and analysis.get('weekly_inside'):
                _body += (" <strong style='color:#ffd070;'>This name is inside week with one session "
                          "left &mdash; a Friday inside-week break has no week left to run: treat any "
                          "trigger as daily-scope/scalp only and let the weekly setup reload for "
                          "Monday.</strong>")
            if trading_day == 0 and analysis.get('weekly_inside'):
                _body += (" <strong style='color:#ffd070;'>This name is ALSO inside week &mdash; "
                          "maximum uncertainty; no weekly swing commitment until Tuesday "
                          "decouples and a side resolves.</strong>")
            session_banner = (
                f"<table width='100%' style='background:{_bg};border:1px solid {_bd};"
                f"border-radius:8px;margin-bottom:14px;border-collapse:collapse;'>"
                f"<tr><td style='padding:9px 14px;'>"
                f"<span style='font-size:12px;font-weight:800;color:{_c};'>&#x1F5D3; {_t}</span> "
                f"<span style='font-size:12px;color:#c8d4e0;line-height:1.6;'> &nbsp;{_body}</span>"
                f"</td></tr></table>")

        # ── 2-going-3 week: forming week broke one side, other side in range ──
        # Stream read: "two going three week" — the conversion level is itself a
        # trigger, and converting makes the week an outside bar with mother-bar
        # (prior week's full range) magnitude behind it.
        week23_banner = ""
        try:
            _wk_h = cache.get('weekly_high', 0.0); _wk_l = cache.get('weekly_low', 0.0)
            if (daily_atr > 0 and _wk_h > 0 and _wk_l > 0
                    and prev_weekly_high > 0 and prev_weekly_low > 0):
                _broke_dn = _wk_l < prev_weekly_low
                _broke_up = _wk_h > prev_weekly_high
                _conv = None
                if _broke_dn and not _broke_up and (prev_weekly_high - current_close) < 1.5 * daily_atr:
                    _conv = ("UP", prev_weekly_high, prev_weekly_high - current_close, '#5fdd8e', '#0a1e12', '#2d7a44')
                elif _broke_up and not _broke_dn and (current_close - prev_weekly_low) < 1.5 * daily_atr:
                    _conv = ("DOWN", prev_weekly_low, current_close - prev_weekly_low, '#ff8080', '#1e0a0a', '#7a2d2d')
                if _conv:
                    _d, _lv, _dist, _c, _bg, _bd = _conv
                    week23_banner = (
                        f"<table width='100%' style='background:{_bg};border:1px solid {_bd};"
                        f"border-radius:10px;margin-bottom:14px;border-collapse:collapse;'>"
                        f"<tr><td style='padding:10px 15px;'>"
                        f"<span style='font-size:13px;font-weight:800;color:{_c};'>&#x1F504; "
                        f"2-GOING-3 WEEK {_d}</span> "
                        f"<span style='font-size:12px;color:#d0dce8;line-height:1.7;'> &nbsp;This week "
                        f"already took out prior week's {'low' if _d == 'UP' else 'high'}; the other side at "
                        f"<strong style='color:{_c};'>${_lv:.2f}</strong> is only ${_dist:.2f} away "
                        f"(&lt;1.5&times; ATR). That conversion level is itself a trigger: through it, the "
                        f"week becomes an OUTSIDE bar with the prior week's full range as mother-bar "
                        f"magnitude &mdash; and everyone positioned off the first break is trapped. "
                        f"Watch it as a standalone trigger tomorrow, separate from the daily levels.</span>"
                        f"</td></tr></table>")
        except Exception:
            week23_banner = ""

        # ── Failed-2 / 50%-rule live banner ────────────────────────────────
        failed2_banner = ""
        for _f2_txt, _f2_dir, _f2c, _f2bg, _f2bd in (
                (analysis.get('failed2_bull', ''), 'BULL', '#5fdd8e', '#0a1e12', '#2d7a44'),
                (analysis.get('failed2_bear', ''), 'BEAR', '#ff8080', '#1e0a0a', '#7a2d2d')):
            if _f2_txt:
                failed2_banner += (
                    f"<table width='100%' style='background:{_f2bg};border:2px solid {_f2bd};"
                    f"border-radius:10px;margin-bottom:14px;border-collapse:collapse;'>"
                    f"<tr><td style='padding:11px 15px;'>"
                    f"<span style='font-size:13px;font-weight:800;color:{_f2c};'>"
                    f"&#x1F6A8; FAILED 2 FORMING &mdash; {_f2_dir} (50% rule, live)</span><br>"
                    f"<span style='font-size:12px;color:#d0dce8;line-height:1.7;'>{_f2_txt} "
                    f"Live read on the forming bar &mdash; it is evidence, not an in-force "
                    f"signal until the conversion level breaks.</span></td></tr></table>")

        def get_dir(seq):
            if not seq: return "UNKNOWN"
            return "UP" if "u" in seq[-1] else ("DOWN" if "d" in seq[-1] else "INSIDE")

        def dir_color(d): return "#5fdd8e" if d == "UP" else ("#ff6b6b" if d == "DOWN" else "#ffbc42")

        etf_d1_dir = get_dir(etf_cache['d1_list']) if etf_cache else "UNKNOWN"

        # ── weekly cascade detection ──────────────────────────────────────
        # Step-through bull: daily trigger sits below the weekly event level.
        # Firing the daily trigger walks price directly into a weekly structural event.
        #
        # Characterise what kind of weekly event price would hit FIRST — the gate
        # below depends on it. prev_wk_strat = the last closed weekly bar's label
        # (its high/low is the breakout/reversal target); prev2_wk_strat = the bar
        # before it (must be a 3 to call it a 3-2x-2y).
        prev_wk_strat  = cache.get('prev_weekly_strat',  '')
        prev2_wk_strat = cache.get('prev2_weekly_strat', '')

        # PROXIMITY GATE — but ONLY for the non-structural case. When the prior week
        # is an inside bar (1) it can only resolve by breaking one side of its mother
        # bar, so that mother bar's high/low IS the target no matter the distance;
        # likewise a reversal off a prior weekly 2 targets that bar's far side. Strat
        # magnitude is structural, not volatility-based, so those cases bypass the
        # gate. Only the plain "price simply sits below a prior weekly high with no
        # inside/reversal structure" case must be CLOSE (within half a daily ATR) to
        # count as cascading on the daily break. Falls back to 1% of price w/o ATR.
        _casc_gate = (0.5 * daily_atr) if daily_atr > 0 else (0.01 * current_close if current_close > 0 else None)
        def _cascade_close(gap):
            return _casc_gate is None or (0 <= gap <= _casc_gate)
        # Bull structural = inside week OR a 2-Down week (reversal-up target);
        # Bear structural = inside week OR a 2-Up week (reversal-down target).
        _bull_structural = (prev_wk_strat == '1') or ('d' in prev_wk_strat)
        _bear_structural = (prev_wk_strat == '1') or ('u' in prev_wk_strat)

        step_through_bull = (
            prev_weekly_high > current_high > current_close
            and not analysis['domino_wk_bull']   # not already a same-price direct domino
            and (_bull_structural or _cascade_close(prev_weekly_high - current_high))
        )
        step_through_bear = (
            prev_weekly_low  < current_low  < current_close
            and not analysis['domino_wk_bear']
            and (_bear_structural or _cascade_close(current_low - prev_weekly_low))
        )

        # Which weekly group is ALREADY active is the week's candle color (FTFC /
        # buy-sell list), NOT the 2u/2d trigger direction: a green week = price above
        # the weekly open = weekly BUY list = buyer group already on. A bull break only
        # "activates" the buyer if the week isn't already green; otherwise it merely
        # extends control. The genuine activation/flip is whichever group is NOT yet on.
        weekly_green = cache.get('weekly_color_green', False)
        weekly_red   = cache.get('weekly_color_red',   False)

        # The weekly reversal narrative that the daily break would create (inside-bar
        # resolve / 2-2 / 3-2x-2y) is now produced inside the unified cascade engine
        # in the Domino section — see _weekly_event_clause there. step_through_bull/
        # bear are retained below because ftfc_flip and the mother-bar runner use them.

        # Mother bar macro target: the 3's boundary 2 completed weeks back
        mother_bar_bull = prev2_weekly_high if (step_through_bull and prev2_weekly_high > prev_weekly_high) else 0.0
        mother_bar_bear = prev2_weekly_low  if (step_through_bear and 0 < prev2_weekly_low < prev_weekly_low)  else 0.0

        # FTFC flip: this trade would genuinely CREATE FTFC by activating a dormant buyer/seller group.
        # Only fires when the weekly is NOT yet aligned — if monthly+weekly are already green and
        # only the daily is temporarily down, that is not a flip, just a short-term pullback.
        # Also suppressed during the month-closed transition (monthly_open == 0) since the monthly
        # candle direction from the just-closed month already reflects the FTFC state — using it
        # to declare a "flip" when the new month hasn't opened yet is misleading.
        ftfc_flip_bull = (not analysis['ftfc_bull']
                          and analysis['monthly_green']
                          and not analysis['weekly_green']
                          and monthly_open > 0
                          and step_through_bull)
        ftfc_flip_bear = (not analysis['ftfc_bear']
                          and analysis['monthly_red']
                          and not analysis['weekly_red']
                          and monthly_open > 0
                          and step_through_bear)

        # ── expiry guidance ───────────────────────────────────────────────
        def expiry_guidance(is_cascade, has_macro, macro_tgt=0.0):
            sessions_left = days_to_fri + 1
            sess_s        = lambda n: "session" if n == 1 else "sessions"

            def _atr_reach(target, label):
                if daily_atr <= 0 or target <= 0:
                    return ""
                dist        = abs(target - current_close)
                atr_mult    = dist / daily_atr
                days_needed = max(1, math.ceil(atr_mult))
                ctx = (f"<strong>{label} (${target:.2f})</strong> is ${dist:.2f} away "
                       f"({atr_mult:.1f}&times; ATR of ${daily_atr:.2f}) &mdash; "
                       f"approximately {days_needed} trading {sess_s(days_needed)} at current volatility. ")
                if sessions_left >= days_needed:
                    ctx += (f"{sessions_left} {sess_s(sessions_left)} remain "
                            f"{week_label} &mdash; current expiration has enough time.")
                elif sessions_left + 5 >= days_needed:
                    ctx += (f"Only {sessions_left} {sess_s(sessions_left)} remain "
                            f"{week_label} &mdash; next-week expiration gives the runway needed.")
                else:
                    weeks_needed = math.ceil(days_needed / 5)
                    ctx += (f"Only {sessions_left} {sess_s(sessions_left)} remain {week_label}. "
                            f"Buy at least {weeks_needed} weeks out.")
                return ctx

            if has_macro and macro_tgt > 0:
                return _atr_reach(macro_tgt, "Full macro target")

            elif is_cascade:
                atr_note = f"Daily ATR is ${daily_atr:.2f}. " if daily_atr > 0 else ""
                atr_note += ("Management rule: if the weekly magnitude prints mid-week, that is "
                             "target exhaustion &mdash; bank it; held to Friday the premium gives "
                             "the move back. ")
                if sessions_left >= 4:
                    return (f"{atr_note}This is a weekly cascade play &mdash; the weekly trigger "
                            f"is step one and the full magnitude extends beyond it. "
                            f"Current expiration is acceptable if momentum follows immediately.")
                elif sessions_left >= 2:
                    return (f"{atr_note}Weekly cascade play &mdash; next-week expiration minimum. "
                            f"Not enough sessions remaining {week_label} for the full move to develop.")
                else:
                    return (f"{atr_note}Next-week expiration required &mdash; do not buy "
                            f"{week_label} contracts on a weekly cascade play.")

            else:
                atr_note = (f"Daily ATR is ${daily_atr:.2f}. " if daily_atr > 0 else "")
                if days_to_fri >= 3:
                    return f"{atr_note}Current week expiration &mdash; sufficient time for a daily-level move."
                elif days_to_fri >= 1:
                    return (f"{atr_note}Current week or next week. Entering Wednesday or later, "
                            "next week gives a useful buffer if the move is slow.")
                else:
                    return (f"{atr_note}Next week expiration. Do not use 0DTE expecting meaningful "
                            "follow-through &mdash; if the move has not triggered by Friday "
                            "it needs time over the weekend to set up for next week.")

        # ── pre-compute reused targets ────────────────────────────────────
        _wick_mid       = current_low + (current_high - current_low) * 0.5
        scout_dip_high  = _wick_mid            # top of the lower wick zone (long scout)
        scout_rip_low   = _wick_mid            # bottom of the upper wick zone (short scout)
        # Scout target = the FIRST real resistance/support, not a far prior-week
        # extreme. From a wick-low entry the reclaim of the trigger (current_high)
        # is the first magnet, then the weekly open, then the prior-week high.
        # Cap at the nearest level and carry the next rung for context.
        _res_ladder = sorted({lv for lv in (current_high, weekly_open, prev_weekly_high)
                              if lv and lv > _wick_mid})
        ttout_target = _res_ladder[0] if _res_ladder else current_high * 1.01
        ttout_next   = _res_ladder[1] if len(_res_ladder) > 1 else 0.0
        _sup_ladder = sorted((lv for lv in (current_low, weekly_open, prev_weekly_low)
                             if lv and lv < _wick_mid), reverse=True)
        ttout_target_b = _sup_ladder[0] if _sup_ladder else current_low * 0.99
        ttout_next_b   = _sup_ladder[1] if len(_sup_ladder) > 1 else 0.0
        prev_day_high = cache.get('prev_day_high', 0.0)
        prev_day_low  = cache.get('prev_day_low',  0.0)

        # ── pivot targets from 2-year daily data ──────────────────────────
        # Fetch one extra pivot beyond what we render: when a target coincides with a
        # higher-timeframe gate (prior week/month low/high) it's demoted to a domino
        # gate row and the next pivot beyond it is promoted to the real next target.
        bull_targets  = self.compute_pivot_targets(df_macro_cached, current_close, 'bull', max_targets=4)
        bear_targets  = self.compute_pivot_targets(df_macro_cached, current_close, 'bear', max_targets=4)

        # ── options chain + key levels (fetched once, used twice) ─────────
        yf_symbol    = TICKER_MAP.get(ticker, ticker)
        # Signal scope per side: a weekly cascade / weekly 2-2 / weekly domino is a
        # SWING play → ATM/ITM strike + an expiry with real DTE (guide: match the
        # expiration to the signal's timeframe; never weekly contracts on a weekly+
        # signal). Plain daily setups keep the slightly-OTM / nearest-expiry default.
        _swing_bull = step_through_bull or analysis['domino_wk_bull'] or analysis['weekly_22_bull']
        _swing_bear = step_through_bear or analysis['domino_wk_bear'] or analysis['weekly_22_bear']
        _min_dte    = 5 if (_swing_bull or _swing_bear) else 0
        options_html, key_levels, options_chain = self.fetch_live_options_html(
            yf_symbol, current_close, selected_expiry, min_dte=_min_dte)

        # ── magnet-zone annotator ─────────────────────────────────────────
        def magnet_note(price):
            """Return HTML annotation if price is within 1% of a key options level."""
            notes = []
            threshold = max(price * 0.01, 0.50)
            checks = [
                ('call_vol',  '&#x26A1; Call Vol Wall',  '#5fdd8e'),
                ('call_oi',   '&#x1F9F2; Call OI Wall',  '#ffbc42'),
                ('put_vol',   '&#x26A1; Put Vol Wall',   '#ff8080'),
                ('put_oi',    '&#x1F9F2; Put OI Wall',   '#ff6b6b'),
            ]
            for key, label, color in checks:
                strike, count = key_levels.get(key, (None, 0))
                if strike and abs(price - strike) <= threshold:
                    notes.append(
                        f"<span style='color:{color};font-weight:700;'>"
                        f"{label} ${strike:.2f} ({count:,})</span>")
            if not notes:
                return ''
            return ("<br><span style='font-size:11px;'>"
                    "&#x1F4CC; Options magnet: " + " &middot; ".join(notes) + "</span>")

        # ── exhaustion-density annotator (the guide's "look left" density read) ──
        # If other prior pivots cluster within ~1% of a target, everyone who bought
        # or sold there is trapped at breakeven — their exits are the profit-taking
        # wall. The denser the cluster, the heavier the exhaustion risk at the level.
        def density_note(price, targets):
            try:
                thr = max(price * 0.01, 0.50)
                n = sum(1 for t in targets
                        if t['price'] > 0 and t['price'] != price
                        and abs(t['price'] - price) <= thr)
            except Exception:
                return ''
            if n < 1:
                return ''
            return (f"<br><span style='font-size:11px;color:#ffd070;'>&#x26A0; Exhaustion "
                    f"density: {n} other prior pivot{'s' if n > 1 else ''} cluster within ~1% of "
                    f"this level &mdash; trapped breakeven exits stack here. Expect an algorithmic "
                    f"pause/snap-back; take partials, don't hold the full line through it.</span>")

        # ── multi-timeframe flip / breakout context for any price level ─────
        # Each set tracks which structural crossings have already been announced
        # for that direction so targets don't repeat what the trigger already said.
        bull_seen = set()
        bear_seen = set()

        def level_context(price, direction):
            seen  = bull_seen if direction == 'bull' else bear_seen
            notes = []
            bull  = direction == 'bull'

            def _above(ref, key):
                if ref > 0 and current_close < ref <= price and key not in seen:
                    seen.add(key)
                    return True
                return False

            def _below(ref, key):
                if ref > 0 and current_close > ref >= price and key not in seen:
                    seen.add(key)
                    return True
                return False

            if bull:
                if _above(weekly_open, 'wk_open'):
                    notes.append(("&#x1F4C8;",
                        f"Crosses above <strong>weekly open ${weekly_open:.2f}</strong> — "
                        f"week flips 2-Up. Weekly buyer group activated, multi-day run potential."))
                if _above(monthly_open, 'mo_open'):
                    notes.append(("&#x1F4C8;",
                        f"Crosses above <strong>monthly open ${monthly_open:.2f}</strong> — "
                        f"month flips green. Stock joins buy list, monthly buyer algorithm triggered. "
                f"Note: monthly-list signals routinely front-run the news &mdash; the 2-2 month kicks "
                f"in BEFORE the catalyst headline. Once on the list, a headline gap in the list's "
                f"direction is confirmation, not surprise."))
                if _above(quarterly_open, 'q_open'):
                    notes.append(("&#x1F4C8;",
                        f"Crosses above <strong>quarterly open ${quarterly_open:.2f}</strong> — "
                        f"quarter flips green. 3-month bull run potential if week confirms."))
                if _above(prev_weekly_high, 'pwh'):
                    notes.append(("&#x26A0;",
                        f"Takes out <strong>prior week high ${prev_weekly_high:.2f}</strong> — "
                        f"weekly broadening formation triggers. Trapped shorts forced to cover, "
                        f"explosive acceleration possible. Also acts as resistance if price stalls here."))
                if _above(prev_monthly_high, 'pmh'):
                    notes.append(("&#x26A0;",
                        f"Takes out <strong>prior month high ${prev_monthly_high:.2f}</strong> — "
                        f"monthly broadening formation expansion. Macro magnitude now in play; "
                        f"expect strong continuation or significant resistance at this level."))
            else:
                if _below(weekly_open, 'wk_open'):
                    notes.append(("&#x1F4C9;",
                        f"Crosses below <strong>weekly open ${weekly_open:.2f}</strong> — "
                        f"week flips 2-Down. Weekly seller group activated, multi-day drop potential."))
                if _below(monthly_open, 'mo_open'):
                    notes.append(("&#x1F4C9;",
                        f"Crosses below <strong>monthly open ${monthly_open:.2f}</strong> — "
                        f"month flips red. Stock joins sell list, monthly seller algorithm triggered."))
                if _below(quarterly_open, 'q_open'):
                    notes.append(("&#x1F4C9;",
                        f"Crosses below <strong>quarterly open ${quarterly_open:.2f}</strong> — "
                        f"quarter flips red. 3-month bear run potential if week confirms."))
                if _below(prev_weekly_low, 'pwl'):
                    notes.append(("&#x26A0;",
                        f"Takes out <strong>prior week low ${prev_weekly_low:.2f}</strong> — "
                        f"weekly broadening formation triggers. Trapped longs forced to sell, "
                        f"explosive drop possible. Also acts as support if price stalls here."))
                if _below(prev_monthly_low, 'pml'):
                    notes.append(("&#x26A0;",
                        f"Takes out <strong>prior month low ${prev_monthly_low:.2f}</strong> — "
                        f"monthly broadening formation expansion to the downside. Macro magnitude now in play."))

            return notes

        def _ctx_html(notes, color):
            if not notes:
                return ''
            lines = "".join(
                f"<br><span style='font-size:11px;color:{color};'>{icon} {text}</span>"
                for icon, text in notes)
            return lines

        # Pre-build trigger-level context so setup cards can reference them
        bull_trigger_ctx = _ctx_html(level_context(current_high, 'bull'), '#7eb8ff')
        bear_trigger_ctx = _ctx_html(level_context(current_low,  'bear'), '#ffaaaa')

        # Target-cluster / pivot-machine-gun read: 2+ prior pivots within one ATR
        # past the trigger = a stop-out cascade zone once the break goes in force.
        def _cluster_note(is_bull):
            if daily_atr <= 0:
                return ""
            trig = current_high if is_bull else current_low
            tl   = bull_targets if is_bull else bear_targets
            n = sum(1 for t in tl
                    if 0 < ((t['price'] - trig) if is_bull else (trig - t['price'])) <= daily_atr)
            if n < 2:
                return ""
            return (f"<br><span style='font-size:11px;color:#ffd070;'>&#x1F52B; Pivot-machine-gun "
                    f"zone: {n} prior pivots cluster within one ATR past the trigger &mdash; a clean "
                    f"in-force break can take them all out in sequence (stop-cover cascade). Momentum "
                    f"target: the far side of the cluster, then reassess.</span>")
        bull_trigger_ctx += _cluster_note(True)
        bear_trigger_ctx += _cluster_note(False)

        # 52-week extremes: blue sky above / capitulation below changes the read.
        try:
            _hi52 = float(df_macro_cached['High'].max())
            _lo52 = float(df_macro_cached['Low'].min())
            if _hi52 > 0 and current_high >= _hi52 * 0.99:
                bull_trigger_ctx += (
                    "<br><span style='font-size:11px;color:#7eb8ff;'>&#x1F30C; Blue sky: the trigger "
                    "sits at/near the lookback high &mdash; no left structure above. Magnitude comes "
                    "from measured moves and round numbers only; longs work but it is permanent "
                    "exhaustion-risk territory &mdash; trail, don't target.</span>")
                bear_trigger_ctx += (
                    "<br><span style='font-size:11px;color:#ffaaaa;'>At/near the lookback high: a "
                    "failed breakout up here traps the most late buyers &mdash; the bear trigger is a "
                    "fade FROM the boundary; instant-go rule applies, same-session exit if no "
                    "follow-through.</span>")
            if _lo52 > 0 and current_low <= _lo52 * 1.01:
                bear_trigger_ctx += (
                    "<br><span style='font-size:11px;color:#ffaaaa;'>&#x1F573; At/near the lookback "
                    "low &mdash; no left structure below; shorts are pressing into capitulation "
                    "territory: trail, don't target.</span>")
                bull_trigger_ctx += (
                    "<br><span style='font-size:11px;color:#7eb8ff;'>Reclaims from the lookback low "
                    "are the highest-payout reversal class (the 'reclaiming all-time lows' read) "
                    "&mdash; PMG/2-2 reversals from here run the entire ladder above.</span>")
        except Exception:
            pass

        # ── target row builder using pivot levels ─────────────────────────
        # A level too close to the trigger isn't a tradeable profit target — once
        # the bid/ask spread and theta are paid, a sub-ATR pop barely clears costs
        # (The Strat's "no magnitude = no trade"). Require T1 to sit at least this
        # far from the trigger; anything nearer is demoted to a "gate" checkpoint.
        TARGET_MIN_ATR_FRAC = 0.33
        def _min_target_mag():
            base = daily_atr * TARGET_MIN_ATR_FRAC if daily_atr > 0 else 0.0
            return max(base, current_close * 0.005)

        def _split_targets(targets, is_bull, trigger):
            """Partition pivot targets into (near_gate_or_None, real_targets).
            'real' = at least the min magnitude beyond the trigger; a single nearest
            'gate' (closer than that, but still in the trade's direction) is surfaced
            as a follow-through checkpoint. Levels behind the trigger are dropped."""
            min_mag = _min_target_mag()
            real, gates = [], []
            for t in targets:
                dist = (t['price'] - trigger) if is_bull else (trigger - t['price'])
                if dist >= min_mag:
                    real.append(t)
                elif dist > 0:
                    gates.append(t)
            near_gate = (min(gates, key=lambda g: abs(g['price'] - trigger))
                         if gates else None)
            return near_gate, real

        # When the prior bar's extreme, the weekly level and the nearest pivot all
        # sit on the same price, listing each separately reads as three targets when
        # it's really ONE level acting as a gate. Fold the cluster into the gate row
        # (checkpoint framing, no profit-taking emphasis) and drop the others.
        def _cluster_tol():
            return max(0.15, current_close * 0.001)

        def _near_gate_price(is_bull):
            tgts = bull_targets if is_bull else bear_targets
            trig = current_high if is_bull else current_low
            g, _ = _split_targets(tgts, is_bull, trig)
            return g['price'] if g else 0.0

        # Higher-timeframe structural levels (prior week / month / quarter extremes)
        # are domino GATES, not clean pivot targets: price tends to stall or bounce
        # there and only a break on expanding volume cascades the broadening formation
        # open. When such a level sits just behind a target already listed, it reads
        # better as a gate checkpoint — with the next pivot beyond it promoted to the
        # real next target — than as a second target crammed right under the first.
        def _htf_gate_label(price, is_bull):
            thr = max(0.50, price * 0.0015)
            cands = ([("prior week high",    prev_weekly_high),
                      ("prior month high",   prev_monthly_high),
                      ("prior quarter high", cache.get('prev_quarterly_high', 0.0))]
                     if is_bull else
                     [("prior week low",     prev_weekly_low),
                      ("prior month low",    prev_monthly_low),
                      ("prior quarter low",  cache.get('prev_quarterly_low', 0.0))])
            for label, lv in cands:
                if lv and abs(price - lv) <= thr:
                    return label
            return None

        def target_rows(targets, fallback_price, fallback_label, is_bull,
                        take_notes=None, trigger=None):
            if take_notes is None:
                take_notes = [
                    "Take 50&ndash;70% profits here (immediate magnitude).",
                    "Runner target — tighten stop after T1 hit.",
                    "Extended runner — trail stop, full BF boundary.",
                ]
            tc        = "#5fdd8e" if is_bull else "#ff6b6b"
            ctx_color = "#7eb8ff" if is_bull else "#ffaaaa"
            direction = "Pivot High" if is_bull else "Pivot Low"
            dir_str   = 'bull' if is_bull else 'bear'
            trig      = trigger if trigger is not None else (current_high if is_bull else current_low)
            rows = ""

            def _gate_row(price):
                mag = magnet_note(price)
                ctx = _ctx_html(level_context(price, dir_str), ctx_color)
                gap = abs(price - trig)
                pct = f", ~{gap / daily_atr * 100:.0f}% ATR" if daily_atr > 0 else ""
                # Cluster fold: if the prior bar's extreme and/or a HTF level sit on
                # this same price, name them here once instead of listing them as
                # separate magnitude rows — at gate distance there's no profit in
                # the "magnitude" read, only the checkpoint read.
                tol = _cluster_tol()
                ids = []
                imm_lvl = (prev_day_high if is_bull and prev_day_high > current_high
                           else (prev_day_low if (not is_bull) and 0 < prev_day_low < current_low
                                 else 0.0))
                if imm_lvl > 0 and abs(price - imm_lvl) <= tol:
                    ids.append(f"the prior bar's {'high' if is_bull else 'low'}")
                htf = _htf_gate_label(price, is_bull)
                if htf:
                    ids.append(f"the {htf}")
                stack = ""
                if ids:
                    stack = (f" This is also {' and '.join(ids)} &mdash; one level wearing "
                             f"{'three hats' if len(ids) > 1 else 'two hats'}, not "
                             f"{'three' if len(ids) > 1 else 'two'} separate targets.")
                mb = mother_bar_bull if is_bull else mother_bar_bear
                domino = ""
                if htf and htf.startswith("prior week") and mb > 0:
                    domino = (f" A break <strong>through</strong> it on volume dominoes the weekly "
                              f"broadening formation toward the mother-bar extreme "
                              f"<strong style='color:{tc};'>${mb:.2f}</strong>.")
                return setup_row("Gate",
                    f"<strong style='color:#ffd070;'>${price:.2f}</strong> "
                    f"(only ${gap:.2f} from the trigger{pct}) &mdash; too tight to trade to once "
                    f"spread/theta are paid.{stack} Treat as a follow-through checkpoint: trail "
                    f"through it, watch for a failed-2 stall here, and bank first profit at the "
                    f"real target below.{domino}{mag}{ctx}")

            def _domino_gate_row(t, gate_lbl, deeper):
                """A higher-TF level sitting just behind a listed target: render it as
                a domino gate (with the next pivot beyond it as the cascade target)
                instead of a second target bunched right under the first."""
                if deeper is not None:
                    nxt = (f"&rarr; next magnitude target "
                           f"<strong style='color:{tc};'>${deeper['price']:.2f}</strong> "
                           f"(Daily {direction} &mdash; {deeper['date']}).")
                else:
                    side = "below" if not is_bull else "above"
                    nxt  = (f"&rarr; opens macro broadening-formation magnitude {side} "
                            f"with no nearer pivot in range.")
                hold = "support" if not is_bull else "resistance"
                mag  = magnet_note(t['price'])
                ctx  = _ctx_html(level_context(t['price'], dir_str), ctx_color)
                return setup_row("Gate 2",
                    f"<strong style='color:#ffd070;'>${t['price']:.2f}</strong> ({gate_lbl}) &mdash; "
                    f"domino gate, not a stand-alone target: it sits just behind Target 1, so banking "
                    f"there and re-listing this double-counts the same move. Expect a stall/bounce at "
                    f"this {hold}; a break <strong>through</strong> it on expanding volume dominoes the "
                    f"broadening formation {nxt} Take Target 1 first; only press for Target 2 once this "
                    f"gate breaks with volume.{mag}{ctx}")

            if targets:
                near_gate, real = _split_targets(targets, is_bull, trig)
                if near_gate is not None:
                    rows += _gate_row(near_gate['price'])
                if real:
                    tnum, last_price = 0, None
                    # Two targets nearer than this read as "bunched"; a HTF gate this
                    # close behind a listed target is demoted rather than double-listed.
                    spacing = max(_min_target_mag(), current_close * 0.0075)
                    for idx, t in enumerate(real):
                        gate_lbl  = _htf_gate_label(t['price'], is_bull)
                        too_close = (last_price is not None
                                     and abs(t['price'] - last_price) < spacing)
                        # HTF gate bunched just behind a target already shown → demote
                        # it to a domino gate and promote the next pivot beyond it.
                        if gate_lbl and tnum >= 1 and too_close:
                            deeper = next(
                                (u for u in real[idx + 1:]
                                 if (u['price'] < t['price']) ^ is_bull), None)
                            rows += _domino_gate_row(t, gate_lbl, deeper)
                            continue
                        if tnum >= 3:
                            break
                        note = take_notes[tnum] if tnum < len(take_notes) else take_notes[-1]
                        mag  = magnet_note(t['price']) + density_note(t['price'], targets)
                        ctx  = _ctx_html(level_context(t['price'], dir_str), ctx_color)
                        tnum += 1
                        rows += setup_row(f"Target {tnum}",
                            f"<strong style='color:{tc};'>${t['price']:.2f}</strong> "
                            f"(Daily {direction} &mdash; {t['date']}) &mdash; {note}{mag}{ctx}")
                        last_price = t['price']
                    if tnum >= 1:
                        return rows
                # all pivots were gates — fall through to the structural target
            mag  = magnet_note(fallback_price) + density_note(fallback_price, targets)
            ctx  = _ctx_html(level_context(fallback_price, dir_str), ctx_color)
            rows += setup_row("Target 1",
                f"<strong style='color:{tc};'>${fallback_price:.2f}</strong> "
                f"({fallback_label}) &mdash; {take_notes[0]}{mag}{ctx}")
            return rows

        # Legacy single-target labels kept for verdict text — use the first REAL
        # target (past the gate), so the verdict never quotes a noise-level level.
        _, _bull_real = _split_targets(bull_targets, True, current_high)
        if _bull_real:
            target1_price = _bull_real[0]['price']
            target1_label = f"${target1_price:.2f} ({_bull_real[0]['date']} pivot high)"
        else:
            target1_price = prev_weekly_high if prev_weekly_high > current_high else current_high * 1.015
            target1_label = f"${target1_price:.2f} ({'Prior Week High' if prev_weekly_high > current_high else '~1.5% BF'})"
        _, _bear_real = _split_targets(bear_targets, False, current_low)
        bear_target_price = (_bear_real[0]['price'] if _bear_real else
                             (prev_weekly_low if prev_weekly_low > 0 else current_low * 0.985))

        # ── contracts to actually trade (primary + Target-1 alt) ──────────
        bull_contract = self._select_contract('bull', options_chain, current_high, target1_price,
                                              key_levels, scope='swing' if _swing_bull else 'daily')
        bear_contract = self._select_contract('bear', options_chain, current_low, bear_target_price,
                                              key_levels, scope='swing' if _swing_bear else 'daily')
        scout_bull_contract = self._select_contract('bull', options_chain, scout_dip_high,
                                                    ttout_target, key_levels)
        scout_bear_contract = self._select_contract('bear', options_chain, scout_rip_low,
                                                    ttout_target_b, key_levels)

        # ── options R/R ───────────────────────────────────────────────────
        # Prices the recommended contract through the trigger → Target 1 move
        # (theta over the hold, spread in and out) and measures it against an
        # OPT_RR_DRAWDOWN loss of the entry premium.
        RR_MIN = 1.5
        def _rr_color(rr):
            return "#5fdd8e" if rr >= 2.0 else ("#ffd070" if rr >= RR_MIN else "#ff6b6b")

        def stop_row(trigger, target, is_bull, contract, trigger_lbl=None):
            """The one stop rule: option down OPT_RR_DRAWDOWN, or price losing the
            trigger level in force — whichever comes first."""
            back = "below" if is_bull else "above"
            col  = "#ff6b6b" if is_bull else "#5fdd8e"
            dd   = int(OPT_RR_DRAWDOWN * 100)
            opt  = f"<strong style='color:{col};'>option &minus;{dd}%</strong>"
            if contract:
                o = self._option_rr(contract, is_bull, current_close, trigger, target) if target > 0 else None
                entry = o['entry'] if o else contract.get('ask', 0.0)
                if entry > 0:
                    kind = "C" if is_bull else "P"
                    opt += (f" (&asymp; ${entry * (1 - OPT_RR_DRAWDOWN):.2f} on the "
                            f"${contract['strike']:.2f}{kind} from &asymp; ${entry:.2f} "
                            f"{'modeled entry' if o else 'ask'})")
            lvl = trigger_lbl or f"the <strong style='color:{col};'>${trigger:.2f}</strong> trigger"
            return setup_row("Stop",
                f"{opt} <strong>or</strong> losing {lvl} in force &mdash; price trades back {back} "
                f"it after the break = signal failed, exit. Whichever comes first. Enter the "
                f"&minus;{dd}% as a stop order before entry &mdash; never held mentally.")

        def rr_row(trigger, target, is_bull, contract=None):
            if not contract:
                return ""
            if target <= 0 or ((target - trigger) if is_bull else (trigger - target)) <= 0:
                return setup_row("Opt R / R",
                    "<strong style='color:#ff6b6b;'>NO MAGNITUDE &mdash; SKIP.</strong> "
                    "The first real target sits at/behind the trigger; there is nothing to "
                    "trade to. No magnitude = no trade.")
            o = self._option_rr(contract, is_bull, current_close, trigger, target)
            kind = "C" if is_bull else "P"
            name = f"${contract['strike']:.2f}{kind}"
            if o is None:
                return setup_row("Opt R / R",
                    f"<span style='color:#8a9ab0;'>{name}: not enough quote data to model "
                    f"(no bid/ask or implied volatility on the chain right now).</span>")
            hold_txt = f"{o['hold']} trading day{'s' if o['hold'] != 1 else ''}"
            ask_now = contract.get('ask', 0.0)
            vs_ask = f" vs ${ask_now:.2f} ask now" if ask_now > 0 else ""
            dd = int(OPT_RR_DRAWDOWN * 100)
            if o['reward'] <= 0:
                head = (f"<strong style='color:#ff6b6b;'>NEGATIVE &mdash; theta/spread outrun the move.</strong> "
                        f"{name} is worth &asymp; ${o['at_target']:.2f} at T1 after {hold_txt}, "
                        f"below the &asymp; ${o['entry']:.2f} entry.")
            else:
                rr = o['rr']
                head = (f"<strong style='color:{_rr_color(rr)};'>{rr:.1f} : 1</strong> "
                        f"on {name} &mdash; &asymp; ${o['entry']:.2f} at the ${trigger:.2f} trigger{vs_ask}, "
                        f"&asymp; ${o['at_target']:.2f} at T1 ${target:.2f} after {hold_txt} "
                        f"(reward ${o['reward']:.2f} vs &minus;{dd}% drawdown ${o['risk']:.2f} per share).")
            spread_s = (f"spread ${o['spread']:.2f} paid in and out" if o['spread'] is not None
                        else "spread unknown (no live bid) &mdash; risk is understated")
            detail = (f"&Delta; {abs(o['delta']):.2f} at trigger &middot; IV {o['iv'] * 100:.0f}% &middot; "
                      f"theta over the hold &minus;${o['theta_cost']:.2f} &middot; {spread_s}.")
            if o['expires_first']:
                detail += (" <strong style='color:#ffd070;'>Contract expires before the hold ends"
                           "</strong> &mdash; T1 value is intrinsic only.")
            return setup_row("Opt R / R",
                head + f"<br><span style='font-size:11px;color:#8a9ab0;'>{detail} "
                f"Black-Scholes estimate on the chain's IV; ignores IV crush/expansion.</span>")

        # ── immediate magnitude (the prior bar's far extreme past the trigger) ──
        # First structural obligation of the break; exhaustion risk begins there.
        imm_bull = prev_day_high if prev_day_high > current_high else 0.0
        imm_bear = prev_day_low  if 0 < prev_day_low < current_low else 0.0
        def imm_mag_row(is_bull):
            lvl = imm_bull if is_bull else imm_bear
            if lvl <= 0:
                return ""
            # Folded into the gate row when it's the same level — see _gate_row.
            gate = _near_gate_price(is_bull)
            if gate > 0 and abs(lvl - gate) <= _cluster_tol():
                return ""
            col = "#5fdd8e" if is_bull else "#ff6b6b"
            return setup_row("Imm. mag",
                f"<strong style='color:{col};'>${lvl + (0.01 if is_bull else -0.01):.2f}</strong> "
                f"(one tick past the prior bar's {'high' if is_bull else 'low'}) &mdash; the candle's "
                f"first structural obligation. Hitting it = <strong>exhaustion risk begins</strong>: "
                f"lock partials / tighten the trail on short-dated contracts and watch the NEXT BAR, "
                f"not price &mdash; inside bar = hold the runner, {'shooter' if is_bull else 'hammer'} = "
                f"reduce, hard reversal 2 = exit the runner. The pivot targets below are the macro "
                f"boundary for runners only.")

        # ── weekly-magnitude rows (the cascade play's headline targets) ──
        # When a daily break dominoes into a weekly event, the trade's REAL targets
        # are the weekly level (weekly immediate magnitude) and the mother-bar
        # extreme (weekly macro).
        def weekly_mag_row(is_bull):
            live = (step_through_bull or analysis['domino_wk_bull']) if is_bull \
                   else (step_through_bear or analysis['domino_wk_bear'])
            wk_lvl = prev_weekly_high if is_bull else prev_weekly_low
            mb     = mother_bar_bull if is_bull else mother_bar_bear
            if not live or wk_lvl <= 0:
                return ""
            # Folded into the gate row when it's the same level — see _gate_row
            # (which also carries the mother-bar domino target in that case).
            gate = _near_gate_price(is_bull)
            if gate > 0 and abs(wk_lvl - gate) <= _cluster_tol():
                return ""
            col  = "#5fdd8e" if is_bull else "#ff6b6b"
            txt = (f"Weekly immediate magnitude <strong style='color:{col};'>${wk_lvl:.2f}</strong> "
                   f"(prior week {'high' if is_bull else 'low'} &mdash; the weekly event level)")
            if mb > 0:
                txt += f"; mother-bar macro target <strong style='color:{col};'>${mb:.2f}</strong>"
            txt += (". These targets are only in play under the instant-go rule &mdash; losing the "
                    "trigger in force ends the trade. <strong>If the weekly magnitude prints "
                    "mid-week, that IS target exhaustion: bank it</strong> &mdash; holding "
                    "short-dated premium to Friday gives the win back (theta + snap-back).")
            return setup_row("Weekly mag", txt)

        now_str = datetime.datetime.now().strftime('%Y-%m-%d %H:%M')

        # ── CSS (Qt-safe base: no grid/flex/vars. The @media block is ignored
        #    by QTextBrowser in-app and only kicks in for the exported HTML when
        #    opened on a narrow screen / phone.) ─────────────────────────────
        css = """<style>
* { box-sizing:border-box; }
body { background:#0d0f12; color:#f0f0f0;
       font-family:-apple-system,'Segoe UI',Arial,sans-serif;
       font-size:13px; line-height:1.5; padding:20px;
       -webkit-text-size-adjust:100%; }
table { max-width:100%; }
img { max-width:100%; height:auto; }

@media (max-width:600px) {
  body { padding:10px !important; font-size:12px !important; }
  table { width:100% !important; }

  /* wrap only at spaces — never shatter prices/numbers/words mid-token
     (this is what turned $135.16 into "$1 35 .16" and PATTERN into "PA TT ER N") */
  td, th { white-space:normal !important; word-break:normal !important;
           overflow-wrap:normal !important; }

  /* fixed pixel column widths (Key Levels, setup rows) → fluid */
  td[style*="width:180px"],
  td[style*="width:130px"]  { width:auto !important; }

  /* price / short-label column shrinks to fit but its value stays on one line */
  td[style*="width:90px"] { width:auto !important; white-space:nowrap !important; }

  /* pill badges (Buy List, Bull Trigger, Macro Resistance, …) stay on one line */
  span[style*="border-radius:5px"] { white-space:nowrap !important; }

  /* options chain: the two 50% columns stack vertically */
  td[width='50%'] { display:block !important; width:100% !important;
                    padding-left:0 !important; padding-right:0 !important; }

  /* market-breadth cells (4 across) stack to full width */
  td[style*="width:25%"] { display:block !important; width:100% !important;
                           margin-bottom:6px; }

  /* metric cards: 6-across squishes to one char per line → 2 per row */
  .mgrid, .mgrid tr, .mgrid tbody { display:block !important; width:100% !important; }
  .mgrid td.mcell { display:inline-block !important; width:48% !important;
                    vertical-align:top; margin:0 0 8px 0 !important;
                    padding:10px 8px !important; }
  .mgrid td.mcell div { white-space:normal !important; }

  /* dial back oversized type so it fits a phone */
  div[style*="font-size:26px"] { font-size:20px !important; }
  div[style*="font-size:16px"],
  span[style*="font-size:16px"] { font-size:14px !important; }

  /* header: drop the forced-wide right column, let badges wrap */
  td[style*="text-align:right"] { text-align:left !important;
                                  white-space:normal !important; }
  td[style*="padding:18px 24px"] { padding:12px 14px !important; }
}
</style>"""

        def seq_label(title):
            return (f"<div style='font-size:11px;font-weight:700;color:#6b7a8d;text-transform:uppercase;"
                    f"letter-spacing:0.1em;margin:20px 0 10px 0;border-bottom:1px solid #232830;"
                    f"padding-bottom:6px;'>{title}</div>")

        # ═══════════════════════════════════════════════════════════════════
        # HEADER
        # ═══════════════════════════════════════════════════════════════════
        bias_bg   = {"BULL": "#1e3a5f", "BEAR": "#3d1a1a", "NEUTRAL": "#1a1e24"}
        bias_bord = {"BULL": "#2e5d9e", "BEAR": "#7a2d2d",  "NEUTRAL": "#2e3540"}
        bias_col  = {"BULL": "#7eb8ff", "BEAR": "#ff9999",  "NEUTRAL": "#8a9ab0"}
        lt = analysis['lt_bias']
        st = analysis['st_bias']

        def bias_badge(label, direction):
            return (f"<span style='background:{bias_bg[direction]};border:1px solid {bias_bord[direction]};"
                    f"border-radius:20px;padding:6px 16px;font-size:12px;font-weight:700;"
                    f"color:{bias_col[direction]};display:inline-block;'>"
                    f"<span style='font-size:10px;font-weight:400;opacity:0.75;"
                    f"text-transform:uppercase;letter-spacing:0.06em;display:block;"
                    f"margin-bottom:2px;'>{label}</span>"
                    f"{direction}</span>")

        header = (
            f"<table width='100%' style='background:#1a1e24;border:1px solid #2e3540;"
            f"border-radius:12px;margin-bottom:16px;border-collapse:collapse;'>"
            f"<tr><td style='padding:18px 24px;'>"
            f"<div style='font-size:26px;font-weight:800;color:#ffffff;letter-spacing:-0.5px;'>"
            f"{ticker} <span style='font-size:15px;color:#8a9ab0;font-weight:400;'>· {etf_home} Sector</span></div>"
            f"<div style='font-size:12px;color:#8a9ab0;margin-top:3px;'>"
            f"Multi-timeframe Strat playbook · {now_str}</div>"
            f"</td>"
            f"<td style='padding:18px 24px;text-align:right;white-space:nowrap;'>"
            f"{bias_badge('Long Term', lt)}"
            f"&nbsp;&nbsp;"
            f"{bias_badge('Short Term', st)}"
            f"</td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # SIMULTANEOUS BREAK BANNER
        # ═══════════════════════════════════════════════════════════════════
        sync_banner = ""
        if spy_cache and etf_cache:
            sync_dir = get_dir(d1_seq)
            spy_dir = get_dir(spy_cache['d1_list'])
            etf_dir = get_dir(etf_cache['d1_list'])
            if sync_dir == etf_dir == spy_dir and sync_dir != "INSIDE":
                sync_banner = (
                    f"<table width='100%' style='background:#0a1e12;border:2px solid #2d7a44;"
                    f"border-radius:10px;margin-bottom:16px;border-collapse:collapse;'>"
                    f"<tr><td style='padding:12px 16px;'>"
                    f"<span style='font-size:14px;font-weight:800;color:#5fdd8e;'>"
                    f"&#x1F525; SIMULTANEOUS BREAK &mdash; {ticker} / {etf_home} / SPY all {sync_dir} (Daily)</span><br>"
                    f"<span style='font-size:12px;color:#c8e8d8;line-height:1.6;'>"
                    f"Institutional order flow confirmed across correlated assets simultaneously. "
                    f"Per The Strat: when the ticker, its sector ETF, and SPY all break the same direction "
                    f"at the same time, algorithm engines at every group level are active. "
                    f"<strong>Max-conviction context &mdash; but still scale in (starter on the tick, "
                    f"add as 30/60-min go in force); the 35&ndash;45% ceiling requires volume "
                    f"confirmation and the stop already working in the system.</strong> "
                    f"Sympathy scan: when the ticker and {etf_home} fire together, the whole group is "
                    f"moving &mdash; check the sector mates; the same trigger in the group's "
                    f"relative-strength leader is often the better expression of this exact signal."
                    f"</span></td></tr></table>")
            elif sync_dir == etf_dir and sync_dir != "INSIDE":
                sync_banner = (
                    f"<table width='100%' style='background:#1a1400;border:2px solid #6b4d00;"
                    f"border-radius:10px;margin-bottom:16px;border-collapse:collapse;'>"
                    f"<tr><td style='padding:12px 16px;'>"
                    f"<span style='font-size:14px;font-weight:800;color:#ffd070;'>"
                    f"&#x26A1; SECTOR BREAK &mdash; {ticker} + {etf_home} ({sync_dir}) &nbsp;&middot;&nbsp; SPY diverging ({spy_dir})</span><br>"
                    f"<span style='font-size:12px;color:#ffe6b3;line-height:1.6;'>"
                    f"Sector confirmation present but broad market not aligned. Reduce size vs full simultaneous break. "
                    f"Watch SPY for escalation or reversal before adding.</span></td></tr></table>")
            else:
                sync_banner = (
                    f"<table width='100%' style='background:#161920;border:1px solid #2e3540;"
                    f"border-radius:10px;margin-bottom:16px;border-collapse:collapse;'>"
                    f"<tr><td style='padding:12px 16px;'>"
                    f"<span style='font-size:13px;font-weight:800;color:#8a9ab0;'>NO SIMULTANEOUS ALIGNMENT (Daily)</span><br>"
                    f"<span style='font-size:12px;color:#d0d8e5;line-height:1.6;'>"
                    f"{ticker} <span style='color:{dir_color(sync_dir)};font-weight:bold;'>{sync_dir}</span> &nbsp;&middot;&nbsp; "
                    f"{etf_home} <span style='color:{dir_color(etf_dir)};font-weight:bold;'>{etf_dir}</span> &nbsp;&middot;&nbsp; "
                    f"SPY <span style='color:{dir_color(spy_dir)};font-weight:bold;'>{spy_dir}</span> "
                    f"&mdash; Asset moving on isolated flow. Lower conviction without sector/index confirmation."
                    f"</span></td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # FTFC ALERT
        # ═══════════════════════════════════════════════════════════════════
        ftfc_alert = ""
        if analysis['ftfc_bull']:
            ftfc_alert = (
                "<table width='100%' style='background:#0a1e12;border:1px solid #2d7a44;"
                "border-radius:8px;margin-bottom:14px;border-collapse:collapse;'>"
                "<tr><td style='padding:10px 14px;'>"
                "<span style='color:#5fdd8e;font-size:13px;font-weight:800;'>"
                "&#x2714; FULL TIME FRAME CONTINUITY &mdash; BULLISH</span>"
                "<span style='color:#c8e8d8;font-size:12px;'> &nbsp;Month &#x2191; &middot; "
                "Week &#x2191; &middot; Day &#x2191; &nbsp;|&nbsp; All timeframes green. "
                "The freeway is going north &mdash; maximum conviction long bias.</span>"
                "</td></tr></table>")
        elif analysis['ftfc_bear']:
            ftfc_alert = (
                "<table width='100%' style='background:#1e0a0a;border:1px solid #7a2d2d;"
                "border-radius:8px;margin-bottom:14px;border-collapse:collapse;'>"
                "<tr><td style='padding:10px 14px;'>"
                "<span style='color:#ff8080;font-size:13px;font-weight:800;'>"
                "&#x2714; FULL TIME FRAME CONTINUITY &mdash; BEARISH</span>"
                "<span style='color:#ffc8c8;font-size:12px;'> &nbsp;Month &#x2193; &middot; "
                "Week &#x2193; &middot; Day &#x2193; &nbsp;|&nbsp; All timeframes red. "
                "Sellers present at every group level.</span>"
                "</td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # POTENTIAL NEXT CANDLE — what today could form based on yesterday
        # ═══════════════════════════════════════════════════════════════════
        def potential_next_html(seq):
            if not seq:
                return ""
            last  = seq[-1]  if len(seq) >= 1 else ''
            prev  = seq[-2]  if len(seq) >= 2 else ''
            third = seq[-3]  if len(seq) >= 3 else ''

            if last == '1':
                if prev == '3':
                    name  = "3-1 Armed &mdash; Inside After Outside Bar"
                    col   = "#cc88ff"; bg = "#1a0f2a"; bord = "#7a40aa"
                    body  = (
                        "The prior bar was an outside bar (3) that set a wide range, then yesterday compressed into an inside bar (1). "
                        "This is one of the highest-conviction armed setups &mdash; the 3 established the broadening boundaries "
                        "and the inside bar is the coil.<br><br>"
                        f"<strong style='color:#5fdd8e;'>Break above yesterday's high &rarr; 3-1-2u.</strong> "
                        f"Bull target: the 3 bar's high (${prev_weekly_high:.2f} weekly boundary). "
                        f"Scout entry: dip into the wick zone before the break (triangle-they-out).<br>"
                        f"<strong style='color:#ff6b6b;'>Break below yesterday's low &rarr; 3-1-2d.</strong> "
                        f"Bear target: the 3 bar's low.<br>"
                        f"<strong style='color:#ffbc42;'>Stays inside &rarr; 3-1-1.</strong> "
                        "Double inside — even tighter compression. Next break will be extremely coiled.")
                elif 'u' in prev:
                    name  = "2-1 Armed &mdash; Inside After 2-Up"
                    col   = "#5fdd8e"; bg = "#061410"; bord = "#2d7a44"
                    third_note = (" Prior bar was a 3 &mdash; this is a 3-2u-1 coil, the full broadening setup is loading."
                                  if third == '3' else "")
                    body  = (
                        f"Yesterday was an inside bar after a 2-Up. The buyer paused but did not reverse.{third_note}<br><br>"
                        f"<strong style='color:#5fdd8e;'>Break above yesterday's high &rarr; 2-1-2u continuation.</strong> "
                        "Buyer resumed after the pause &mdash; add in force above the trigger.<br>"
                        f"<strong style='color:#ff6b6b;'>Break below yesterday's low &rarr; 2-1-2d reversal.</strong> "
                        "Seller stepped in during the compression &mdash; bear case activated.")
                elif 'd' in prev:
                    name  = "2-1 Armed &mdash; Inside After 2-Down"
                    col   = "#ff8080"; bg = "#1e0a0a"; bord = "#7a2d2d"
                    third_note = (" Prior bar was a 3 &mdash; this is a 3-2d-1 coil."
                                  if third == '3' else "")
                    body  = (
                        f"Yesterday was an inside bar after a 2-Down. The seller paused but did not reverse.{third_note}<br><br>"
                        f"<strong style='color:#5fdd8e;'>Break above yesterday's high &rarr; 2-1-2u reversal.</strong> "
                        "Buyer defended during the pause &mdash; bull case activated.<br>"
                        f"<strong style='color:#ff6b6b;'>Break below yesterday's low &rarr; 2-1-2d continuation.</strong> "
                        "Seller resuming after the pause.")
                else:
                    name  = "Inside Bar Armed &mdash; Awaiting Resolution"
                    col   = "#ffbc42"; bg = "#1a1400"; bord = "#6b4d00"
                    body  = (
                        "Yesterday was an inside bar. Both triggers are live &mdash; no directional lean until one side breaks.<br><br>"
                        "<strong style='color:#5fdd8e;'>Break above high &rarr; 2-Up (bull trigger).</strong><br>"
                        "<strong style='color:#ff6b6b;'>Break below low &rarr; 2-Down (bear trigger).</strong>")

            elif 'u' in last:
                name  = "2-Up Yesterday &mdash; Four Possible Resolutions Today"
                col   = "#5fdd8e"; bg = "#061410"; bord = "#2d7a44"
                third_note = (f" (prior bar was a 3 &mdash; this 2-Up may be the start of a 3-2u broadening move)"
                              if third == '3' else "")
                body  = (
                    f"Yesterday closed 2-Up{third_note}. Today has four possible resolutions:<br><br>"
                    "<strong style='color:#5fdd8e;'>1. 2-Up continuation:</strong> New higher high and higher low &mdash; "
                    "buyer still pressing. Trigger above today's high confirms.<br>"
                    "<strong style='color:#ff6b6b;'>2. 2-Down reversal (2-2 bear):</strong> Lower high and lower low &mdash; "
                    "buyer exhausted, seller reclaiming. Trigger below today's low.<br>"
                    "<strong style='color:#ffbc42;'>3. Inside bar (1):</strong> Stays within yesterday's range &mdash; "
                    "compression loading. Arms a 2u-1 for tomorrow's break.<br>"
                    f"<strong style='color:#cc88ff;'>4. Outside bar (3) &mdash; Triangle They Out:</strong> "
                    f"Today first breaks above yesterday's high (2-Up start), triggering stops above. "
                    f"If price then retraces back <em>below the 50% midpoint of yesterday's range "
                    f"(${(current_high + current_low) / 2:.2f})</em>, that reclaim of the midpoint is the signal &mdash; "
                    f"the liquidity collected from the upside stop sweep is now fueling a run back down "
                    f"through yesterday's low to complete the outside bar. "
                    f"Vice versa if today opens lower first: a break below yesterday's low that then reclaims above "
                    f"${(current_high + current_low) / 2:.2f} signals the downside liquidity is being used to drive price "
                    f"back up through yesterday's high. The 50% level is the pivot &mdash; "
                    f"which side of it price is on after the initial sweep tells you where it is going.")

            elif 'd' in last:
                name  = "2-Down Yesterday &mdash; Four Possible Resolutions Today"
                col   = "#ff8080"; bg = "#1e0a0a"; bord = "#7a2d2d"
                third_note = (f" (prior bar was a 3 &mdash; this 2-Down may be the start of a 3-2d broadening move)"
                              if third == '3' else "")
                body  = (
                    f"Yesterday closed 2-Down{third_note}. Today has four possible resolutions:<br><br>"
                    "<strong style='color:#ff6b6b;'>1. 2-Down continuation:</strong> New lower high and lower low &mdash; "
                    "seller still pressing. Trigger below today's low confirms.<br>"
                    "<strong style='color:#5fdd8e;'>2. 2-Up reversal (2-2 bull):</strong> Higher high and higher low &mdash; "
                    "seller exhausted, buyer reclaiming. Trigger above today's high.<br>"
                    "<strong style='color:#ffbc42;'>3. Inside bar (1):</strong> Stays within yesterday's range &mdash; "
                    "compression loading. Arms a 2d-1 for tomorrow's break.<br>"
                    f"<strong style='color:#cc88ff;'>4. Outside bar (3) &mdash; Triangle They Out:</strong> "
                    f"Today first breaks below yesterday's low (2-Down start), triggering stops below. "
                    f"If price then retraces back <em>above the 50% midpoint of yesterday's range "
                    f"(${(current_high + current_low) / 2:.2f})</em>, that reclaim of the midpoint is the signal &mdash; "
                    f"the liquidity collected from the downside stop sweep is now fueling a run back up "
                    f"through yesterday's high to complete the outside bar. "
                    f"Vice versa if today opens higher first: a break above yesterday's high that then loses "
                    f"${(current_high + current_low) / 2:.2f} signals the upside liquidity is being used to drive price "
                    f"back down through yesterday's low. The 50% level is the pivot &mdash; "
                    f"which side of it price is on after the initial sweep tells you where it is going.")

            elif last == '3':
                name  = "Outside Bar (3) Yesterday &mdash; Watch What Forms Today"
                col   = "#cc88ff"; bg = "#1a0f2a"; bord = "#7a40aa"
                body  = (
                    "Yesterday was an outside bar (3) that expanded beyond both prior boundaries. "
                    "Four resolutions are possible today:<br><br>"
                    "<strong style='color:#ffbc42;'>1. Inside bar (1) &mdash; most common:</strong> Today compresses inside yesterday's range, "
                    "arming a 3-1 setup. The next break from the 1 becomes a 3-1-2 play &mdash; "
                    "wait for tomorrow's trigger.<br>"
                    "<strong style='color:#5fdd8e;'>2. 2-Up:</strong> Takes out yesterday's high but not low &mdash; "
                    "buyer won the outside bar battle. Bull continuation in force.<br>"
                    "<strong style='color:#ff6b6b;'>3. 2-Down:</strong> Takes out yesterday's low but not high &mdash; "
                    "seller won the outside bar battle. Bear continuation in force.<br>"
                    "<strong style='color:#cc88ff;'>4. Outside bar (3) again:</strong> Takes out both yesterday's high and low &mdash; "
                    "another expansion bar. Range keeps broadening; whichever side it closes toward shows who is winning the fight.")
            else:
                return ""

            return (
                f"<table width='100%' style='background:{bg};border:2px solid {bord};"
                f"border-radius:10px;margin-bottom:16px;border-collapse:collapse;'>"
                f"<tr><td style='padding:12px 16px;'>"
                f"<span style='font-size:14px;font-weight:800;color:{col};'>"
                f"TODAY&#x2019;S POTENTIAL CANDLE: {name}</span><br><br>"
                f"<span style='font-size:12px;color:#c8d4e0;line-height:1.8;'>{body}</span>"
                f"</td></tr></table>")

        pattern_alert = potential_next_html(d1_seq)

        # ═══════════════════════════════════════════════════════════════════
        # METRICS GRID
        # ═══════════════════════════════════════════════════════════════════
        above_mo  = analysis['above_monthly_open']
        if monthly_open == 0:
            mo_color = "#8a9ab0"
            mo_txt   = "Month Closed &mdash; TBD"
        else:
            mo_color = "#5fdd8e" if above_mo else ("#ff6b6b" if above_mo is False else "#8a9ab0")
            mo_txt   = "Above MO (Buy List)" if above_mo else ("Below MO (Sell List)" if above_mo is False else "&mdash;")

        def metric_cell(label, val_html):
            return (f"<td class='mcell' style='background:#1a1e24;border:1px solid #2e3540;border-radius:8px;"
                    f"padding:11px 13px;text-align:center;'>"
                    f"<div style='font-size:10px;color:#8a9ab0;text-transform:uppercase;"
                    f"letter-spacing:0.07em;margin-bottom:4px;white-space:nowrap;'>{label}</div>"
                    f"<div style='font-size:16px;font-weight:800;white-space:nowrap;'>{val_html}</div></td>")

        atr_str = f"${daily_atr:.2f}" if daily_atr > 0 else "N/A"
        metrics = (
            "<table width='100%' class='mgrid' style='border-collapse:separate;border-spacing:8px;margin-bottom:16px;'><tr>"
            + metric_cell("Current Close",  f"<span style='color:#ffffff;'>${current_close:.2f}</span>")
            + metric_cell("Prior Day High", f"<span style='color:#5fdd8e;'>${current_high:.2f}</span>")
            + metric_cell("Prior Day Low",  f"<span style='color:#ff6b6b;'>${current_low:.2f}</span>")
            + metric_cell("Daily ATR RMA (14)", f"<span style='color:#ffbc42;'>{atr_str}</span>")
            + metric_cell("Monthly Open",   f"<span style='color:{'#8a9ab0' if monthly_open == 0 else '#cc88ff'};'>{'TBD' if monthly_open == 0 else f'${monthly_open:.2f}'}</span>")
            + metric_cell("Monthly Status", f"<span style='color:{mo_color};font-size:12px;'>{mo_txt}</span>")
            + metric_cell("Close Location",
                (lambda _rng: (f"<span style='color:{'#5fdd8e' if _clv >= 0.75 and analysis['daily_green'] else ('#ff6b6b' if _clv <= 0.25 and analysis['daily_red'] else '#8a9ab0')};'>"
                               f"{int(_clv * 100)}% of range</span>") if _rng > 0 else "N/A")
                (current_high - current_low))
            + metric_cell("Vol vs 20d Avg",
                f"<span style='color:{'#5fdd8e' if vol_ratio >= 1.5 else ('#ff6b6b' if 0 < vol_ratio < 0.7 else '#8a9ab0')};'>"
                + (f"{vol_ratio:.1f}&times;" if vol_ratio > 0 else "N/A") + "</span>")
            + "</tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # TIMEFRAME OPENS (FTFC reference levels)
        # ═══════════════════════════════════════════════════════════════════
        def open_row(label, open_price, price, show_tbd=False):
            if open_price <= 0:
                if not show_tbd:
                    return ""
                return (
                    f"<tr style='border-bottom:1px solid #1e2530;'>"
                    f"<td style='padding:9px 14px;font-size:12px;font-weight:700;color:#c8d4e0;width:130px;'>{label}</td>"
                    f"<td style='padding:9px 14px;font-size:14px;font-weight:800;color:#8a9ab0;width:100px;'>TBD</td>"
                    f"<td colspan='2' style='padding:9px 14px;'>"
                    f"<span style='font-size:12px;color:#8a9ab0;font-style:italic;'>"
                    f"Month closed &mdash; awaiting new month open</span></td>"
                    f"</tr>")
            above = price >= open_price
            status_color = "#5fdd8e" if above else "#ff6b6b"
            status_text  = "&#x2191; ABOVE" if above else "&#x2193; BELOW"
            list_txt     = "Buy List" if above else "Sell List"
            pct          = (price - open_price) / open_price * 100
            pct_str      = f"+{pct:.2f}%" if pct >= 0 else f"{pct:.2f}%"
            return (
                f"<tr style='border-bottom:1px solid #1e2530;'>"
                f"<td style='padding:9px 14px;font-size:12px;font-weight:700;color:#c8d4e0;"
                f"width:130px;'>{label}</td>"
                f"<td style='padding:9px 14px;font-size:14px;font-weight:800;color:#ffffff;"
                f"width:100px;'>${open_price:.2f}</td>"
                f"<td style='padding:9px 14px;'>"
                f"<span style='font-size:13px;font-weight:800;color:{status_color};'>{status_text}</span>"
                f"<span style='font-size:11px;color:#8a9ab0;margin-left:8px;'>by {pct_str}</span></td>"
                f"<td style='padding:9px 14px;text-align:right;'>"
                f"<span style='font-size:11px;font-weight:700;padding:3px 9px;border-radius:5px;"
                f"background:{'#0a1e12' if above else '#1e0a0a'};"
                f"color:{status_color};border:1px solid {'#2d7a44' if above else '#7a2d2d'};'>"
                f"{list_txt}</span></td>"
                f"</tr>")

        tf_opens_html = (
            seq_label("Timeframe Opens &mdash; FTFC Reference")
            + f"<table width='100%' style='background:#1a1e24;border:1px solid #2e3540;"
            f"border-radius:10px;border-collapse:collapse;margin-bottom:16px;'>"
            f"<tr style='background:#151820;'>"
            f"<th style='padding:8px 14px;font-size:10px;color:#6b7a8d;text-transform:uppercase;"
            f"letter-spacing:0.08em;font-weight:700;text-align:left;'>Timeframe</th>"
            f"<th style='padding:8px 14px;font-size:10px;color:#6b7a8d;text-transform:uppercase;"
            f"letter-spacing:0.08em;font-weight:700;text-align:left;'>Open</th>"
            f"<th style='padding:8px 14px;font-size:10px;color:#6b7a8d;text-transform:uppercase;"
            f"letter-spacing:0.08em;font-weight:700;text-align:left;'>vs Current Price</th>"
            f"<th style='padding:8px 14px;font-size:10px;color:#6b7a8d;text-transform:uppercase;"
            f"letter-spacing:0.08em;font-weight:700;text-align:right;'>Status</th>"
            f"</tr>"
            + open_row("Week", weekly_open, current_close)
            + open_row("Month", monthly_open, current_close, show_tbd=True)
            + open_row("Quarter", quarterly_open, current_close)
            + open_row("Year", yearly_open, current_close)
            + "</table>")

        # ═══════════════════════════════════════════════════════════════════
        # KEY LEVELS
        # ═══════════════════════════════════════════════════════════════════
        def level_row(name, price, desc, badge, bg, bord, nc, bb, bc):
            return (f"<tr style='background:{bg};'>"
                    f"<td style='padding:10px 14px;border:1px solid {bord};width:180px;'>"
                    f"<span style='font-size:12px;font-weight:800;color:{nc};'>{name}</span></td>"
                    f"<td style='padding:10px 14px;border-top:1px solid {bord};border-bottom:1px solid {bord};width:90px;'>"
                    f"<span style='font-size:16px;font-weight:800;color:#ffffff;'>${price:.2f}</span></td>"
                    f"<td style='padding:10px 14px;border-top:1px solid {bord};border-bottom:1px solid {bord};'>"
                    f"<span style='font-size:12px;color:#c8d4e0;'>{desc}</span></td>"
                    f"<td style='padding:10px 14px;border:1px solid {bord};text-align:right;width:130px;'>"
                    f"<span style='font-size:11px;font-weight:700;padding:4px 10px;border-radius:5px;"
                    f"background:{bb};color:{bc};'>{badge}</span></td></tr>"
                    f"<tr><td colspan='4' style='height:5px;'></td></tr>")

        levels_html = ("<div style='font-size:11px;font-weight:700;color:#6b7a8d;text-transform:uppercase;"
                       "letter-spacing:0.1em;margin:20px 0 10px 0;border-bottom:1px solid #232830;"
                       "padding-bottom:6px;'>Key Levels</div>"
                       "<table width='100%' style='border-collapse:collapse;'>")

        # Support/resistance is relative to where price is NOW — a prior level
        # that price has broken through flips role (e.g. a prior-month low that
        # price is trading below is overhead resistance, not support).
        # Warm scheme = resistance overhead; cool scheme = support below.
        _MACRO_RES = ("Macro Resistance", "#1f1820", "#6b2060", "#e080e0", "#3d1a38", "#f0a0f0")
        _MACRO_SUP = ("Macro Support",    "#101820", "#204060", "#60c0e0", "#0e2030", "#80d0f0")
        _WK_RES    = ("Resistance",       "#1f1418", "#5c2828", "#ff8080", "#3d1a1a", "#ff9999")
        _WK_SUP    = ("Support",          "#10151a", "#1a3040", "#70c8d8", "#0e2028", "#80d8e8")

        def oriented_level_row(name, price, kind):
            """Render a prior high/low, flipping support↔resistance by price position.
            kind ∈ {'PMH','PML','PWH','PWL'}."""
            overhead = price > current_close          # level sits above price → resistance
            macro    = kind in ('PMH', 'PML')
            ceil_floor = "ceiling" if kind in ('PMH', 'PWH') else "floor"
            ident = {'PMH': "Prior month's high", 'PML': "Prior month's low",
                     'PWH': "Prior week's high",  'PWL': "Prior week's low"}[kind]
            if macro:
                style = _MACRO_RES if overhead else _MACRO_SUP
                role  = ("overhead resistance" if overhead else "support below")
                desc  = f"{ident} &mdash; monthly broadening {ceil_floor}; now {role}"
            else:
                style = _WK_RES if overhead else _WK_SUP
                role  = ("first resistance / target above" if overhead
                         else "first support / target below")
                desc  = f"{ident} &mdash; {role}"
            badge, bg, bord, nc, bb, bc = style
            return level_row(name, price, desc, badge, bg, bord, nc, bb, bc)

        if prev_monthly_high > 0:
            levels_html += oriented_level_row("Prior Month High (PMH)", prev_monthly_high, 'PMH')

        if prev_weekly_high > 0:
            levels_html += oriented_level_row("Prior Week High (PWH)", prev_weekly_high, 'PWH')

        domino_note = " &mdash; DOMINO to Weekly 2-Up" if analysis['domino_wk_bull'] else ""
        levels_html += level_row("Prior Day High (PDH)", current_high,
            f"Bull trigger &mdash; break above in force (${current_high + 0.01:.2f} tick){domino_note}",
            "Bull Trigger", "#141520", "#2e2e5e", "#a080ff", "#1a1a3d", "#c0b0ff")

        mo_desc = ("Month closed &mdash; awaiting new month open" if monthly_open == 0
                   else "Above monthly open &mdash; BUY LIST" if above_mo
                   else "Below monthly open &mdash; SELL LIST")
        levels_html += level_row("Current Close", current_close,
            mo_desc, "Price", "#13161c", "#2e3540", "#c8d4e0", "#1a1e24", "#8a9ab0")

        domino_note_b = " &mdash; DOMINO to Weekly 2-Down" if analysis['domino_wk_bear'] else ""
        levels_html += level_row("Prior Day Low (PDL)", current_low,
            f"Bear trigger &mdash; break below in force (${current_low - 0.01:.2f} tick){domino_note_b}",
            "Bear Trigger", "#111820", "#1a3a5c", "#60b0ff", "#0e2040", "#90c8ff")

        if prev_weekly_low > 0:
            levels_html += oriented_level_row("Prior Week Low (PWL)", prev_weekly_low, 'PWL')

        if prev_monthly_low > 0:
            levels_html += oriented_level_row("Prior Month Low (PML)", prev_monthly_low, 'PML')

        if monthly_open > 0:
            levels_html += level_row("Monthly Open", monthly_open,
                "Above = Buy List &middot; Below = Sell List &middot; Key structural anchor",
                "Monthly Anchor", "#1a1610", "#4a3a10", "#ffbc42", "#2a2010", "#ffd070")

        levels_html += "</table>"

        # ═══════════════════════════════════════════════════════════════════
        # CANDLE SEQUENCE (daily + weekly)
        # ═══════════════════════════════════════════════════════════════════
        bar_bg    = {"2u": "#0f2d18", "2d": "#2d0f0f", "3": "#1e1020", "1": "#181c22"}
        bar_bord  = {"2u": "#2d7a44", "2d": "#7a2d2d", "3": "#7a40aa", "1": "#2e3540"}
        bar_color = {"2u": "#5fdd8e", "2d": "#ff8080", "3": "#cc88ff", "1": "#ffbc42"}

        def candle_td(label, bar_type, sub_text):
            bg = bar_bg.get(bar_type, "#181c22")
            bd = bar_bord.get(bar_type, "#2e3540")
            cl = bar_color.get(bar_type, "#8a9ab0")
            return (f"<td style='text-align:center;padding:4px;'>"
                    f"<div style='width:70px;padding:8px 4px;border-radius:6px;border:1px solid {bd};"
                    f"background:{bg};color:{cl};font-size:12px;font-weight:800;'>{label}</div>"
                    f"<div style='font-size:10px;color:#8a9ab0;font-weight:600;margin-top:3px;'>{sub_text}</div>"
                    f"</td>")

        d_labels = ["3 Days Ago", "2 Days Ago", "Yesterday"]
        w_labels = ["3 Wks Ago",  "2 Wks Ago",  "Last Week"]

        d_disp = cache.get('d1_disp', d1_seq)
        w_disp = cache.get('w1_disp', w1_seq)
        d_form = cache.get('d1_form', '')
        w_form = cache.get('w1_form', '')
        d_row = "".join(candle_td(c.upper(), c, d_labels[i]) for i, c in enumerate(d_disp))
        d_row += candle_td(d_form.upper() if d_form else "?",   d_form or "1", "Today / Open")
        w_row = "".join(candle_td(c.upper(), c, w_labels[i]) for i, c in enumerate(w_disp))
        w_row += candle_td(w_form.upper() if w_form else "TBD", w_form or "1", "This Week")

        candle_html = (seq_label("Daily Strat Candle Sequence")
                       + f"<table style='border-collapse:collapse;margin-bottom:4px;'><tr>{d_row}</tr></table>"
                       + seq_label("Weekly Strat Candle Sequence")
                       + f"<table style='border-collapse:collapse;margin-bottom:4px;'><tr>{w_row}</tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # REVERSAL CANDLES — Hammer / Shooting Star (per timeframe)
        # Reads the shape of the last CLOSED daily/weekly/monthly/quarterly bar.
        # ═══════════════════════════════════════════════════════════════════
        shapes = cache.get('candle_shapes', {}) or {}
        # Higher timeframe = a rarer, heavier signal — order top-down and weight it.
        _tf_meta = [
            ('Quarterly', 'quarterly', 'a major macro reversal tell'),
            ('Monthly',   'monthly',   'a heavyweight swing signal'),
            ('Weekly',    'weekly',    'a multi-day swing signal'),
            ('Daily',     'daily',     'an intraday-to-swing signal'),
        ]
        _strength_word = {'strong': 'Textbook', 'moderate': 'Decent', 'weak': 'Marginal'}
        # Trend context drives the read. Per the guide a hammer/shooter is NOT
        # inherently a reversal — its meaning flips with FTFC and location.
        _trend_up   = analysis['ftfc_bull'] or analysis['monthly_green'] or (analysis['above_monthly_open'] is True)
        _trend_down = analysis['ftfc_bear'] or analysis['monthly_red']   or (analysis['above_monthly_open'] is False)
        # Count shapes by type up front so we can flag time-frame escalation
        # (same shape stacking across timeframes = escalating conviction).
        _ham_tfs = [m[0] for m in _tf_meta if (shapes.get(m[1]) or {}).get('type') == 'hammer']
        _sho_tfs = [m[0] for m in _tf_meta if (shapes.get(m[1]) or {}).get('type') == 'shooter']
        _shape_rows = ""
        for tf_label, tf_key, tf_weight in _tf_meta:
            sh = shapes.get(tf_key)
            if not sh:
                continue
            is_hammer = sh['type'] == 'hammer'
            accent    = "#5fdd8e" if is_hammer else "#ff6b6b"
            icon      = "&#x1F528;" if is_hammer else "&#x2604;"   # hammer / comet
            name      = "Hammer" if is_hammer else "Shooting Star"
            body_col  = "green" if sh['green'] else "red"
            wick_pct  = (sh['lower_frac'] if is_hammer else sh['upper_frac']) * 100
            quality   = _strength_word.get(sh['strength'], 'Marginal')
            tl        = tf_label.lower()

            if is_hammer:
                # Textbook Strat hammer is a RED bar closing near its high; a green
                # one is even more bullish. Long lower wick = sellers rejected.
                base = (
                    f"Sellers drove the {tl} down then got rejected &mdash; the long lower wick "
                    f"({wick_pct:.0f}% of the bar's range) is the stop-run; buyers reclaimed into a "
                    f"{body_col} close ({'classic triangle-they-out colour' if not sh['green'] else 'green body = extra demand'}).")
                if _trend_up:
                    context = (
                        f" <strong style='color:#5fdd8e;'>With the {tl} trend up, this is a continuation "
                        f"entry, not a bottom-call</strong> &mdash; the corrective pullback stopped out weak "
                        f"longs and the buyer who owns the trend stepped back in. {tf_weight.capitalize()}.")
                elif _trend_down:
                    context = (
                        f" The broader trend is down, so this is a <strong>counter-trend</strong> bottoming "
                        f"shape &mdash; only a failed breakdown until FTFC actually starts turning up. "
                        f"{tf_weight.capitalize()}; a hammer this high up the chain is an early accumulation tell.")
                else:
                    context = f" Trend is mixed &mdash; treat as a failed breakdown that needs the reclaim to confirm. {tf_weight.capitalize()}."
                confirm = (
                    f"<strong style='color:#5fdd8e;'>Long confirms</strong> on a reclaim of the {tl} hammer high "
                    f"<strong style='color:#5fdd8e;'>${sh['h']:.2f}</strong> (a 2-up off the wick &mdash; the "
                    f"Triangle-They-Out long, Setup C). It should go almost immediately; if it stalls at that "
                    f"high, limit sellers are parked there &mdash; wait for the re-break. Stop: "
                    f"{STOP_RULE} (the hammer high is the trigger).")
                if len(_ham_tfs) > 1:
                    confirm += (f" <strong style='color:#5fdd8e;'>Escalation:</strong> hammers stacked on "
                                f"{', '.join(_ham_tfs)} &mdash; the buyer is defending at multiple group levels.")
            else:
                # Textbook Strat shooter is a GREEN bar closing near its low. Per the
                # guide it is NOT inherently bearish — context decides.
                base = (
                    f"Buyers drove the {tl} up then got rejected &mdash; the long upper wick "
                    f"({wick_pct:.0f}% of the bar's range) is the failed push; sellers reclaimed into a "
                    f"{body_col} close ({'classic shooter colour' if sh['green'] else 'red body = extra supply'}).")
                if _trend_down:
                    context = (
                        f" <strong style='color:#ff6b6b;'>With the {tl} trend down, this is with-the-seller "
                        f"&mdash; a genuine bearish continuation / reversal shape.</strong> {tf_weight.capitalize()}.")
                elif _trend_up:
                    context = (
                        f" <strong style='color:#ffd070;'>In this uptrend a shooter is profit-taking, NOT a short</strong> "
                        f"&mdash; the mirror of triangle-they-out. Per the guide it only becomes a sell when "
                        f"(1)&nbsp;FTFC turns down, (2)&nbsp;it sits at a broadening-formation exhaustion top, or "
                        f"(3)&nbsp;it's at weekly/monthly-open resistance. Otherwise it's just a pause.")
                else:
                    context = f" Trend is mixed &mdash; a failed breakout that needs the break of its low (and FTFC) to mean anything. {tf_weight.capitalize()}."
                confirm = (
                    f"<strong style='color:#ff6b6b;'>Short confirms only</strong> on a break of the {tl} shooter low "
                    f"<strong style='color:#ff6b6b;'>${sh['l']:.2f}</strong> (a 2-down off the wick &mdash; the "
                    f"Downside Scout, Setup C). Stop: {STOP_RULE} (the shooter low is the trigger).")
                if len(_sho_tfs) > 1:
                    confirm += (f" <strong style='color:#ff6b6b;'>Escalation:</strong> shooters stacked on "
                                f"{', '.join(_sho_tfs)} &mdash; sellers defending at multiple group levels.")

            _shape_rows += (
                f"<tr><td style='padding:11px 14px;border-bottom:1px solid #232830;"
                f"font-size:12px;line-height:1.6;vertical-align:top;'>"
                f"<div style='font-weight:800;color:{accent};margin-bottom:4px;'>"
                f"{icon} {tf_label} {name}"
                f"<span style='font-size:10px;font-weight:700;padding:2px 8px;border-radius:10px;"
                f"background:#1a1e24;border:1px solid #2e3540;color:#8a9ab0;margin-left:8px;'>"
                f"{quality} &middot; {body_col}-bodied</span></div>"
                f"<span style='color:#c8d4e0;'>{base}{context}</span><br>"
                f"<span style='color:#a8b4c0;'>{confirm}</span>"
                f"</td></tr>")

        if _shape_rows:
            candle_shape_html = (
                seq_label("Reversal Candles &mdash; Hammer / Shooting Star")
                + f"<table width='100%' style='background:#12151b;border:1px solid #232830;"
                f"border-radius:8px;border-collapse:collapse;margin-bottom:6px;'>"
                f"{_shape_rows}</table>")
        else:
            candle_shape_html = (
                seq_label("Reversal Candles &mdash; Hammer / Shooting Star")
                + f"<table width='100%' style='background:#12151b;border:1px solid #232830;"
                f"border-radius:8px;border-collapse:collapse;margin-bottom:6px;'>"
                f"<tr><td style='padding:11px 14px;font-size:12px;line-height:1.6;color:#6b7a8d;'>"
                f"No hammer or shooting star on the last closed daily, weekly, monthly, or quarterly "
                f"candle &mdash; all ordinary bodies. Nothing to fade or follow on shape alone.</td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # DOMINO ANALYSIS
        # ═══════════════════════════════════════════════════════════════════
        domino_rows = ""

        # ═══ UNIFIED CASCADE ENGINE ═══════════════════════════════════════════
        # One model for every "daily break takes out a higher-timeframe prior HIGH
        # (bull) / LOW (bear)" event — merging the old domino, step-through and
        # untested-liquidity rows. Each prior weekly/monthly/quarterly level is
        # classified by HOW the daily break reaches it:
        #   • domino — the level sits between price and the trigger, so breaking the
        #              daily trigger takes it out on the same move;
        #   • step   — the level sits just beyond the trigger but within a session's
        #              reach (<= daily ATR), so the break walks into it;
        #   • (skip) — already cleared, or too far to reach this session.
        # VIRGINITY (untested since forming) is the accelerant: resting orders only
        # still pool at levels price has NOT traded back through. The weekly level
        # additionally folds in its reversal narrative + buy/sell-list activation.
        _reach = daily_atr if daily_atr > 0 else (0.01 * current_close if current_close > 0 else 0.0)

        def _virgin_clause(is_high, virgin):
            if virgin:
                stops = ("breakout buy-stops and resting sell orders" if is_high
                         else "breakdown sell-stops and resting bids")
                return (f" The level is <strong>virgin</strong> &mdash; untested since it formed &mdash; so "
                        f"{stops} still pool there; taking it out can <strong>accelerate</strong> the move as "
                        f"that liquidity fires.")
            return (" The level has already been tested since forming, so the resting orders there are largely "
                    "gone &mdash; expect little extra acceleration from it.")

        def _weekly_event_clause(is_bull):
            if is_bull:
                if prev_wk_strat == '1':
                    return "resolves the inside week up into a weekly 2-Up"
                if prev2_wk_strat == '3' and 'd' in prev_wk_strat:
                    return "completes a 3-2d-2u weekly reversal, forcing trapped weekly shorts to cover"
                if 'd' in prev_wk_strat:
                    return "flips the 2-Down week to a 2-Up, trapping the shorts who sold the breakdown"
                return "prints a weekly 2-Up"
            if prev_wk_strat == '1':
                return "resolves the inside week down into a weekly 2-Down"
            if prev2_wk_strat == '3' and 'u' in prev_wk_strat:
                return "completes a 3-2u-2d weekly reversal, forcing trapped weekly longs to sell"
            if 'u' in prev_wk_strat:
                return "flips the 2-Up week to a 2-Down, trapping the longs who bought the breakout"
            return "prints a weekly 2-Down"

        def _weekly_state_clause(is_bull):
            if is_bull:
                if weekly_green:
                    return (" The week is already green (weekly BUY list) &mdash; this extends an active buyer, "
                            "not a fresh activation.")
                if weekly_red:
                    return (" &#x1F504; The week is currently red (weekly SELL list) &mdash; clearing the weekly "
                            "high flips it green and newly activates the weekly buyer group: the highest-"
                            "conviction version.")
            else:
                if weekly_red:
                    return (" The week is already red (weekly SELL list) &mdash; this extends an active seller, "
                            "not a fresh activation.")
                if weekly_green:
                    return (" &#x1F504; The week is currently green (weekly BUY list) &mdash; losing the weekly "
                            "low flips it red and newly activates the weekly seller group: the highest-"
                            "conviction version.")
            return ""

        # (timeframe, prior_high, high_virgin, prior_low, low_virgin)
        _tf_levels = [
            ("weekly",    prev_weekly_high,  cache.get('prev_weekly_high_virgin', False),
                          prev_weekly_low,   cache.get('prev_weekly_low_virgin',  False)),
            ("monthly",   prev_monthly_high, cache.get('prev_monthly_high_virgin', False),
                          prev_monthly_low,  cache.get('prev_monthly_low_virgin',  False)),
            ("quarterly", cache.get('prev_quarterly_high', 0.0), cache.get('prev_quarterly_high_virgin', False),
                          cache.get('prev_quarterly_low',  0.0), cache.get('prev_quarterly_low_virgin',  False)),
        ]

        def _classify(level, is_high, structural):
            """How does a daily break reach this level? -> ('domino'|'step', dist) or (None, 0)."""
            if level <= 0 or _reach <= 0:
                return None, 0.0
            if is_high:
                if level < current_close:                 # already cleared overhead
                    return None, 0.0
                if level <= current_high:                 # between price and trigger -> same break
                    return 'domino', level - current_close
                if (level - current_high) <= _reach or structural:
                    return 'step', level - current_close
                return None, 0.0
            if level > current_close:                     # already cleared below
                return None, 0.0
            if level >= current_low:
                return 'domino', current_close - level
            if (current_low - level) <= _reach or structural:
                return 'step', current_close - level
            return None, 0.0

        def _cascade_row(tf, level, virgin, relation, dist, is_bull):
            is_high = is_bull
            trig    = current_high if is_bull else current_low
            ecol    = "#5fdd8e" if is_bull else "#ff6b6b"
            tcol    = "#c8e8d8" if is_bull else "#ffc8c8"
            arrow   = "&#x1F4C8;" if is_bull else "&#x1F4C9;"
            ud      = "2-Up" if is_bull else "2-Down"
            updn    = "above" if is_bull else "below"
            hl      = "high" if is_high else "low"
            tname   = "bull" if is_bull else "bear"
            if relation == 'domino':
                lead = (f"Breaking the daily {tname} trigger (<strong>${trig:.2f}</strong>) "
                        f"<strong>simultaneously</strong> takes out the prior {tf} {hl} "
                        f"<strong style='color:{ecol};'>${level:.2f}</strong>")
            else:
                pct = f", ~{dist / daily_atr * 100:.0f}% ATR" if daily_atr > 0 else ""
                lead = (f"Breaking the daily {tname} trigger (<strong>${trig:.2f}</strong>) walks price {updn} "
                        f"the prior {tf} {hl} <strong style='color:{ecol};'>${level:.2f}</strong> "
                        f"(<strong>${dist:.2f}</strong>{pct} away)")
            if tf == "weekly":
                mb     = mother_bar_bull if is_bull else mother_bar_bear
                runner = (f" Next weekly boundary / runner target: "
                          f"<strong style='color:{ecol};'>${mb:.2f}</strong>." if mb > 0 else "")
                tail   = f" &mdash; that {_weekly_event_clause(is_bull)}." + _weekly_state_clause(is_bull) + runner
            else:
                tail   = f" &mdash; a {tf} {ud} on the same break."
            return (
                f"<tr><td style='padding:8px 14px;border-bottom:1px solid #232830;font-size:12px;line-height:1.6;'>"
                f"<span style='color:{ecol};font-weight:700;'>{arrow} CASCADE &mdash; {tf.upper()} "
                f"{'BULL' if is_bull else 'BEAR'}:</span> "
                f"<span style='color:{tcol};'>{lead}{tail}{_virgin_clause(is_high, virgin)}</span></td></tr>")

        for _is_bull in (True, False):
            _structural = _bull_structural if _is_bull else _bear_structural
            _hits = []
            for tf, ph, phv, pl, plv in _tf_levels:
                lvl, vrg = (ph, phv) if _is_bull else (pl, plv)
                rel, dist = _classify(lvl, _is_bull, _structural and tf == "weekly")
                if rel:
                    _hits.append((tf, lvl, vrg, rel, dist))
            for tf, lvl, vrg, rel, dist in sorted(_hits, key=lambda x: x[4]):
                domino_rows += _cascade_row(tf, lvl, vrg, rel, dist, _is_bull)
            # Stacked virgin liquidity: 2+ untested levels in reach on the same side.
            _virg = [h for h in _hits if h[2]]
            if len(_virg) >= 2:
                _lo = min(h[1] for h in _virg); _hi = max(h[1] for h in _virg)
                _names = ", ".join(h[0] for h in sorted(_virg, key=lambda x: x[1]))
                _col = "#5fdd8e" if _is_bull else "#ff6b6b"
                domino_rows += (
                    f"<tr><td style='padding:8px 14px;border-bottom:1px solid #232830;font-size:12px;line-height:1.6;'>"
                    f"<span style='color:#ffbc42;font-weight:700;'>&#x26A1; STACKED LIQUIDITY &mdash; "
                    f"{'BULL' if _is_bull else 'BEAR'}:</span> "
                    f"<span style='color:#ffe6b3;'>{len(_virg)} untested prior levels ({_names}) are stacked "
                    f"between <strong style='color:{_col};'>${_lo:.2f}</strong> and "
                    f"<strong style='color:{_col};'>${_hi:.2f}</strong> within one session's reach &mdash; a break "
                    f"that clears the cluster can cascade through all of them as the layered resting orders fire "
                    f"together.</span></td></tr>")

        # Weekly → Monthly domino — weekly-driven (price clearing a monthly level while
        # the week is already green/red); kept distinct from the daily-break engine above.
        if analysis['domino_mo_bull']:
            domino_rows += (
                "<tr><td style='padding:8px 14px;font-size:12px;line-height:1.6;'>"
                "<span style='color:#cc88ff;font-weight:700;'>&#x1F4C8; WEEKLY &rarr; MONTHLY DOMINO:</span> "
                "<span style='color:#e0d0f8;'>Weekly is already green AND price has cleared a monthly structural level. "
                "Multi-timeframe cascade in effect &mdash; broadening formation target extends to monthly boundaries.</span></td></tr>")
        if analysis['domino_mo_bear']:
            domino_rows += (
                "<tr><td style='padding:8px 14px;border-bottom:1px solid #232830;font-size:12px;line-height:1.6;'>"
                "<span style='color:#ff8080;font-weight:700;'>&#x1F4C9; WEEKLY &rarr; MONTHLY DOMINO (BEAR):</span> "
                "<span style='color:#ffc8c8;'>Weekly is red AND price has broken a monthly structural level. "
                "Multi-timeframe cascade to the downside &mdash; macro broadening formation lower boundary in play.</span></td></tr>")

        # ── timeframe-open color-flip cascades (weekly / monthly / quarterly / yearly) ──
        # A higher-timeframe candle is green or red by its OPEN, not by a 2u/2d break:
        # price above the open = that timeframe on the BUY list (buyer group active),
        # below = SELL list (seller active). If today's daily break carries price across
        # one of those opens, that timeframe FLIPS color and its buyer/seller group
        # activates — a real cascade. Flag any open within one daily ATR of price (in
        # reach this session), naming the level it would near/cross and the group it arms.
        if daily_atr > 0:
            _tf_opens = [
                ("weekly",    "week",    weekly_open),
                ("monthly",   "month",   monthly_open),
                ("quarterly", "quarter", quarterly_open),
                ("yearly",    "year",    yearly_open),
            ]
            for _adj, _noun, _open in _tf_opens:
                if _open <= 0:
                    continue
                _d    = _open - current_close      # >0 open above price (bull flip); <0 below (bear flip)
                _dist = abs(_d)
                if _dist > daily_atr:
                    continue                       # beyond one-session reach — not yet in play
                _near    = _dist <= 0.6 * daily_atr
                _pct_atr = (_dist / daily_atr) * 100
                if _d > 0:
                    # price below the open → timeframe RED (sell list) → a bull break flips it green
                    _move = (
                        f"A daily 2-Up (break above <strong>${current_high:.2f}</strong>) would "
                        + (f"<strong>clear</strong> the {_adj} open; crossing it"
                           if _near else
                           f"bring the {_adj} open into range; a continued push across it would")
                        + f" flip the {_noun} <strong>green</strong> and activate the {_adj} buyer group")
                    domino_rows += (
                        f"<tr><td style='padding:8px 14px;border-bottom:1px solid #232830;font-size:12px;line-height:1.6;'>"
                        f"<span style='color:#5fdd8e;font-weight:700;'>&#x1F4C8; {_adj.upper()} OPEN FLIP &mdash; BULL:</span> "
                        f"<span style='color:#c8e8d8;'>Price <strong>${current_close:.2f}</strong> sits "
                        f"<strong>${_dist:.2f}</strong> (~{_pct_atr:.0f}% ATR) below the {_adj} open "
                        f"<strong style='color:#5fdd8e;'>${_open:.2f}</strong> &mdash; the {_noun} is currently "
                        f"<strong>red</strong> ({_adj} SELL list), so its buyer group is dormant. {_move} "
                        f"&mdash; a higher-timeframe cascade.</span></td></tr>")
                else:
                    # price above the open → timeframe GREEN (buy list) → a bear break flips it red
                    _move = (
                        f"A daily 2-Down (break below <strong>${current_low:.2f}</strong>) would "
                        + (f"<strong>lose</strong> the {_adj} open; breaking it"
                           if _near else
                           f"press toward the {_adj} open; a continued drop through it would")
                        + f" flip the {_noun} <strong>red</strong> and activate the {_adj} seller group")
                    domino_rows += (
                        f"<tr><td style='padding:8px 14px;border-bottom:1px solid #232830;font-size:12px;line-height:1.6;'>"
                        f"<span style='color:#ff6b6b;font-weight:700;'>&#x1F4C9; {_adj.upper()} OPEN FLIP &mdash; BEAR:</span> "
                        f"<span style='color:#ffc8c8;'>Price <strong>${current_close:.2f}</strong> sits "
                        f"<strong>${_dist:.2f}</strong> (~{_pct_atr:.0f}% ATR) above the {_adj} open "
                        f"<strong style='color:#ff6b6b;'>${_open:.2f}</strong> &mdash; the {_noun} is currently "
                        f"<strong>green</strong> ({_adj} BUY list). {_move} "
                        f"&mdash; a higher-timeframe cascade.</span></td></tr>")

        # (Prior-swing virgin-liquidity cascades are now produced by the unified
        #  cascade engine above — domino / step-through / virginity in one model.)

        if ftfc_flip_bull:
            domino_rows += (
                "<tr><td style='padding:8px 14px;border-bottom:1px solid #232830;font-size:12px;line-height:1.6;'>"
                "<span style='color:#ffbc42;font-weight:700;'>&#x26A1; FTFC FLIP POTENTIAL &mdash; BULL:</span> "
                "<span style='color:#ffe6b3;'>Monthly is already green but Full Timeframe Continuity is not yet active. "
                "If this trade triggers a weekly 2-Up, the monthly &ndash; weekly &ndash; daily alignment achieves FTFC &mdash; "
                "activating the monthly buyer algorithm group that is currently dormant. "
                "A trade that <em>creates</em> FTFC mid-move is more explosive than trading into existing FTFC "
                "because it brings in a fresh institutional buyer group. Size for a multi-session runner "
                "if the weekly trigger clears.</span></td></tr>")

        if ftfc_flip_bear:
            domino_rows += (
                "<tr><td style='padding:8px 14px;font-size:12px;line-height:1.6;'>"
                "<span style='color:#ffbc42;font-weight:700;'>&#x26A1; FTFC FLIP POTENTIAL &mdash; BEAR:</span> "
                "<span style='color:#ffe6b3;'>Monthly is already red but Full Timeframe Continuity is not yet active. "
                "If this trade triggers a weekly 2-Down, monthly &ndash; weekly &ndash; daily achieves FTFC bear &mdash; "
                "activating the monthly seller group. A trade that creates FTFC bear is more explosive than "
                "trading into existing bearish FTFC. Size for a multi-session runner if the weekly trigger breaks.</span></td></tr>")

        domino_html = ""
        if domino_rows:
            domino_html = (seq_label("Timeframe Cascade &mdash; Resting-Order Liquidity")
                           + f"<table width='100%' style='background:#181c22;border:1px solid #2e3540;"
                           f"border-radius:8px;border-collapse:collapse;margin-bottom:16px;'>"
                           f"{domino_rows}</table>")

        # ═══════════════════════════════════════════════════════════════════
        # SETUP CARDS A / B / C
        # ═══════════════════════════════════════════════════════════════════
        def setup_row(key, val):
            return (f"<tr><td style='font-size:11px;font-weight:800;text-transform:uppercase;"
                    f"letter-spacing:0.03em;margin-top:1px;padding-bottom:6px;width:90px;"
                    f"vertical-align:top;'>{key}</td>"
                    f"<td style='font-size:12px;line-height:1.5;padding-bottom:6px;'>{val}</td></tr>")

        # Conviction → size discipline: FTFC-aligned = full; with-monthly = half;
        # counter to the monthly = reduced. Drives the Size row in each card.
        bull_conv = 'high' if analysis['ftfc_bull'] else ('partial' if analysis['monthly_green'] else 'counter')
        bear_conv = 'high' if analysis['ftfc_bear'] else ('partial' if analysis['monthly_red'] else 'counter')

        # ── options-chain conviction modifier (confirmatory only — NEVER flips
        # direction). Fresh positioning aligned with the setup bumps conviction;
        # a dealer wall capping the runner just past the trigger trims it. ──
        _CONV_LADDER = ['counter', 'partial', 'high']
        def _adj_conv(conv, delta):
            if conv not in _CONV_LADDER:
                return conv                       # 'scout' left untouched
            return _CONV_LADDER[max(0, min(len(_CONV_LADDER) - 1, _CONV_LADDER.index(conv) + delta))]

        def _chain_modifier(is_bull):
            """Return (conviction delta, [notes]) the options chain implies for a side."""
            delta, notes = 0, []
            fstrike, fvol, foi = key_levels.get('call_fresh' if is_bull else 'put_fresh', (None, 0, 0))
            if fstrike is not None:
                delta += 1
                side = 'call' if is_bull else 'put'
                notes.append(
                    f"&#x1F195; Fresh {side} positioning at ${fstrike:.2f} "
                    f"(vol {fvol:,} vs OI {foi:,}) &mdash; new money aligned with the "
                    f"{'long' if is_bull else 'short'}; +1 conviction.")
            wstrike, wct = key_levels.get('call_oi' if is_bull else 'put_oi', (None, 0))
            trig = current_high if is_bull else current_low
            if wstrike is not None and daily_atr > 0:
                room = (wstrike - trig) if is_bull else (trig - wstrike)
                if 0 < room < 0.5 * daily_atr:
                    delta -= 1
                    notes.append(
                        f"&#x1F9F1; Dealer {'call' if is_bull else 'put'} wall at ${wstrike:.2f} "
                        f"({wct:,}) caps the runner only ${room:.2f} past the trigger "
                        f"(&lt;0.5&times; ATR) &mdash; trim target/size; &minus;1 conviction.")
            return delta, notes

        # ── macro-horizon check (guide): a trigger firing directly into a TESTED
        # higher-timeframe boundary has little fresh magnitude — the resting orders
        # at a non-virgin level are largely spent, so it's exhaustion risk, not
        # cascade fuel. Virgin levels keep their (positive) cascade treatment.
        def _htf_headroom_modifier(is_bull):
            delta, notes = 0, []
            if daily_atr <= 0:
                return delta, notes
            trig = current_high if is_bull else current_low
            levels = ([("prior week high",  prev_weekly_high,  cache.get('prev_weekly_high_virgin',  False)),
                       ("prior month high", prev_monthly_high, cache.get('prev_monthly_high_virgin', False))]
                      if is_bull else
                      [("prior week low",   prev_weekly_low,   cache.get('prev_weekly_low_virgin',   False)),
                       ("prior month low",  prev_monthly_low,  cache.get('prev_monthly_low_virgin',  False))])
            for lbl, lv, virgin in levels:
                if lv <= 0 or virgin:
                    continue
                room = (lv - trig) if is_bull else (trig - lv)
                if 0 < room < 0.5 * daily_atr:
                    delta -= 1
                    notes.append(
                        f"&#x26F0; Macro horizon check: TESTED {lbl} ${lv:.2f} sits only "
                        f"${room:.2f} past the trigger (&lt;0.5&times; ATR). Triggering straight "
                        f"into a spent macro boundary leaves the {'long' if is_bull else 'short'} "
                        f"with little fresh magnitude &mdash; exhaustion risk, not cascade fuel; "
                        f"&minus;1 conviction. Trade only if the level breaks on expanding volume.")
                    break
            return delta, notes

        # ── volume confirmation modifier (the "fourth truth") ──────────────
        def _volume_modifier(is_bull):
            aligned = analysis['daily_green'] if is_bull else analysis['daily_red']
            if vol_ratio >= 1.5 and aligned:
                return 1, [(f"&#x1F50A; Volume confirmation: today is running "
                            f"{vol_ratio:.1f}&times; the 20-day average with the daily candle "
                            f"in the trade's direction &mdash; institutional participation; "
                            f"+1 conviction.")]
            if 0 < vol_ratio < 0.7:
                return 0, [(f"&#x1F507; Thin tape: volume at {vol_ratio:.1f}&times; the 20-day "
                            f"average &mdash; breaks on volume this light are fade-prone; do not "
                            f"size up the ladder without expansion.")]
            return 0, []

        _bull_delta, bull_chain_notes = _chain_modifier(True)
        _bear_delta, bear_chain_notes = _chain_modifier(False)
        for _fn in (_htf_headroom_modifier, _volume_modifier):
            _d, _n = _fn(True);  _bull_delta += _d; bull_chain_notes += _n
            _d, _n = _fn(False); _bear_delta += _d; bear_chain_notes += _n
        bull_conv = _adj_conv(bull_conv, _bull_delta)
        bear_conv = _adj_conv(bear_conv, _bear_delta)

        def chain_note_row(notes):
            return setup_row("Chain", " ".join(notes)) if notes else ""

        # ── directional bias: which side is the A-play ────────────────────────
        # FTFC lean across Month/Week/Day decides which directional setup is the
        # headline. When the higher timeframes line up one way, the counter-trend
        # side must NOT get equal billing — it's a fade, not a primary play.
        _greens = sum([analysis['monthly_green'], analysis['weekly_green'], analysis['daily_green']])
        _reds   = sum([analysis['monthly_red'],   analysis['weekly_red'],   analysis['daily_red']])
        bear_bias = _reds >= 2 and _reds > _greens
        bull_bias = _greens >= 2 and _greens > _reds

        def _badge(txt, bg, col):
            return (f"<span style='font-size:11px;font-weight:700;padding:3px 10px;border-radius:12px;"
                    f"background:{bg};color:{col};margin-left:8px;'>{txt}</span>")
        if bear_bias:
            bull_badge_html = _badge("Counter-Trend &middot; Fade Only", "#3a2a0a", "#ffd070")
            bear_badge_html = _badge("Highest Conviction &middot; FTFC Aligned", "#6b1d1d", "#ffaaaa")
        elif bull_bias:
            bull_badge_html = _badge("Highest Conviction &middot; FTFC Aligned", "#1d6b35", "#9feebc")
            bear_badge_html = _badge("If Bull Fails", "#6b1d1d", "#ffaaaa")
        else:
            bull_badge_html = _badge("Primary Bull", "#1d6b35", "#9feebc")
            bear_badge_html = _badge("If Bull Fails", "#6b1d1d", "#ffaaaa")

        # Session-aware trigger label. bull_trigger/bear_trigger come from the most
        # recently CLOSED daily bar; when the session is live that bar is the PRIOR
        # day (often the inside bar of a 3-1), so "today's high" is wrong — only
        # after the close is the trigger bar actually today's.
        _day_closed = cache.get('day_closed', True)
        trig_hi_lbl = "today's high" if _day_closed else "the prior session's high"
        trig_lo_lbl = "today's low"  if _day_closed else "the prior session's low"

        # Setup A — Primary Bull
        if bull_pats:
            pat_name, pat_desc = bull_pats[0]
            ftfc_line = ("Month &#x2191; &middot; Week &#x2191; &middot; Day &#x2191; &mdash; FTFC fully aligned. Maximum conviction."
                         if analysis['ftfc_bull']
                         else f"Month {'&#x2191;' if analysis['monthly_green'] else '&#x2193;'} &middot; "
                              f"Week {'&#x2191;' if analysis['weekly_green'] else '&#x2193;'} &middot; "
                              f"Day {'&#x2191;' if analysis['daily_green'] else '&#x2193;'} &mdash; Partial FTFC. Confirm hourly before full size.")
            setup_a = (
                f"<table width='100%' style='border:2px solid #2d7a44;border-radius:10px;"
                f"overflow:hidden;margin-bottom:10px;border-collapse:collapse;'>"
                f"<tr style='background:#0a2018;'><td style='padding:11px 16px;font-size:13px;"
                f"font-weight:700;color:#5fdd8e;'>A &mdash; {pat_name} (PRIMARY BULL)"
                f"{bull_badge_html}</td></tr>"
                f"<tr style='background:#061410;'><td style='padding:12px 16px;'>"
                f"<table width='100%' style='color:#c8e8d8;'>"
                + setup_row("Pattern", pat_desc)
                + setup_row("Trigger",
                    f"Break above {trig_hi_lbl} <strong style='color:#5fdd8e;'>${current_high:.2f}</strong> "
                    f"in force (${current_high + 0.01:.2f} tick). Do NOT enter before this prints."
                    + bull_trigger_ctx)
                + imm_mag_row(True)
                + weekly_mag_row(True)
                + target_rows(bull_targets, target1_price, target1_label, True)
                + stop_row(current_high, target1_price, True, bull_contract)
                + rr_row(current_high, target1_price, True, bull_contract)
                + self._options_rows(setup_row, 'bull', bull_contract, bull_conv)
                + chain_note_row(bull_chain_notes)
                + setup_row("FTFC", ftfc_line)
                + setup_row("Expiry", expiry_guidance(step_through_bull, mother_bar_bull > 0, mother_bar_bull))
                + "</table></td></tr></table>")
        else:
            # No named pattern — forced structural bull thesis from price levels alone
            forced_ftfc = (
                "Month &#x2191; &middot; Week &#x2191; &middot; Day &#x2191; &mdash; FTFC fully aligned. Maximum conviction."
                if analysis['ftfc_bull']
                else f"Month {'&#x2191;' if analysis['monthly_green'] else '&#x2193;'} &middot; "
                     f"Week {'&#x2191;' if analysis['weekly_green'] else '&#x2193;'} &middot; "
                     f"Day {'&#x2191;' if analysis['daily_green'] else '&#x2193;'} &mdash; "
                     f"{'Monthly buyer present &mdash; structure favors longs.' if analysis['monthly_green'] else 'Monthly seller in control &mdash; long plays are counter-trend; require extra confirmation.'}")
            if monthly_open > 0:
                _mo_bull_line = (f"price is {'above' if analysis['above_monthly_open'] is True else 'below'} "
                                 f"the monthly open (${monthly_open:.2f}) placing it on the "
                                 f"{'buy list' if analysis['above_monthly_open'] is True else 'sell list'}.")
            else:
                _mo_bull_line = "the month is closed &mdash; buy/sell list status resets when the new monthly open prints."
            forced_pat_desc = (
                f"This is a level-driven long rather than a named pattern &mdash; {_mo_bull_line} "
                f"{'Weekly is green &mdash; buyer present at the weekly level.' if analysis['weekly_green'] else 'Weekly is red &mdash; longs are counter-trend on the weekly.'} "
                f"A break above {trig_hi_lbl} creates a structural 2-Up in force &mdash; that IS the trigger regardless of the prior sequence.")
            setup_a = (
                f"<table width='100%' style='border:2px solid #2d7a44;border-radius:10px;"
                f"overflow:hidden;margin-bottom:10px;border-collapse:collapse;'>"
                f"<tr style='background:#0a2018;'><td style='padding:11px 16px;font-size:13px;"
                f"font-weight:700;color:#5fdd8e;'>A &mdash; Structural 2-Up Long"
                f"{bull_badge_html}</td></tr>"
                f"<tr style='background:#061410;'><td style='padding:12px 16px;'>"
                f"<table width='100%' style='color:#c8e8d8;'>"
                + setup_row("Thesis", forced_pat_desc)
                + setup_row("Trigger",
                    f"Break above {trig_hi_lbl} <strong style='color:#5fdd8e;'>${current_high:.2f}</strong> "
                    f"in force (${current_high + 0.01:.2f} tick) with {etf_home} and/or SPY simultaneously going 2-Up. "
                    f"The in-force tick is the signal &mdash; do not anticipate."
                    + bull_trigger_ctx)
                + imm_mag_row(True)
                + weekly_mag_row(True)
                + target_rows(bull_targets, target1_price, target1_label, True)
                + stop_row(current_high, target1_price, True, bull_contract)
                + rr_row(current_high, target1_price, True, bull_contract)
                + self._options_rows(setup_row, 'bull', bull_contract, bull_conv)
                + chain_note_row(bull_chain_notes)
                + setup_row("FTFC", forced_ftfc)
                + setup_row("Expiry", expiry_guidance(step_through_bull, mother_bar_bull > 0, mother_bar_bull))
                + "</table></td></tr></table>")

        # Setup B — Bear
        if bear_pats:
            b_name, b_desc = bear_pats[0]
            setup_b = (
                f"<table width='100%' style='border:2px solid #7a2d2d;border-radius:10px;"
                f"overflow:hidden;margin-bottom:10px;border-collapse:collapse;'>"
                f"<tr style='background:#2d0f0f;'><td style='padding:11px 16px;font-size:13px;"
                f"font-weight:700;color:#ff8080;'>B &mdash; {b_name}"
                f"{bear_badge_html}</td></tr>"
                f"<tr style='background:#1e0a0a;'><td style='padding:12px 16px;'>"
                f"<table width='100%' style='color:#ffc8c8;'>"
                + setup_row("Pattern", b_desc)
                + setup_row("Trigger",
                    f"Break below {trig_lo_lbl} <strong style='color:#ff6b6b;'>${current_low:.2f}</strong> "
                    f"in force with {etf_home} + SPY simultaneously confirming."
                    + bear_trigger_ctx)
                + imm_mag_row(False)
                + weekly_mag_row(False)
                + target_rows(bear_targets, bear_target_price,
                              f"${bear_target_price:.2f} ({'Prior Week Low' if prev_weekly_low > 0 else '~1.5% extension'})",
                              False)
                + stop_row(current_low, bear_target_price, False, bear_contract)
                + rr_row(current_low, bear_target_price, False, bear_contract)
                + self._options_rows(setup_row, 'bear', bear_contract, bear_conv)
                + chain_note_row(bear_chain_notes)
                + setup_row("Expiry", expiry_guidance(step_through_bear, mother_bar_bear > 0, mother_bar_bear))
                + "</table></td></tr></table>")
        else:
            # No named pattern — forced structural bear thesis from price levels alone
            if monthly_open > 0:
                _mo_bear_line = (f"price is {'below' if analysis['above_monthly_open'] is False else 'above'} "
                                 f"the monthly open (${monthly_open:.2f}).")
            else:
                _mo_bear_line = "the month is closed &mdash; buy/sell list status resets when the new monthly open prints."
            forced_bear_desc = (
                f"This is a level-driven short rather than a named pattern &mdash; {_mo_bear_line} "
                f"{'Monthly seller in control &mdash; structure favors shorts.' if analysis['monthly_red'] else 'Monthly buyer is present &mdash; shorts are counter-trend; require extra confirmation and size reduction.'} "
                f"{'Weekly is red &mdash; seller present at the weekly level.' if analysis['weekly_red'] else 'Weekly is green &mdash; any short is fighting the weekly buyer.'} "
                f"A break below {trig_lo_lbl} creates a structural 2-Down in force &mdash; that IS the trigger regardless of prior sequence.")
            forced_bear_ftfc = (
                "Month &#x2193; &middot; Week &#x2193; &middot; Day &#x2193; &mdash; FTFC bearish. Full conviction short."
                if analysis['ftfc_bear']
                else f"Month {'&#x2193;' if analysis['monthly_red'] else '&#x2191;'} &middot; "
                     f"Week {'&#x2193;' if analysis['weekly_red'] else '&#x2191;'} &middot; "
                     f"Day {'&#x2193;' if analysis['daily_red'] else '&#x2191;'} &mdash; Partial bear alignment. Require simultaneous sector break before full size.")
            setup_b = (
                f"<table width='100%' style='border:2px solid #7a2d2d;border-radius:10px;"
                f"overflow:hidden;margin-bottom:10px;border-collapse:collapse;'>"
                f"<tr style='background:#2d0f0f;'><td style='padding:11px 16px;font-size:13px;"
                f"font-weight:700;color:#ff8080;'>B &mdash; Structural 2-Down Short"
                f"{bear_badge_html}</td></tr>"
                f"<tr style='background:#1e0a0a;'><td style='padding:12px 16px;'>"
                f"<table width='100%' style='color:#ffc8c8;'>"
                + setup_row("Thesis", forced_bear_desc)
                + setup_row("Trigger",
                    f"Break below {trig_lo_lbl} <strong style='color:#ff6b6b;'>${current_low:.2f}</strong> "
                    f"in force (${current_low - 0.01:.2f} tick) with {etf_home} and/or SPY simultaneously going 2-Down. "
                    f"Do not short before the trigger prints."
                    + bear_trigger_ctx)
                + imm_mag_row(False)
                + weekly_mag_row(False)
                + target_rows(bear_targets, bear_target_price,
                              f"${bear_target_price:.2f} ({'Prior Week Low' if prev_weekly_low > 0 else '~1.5% extension'})",
                              False)
                + stop_row(current_low, bear_target_price, False, bear_contract)
                + rr_row(current_low, bear_target_price, False, bear_contract)
                + self._options_rows(setup_row, 'bear', bear_contract, bear_conv)
                + chain_note_row(bear_chain_notes)
                + setup_row("FTFC", forced_bear_ftfc)
                + setup_row("Expiry", expiry_guidance(step_through_bear, mother_bar_bear > 0, mother_bar_bear))
                + "</table></td></tr></table>")

        # Setup C — Triangle-They-Out Scout (both directions: the wick sweep can
        # happen either way, so model the long AND the short version)
        def scout_subhead(text, color):
            return (f"<tr><td colspan='2' style='padding:9px 0 5px;font-size:12px;"
                    f"font-weight:800;color:{color};border-top:1px solid #2a1a3a;'>"
                    f"{text}</td></tr>")

        setup_c = (
            f"<table width='100%' style='border:2px solid #7a40aa;border-radius:10px;"
            f"overflow:hidden;margin-bottom:10px;border-collapse:collapse;'>"
            f"<tr style='background:#1a0f2a;'><td style='padding:11px 16px;font-size:13px;"
            f"font-weight:700;color:#cc88ff;'>C &mdash; Triangle-They-Out Scout Entry"
            f"<span style='font-size:11px;font-weight:700;padding:3px 10px;border-radius:12px;"
            f"background:#40207a;color:#d8a0ff;margin-left:8px;'>Wick-Reclaim Scout</span></td></tr>"
            f"<tr style='background:#10091a;'><td style='padding:12px 16px;'>"
            f"<table width='100%' style='color:#e0d0f8;'>"
            + setup_row("Concept",
                f"The wick sweep can fire in <em>either</em> direction. They 'triangle you out or "
                f"stop you out and reclaim' &mdash; price pokes a wick to trip resting stops, then "
                f"snaps back inside the range. Take the reclaim, not the poke. Wick midpoint "
                f"&asymp; ${_wick_mid:.2f} splits the two zones.")
            # ── UPSIDE: sweep the LOW, reclaim up → long ──────────────────────
            + scout_subhead("&#x2191; Upside Scout &mdash; long the lower-wick sweep", "#9feebc")
            + setup_row("Pattern",
                f"Price dips into the lower wick zone (${current_low:.2f}&ndash;${scout_dip_high:.2f}), "
                f"sweeps the stops below, then reclaims &mdash; that snap-back is the long scout entry.")
            + setup_row("Entry",
                f"Buy the dip to ${current_low:.2f}&ndash;${scout_dip_high:.2f} ONLY on a green reversal bar. "
                f"Never catch the falling knife &mdash; wait for the bar to close green first.")
            + setup_row("Target",
                f"First real resistance: <strong>${ttout_target:.2f}</strong> (the trigger reclaim)"
                + (f", then ${ttout_next:.2f}" if ttout_next else "")
                + f". Do not stretch to a far prior-week high &mdash; take the reclaim level "
                f"first; trail only if it holds."
                + (f" <strong style='color:#ffd070;'>Counter-trend with the higher timeframes down "
                   f"&mdash; fade only on the reclaim, scout size, first target then out.</strong>"
                   if bear_bias else ""))
            + stop_row(scout_dip_high, ttout_target, True, scout_bull_contract,
                       "the green reversal bar's high (the scout's trigger)")
            + self._options_rows(setup_row, 'bull', scout_bull_contract, 'scout')
            + chain_note_row(bull_chain_notes)
            # ── DOWNSIDE: sweep the HIGH, reject down → short ─────────────────
            + scout_subhead("&#x2193; Downside Scout &mdash; short the upper-wick sweep", "#ffaaaa")
            + setup_row("Pattern",
                f"Mirror image: price rips into the upper wick zone (${scout_rip_low:.2f}&ndash;${current_high:.2f}), "
                f"runs the buy-stops / fakes the breakout, then rejects back inside &mdash; that failed poke "
                f"is the short scout entry. 'Stop them out above and reclaim down.'")
            + setup_row("Entry",
                f"Short or buy puts on the rip to ${scout_rip_low:.2f}&ndash;${current_high:.2f} ONLY on a red "
                f"reversal bar. Never short into strength &mdash; wait for the bar to close red back inside the range.")
            + setup_row("Target",
                f"First real support: <strong>${ttout_target_b:.2f}</strong> (the trigger break)"
                + (f", then ${ttout_next_b:.2f}" if ttout_next_b else "")
                + f". Take the nearby level first rather than projecting a far prior-week low."
                + (f" <strong style='color:#9feebc;'>Aligned with the higher timeframes down &mdash; "
                   f"this is the A-direction; can carry to the next rung once the first target pays.</strong>"
                   if bear_bias else ""))
            + stop_row(scout_rip_low, ttout_target_b, False, scout_bear_contract,
                       "the red reversal bar's low (the scout's trigger)")
            + self._options_rows(setup_row, 'bear', scout_bear_contract, 'scout')
            + chain_note_row(bear_chain_notes)
            + "</table></td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # options_html and key_levels already fetched above the setup cards

        # ═══════════════════════════════════════════════════════════════════
        # FTFC CHIP ROW
        # ═══════════════════════════════════════════════════════════════════
        def chip(label, arrow, state):
            """label = timeframe name, arrow = ↑ or ↓ or status text, state = bull/bear/warn/unk"""
            cfg = {
                "bull": ("#0a1e12", "#2d7a44", "#5fdd8e"),
                "bear": ("#2d0f0f", "#7a2d2d", "#ff8080"),
                "warn": ("#2a2000", "#6b4d00", "#ffd070"),
                "unk":  ("#1a1e24", "#2e3540", "#8a9ab0"),
            }
            bg, bd, cl = cfg.get(state, cfg["unk"])
            return (f"<td style='padding:3px;'>"
                    f"<span style='padding:6px 16px;border-radius:20px;font-size:12px;font-weight:700;"
                    f"background:{bg};border:1px solid {bd};color:{cl};"
                    f"display:inline-block;white-space:nowrap;'>"
                    f"{label}"
                    f"{'&nbsp;&nbsp;<strong>' + arrow + '</strong>' if arrow else ''}"
                    f"</span></td>")

        mo_st = "bull" if analysis['monthly_green'] else ("bear" if analysis['monthly_red'] else "unk")
        wk_st = "bull" if analysis['weekly_green']  else ("bear" if analysis['weekly_red']  else "unk")
        dy_st = "bull" if analysis['daily_green']   else ("bear" if analysis['daily_red']   else "unk")
        hr_st = "bull" if analysis['hourly_green']  else ("bear" if analysis['hourly_red']  else "unk")
        mo_mo_st = "bull" if above_mo else ("bear" if above_mo is False else "unk")
        etf_st = "bull" if etf_d1_dir == "UP" else ("bear" if etf_d1_dir == "DOWN" else "unk")

        spy_d1_dir = get_dir(spy_cache['d1_list']) if spy_cache else "UNKNOWN"
        spy_st     = "bull" if spy_d1_dir == "UP" else ("bear" if spy_d1_dir == "DOWN" else "unk")

        def _color_arrow(g, r):  # ↑ green, ↓ red, ↔ neither (doji / inside-flat)
            return "&#x2191;" if g else ("&#x2193;" if r else "&#x2194;")
        mo_arrow  = _color_arrow(analysis['monthly_green'], analysis['monthly_red'])
        wk_arrow  = _color_arrow(analysis['weekly_green'],  analysis['weekly_red'])
        dy_arrow  = _color_arrow(analysis['daily_green'],   analysis['daily_red'])
        hr_arrow  = _color_arrow(analysis['hourly_green'],  analysis['hourly_red'])
        etf_arrow = "&#x2191;" if etf_d1_dir == "UP"       else "&#x2193;"
        spy_arrow = "&#x2191;" if spy_d1_dir  == "UP"       else "&#x2193;"
        mo_status = ("Above Monthly Open &mdash; Buy List" if above_mo is True
                     else "Below Monthly Open &mdash; Sell List" if above_mo is False
                     else "Month Closed &mdash; Awaiting New Open")

        def chip_row(*chips):
            return ("<table style='border-collapse:collapse;margin-bottom:6px;'><tr>"
                    + "".join(chips) + "</tr></table>")

        ftfc_chips = (
            seq_label("FTFC + Confirmation Checklist")
            # Row 1: four timeframes
            + chip_row(
                chip("Month",  mo_arrow, mo_st),
                chip("Week",   wk_arrow, wk_st),
                chip("Day",    dy_arrow, dy_st),
                chip("60-Min", hr_arrow, hr_st),
            )
            # Row 2: monthly open status + volume truth
            + chip_row(
                chip(mo_status, "", mo_mo_st),
                chip(("Vol " + (f"{vol_ratio:.1f}&times;" if vol_ratio > 0 else "N/A")), "",
                     "bull" if vol_ratio >= 1.5 else ("warn" if 0 < vol_ratio < 0.7 else "unk")),
                chip(("VIX " + ({'red': '&#x2193; risk-on', 'green': '&#x2191; risk-off',
                                 'flat': 'flat'}.get(vix_state, 'N/A'))), "",
                     "bull" if vix_state == 'red' else ("bear" if vix_state == 'green' else "unk")),
            )
            # Row 3: sector ETF + SPY
            + chip_row(
                chip(etf_home, etf_arrow, etf_st),
                chip("SPY",    spy_arrow, spy_st),
            )
            + f"<table width='100%' style='background:#151820;border:1px solid #1e2530;"
            f"border-radius:8px;border-collapse:collapse;margin-bottom:16px;margin-top:4px;'>"
            f"<tr><td style='padding:8px 12px;font-size:12px;color:#c0ccd8;line-height:1.6;'>"
            f"For maximum conviction: need the 60-min to open green AND {etf_home} + SPY to "
            f"simultaneously confirm. Per The Strat: when all four timeframes align AND sector "
            f"confirms simultaneously &mdash; that is institutional buying, not a dead-cat move."
            f"</td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # VERDICT / PLAYBOOK
        # ═══════════════════════════════════════════════════════════════════
        def verdict_step(num, style, content):
            styles = {
                "bull":  ("background:#1d6b35;color:#9feebc;", "#c8e8d8"),
                "bear":  ("background:#6b1d1d;color:#ffaaaa;", "#ffc8c8"),
                "scout": ("background:#40207a;color:#d8a0ff;", "#e0d0f8"),
                "warn":  ("background:#4a3a00;color:#ffd070;", "#ffe6b3"),
            }
            ns, tc = styles.get(style, styles["warn"])
            return (f"<tr><td style='vertical-align:top;padding:8px 14px 8px 0;width:30px;'>"
                    f"<span style='font-size:11px;font-weight:800;width:22px;height:22px;"
                    f"border-radius:50%;display:inline-block;text-align:center;line-height:22px;{ns}'>"
                    f"{num}</span></td>"
                    f"<td style='font-size:13px;color:{tc};padding:8px 0;line-height:1.6;'>{content}</td></tr>")

        vs = ""
        vs += verdict_step("1", "warn",
            f"<strong>Pre-check:</strong> Confirm {etf_home} and SPY alignment before entry. "
            f"Is the 60-min opening above or below today's prior close? "
            f"Pre-market above ${current_close:.2f} = bullish lean confirmed before the open.")

        if bull_pats:
            _bull_step_lbl = (f"COUNTER-TREND &mdash; fade only (Setup A &mdash; {bull_pats[0][0]})"
                              if bear_bias else f"PRIMARY (Setup A &mdash; {bull_pats[0][0]})")
            vs += verdict_step("2", "bull",
                f"<strong>{_bull_step_lbl}:</strong> "
                f"If {ticker} breaks above <strong style='color:#5fdd8e;'>${current_high:.2f}</strong> "
                f"with {etf_home} + SPY simultaneously going 2-Up &rarr; buy calls. "
                f"Take 60&ndash;70% profits at {target1_label} &mdash; exhaustion risk begins there: "
                f"watch the NEXT BAR, not price (inside = hold runner, shooter = reduce, hard 2-down = "
                f"exit runner; runner stays on only while the 30/60-min stay green). "
                f"Stop: {STOP_RULE} (${current_high:.2f}).")

        vs += verdict_step("3", "scout",
            f"<strong>WICK-RECLAIM SCOUT (Setup C &mdash; either direction):</strong> "
            f"<span style='color:#9feebc;'>Upside:</span> if price sweeps down to "
            f"${current_low:.2f}&ndash;${scout_dip_high:.2f} then prints a green reversal bar &rarr; "
            f"go long, first target ${ttout_target:.2f} (reclaim)"
            + (" &mdash; counter-trend, fade only" if bear_bias else "") + ". "
            f"<span style='color:#ffaaaa;'>Downside:</span> if price ripped up to "
            f"${scout_rip_low:.2f}&ndash;${current_high:.2f} then prints a red reversal bar &rarr; "
            f"short, first target ${ttout_target_b:.2f}. "
            f"Stop either way: {STOP_RULE} (the reversal bar's extreme). "
            f"Take the nearby first target &mdash; don't project a distant magnet.")

        if bear_pats:
            _bear_step_lbl = (f"PRIMARY &mdash; FTFC aligned (Setup B &mdash; {bear_pats[0][0]})"
                              if bear_bias else f"IF BULL FAILS (Setup B &mdash; {bear_pats[0][0]})")
            vs += verdict_step("4", "bear",
                f"<strong>{_bear_step_lbl}:</strong> "
                f"Price opens flat, cannot reclaim ${current_close:.2f}, breaks ${current_low:.2f} "
                f"with {etf_home}/SPY confirming &rarr; buy puts. "
                f"Target ${bear_target_price:.2f}. Stop: {STOP_RULE} (${current_low:.2f}). "
                f"Require clean in-force break before sizing up.")

        if analysis['domino_wk_bull'] or analysis['domino_wk_bear']:
            d_note = (f"Prior week high ${prev_weekly_high:.2f} sits between price and the bull trigger ${current_high:.2f}"
                      if analysis['domino_wk_bull']
                      else f"Prior week low ${prev_weekly_low:.2f} sits between price and the bear trigger ${current_low:.2f}")
            vs += verdict_step("5", "warn",
                f"<strong>Domino opportunity:</strong> {d_note}. "
                f"Breaking the daily trigger simultaneously creates a weekly signal &mdash; "
                f"position for multi-day follow-through, not just an intraday scalp. "
                f"Use longer-dated options to give the weekly magnitude time to work. "
                f"And the exit half of the rule: when the weekly magnitude prints mid-week, "
                f"that is target exhaustion &mdash; bank it; don't ride short-dated premium "
                f"into Friday hoping for more.")

        verdict = (
            seq_label("Playbook")
            + f"<table width='100%' style='background:#0a1e12;border:2px solid #2d7a44;"
            f"border-radius:12px;border-collapse:collapse;margin-bottom:16px;'>"
            f"<tr><td style='padding:16px 20px;'>"
            f"<div style='font-size:15px;font-weight:800;color:#5fdd8e;margin-bottom:12px;'>"
            f"Execution Playbook &mdash; {ticker}</div>"
            f"<table width='100%'>{vs}</table>"
            f"</td></tr></table>"
            f"<table width='100%' style='background:#1a1400;border:1px solid #6b4d00;"
            f"border-radius:8px;border-collapse:collapse;margin-bottom:16px;'>"
            f"<tr><td style='padding:10px 14px;font-size:12px;font-weight:700;color:#ffd070;line-height:1.6;'>"
            f"&#x26A0; The pattern is evidence &mdash; it is NOT a confirmed trade until price goes in force "
            f"past the trigger. Do not buy options pre-market or at the open before the trigger prints. "
            f"A signal that doesn't follow through immediately is at risk of broadening back against you. "
            f"<strong>Wait. For. The. Signal.</strong><br><br>"
            f"<strong>Re-entry rule:</strong> a stop-out that does NOT change the higher-timeframe "
            f"opens (60-min/day still {'red' if bear_bias else 'green'}) is a triangle-out &mdash; "
            f"they stopped you, not the trade. The reclaim of the trigger is the SAME trade again "
            f"with a fresh stop; take it without hesitation. A stop-out that flips the 60/daily "
            f"opens is information &mdash; the read was wrong, stand down and let it reload."
            f"</td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # TOMORROW'S SESSION SCRIPT — the streams' intraday decision tree,
        # pre-computed the night before with this ticker's actual levels.
        # Time-blocked: pre-market → open → second 30 → the flip → midday →
        # afternoon → close. Every branch is an if/then keyed to tonight's
        # numbers so there is nothing to calculate live — only to recognize.
        # ═══════════════════════════════════════════════════════════════════
        def script_step(time_lbl, title, body, accent="#8a9ab0"):
            return (f"<tr><td style='vertical-align:top;padding:9px 12px 9px 0;width:88px;white-space:nowrap;'>"
                    f"<span style='font-size:11px;font-weight:800;color:{accent};'>{time_lbl}</span></td>"
                    f"<td style='padding:9px 0;font-size:12px;color:#c8d4e0;line-height:1.7;'>"
                    f"<strong style='color:#ffffff;'>{title}</strong><br>{body}</td></tr>")

        _g = "#5fdd8e"; _r = "#ff6b6b"; _y = "#ffd070"; _p = "#cc88ff"

        # Gap classification levels for tomorrow, from tonight's data
        _gap_up_wk  = prev_weekly_high if prev_weekly_high > current_high else 0.0
        _gap_dn_wk  = prev_weekly_low  if 0 < prev_weekly_low < current_low else 0.0

        ss = ""

        # ── pre-market ──
        _pm_body = (
            f"Mark futures' pre-market high/low before the open &mdash; first intraday S/R of the day. "
            f"Check {etf_home} + SPY vs their key levels and the VIX (selling VIX = algos buying indexes). "
            f"Then classify the open vs tonight's levels: "
            f"<strong style='color:{_g};'>above ${current_high:.2f}</strong> = trigger gapping in force; "
            f"<strong style='color:#c8d4e0;'>inside ${current_low:.2f}&ndash;${current_high:.2f}</strong> = "
            f"normal trigger day; <strong style='color:{_r};'>below ${current_low:.2f}</strong> = bear "
            f"trigger gapping in force.")
        if _gap_up_wk > 0:
            _pm_body += (f" A gap above <strong style='color:{_g};'>${_gap_up_wk:.2f}</strong> (prior week "
                         f"high) opens as a potential <strong>outside week</strong> &mdash; massive target; "
                         f"weekly magnitude is instantly live.")
        if _gap_dn_wk > 0:
            _pm_body += (f" A gap below <strong style='color:{_r};'>${_gap_dn_wk:.2f}</strong> (prior week "
                         f"low) opens as a potential <strong>outside week down</strong>.")
        ss += script_step("PRE-MKT", "Classify the open before it happens", _pm_body, _y)

        # ── gap scenarios ──
        _mw_green = analysis['monthly_green'] and analysis['weekly_green']
        ss += script_step("GAP UP", "Above the bull trigger &mdash; do NOT chase the open",
            (f"The gap IS the in-force print, but chasing the first thrust is the amateur entry. "
             f"Two valid plays: <strong style='color:{_g};'>Gap-up / buy (continuation)</strong> &mdash; "
             + ("month + week are green so this is permitted: " if _mw_green else
                "<strong>caution: month/week are NOT both green, so this version is off the table per "
                "the gapper rules</strong>; if taken anyway it's counter-trend scout size only: ")
             + f"wait for the first 15/30-min to go corrective RED first, then buy the red-to-green "
             f"reversal; stop: {STOP_RULE}. "
             f"<strong style='color:{_r};'>Gap-up / sell (fade)</strong> &mdash; if the first 30-min goes "
             f"bright red OR prints a shooter/inside bar, sellers are using the gap: short the 2-down "
             f"on the 30/60, stop: {STOP_RULE}. Never short into new lows &mdash; wait for the "
             f"corrective rip, short the lower high. A gap that goes outside bar (3) mid-morning = "
             f"conflict; take partials, don't add."), _g)

        ss += script_step("GAP DN", "Below the bear trigger &mdash; never buy into new lows",
            (f"Gap-down opens the bear trigger in force. <strong style='color:{_g};'>Gap-down / buy</strong> "
             f"&mdash; the failed-breakdown play: it must go corrective (bounce) FIRST; buy the first "
             f"lower-high that reclaims the gap (3-1-2 or inside-30 up), stop: {STOP_RULE}. "
             f"<strong style='color:{_r};'>Kicking pattern check</strong>: if the first 30-min is a long "
             f"red bar with no upper wick and no bounce at all, FTFC kicked in at the open &mdash; that's "
             f"the most aggressive gap-down sell; do not knife-catch it, trade WITH it or stand aside. "
             f"Gap below ${current_low:.2f} that can't reclaim it = stay out of longs entirely."), _r)

        # ── 9:30-9:45 relative strength read ──
        _rs_body = (
            f"First read is RELATIVE, not absolute: if SPY/{etf_home} gap up and {ticker} is NOT going up "
            f"&mdash; that divergence is <strong style='color:{_r};'>natural selling</strong> (institutions "
            f"exiting into strength): favor Setup B regardless of the market. If the market opens weak and "
            f"{ticker} refuses to go down &mdash; <strong style='color:{_g};'>natural buying / relative "
            f"strength</strong>: it flies first and fastest when the market firms; buy ITS recovery trigger, "
            f"not the index's. Divergence in the right direction is a signal, not a disqualifier.")
        ss += script_step("9:30&ndash;9:45", "Relative strength / weakness scan", _rs_body, _y)

        # ── morning range ──
        ss += script_step("FIRST 15/30", "Let the morning range build &mdash; it is the mother bar",
            (f"The first 15-min bar is the morning range; everything inside it afterward is mother-bar "
             f"chop &mdash; do not trade inside it. It hands you the day's two known pivots (high of day "
             f"/ low of day) to run the Setup C scout against: sweep of one side + reclaim = the "
             f"triangle-they-out entry, stop: {STOP_RULE}. The first 60-min bar is the daily "
             f"group's vote &mdash; note its open price; it's the line FTFC management runs off all day."), "#8a9ab0")

        # ── second 30 ──
        ss += script_step("10:00", "Second 30 &mdash; first confirmation or first trap",
            (f"The second 30-min bar either confirms the open's direction or triangles-they-out the morning "
             f"entrants (takes out morning stops, then reclaims). A 30-min dip that does NOT change the "
             f"60-min open is just the stop-run &mdash; buy the reclaim, don't panic the position. If the "
             f"30 reverses the 60, the open's direction is genuinely failing &mdash; stand down and re-read."), "#8a9ab0")

        # ── the flip ──
        _flip_dir = "2-Up" if not bear_bias else "2-Down"
        ss += script_step("10:30", "THE FLIP &mdash; the second 60 shows its hand",
            (f"Algorithms reset; the second 60-min bar is the 60-min group voting separately from the daily "
             f"open. Ask one question: <em>what does the next 2 create or negate?</em> "
             f"A second-60 going <strong style='color:{_g};'>green/{_flip_dir}</strong> in the trade's "
             f"direction = the add signal on the ladder (this is the 'came back for a second serving' "
             f"read). Inside-60 = consolidation, hold but don't add; the inside-60 BREAK is then itself an "
             f"actionable trigger. A second-60 reversing through the first hour's open = the daily group is "
             f"being negated &mdash; exit on losing the trigger in force. If price is at the trigger right at the "
             f"flip with pivots stacked above, an inside-up on the flip is pivot-machine-gun fuel."), _p)

        # ── midday ──
        ss += script_step("11:30&ndash;1:30", "Midday &mdash; mostly don't",
            (f"Hours two and three stuck in the morning range = the worst environment: inside bars, thin "
             f"tape, chop. No reclaim of anything = no trade &mdash; sitting mid-range is maximum "
             f"uncertainty. Use the time for the bright-green/red scan instead: is {ticker} bright "
             f"{'red' if bear_bias else 'green'} on the day AND did the 60 come back for a second serving? "
             f"That's the with-trend afternoon candidate. By 12:30&ndash;1:30 you know the day's strongest "
             f"names &mdash; the best afternoon setup is usually in those, same signals, less noise."), "#8a9ab0")

        # ── afternoon / close ──
        ss += script_step("2:00&ndash;4:00", "Afternoon drive &amp; time exhaustion",
            (f"The 2&ndash;3pm flip is where late setups emerge: inside-60 &rarr; triangle &rarr; 15-min "
             f"break out of the morning range = last-hour acceleration (the valid late 0DTE window &mdash; "
             f"ATM/1-OTM only, stop: {STOP_RULE}). Into the close, time exhaustion is real: a red day "
             f"that can't make new lows in the final 10 minutes gets short-covered into the bell &mdash; "
             f"that strength often carries into tomorrow's open. Long green bar into the close = expect "
             f"profit-taking; reduce into the highs, don't add there. If holding overnight: only with the "
             f"weekly {'red' if bear_bias else 'green'} as the backstop, partials banked, runner only "
             f"&mdash; and never overnight a position against a 2-down day's seller."), _y)

        session_script = (
            seq_label("Tomorrow's Session Script &mdash; Pre-Computed Decision Tree")
            + f"<table width='100%' style='background:#12151b;border:1px solid #232830;"
            f"border-radius:10px;border-collapse:collapse;margin-bottom:16px;'>"
            f"<tr><td style='padding:4px 16px 10px 16px;'>"
            f"<table width='100%'>{ss}</table>"
            f"<div style='font-size:11px;color:#6b7a8d;border-top:1px solid #1e2530;padding-top:8px;"
            f"margin-top:4px;'>Levels are tonight's numbers: bull trigger ${current_high:.2f} &middot; "
            f"bear trigger ${current_low:.2f} &middot; stops: {STOP_RULE} "
            f"&middot; weekly open ${weekly_open:.2f}. Nothing here is a new signal &mdash; it's the "
            f"execution order for the setups above; the cards' triggers, stops and targets still govern.</div>"
            f"</td></tr></table>")

        # ═══════════════════════════════════════════════════════════════════
        # MARKET BREADTH — cap-weight vs equal-weight (auto sector + theme)
        # ═══════════════════════════════════════════════════════════════════
        breadth_html = self._breadth_section_html(
            ticker, breadth_layers or [], mega_cap, breadth_caches or {})

        # ═══════════════════════════════════════════════════════════════════
        # EARNINGS — most recent (actual vs estimate) + next scheduled date
        # ═══════════════════════════════════════════════════════════════════
        earnings_html = self._earnings_section_html(cache, ticker)

        # ═══════════════════════════════════════════════════════════════════
        # ASSEMBLE
        # ═══════════════════════════════════════════════════════════════════
        full_html = (
            f"<html><head>"
            f"<meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width, initial-scale=1'>"
            f"{css}</head><body>"
            + header
            + earnings_html
            + stale_banner
            + session_banner
            + breadth_html
            + sync_banner
            + ftfc_alert
            + week23_banner
            + failed2_banner
            + pattern_alert
            + metrics
            + tf_opens_html
            + levels_html
            + candle_html
            + candle_shape_html
            + domino_html
            + seq_label("Trade Setups")
            # Lead with the FTFC-aligned directional setup; the counter-trend side
            # is rendered second so it doesn't read as an equal, co-primary play.
            + ((setup_b + setup_a) if bear_bias else (setup_a + setup_b)) + setup_c
            + seq_label("Options Chain &mdash; Nearest Expiry")
            + options_html
            + ftfc_chips
            + verdict
            + session_script
            + f"<div style='margin-top:22px;text-align:center;font-size:11px;color:#4a5568;"
            f"border-top:1px solid #1e2530;padding-top:14px;'>"
            f"Strat Playbook &middot; {ticker} &middot; {now_str} "
            f"&middot; Built with The Strat framework &middot; Not financial advice</div>"
            + "</body></html>")

        return full_html

    # ─────────────────────────────────────────────────── data fetching ──

    def fetch_all_market_data(self):
        results = {}
        current_watchlist = self.watchlist.copy()

        # Resolve GICS sectors first so the auto sector breadth ETFs below are known.
        self.ensure_sectors_resolved(current_watchlist)

        fetch_list = []

        def _add(sym):
            if sym and sym not in fetch_list:
                fetch_list.append(sym)

        for item in current_watchlist:
            _add(item["ticker"])
            _add(item["etf"])
            # auto sector breadth pair (cap + equal weight) from the resolved sector
            sec_cap, sec_eq = SECTOR_ETF_MAP.get(item.get("sector") or "", (None, None))
            _add(sec_cap)
            _add(sec_eq)
            # equal-weight twin of the manual theme ETF
            _add(ETF_EQUAL_WEIGHT_MAP.get(item["etf"], ""))
        # market breadth pair (SPY already common; RSP is the equal-weight side)
        _add(MARKET_BREADTH_PAIR[0])
        _add(MARKET_BREADTH_PAIR[1])

        # ── Phase 1: fetch raw frames for every symbol IN PARALLEL ────────────
        # The per-ticker network calls (yfinance/requests) release the GIL, so a
        # bounded thread pool turns a long sequential chain of round-trips into a
        # few concurrent batches. We grab only TWO frames per symbol: the 1h/30d
        # and the 1d/1y. The old 1d/1mo "daily" call is redundant — the 1-year
        # daily frame already contains the last month, so we derive df_daily from
        # it (see Phase 2). Earnings (watchlist-only) are fetched here too so the
        # processing phase touches the network zero times.
        def _prefetch(ticker):
            yf_symbol = TICKER_MAP.get(ticker, ticker)
            is_wl = any(d["ticker"] == ticker for d in current_watchlist)
            for _ in range(3):
                try:
                    obj = yf.Ticker(yf_symbol)
                    h = obj.history(interval="1h", period="30d")
                    m = obj.history(interval="1d", period="1y")
                    if h.empty or m.empty:
                        return ticker, None
                    earn = self.fetch_earnings_info(obj) if is_wl else None
                    return ticker, (h, m, earn)
                except Exception:
                    time.sleep(0.3)
            return ticker, None

        raw = {}
        done = 0
        total = len(fetch_list)
        with ThreadPoolExecutor(max_workers=min(8, max(1, total))) as ex:
            futures = [ex.submit(_prefetch, tk) for tk in fetch_list]
            for fut in as_completed(futures):
                tk, data = fut.result()
                raw[tk] = data
                done += 1
                self.signals.status_update.emit(f"Syncing market data... {done}/{total}")

        # ── Phase 2: process each symbol's frames (CPU-only, no network) ──────
        for ticker in fetch_list:
            for _once in range(1):       # one pass; `break` skips a bad symbol
                try:
                    _pf = raw.get(ticker)
                    if not _pf:
                        break
                    df_hourly_raw, df_macro, earnings_info = _pf
                    df_daily = df_macro          # 1y daily already covers the month

                    if df_hourly_raw.empty or df_macro.empty:
                        break

                    for df in (df_hourly_raw, df_daily, df_macro):
                        try:
                            df.index = pd.to_datetime(df.index).tz_convert(None)
                        except TypeError:
                            df.index = pd.to_datetime(df.index)

                    # Yahoo frequently leaves the CURRENT day's daily bar as an all-NaN
                    # placeholder for hours after the close, while the intraday (hourly)
                    # feed already holds the full session. Dropping that row would shift
                    # every "prior day" level back a session and put the play on yesterday's
                    # close — wrong. Instead, when today's daily bar is a NaN placeholder,
                    # rebuild its OHLC from today's hourly bars so the play stays anchored
                    # to today's close. (Hourly is regular-hours only, so Open=09:30 bar,
                    # Close=last bar ≈ the 16:00 print.)
                    _ohlc = ['Open', 'High', 'Low', 'Close']
                    df_hourly_raw = df_hourly_raw.dropna(subset=_ohlc)
                    if len(df_macro) and df_macro[_ohlc].iloc[-1].isna().any():
                        _last_day = df_macro.index[-1].normalize()
                        _hd = df_hourly_raw[df_hourly_raw.index.normalize() == _last_day]
                        if len(_hd):
                            _i = df_macro.index[-1]
                            df_macro.loc[_i, 'Open']  = float(_hd['Open'].iloc[0])
                            df_macro.loc[_i, 'High']  = float(_hd['High'].max())
                            df_macro.loc[_i, 'Low']   = float(_hd['Low'].min())
                            df_macro.loc[_i, 'Close'] = float(_hd['Close'].iloc[-1])
                            if 'Volume' in df_macro.columns and 'Volume' in _hd.columns:
                                df_macro.loc[_i, 'Volume'] = float(_hd['Volume'].sum())
                        else:
                            # No intraday data to rebuild from → drop the empty placeholder
                            # rather than render "H nan L nan".
                            df_macro = df_macro.dropna(subset=_ohlc)
                    df_daily = df_macro

                    df_hourly  = df_hourly_raw.copy()
                    df_weekly  = df_macro.resample('W').agg(
                        {'Open': 'first', 'High': 'max', 'Low': 'min', 'Close': 'last'}).dropna()
                    df_monthly = df_macro.resample('ME').agg(
                        {'Open': 'first', 'High': 'max', 'Low': 'min', 'Close': 'last'}).dropna()
                    df_quarterly = df_macro.resample('QE').agg(
                        {'Open': 'first', 'High': 'max', 'Low': 'min', 'Close': 'last'}).dropna()

                    h1_res = self.process_timeframe_sequence(df_hourly, is_hourly=True)
                    d1_res = self.process_timeframe_sequence(df_daily,  is_hourly=False)
                    w1_res = self.process_timeframe_sequence(df_weekly, is_hourly=False)
                    m1_res = self.process_timeframe_sequence(df_monthly, is_hourly=False)

                    is_watchlist_stock = any(d["ticker"] == ticker for d in current_watchlist)
                    if is_watchlist_stock:
                        results[ticker] = {'1h': h1_res, '1d': d1_res, '1w': w1_res, '1m': m1_res}

                    # earnings_info was fetched in the parallel prefetch above
                    # (watchlist-only; None for breadth/sector ETFs and futures).

                    def _f(df, row, col):
                        try: return float(df.iloc[row][col])
                        except: return 0.0

                    def _atr(df, period=14):
                        try:
                            prev_c = df['Close'].shift(1)
                            tr = pd.concat([
                                df['High'] - df['Low'],
                                (df['High'] - prev_c).abs(),
                                (df['Low']  - prev_c).abs(),
                            ], axis=1).max(axis=1)
                            val = tr.ewm(alpha=1/period, adjust=False).mean().iloc[-1]
                            return float(val) if pd.notna(val) else 0.0
                        except Exception:
                            return 0.0

                    def _resample_open(df, freq):
                        try:
                            return float(df.resample(freq).agg({'Open': 'first'}).dropna().iloc[-1]['Open'])
                        except Exception:
                            return 0.0

                    # "Prior period" = the most recent FULLY-CLOSED bin. Whether the
                    # latest resampled bin is still in progress is decided from the
                    # BIN'S OWN period-end vs now — not the wall clock alone — so a
                    # render before the new period's first bar prints (Monday pre-open,
                    # first-of-month) doesn't skip an extra period back. Convention:
                    # once a period's close passes (Fri 4 PM ET for a week, the
                    # session 4 PM ET close for a day), it rolls to "prior" — ready
                    # for the next session (a Saturday run already shows last week).
                    now_et = datetime.datetime.now(ZoneInfo("America/New_York"))
                    _now_naive = now_et.replace(tzinfo=None)

                    def _last_bin_closed(df, kind):
                        """Has the latest resampled bin's trading period already closed?"""
                        if df is None or len(df) == 0:
                            return False
                        lbl = pd.Timestamp(df.index[-1]).normalize()
                        if kind == 'day':
                            return _now_naive >= lbl + pd.Timedelta(hours=16)
                        # weekly: W-SUN label is the Sunday end; last session is Friday.
                        return _now_naive >= lbl - pd.Timedelta(days=2) + pd.Timedelta(hours=16)

                    _week_closed = _last_bin_closed(df_weekly, 'week')
                    _pw_idx = -1 if _week_closed else -2
                    _pw_min_len = 1 if _week_closed else 2
                    _pw2_idx = -2 if _week_closed else -3
                    _pw2_min_len = 2 if _week_closed else 3

                    _day_closed = _last_bin_closed(df_daily, 'day')
                    _pd_idx = -1 if _day_closed else -2
                    _pd_min_len = 1 if _day_closed else 2

                    # Month closes after 4 PM ET on the last trading day of the calendar
                    # month (handles month-ends landing on a weekend). Additionally, if
                    # the latest monthly bin is already from a prior calendar month (new
                    # month opened but its first bar hasn't printed yet), treat it closed.
                    _first_next_month = (now_et.replace(day=1) + datetime.timedelta(days=32)).replace(day=1)
                    _last_cal_day = (_first_next_month - datetime.timedelta(days=1)).day
                    _has_later_weekday = any(
                        datetime.date(now_et.year, now_et.month, d).weekday() < 5
                        for d in range(now_et.day + 1, _last_cal_day + 1)
                    )
                    _on_last_trade_day = now_et.weekday() < 5 and not _has_later_weekday
                    _month_closed = (_on_last_trade_day and now_et.hour >= 16) or \
                                    (now_et.weekday() >= 5 and not _has_later_weekday)
                    if len(df_monthly) > 0:
                        _last_m = pd.Timestamp(df_monthly.index[-1])
                        if (now_et.year, now_et.month) > (_last_m.year, _last_m.month):
                            _month_closed = True
                    _pm_idx = -1 if _month_closed else -2
                    _pm_min_len = 1 if _month_closed else 2

                    # Quarter is "closed" when the latest QE bin belongs to an earlier
                    # calendar quarter than the current one (new quarter open, no bar yet);
                    # otherwise the last bin is the in-progress quarter.
                    _q_now = (now_et.year, (now_et.month - 1) // 3)
                    _quarter_closed = False
                    if len(df_quarterly) > 0:
                        _lq = pd.Timestamp(df_quarterly.index[-1])
                        _quarter_closed = (_lq.year, (_lq.month - 1) // 3) < _q_now
                    _pq_idx = -1 if _quarter_closed else -2
                    _pq_min_len = 1 if _quarter_closed else 2

                    # Prior-period swing levels + "virgin" (untested since forming) flag.
                    # A prior period's high/low is a liquidity pool only if price has NOT
                    # traded back through it since that period closed — resting stop/limit
                    # orders still sit there, so a daily trigger reaching it can cascade.
                    def _virgin(level, since, is_high):
                        if level <= 0 or since is None:
                            return False
                        after = df_macro[df_macro.index > since]
                        if len(after) == 0:
                            return True
                        return (float(after['High'].max()) < level if is_high
                                else float(after['Low'].min()) > level)

                    def _since(df_p, idx, need):
                        return (pd.Timestamp(df_p.index[idx]) if len(df_p) >= need else None)

                    _pw_since = _since(df_weekly,    _pw_idx, _pw_min_len)
                    _pm_since = _since(df_monthly,   _pm_idx, _pm_min_len)
                    _pq_since = _since(df_quarterly, _pq_idx, _pq_min_len)
                    _pq_high  = _f(df_quarterly, _pq_idx, 'High') if len(df_quarterly) >= _pq_min_len else 0.0
                    _pq_low   = _f(df_quarterly, _pq_idx, 'Low')  if len(df_quarterly) >= _pq_min_len else 0.0

                    # FTFC candle COLOR (close vs open) per timeframe — the basis for
                    # Full Time Frame Continuity. Distinct from the 2u/2d directional
                    # Strat label carried in *1_list. Uses the live forming bar, whose
                    # Close tracks the current price; a doji (close == open) is neither.
                    def _color(df):
                        o, c = _f(df, -1, 'Open'), _f(df, -1, 'Close')
                        if o == 0.0 or c == 0.0:
                            return (False, False)
                        return (c > o, c < o)
                    _mo_g, _mo_r = _color(df_monthly)
                    _wk_g, _wk_r = _color(df_weekly)
                    _dy_g, _dy_r = _color(df_daily)
                    _hr_g, _hr_r = _color(df_hourly)

                    # Closed-aware Strat sequence for the candle-sequence display:
                    # the 3 most-recently-CLOSED bars only. The forming bar lives in
                    # the separate "This Week"/"Today" (TBD) cell, so it must NOT leak
                    # into the historical cells. When the latest bar is still forming
                    # (period not closed) the last closed bar is at -2, else -1.
                    def _closed_seq(df, closed):
                        last = -1 if closed else -2
                        if df is None or len(df) < (-last) + 3:
                            return []
                        return [self.get_strat_label(df.iloc[i], df.iloc[i - 1])
                                for i in (last - 2, last - 1, last)]

                    # Live strat label of the still-forming bar (this week / today) as
                    # of report run. Display-only — strategies key off the closed bars,
                    # never this. '' when the period has already closed (no live bar).
                    def _forming_label(df, closed):
                        if closed or df is None or len(df) < 2:
                            return ''
                        return self.get_strat_label(df.iloc[-1], df.iloc[-2])

                    # Hammer / shooting-star shape of the most-recently-CLOSED bar
                    # on each timeframe (closed-aware indices, same as the swing
                    # levels above). None when the bar is an ordinary candle.
                    def _shape_at(df, idx, min_len):
                        if df is None or len(df) < min_len:
                            return None
                        return self._classify_candle(
                            _f(df, idx, 'Open'), _f(df, idx, 'High'),
                            _f(df, idx, 'Low'),  _f(df, idx, 'Close'))

                    self.raw_df_cache[ticker] = {
                        'candle_shapes': {
                            'daily':     _shape_at(df_daily,     _pd_idx, _pd_min_len),
                            'weekly':    _shape_at(df_weekly,    _pw_idx, _pw_min_len),
                            'monthly':   _shape_at(df_monthly,   _pm_idx, _pm_min_len),
                            'quarterly': _shape_at(df_quarterly, _pq_idx, _pq_min_len),
                        },
                        'h1_list': h1_res[3], 'd1_list': d1_res[3],
                        'w1_list': w1_res[3], 'm1_list': m1_res[3],
                        # closed-only sequences for the candle-sequence display cells
                        'd1_disp': _closed_seq(df_daily,  _day_closed)  or d1_res[3],
                        'w1_disp': _closed_seq(df_weekly, _week_closed) or w1_res[3],
                        # live label of the forming today/this-week bar (display only)
                        'd1_form': _forming_label(df_daily,  _day_closed),
                        'w1_form': _forming_label(df_weekly, _week_closed),
                        'day_closed': _day_closed,
                        'last_close': _f(df_daily, -1, 'Close'),
                        'last_high':  _f(df_daily, -1, 'High'),
                        'last_low':   _f(df_daily, -1, 'Low'),
                        'daily_atr':  _atr(df_macro),
                        'bull_trigger': _f(df_daily, _pd_idx, 'High') if len(df_daily) >= _pd_min_len else 0.0,
                        'bear_trigger': _f(df_daily, _pd_idx, 'Low')  if len(df_daily) >= _pd_min_len else 0.0,
                        'prev_day_high': _f(df_daily, -2, 'High') if len(df_daily) >= 2 else _f(df_daily, -1, 'High'),
                        'prev_day_low':  _f(df_daily, -2, 'Low')  if len(df_daily) >= 2 else _f(df_daily, -1, 'Low'),
                        'weekly_high':       _f(df_weekly, -1, 'High') if len(df_weekly) >= 1 else 0.0,
                        'weekly_low':        _f(df_weekly, -1, 'Low')  if len(df_weekly) >= 1 else 0.0,
                        'prev_weekly_high':  _f(df_weekly, _pw_idx,  'High') if len(df_weekly) >= _pw_min_len  else 0.0,
                        'prev_weekly_low':   _f(df_weekly, _pw_idx,  'Low')  if len(df_weekly) >= _pw_min_len  else 0.0,
                        'prev2_weekly_high': _f(df_weekly, _pw2_idx, 'High') if len(df_weekly) >= _pw2_min_len else 0.0,
                        'prev2_weekly_low':  _f(df_weekly, _pw2_idx, 'Low')  if len(df_weekly) >= _pw2_min_len else 0.0,
                        # Strat state of the SAME bars whose highs/lows are above, so
                        # the cascade narrative reads the candle that prev_weekly_high
                        # actually points at (closed-aware) instead of a fixed index.
                        'prev_weekly_strat':  (w1_res[3][_pw_idx]  if len(w1_res[3]) >= _pw_min_len  else ''),
                        'prev2_weekly_strat': (w1_res[3][_pw2_idx] if len(w1_res[3]) >= _pw2_min_len else ''),
                        'weekly_open':       _f(df_weekly,  -1, 'Open') if len(df_weekly)  >= 1 else 0.0,
                        'monthly_open':      0.0 if _month_closed else (_f(df_monthly, -1, 'Open') if len(df_monthly) >= 1 else 0.0),
                        'monthly_high':      _f(df_monthly, -1, 'High') if len(df_monthly) >= 1 else 0.0,
                        'monthly_low':       _f(df_monthly, -1, 'Low')  if len(df_monthly) >= 1 else 0.0,
                        'prev_monthly_high': _f(df_monthly, _pm_idx, 'High') if len(df_monthly) >= _pm_min_len else 0.0,
                        'prev_monthly_low':  _f(df_monthly, _pm_idx, 'Low')  if len(df_monthly) >= _pm_min_len else 0.0,
                        'prev_quarterly_high': _pq_high,
                        'prev_quarterly_low':  _pq_low,
                        # "virgin" = untested since forming → resting orders still pooled there
                        'prev_weekly_high_virgin':    _virgin(_f(df_weekly,  _pw_idx, 'High') if len(df_weekly)  >= _pw_min_len else 0.0, _pw_since, True),
                        'prev_weekly_low_virgin':     _virgin(_f(df_weekly,  _pw_idx, 'Low')  if len(df_weekly)  >= _pw_min_len else 0.0, _pw_since, False),
                        'prev_monthly_high_virgin':   _virgin(_f(df_monthly, _pm_idx, 'High') if len(df_monthly) >= _pm_min_len else 0.0, _pm_since, True),
                        'prev_monthly_low_virgin':    _virgin(_f(df_monthly, _pm_idx, 'Low')  if len(df_monthly) >= _pm_min_len else 0.0, _pm_since, False),
                        'prev_quarterly_high_virgin': _virgin(_pq_high, _pq_since, True),
                        'prev_quarterly_low_virgin':  _virgin(_pq_low,  _pq_since, False),
                        'monthly_color_green': _mo_g, 'monthly_color_red': _mo_r,
                        'weekly_color_green':  _wk_g, 'weekly_color_red':  _wk_r,
                        'daily_color_green':   _dy_g, 'daily_color_red':   _dy_r,
                        'hourly_color_green':  _hr_g, 'hourly_color_red':  _hr_r,
                        'quarterly_open':    _resample_open(df_macro, 'QE'),
                        'yearly_open':       _resample_open(df_macro, 'YE'),
                        # earnings dates (None for ETFs/breadth symbols/futures)
                        'earnings': earnings_info,
                        # df_macro stored for on-click use: pivot targets
                        'df_macro': df_macro.copy(),
                        # raw 1h OHLC kept for the on-click hourly candlestick chart
                        'df_hourly': df_hourly.copy(),
                    }
                    break
                except Exception:
                    break       # processing error for this symbol — skip it

        self.signals.data_ready.emit(results)

    def start_data_thread(self):
        if self.is_fetching:
            return
        self.is_fetching = True
        self.force_btn.setEnabled(False)
        self.force_btn.setText("Fetching...")
        threading.Thread(target=self.fetch_all_market_data, daemon=True).start()

    # ──────────────────────────────────────────────── table update slot ──

    @Slot(dict)
    def update_table_data(self, data):
        self.table.setCellWidget(0, 0, None)

        for row, item_dict in enumerate(self.watchlist):
            ticker = item_dict["ticker"]
            ticker_data = data.get(ticker)
            if not ticker_data:
                continue

            any_alert = False
            for col, key in enumerate(['1h', '1d', '1w', '1m'], start=1):
                _, meta_text, is_alert, candles = ticker_data[key]
                if col in [1, 2] and is_alert:
                    any_alert = True

                # Remove the "Awaiting Data..." item entirely so it can't bleed through
                self.table.takeItem(row, col)

                cell = QTextEdit()
                cell.setReadOnly(True)
                cell.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
                cell.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
                cell.document().setDocumentMargin(0)
                cell.setFixedHeight(36)
                cell.setStyleSheet(
                    "QTextEdit { background-color: #16191f; border: none; padding: 0px; margin: 0px; }")

                cursor = cell.textCursor()
                bf = cursor.blockFormat()
                bf.setAlignment(Qt.AlignmentFlag.AlignCenter)
                cursor.setBlockFormat(bf)

                for idx, c_val in enumerate(candles):
                    fmt = QTextCharFormat()
                    fmt.setFont(QFont("Arial", 11, QFont.Weight.Bold))
                    fmt.setForeground(QBrush(QColor(STRAT_COLORS.get(c_val, "#FFFFFF"))))
                    cursor.insertText(c_val, fmt)
                    if idx < len(candles) - 1:
                        df = QTextCharFormat()
                        df.setFont(QFont("Arial", 11, QFont.Weight.Bold))
                        df.setForeground(QBrush(QColor("#556275")))
                        cursor.insertText("-", df)

                cursor.insertText("\n")
                mf = QTextCharFormat()
                mf.setFont(QFont("Arial", 9, QFont.Weight.Normal))
                mf.setForeground(QBrush(QColor("#FFFFFF")))
                cursor.insertText(meta_text, mf)

                if row < self.table.rowCount():
                    self.table.setCellWidget(row, col, cell)

            if row < self.table.rowCount():
                ti = self.table.item(row, 0)
                if ti:
                    display = self._row_display_name(item_dict)
                    if any_alert:
                        ti.setForeground(QBrush(QColor("#00FFFF")))
                        ti.setText(f"★ {display}")
                    else:
                        ti.setForeground(QBrush(QColor("#FFFFFF")))
                        ti.setText(display)

        now_str = datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        self.status_label.setText(f"Last Sync: {now_str} | Mode: {self.refresh_mode}")
        self.table.resizeRowsToContents()
        self.is_fetching = False
        self.force_btn.setEnabled(True)
        self.force_btn.setText("🔄 Refresh Now")

    # ──────────────────────────────────────────────────── timing engine ──

    def handle_timing_engine(self):
        if self.is_fetching:
            return
        now = datetime.datetime.now()
        if self.refresh_mode == "46m Past Hour":
            if now.minute == 46 and self.last_run_hour != now.hour:
                self.last_run_hour = now.hour
                self.start_data_thread()
            return
        mapping = {"1 Minute": 60, "5 Minutes": 300, "15 Minutes": 900, "30 Minutes": 1800}
        if time.time() - self.last_interval_sync >= mapping.get(self.refresh_mode, 300):
            self.last_interval_sync = time.time()
            self.start_data_thread()


if __name__ == "__main__":
    app = QApplication(sys.argv)
    monitor = StratMonitorApp()
    monitor.show()
    sys.exit(app.exec())
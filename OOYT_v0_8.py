"""
OOYT v0.8  (Private Terminal edition)
===================================
Research, back-testing and paper trading for Indian markets and crypto.

Run
    pip install streamlit pandas numpy requests yfinance plotly
    streamlit run OOYT_v0_8.py

Highlights of v0.8
  * Complete visual redesign: midnight + champagne-gold theme, serif display type,
    live ticker tape, refined KPI cards, hand-built tables and Plotly charts.
  * Back-test engine rewritten: next-bar-open fills, intrabar stop/target,
    correct long/short handling, honest equity accounting, Sharpe/Sortino/Calmar.
  * Fixed v0.7 defects: duplicate dict keys that destroyed trade entry times,
    breakout rules that could never fire, long/short mode lasting a single bar,
    fake strategy versioning, look-ahead in equity accounting, non-Wilder ATR/ADX,
    VWAP that never reset, DB connections that were never closed, a needless
    sleep() in the loader, and Streamlit `use_container_width` deprecations.
  * Faster: parallel data fetching for the ticker, scanner, watchlist, portfolio.
  * Portfolio holdings with average cost + P&L, alert management, dataset reuse in
    the back-tester, system check page.

Research / paper trading only. No broker orders are ever sent.
Your existing ooyt_data.sqlite3 from v0.7 keeps working unchanged.
"""
from __future__ import annotations

import json
import math
import os
import sqlite3
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from html import escape
from pathlib import Path

import numpy as np
import pandas as pd
import requests
import streamlit as st

try:
    import yfinance as yf
except Exception:  # pragma: no cover - optional dependency
    yf = None
try:
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
except Exception:  # pragma: no cover - optional dependency
    go = None
    make_subplots = None

# ─────────────────────────────── constants ────────────────────────────────
APP_VERSION = "0.8"
BRAND = "OOYT"
DELTA_BASE = "https://api.india.delta.exchange"
TIMEOUT = 15
STARTING_CASH = 100_000.0
DB_PATH = Path("ooyt_data.sqlite3")
IST = "Asia/Kolkata"

C = dict(ink="#0B1220", panel="#111A2B", raised="#16223A", line="#24324A",
         gold="#CDAE6A", gold_hi="#E4C98A", ivory="#F1EBDD", mist="#93A0B5",
         up="#3DBE92", down="#E2606F", sky="#6FA8DC", violet="#B08CE0")
SERIF = "Cormorant Garamond, Georgia, serif"
SANS = "Manrope, Segoe UI, system-ui, sans-serif"

CSS = """
@import url('https://fonts.googleapis.com/css2?family=Cormorant+Garamond:wght@500;600;700&family=Manrope:wght@400;500;600;700&display=swap');
:root{--ink:#0B1220;--panel:#111A2B;--raised:#16223A;--line:#24324A;--gold:#CDAE6A;--gold-hi:#E4C98A;--ivory:#F1EBDD;--mist:#93A0B5;--up:#3DBE92;--down:#E2606F}
html,body,.stApp{background:var(--ink)!important;color:var(--ivory);font-family:'Manrope','Segoe UI',system-ui,sans-serif;font-variant-numeric:tabular-nums}
[data-testid="stSidebar"],[data-testid="collapsedControl"],#MainMenu,footer,.stDeployButton,[data-testid="stToolbar"]{display:none!important}
header[data-testid="stHeader"]{background:transparent;height:0}
.block-container{max-width:1500px;padding:1.4rem 2.2rem 3rem}
.stApp h1,.stApp h2,.stApp h3,.stApp h4{font-family:'Cormorant Garamond',Georgia,serif;font-weight:600;color:var(--ivory);letter-spacing:.005em}
.stApp h2{font-size:2rem}.stApp h3{font-size:1.5rem}
.stApp p,.stApp li,.stApp [data-testid="stMarkdownContainer"] li{color:#DAD4C6}
.stApp [data-testid="stWidgetLabel"] p,.stApp label p{color:var(--mist);font-size:.86rem}
[data-testid="stCaptionContainer"],.stApp small{color:var(--mist)!important}
/* masthead + ticker */
.mast{display:flex;justify-content:space-between;align-items:flex-end;padding-bottom:.7rem;border-bottom:1px solid var(--line)}
.brand-name{font-family:'Cormorant Garamond',Georgia,serif;font-size:2.9rem;font-weight:600;line-height:1;color:var(--ivory)}
.brand-name:after{content:"";display:block;width:56px;height:2px;background:var(--gold);margin-top:.55rem}
.brand-sub{display:block;margin-top:.45rem;color:var(--mist);font-size:.9rem}
.mast-right{text-align:right;color:var(--mist);font-size:.85rem;line-height:1.5}
.tape{overflow:hidden;white-space:nowrap;border-bottom:1px solid var(--line);margin-bottom:1.1rem}
.tape-track{display:inline-flex;gap:2.6rem;padding:.6rem 0;animation:tape 70s linear infinite}
.tape:hover .tape-track{animation-play-state:paused}
@keyframes tape{from{transform:translateX(0)}to{transform:translateX(-25%)}}
.tq{font-size:.86rem;color:var(--mist)}.tq b{color:var(--ivory);font-weight:600;margin-right:.55rem}
.up,.tone-up,.k-sub.up,.tbl td.tone-up{color:var(--up)}.down,.tone-down,.k-sub.down,.tbl td.tone-down{color:var(--down)}.flat,.tone-flat,.k-sub.flat,.tbl td.tone-flat{color:var(--mist)}
@media (prefers-reduced-motion:reduce){.tape-track{animation:none}.tape{overflow-x:auto}.candle{animation:none!important}}
/* hero + tiles */
.hero h1{font-size:3.1rem;line-height:1.08;margin:.3rem 0 .6rem;max-width:22ch}
.hero p{max-width:60ch;font-size:1.02rem;line-height:1.65;color:var(--mist)}
.tile{background:var(--panel);border:1px solid var(--line);border-radius:3px;padding:22px 20px 18px;min-height:150px}
.tile:hover{border-color:var(--gold)}
.tile svg{width:30px;height:30px;stroke:var(--gold);fill:none;stroke-width:1.4;stroke-linecap:round;stroke-linejoin:round}
.tile h3{margin:14px 0 6px;font-size:1.55rem}
.tile p{color:var(--mist);font-size:.9rem;line-height:1.55;margin:0}
/* kpi */
.kpi{background:var(--panel);border:1px solid var(--line);border-radius:3px;padding:14px 16px 12px;min-height:106px}
.kpi.lead{border-top:2px solid var(--gold)}
.k-label{color:var(--mist);font-size:.82rem}
.k-value{font-family:'Cormorant Garamond',Georgia,serif;font-size:2.05rem;font-weight:600;line-height:1.15;margin-top:2px;color:var(--ivory)}
.k-sub{font-size:.85rem;margin-top:3px;color:var(--mist)}
.inst-head{display:flex;align-items:baseline;gap:.9rem;flex-wrap:wrap;margin:.2rem 0 .9rem}
.inst-name{font-family:'Cormorant Garamond',Georgia,serif;font-size:2.3rem;font-weight:600}
.inst-sym{color:var(--mist);font-size:.95rem}
.pill{display:inline-block;padding:2px 11px;border:1px solid var(--line);border-radius:20px;font-size:.78rem;color:var(--mist)}
.pill.live{color:var(--up);border-color:rgba(61,190,146,.55)}.pill.session{color:var(--gold-hi);border-color:rgba(205,174,106,.55)}
.pill.stale,.pill.none{color:var(--down);border-color:rgba(226,96,111,.55)}
/* tables */
.tbl-wrap{overflow-x:auto;border:1px solid var(--line);border-radius:3px;background:var(--panel)}
table.tbl{width:100%;border-collapse:collapse;font-size:.9rem}
.tbl th{text-align:left;color:var(--mist);font-weight:600;font-size:.8rem;padding:10px 14px;border-bottom:1px solid var(--line);white-space:nowrap}
.tbl td{padding:9px 14px;border-bottom:1px solid rgba(36,50,74,.55);white-space:nowrap;color:var(--ivory)}
.tbl tr:last-child td{border-bottom:none}
.tbl .num{text-align:right}
/* widgets */
.stApp button[data-testid^="stBaseButton"],.stButton>button,[data-testid="stDownloadButton"] button,[data-testid="stFormSubmitButton"] button{background:transparent;border:1px solid var(--line);color:var(--ivory);border-radius:2px;font-weight:600}
.stApp button[data-testid^="stBaseButton"]:hover,.stButton>button:hover,[data-testid="stDownloadButton"] button:hover{border-color:var(--gold);color:var(--gold-hi);background:transparent}
.stApp button[data-testid="stBaseButton-primary"],.stApp button[data-testid="stBaseButton-primaryFormSubmit"],button[kind="primary"],button[kind="primaryFormSubmit"]{background:var(--gold)!important;border-color:var(--gold)!important;color:#1B1405!important}
.stApp button[data-testid="stBaseButton-primary"]:hover,button[kind="primary"]:hover{background:var(--gold-hi)!important;color:#1B1405!important}
.stApp input,.stApp textarea{color:var(--ivory)!important}
div[data-baseweb="input"],div[data-baseweb="base-input"],div[data-baseweb="select"]>div,div[data-baseweb="textarea"]{background:var(--panel)!important;border-color:var(--line)!important;border-radius:2px!important}
div[data-baseweb="popover"] ul,div[data-baseweb="menu"]{background:var(--raised)!important}
li[role="option"]{color:var(--ivory)!important}
div[data-testid="stMetric"]{background:var(--panel);border:1px solid var(--line);border-radius:3px;padding:12px 14px}
[data-testid="stMetricLabel"] p{color:var(--mist)!important}
[data-testid="stMetricValue"]{font-family:'Cormorant Garamond',Georgia,serif;font-weight:600}
details{border:1px solid var(--line)!important;border-radius:3px!important;background:var(--panel)}
button[data-baseweb="tab"] p{color:var(--mist)}button[data-baseweb="tab"][aria-selected="true"] p{color:var(--gold-hi)}
div[data-baseweb="tab-highlight"]{background:var(--gold)!important}
.st-key-nav div[role="radiogroup"]{gap:.3rem;flex-wrap:wrap}
.st-key-nav label{border-bottom:1px solid var(--line);padding:.35rem .85rem;border-radius:2px;cursor:pointer;margin:0}
.st-key-nav label[data-baseweb="radio"]>div:first-child{display:none}
.st-key-nav label:hover p{color:var(--gold-hi)}
.st-key-nav label:has(input:checked){border-bottom:2px solid var(--gold)}
.st-key-nav label:has(input:checked) p{color:var(--gold-hi);font-weight:600}
/* loader */
.loading-wrap{border:1px solid var(--line);background:var(--panel);border-radius:3px;padding:16px;text-align:center;margin:10px 0}
.candle-row{height:58px;display:flex;gap:9px;align-items:center;justify-content:center}
.candle{width:9px;border-radius:2px;position:relative;animation:pulse 1.05s infinite ease-in-out}
.candle:before{content:"";position:absolute;left:4px;top:-9px;width:1px;height:calc(100% + 18px);background:#71839a}
.candle.red{background:#EF5350}.candle.green{background:#37D67A}
@keyframes pulse{0%,100%{transform:scaleY(.55);opacity:.45}50%{transform:scaleY(1.1);opacity:1}}
.foot{color:var(--mist);font-size:.78rem;border-top:1px solid var(--line);margin-top:2.4rem;padding-top:.8rem}
"""

THEME_TOML = """[theme]
base = "dark"
primaryColor = "#CDAE6A"
backgroundColor = "#0B1220"
secondaryBackgroundColor = "#111A2B"
textColor = "#F1EBDD"
font = "sans serif"
"""

# ───────────────────────────── formatting helpers ─────────────────────────
def fnum(v):
    try:
        n = float(v)
        return n if math.isfinite(n) else None
    except (TypeError, ValueError):
        return None


def h(text) -> str:
    """HTML-escape text and neutralise '$' so Streamlit never parses it as LaTeX."""
    return escape(str(text)).replace("$", "&#36;")


def indian(n, dec=2) -> str:
    """Indian digit grouping: 12,34,567.89"""
    n = float(n)
    s = f"{abs(n):.{dec}f}"
    ip, _, fp = s.partition(".")
    if len(ip) > 3:
        head, tail, groups = ip[:-3], ip[-3:], []
        while len(head) > 2:
            groups.insert(0, head[-2:])
            head = head[:-2]
        if head:
            groups.insert(0, head)
        ip = ",".join(groups + [tail])
    return ("-" if n < 0 and float(s) != 0 else "") + ip + (("." + fp) if dec else "")


def money(v, cur="₹", dec=2) -> str:
    v = fnum(v)
    return "—" if v is None else f"{'-' if v < 0 else ''}{cur}{indian(abs(v), dec)}"


def price_str(v) -> str:
    v = fnum(v)
    if v is None:
        return "—"
    a = abs(v)
    return indian(v, 2 if a >= 10 else (4 if a >= 0.1 else 6))


def pct(v, dec=2) -> str:
    v = fnum(v)
    return "—" if v is None else f"{v:+.{dec}f}%"


def tone_of(v) -> str:
    v = fnum(v)
    return "flat" if v is None or v == 0 else ("up" if v > 0 else "down")


def cur_symbol(asset) -> str:
    return "$" if asset == "Crypto" else "₹"


# ───────────────────────── Streamlit compatibility layer ──────────────────
def _st_version():
    try:
        return tuple(int(p) for p in st.__version__.split(".")[:2])
    except Exception:
        return (1, 0)


NEW_WIDTH = _st_version() >= (1, 50)


def wide(fn, *a, **k):
    """Call a Streamlit element full-width on old and new releases alike."""
    if NEW_WIDTH:
        try:
            return fn(*a, width="stretch", **k)
        except TypeError:
            pass
    try:
        return fn(*a, use_container_width=True, **k)
    except TypeError:
        return fn(*a, **k)


def df_show(df, **k):
    return wide(st.dataframe, df, hide_index=True, **k)


def btn(label, **k):
    return wide(st.button, label, **k)


def plot(fig, key):
    """Render a Plotly figure with our own styling (theme=None keeps our fonts/colours)."""
    cfg = {"displaylogo": False, "scrollZoom": True, "modeBarButtonsToRemove": ["lasso2d", "select2d"]}
    attempts = []
    if NEW_WIDTH:
        attempts.append(dict(width="stretch", theme=None))
    attempts += [dict(use_container_width=True, theme=None), dict(use_container_width=True), {}]
    last = None
    for kw in attempts:
        try:
            return st.plotly_chart(fig, key=key, config=cfg, **kw)
        except TypeError as e:
            last = e
    raise last


@contextmanager
def loading(label="Loading market data"):
    """Red/green candlestick loader shown only while the wrapped block runs."""
    ph = st.empty()
    bars = "".join(
        f"<div class='candle {'green' if i % 2 else 'red'}' style='height:{22 + (i % 4) * 8}px;animation-delay:{i * .06:.2f}s'></div>"
        for i in range(12))
    ph.markdown(f"<div class='loading-wrap'><b>{h(label)}</b><div class='candle-row'>{bars}</div>"
                f"<span style='color:#93A0B5'>Fetching and validating data</span></div>", unsafe_allow_html=True)
    try:
        yield
    finally:
        ph.empty()


# ───────────────────────────── persistence ────────────────────────────────
def now() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


@contextmanager
def _con():
    con = sqlite3.connect(DB_PATH, timeout=10)
    con.row_factory = sqlite3.Row
    try:
        yield con
        con.commit()
    except Exception:
        con.rollback()
        raise
    finally:
        con.close()


def q(sql, args=()):
    with _con() as c:
        return c.execute(sql, args).fetchall()


def one(sql, args=()):
    with _con() as c:
        return c.execute(sql, args).fetchone()


def run(sql, args=()):
    with _con() as c:
        c.execute(sql, args)


def uid() -> str:
    return str(uuid.uuid4())


def init_db():
    with _con() as con:
        con.executescript("""
        CREATE TABLE IF NOT EXISTS strategies(id TEXT PRIMARY KEY,name TEXT NOT NULL,version INTEGER NOT NULL,config TEXT NOT NULL,created_at TEXT NOT NULL,updated_at TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS portfolios(id TEXT PRIMARY KEY,name TEXT NOT NULL,cash REAL NOT NULL DEFAULT 0,created_at TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS portfolio_tx(id TEXT PRIMARY KEY,portfolio_id TEXT NOT NULL,symbol TEXT NOT NULL,asset_class TEXT NOT NULL,side TEXT NOT NULL,quantity REAL NOT NULL,price REAL NOT NULL,fees REAL NOT NULL DEFAULT 0,ts TEXT NOT NULL,note TEXT);
        CREATE TABLE IF NOT EXISTS watchlists(id TEXT PRIMARY KEY,name TEXT NOT NULL UNIQUE,created_at TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS watchlist_items(watchlist_id TEXT NOT NULL,symbol TEXT NOT NULL,asset_class TEXT NOT NULL,position INTEGER NOT NULL DEFAULT 0,PRIMARY KEY(watchlist_id,symbol));
        CREATE TABLE IF NOT EXISTS paper_accounts(id TEXT PRIMARY KEY,name TEXT NOT NULL,initial_cash REAL NOT NULL,cash REAL NOT NULL,created_at TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS paper_trades(id TEXT PRIMARY KEY,account_id TEXT NOT NULL,asset_class TEXT NOT NULL,symbol TEXT NOT NULL,side TEXT NOT NULL,quantity REAL NOT NULL,entry REAL NOT NULL,exit REAL,fees REAL NOT NULL DEFAULT 0,opened_at TEXT NOT NULL,closed_at TEXT,note TEXT,status TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS journal(id TEXT PRIMARY KEY,trade_id TEXT,symbol TEXT,asset_class TEXT,entry_reason TEXT,exit_reason TEXT,notes TEXT,tags TEXT,ts TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS alerts(id TEXT PRIMARY KEY,name TEXT NOT NULL,asset_class TEXT NOT NULL,symbol TEXT NOT NULL,kind TEXT NOT NULL,value REAL NOT NULL,active INTEGER NOT NULL DEFAULT 1,last_triggered TEXT);
        CREATE TABLE IF NOT EXISTS datasets(id TEXT PRIMARY KEY,name TEXT NOT NULL,path TEXT NOT NULL,rows INTEGER NOT NULL,columns TEXT NOT NULL,metadata TEXT,created_at TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY,value TEXT NOT NULL);
        """)
        if con.execute("SELECT COUNT(*) FROM portfolios").fetchone()[0] == 0:
            con.execute("INSERT INTO portfolios VALUES(?,?,?,?)", (uid(), "Main Portfolio", 0.0, now()))
        if con.execute("SELECT COUNT(*) FROM paper_accounts").fetchone()[0] == 0:
            con.execute("INSERT INTO paper_accounts VALUES(?,?,?,?,?)", (uid(), "Paper Account", STARTING_CASH, STARTING_CASH, now()))
        if con.execute("SELECT COUNT(*) FROM watchlists").fetchone()[0] == 0:
            con.execute("INSERT INTO watchlists VALUES(?,?,?)", (uid(), "Default", now()))

# ───────────────────────────── market universe ────────────────────────────
STOCKS = {
    "Reliance Industries": "RELIANCE.NS", "TCS": "TCS.NS", "HDFC Bank": "HDFCBANK.NS", "Infosys": "INFY.NS",
    "ICICI Bank": "ICICIBANK.NS", "ITC": "ITC.NS", "State Bank of India": "SBIN.NS", "Larsen & Toubro": "LT.NS",
    "Bharti Airtel": "BHARTIARTL.NS", "Axis Bank": "AXISBANK.NS", "Kotak Mahindra Bank": "KOTAKBANK.NS",
    "Hindustan Unilever": "HINDUNILVR.NS", "Bajaj Finance": "BAJFINANCE.NS", "Bajaj Finserv": "BAJAJFINSV.NS",
    "Maruti Suzuki": "MARUTI.NS", "Mahindra & Mahindra": "M&M.NS", "Tata Motors": "TATAMOTORS.NS",
    "Tata Steel": "TATASTEEL.NS", "Sun Pharma": "SUNPHARMA.NS", "Dr Reddy's": "DRREDDY.NS", "Cipla": "CIPLA.NS",
    "Adani Enterprises": "ADANIENT.NS", "Adani Ports": "ADANIPORTS.NS", "Power Grid": "POWERGRID.NS",
    "NTPC": "NTPC.NS", "ONGC": "ONGC.NS", "Coal India": "COALINDIA.NS", "Wipro": "WIPRO.NS",
    "HCL Technologies": "HCLTECH.NS", "Tech Mahindra": "TECHM.NS", "Asian Paints": "ASIANPAINT.NS",
    "Titan": "TITAN.NS", "Nestle India": "NESTLEIND.NS", "Eicher Motors": "EICHERMOT.NS",
    "Bajaj Auto": "BAJAJ-AUTO.NS", "Tata Consumer": "TATACONSUM.NS", "UltraTech Cement": "ULTRACEMCO.NS",
    "Grasim Industries": "GRASIM.NS", "JSW Steel": "JSWSTEEL.NS", "Hindalco": "HINDALCO.NS",
    "Indian Oil": "IOC.NS", "BPCL": "BPCL.NS", "BEL": "BEL.NS", "HAL": "HAL.NS", "Zomato": "ZOMATO.NS",
    "Eternal (Zomato)": "ETERNAL.NS", "Trent": "TRENT.NS", "Apollo Hospitals": "APOLLOHOSP.NS",
    "Britannia": "BRITANNIA.NS", "Divi's Laboratories": "DIVISLAB.NS", "Hero MotoCorp": "HEROMOTOCO.NS",
    "HDFC Life": "HDFCLIFE.NS", "SBI Life": "SBILIFE.NS", "IndusInd Bank": "INDUSINDBK.NS",
    "Shriram Finance": "SHRIRAMFIN.NS", "Jio Financial": "JIOFIN.NS", "Tata Power": "TATAPOWER.NS",
    "DLF": "DLF.NS", "Bank of Baroda": "BANKBARODA.NS", "IRCTC": "IRCTC.NS", "Pidilite": "PIDILITIND.NS",
}
INDICES = {
    "NIFTY 50": "^NSEI", "BANK NIFTY": "^NSEBANK", "SENSEX": "^BSESN", "NIFTY IT": "^CNXIT",
    "NIFTY AUTO": "^CNXAUTO", "NIFTY PHARMA": "^CNXPHARMA", "NIFTY FMCG": "^CNXFMCG",
    "NIFTY METAL": "^CNXMETAL", "NIFTY PSU BANK": "^CNXPSUBANK", "NIFTY MIDCAP 50": "^NSEMDCP50",
    "India VIX": "^INDIAVIX",
}
ETFS = {
    "NIFTYBEES": "NIFTYBEES.NS", "JUNIORBEES": "JUNIORBEES.NS", "GOLDBEES": "GOLDBEES.NS",
    "BANKBEES": "BANKBEES.NS", "ITBEES": "ITBEES.NS", "PHARMABEES": "PHARMABEES.NS", "AUTOBEES": "AUTOBEES.NS",
    "CPSEETF": "CPSEETF.NS", "MON100": "MON100.NS", "SETFNIF50": "SETFNIF50.NS",
    "HNGSNGBEES": "HNGSNGBEES.NS", "SILVERBEES": "SILVERBEES.NS",
}
# Fund symbols vary by provider; they are candidates and only shown as valid once data returns.
MUTUAL_FUNDS = {
    "Parag Parikh Flexi Cap": "0P0000XVU8.BO", "HDFC Flexi Cap": "0P0000XVU5.BO", "SBI BlueChip": "0P0000XV4L.BO",
    "Axis Bluechip": "0P0000XV2K.BO", "Mirae Asset Large & Midcap": "0P0000XUZS.BO",
    "ICICI Prudential Bluechip": "0P0000XV1R.BO", "Kotak Flexicap": "0P0000XUVV.BO",
    "UTI Nifty 50 Index": "0P0000XW7D.BO", "HDFC Index Nifty 50": "0P0000XW6A.BO",
}
ASSETS = ["Share Investment", "Indices", "ETFs", "Mutual Funds", "Crypto"]
ASSET_MAP = {"Share Investment": STOCKS, "Indices": INDICES, "ETFs": ETFS, "Mutual Funds": MUTUAL_FUNDS, "Crypto": {}}
WORKSPACES = ["Dashboard", "Analyser", "Strategy Builder", "Backtester", "Scanner", "Paper Trading", "Portfolio",
              "Watchlist", "Data Center", "Trading Journal", "Alerts", "Analytics", "Learn", "Settings"]
TAPE = [("Nifty 50", "^NSEI", "yahoo"), ("Bank Nifty", "^NSEBANK", "yahoo"), ("Sensex", "^BSESN", "yahoo"),
        ("India VIX", "^INDIAVIX", "yahoo"), ("Nifty IT", "^CNXIT", "yahoo"),
        ("Bitcoin", "BTCUSD", "crypto"), ("Ethereum", "ETHUSD", "crypto")]

INTERVALS = ["5m", "15m", "1h", "4h", "1d", "1wk"]
PERIOD_DAYS = {"5d": 5, "1mo": 30, "3mo": 91, "6mo": 182, "1y": 365, "2y": 730, "5y": 1825, "10y": 3650}
INTERVAL_CAP_DAYS = {"5m": 58, "15m": 58, "1h": 720, "4h": 720}
DEFAULT_PERIOD = {"5m": "5d", "15m": "1mo", "1h": "3mo", "4h": "6mo", "1d": "1y", "1wk": "5y"}
INTERVAL_HOURS = {"5m": 5 / 60, "15m": .25, "1h": 1, "4h": 4, "1d": 24, "1wk": 168}
BAR_SECONDS = {"5m": 300, "15m": 900, "1h": 3600, "4h": 14400, "1d": 86400}
OHLCV = ["open", "high", "low", "close", "volume"]


def provider_of(asset) -> str:
    return "crypto" if asset == "Crypto" else "yahoo"


def is_indian(symbol) -> bool:
    s = str(symbol).upper()
    return s.endswith((".NS", ".BO")) or s.startswith(("^NSE", "^BSE", "^CNX", "^INDIA", "^NIFTY"))


def period_options(interval):
    cap = INTERVAL_CAP_DAYS.get(interval)
    opts = [p for p, d in PERIOD_DAYS.items() if cap is None or d <= cap]
    return opts or ["5d"]


def days_for(period, interval) -> int:
    d = PERIOD_DAYS.get(period, 365)
    cap = INTERVAL_CAP_DAYS.get(interval)
    return min(d, cap) if cap else d


def source_name(asset) -> str:
    return "Delta Exchange India public API" if asset == "Crypto" else "Yahoo Finance via yfinance"


def label_for(asset, symbol) -> str:
    for name, sym in ASSET_MAP.get(asset, {}).items():
        if sym == symbol:
            return name
    return symbol


def default_symbol(asset) -> str:
    return "BTCUSD" if asset == "Crypto" else next(iter(ASSET_MAP[asset].values()))


# ───────────────────────────── data adapters ──────────────────────────────
def api_get(path, params=None):
    r = requests.get(DELTA_BASE + path, params=params, timeout=TIMEOUT, headers={"Accept": "application/json"})
    r.raise_for_status()
    payload = r.json()
    if isinstance(payload, dict) and payload.get("success") is False:
        raise RuntimeError(payload.get("error", payload.get("message", "Delta API error")))
    return payload.get("result", payload) if isinstance(payload, dict) else payload


def _delta_tickers_raw():
    x = api_get("/v2/tickers")
    if isinstance(x, dict):
        x = x.get("tickers", x.get("result", []))
    return x if isinstance(x, list) else []


@st.cache_data(ttl=45, show_spinner=False)
def delta_products():
    x = api_get("/v2/products")
    return x if isinstance(x, list) else []


@st.cache_data(ttl=15, show_spinner=False)
def delta_tickers():
    return _delta_tickers_raw()


@st.cache_data(ttl=120, show_spinner=False)
def delta_symbol_options():
    try:
        return sorted({str(p.get("symbol")) for p in delta_products()
                       if isinstance(p, dict) and p.get("symbol")
                       and str(p.get("state", p.get("status", "live"))).lower() not in ("expired", "inactive", "delisted")})
    except Exception:
        return []


@st.cache_data(ttl=1800, show_spinner=False)
def usd_inr_rate():
    r = requests.get("https://open.er-api.com/v6/latest/USD", timeout=TIMEOUT)
    r.raise_for_status()
    rate = r.json().get("rates", {}).get("INR")
    if not rate:
        raise RuntimeError("INR rate missing from FX response")
    return float(rate)


def clean_ohlcv(df, tz=None) -> pd.DataFrame:
    """Normalise any OHLCV frame: lower-case columns, numeric, repaired highs/lows, tz-aware sorted index."""
    empty = pd.DataFrame(columns=OHLCV, index=pd.DatetimeIndex([], tz="UTC", name="time"))
    if df is None or len(df) == 0:
        return empty
    x = df.copy()
    x.columns = [str(c).strip().lower() for c in x.columns]
    if "close" not in x:
        return empty
    for c in OHLCV:
        if c not in x:
            x[c] = 0.0 if c == "volume" else np.nan
        x[c] = pd.to_numeric(x[c], errors="coerce")
    x = x[OHLCV].copy()
    for c in ("open", "high", "low"):
        x[c] = x[c].where(x[c] > 0)
    x = x.dropna(subset=["close"])
    for c in ("open", "high", "low"):
        x[c] = x[c].fillna(x["close"])
    x["high"] = x[["open", "high", "low", "close"]].max(axis=1)
    x["low"] = x[["open", "high", "low", "close"]].min(axis=1)
    x["volume"] = x["volume"].fillna(0).clip(lower=0)
    idx = pd.DatetimeIndex(pd.to_datetime(x.index, errors="coerce"))
    if idx.tz is None:
        idx = idx.tz_localize("UTC")
    if tz:
        idx = idx.tz_convert(tz)
    x.index = idx
    x = x[x.index.notna()]
    x = x[~x.index.duplicated(keep="last")].sort_index()
    x.index.name = "time"
    return x if len(x) else empty


def resample_ohlcv(df, rule, offset=None) -> pd.DataFrame:
    if df is None or df.empty:
        return df
    kw = {"offset": offset} if offset is not None else {}
    out = df.resample(rule, **kw).agg({"open": "first", "high": "max", "low": "min", "close": "last", "volume": "sum"})
    return out.dropna(subset=["open", "high", "low", "close"])


def _yahoo_history(symbol, days, interval):
    if yf is None:
        raise RuntimeError("yfinance is not installed. Run: pip install yfinance")
    end = datetime.now(timezone.utc) + timedelta(days=1)
    start = end - timedelta(days=int(days) + 1)
    df = yf.Ticker(symbol).history(start=start.strftime("%Y-%m-%d"), end=end.strftime("%Y-%m-%d"),
                                   interval=interval, auto_adjust=False)
    return clean_ohlcv(df, IST if is_indian(symbol) else None)


def _delta_history(symbol, days, interval):
    if interval == "1wk":
        d = _delta_history(symbol, days, "1d")
        return resample_ohlcv(d, "W-SUN") if not d.empty else d
    step = BAR_SECONDS[interval]
    end = int(datetime.now(timezone.utc).timestamp())
    cur, frames, calls = end - int(days) * 86400, [], 0
    while cur < end and calls < 12:
        nxt = min(cur + 1500 * step, end)
        x = api_get("/v2/history/candles", {"symbol": symbol, "resolution": interval, "start": cur, "end": nxt})
        if isinstance(x, dict):
            x = x.get("candles", x.get("result", []))
        if x:
            frames.append(pd.DataFrame(x))
        cur, calls = nxt, calls + 1
    if not frames:
        return clean_ohlcv(None)
    raw = pd.concat(frames, ignore_index=True)
    raw["time"] = pd.to_datetime(raw["time"], unit="s", utc=True, errors="coerce")
    return clean_ohlcv(raw.dropna(subset=["time"]).set_index("time"), "UTC")


def fetch_market_raw(symbol, provider, period="1y", interval="1d") -> pd.DataFrame:
    """Uncached fetch (safe to call from worker threads)."""
    days = days_for(period, interval)
    if provider == "crypto":
        return _delta_history(symbol, days, interval)
    if interval == "4h":
        base = _yahoo_history(symbol, days, "1h")
        off = pd.Timedelta(hours=9, minutes=15) if is_indian(symbol) else None
        return resample_ohlcv(base, pd.Timedelta(hours=4), off)
    return _yahoo_history(symbol, days, interval)


@st.cache_data(ttl=90, show_spinner=False)
def get_market_df(symbol, provider, period="1y", interval="1d") -> pd.DataFrame:
    return fetch_market_raw(symbol, provider, period, interval)


def snapshot_raw(symbol, provider) -> dict:
    df = fetch_market_raw(symbol, provider, "1mo", "1d")
    if df.empty:
        return {}
    last, prev = df.iloc[-1], (df["close"].iloc[-2] if len(df) > 1 else None)
    snap = {"last": fnum(last["close"]), "prev": fnum(prev), "open": fnum(last["open"]), "high": fnum(last["high"]),
            "low": fnum(last["low"]), "volume": fnum(last["volume"]), "asof": df.index[-1], "bid": None, "ask": None}
    if provider == "crypto":
        try:
            row = next((t for t in _delta_tickers_raw() if isinstance(t, dict)
                        and str(t.get("symbol") or t.get("product_symbol")) == symbol), {})
            snap["last"] = fnum(row.get("mark_price") or row.get("close") or row.get("last_price")) or snap["last"]
            snap["bid"] = fnum(row.get("best_bid") or row.get("bid"))
            snap["ask"] = fnum(row.get("best_ask") or row.get("ask"))
            snap["volume"] = fnum(row.get("volume") or row.get("volume_24h")) or snap["volume"]
        except Exception:
            pass
    snap["change"] = ((snap["last"] / snap["prev"] - 1) * 100) if snap["last"] and snap["prev"] else None
    return snap


@st.cache_data(ttl=45, show_spinner=False)
def market_snapshot(symbol, provider) -> dict:
    return snapshot_raw(symbol, provider)


@st.cache_data(ttl=60, show_spinner=False)
def batch_snapshots(pairs) -> dict:
    """pairs: tuple of (symbol, provider). Fetched in parallel; failures become {}."""
    def one_snap(p):
        try:
            return p[0], snapshot_raw(p[0], p[1])
        except Exception:
            return p[0], {}
    with ThreadPoolExecutor(max_workers=8) as ex:
        return dict(ex.map(one_snap, pairs))


def overview_snaps() -> dict:
    try:
        return batch_snapshots(tuple((s, p) for _, s, p in TAPE))
    except Exception:
        return {}


def data_status(df, interval="1d"):
    """Returns (kind, label, detail) where kind is live | session | stale | none."""
    if df is None or df.empty:
        return "none", "Unavailable", "No candles returned"
    last = df.index[-1]
    age_h = (pd.Timestamp.now(tz="UTC") - last.tz_convert("UTC")).total_seconds() / 3600
    when = f"Latest candle {last.strftime('%d %b %Y, %H:%M')} {last.tzname() or ''}".strip()
    ih = INTERVAL_HOURS.get(interval, 24)
    if age_h <= 2.5 * ih:
        return "live", "Current", when
    if age_h <= 120:
        return "session", "Last session", when
    return "stale", "Stale", when


def fetch_error_message(e) -> str:
    if isinstance(e, requests.exceptions.Timeout):
        return "The data provider took too long to respond. Press Refresh to try again."
    if isinstance(e, requests.exceptions.ConnectionError):
        return "Could not reach the data provider. Check your internet connection, then press Refresh."
    if isinstance(e, RuntimeError):
        return str(e)
    return f"Data request failed ({type(e).__name__}): {e}"


# ───────────────────────────── catalogue + search ─────────────────────────
def catalog_rows():
    rows = [{"name": n, "symbol": s, "asset": a} for a, m in ASSET_MAP.items() for n, s in m.items()]
    rows += [{"name": s, "symbol": s, "asset": "Crypto"} for s in delta_symbol_options()]
    return rows


def search_catalog(term):
    t = term.strip().lower()
    rows = catalog_rows()
    if not t:
        return rows[:30]
    return [r for r in rows if t in r["name"].lower() or t in r["symbol"].lower()][:40]


# ───────────────────────────── indicators ─────────────────────────────────
def _wilder(s, n):
    return s.ewm(alpha=1 / n, adjust=False, min_periods=n).mean()


def is_intraday(idx) -> bool:
    if len(idx) < 3:
        return False
    return pd.Series(idx).diff().median() < pd.Timedelta(hours=20)


def _supertrend(high, low, close, atr, mult=3.0):
    n = len(close)
    line, direction = np.full(n, np.nan), np.full(n, np.nan)
    valid = np.where(~np.isnan(atr))[0]
    if len(valid) == 0:
        return line, direction
    s = valid[0]
    hl2 = (high + low) / 2
    ub, lb = hl2 + mult * atr, hl2 - mult * atr
    fu, fl = ub.copy(), lb.copy()
    direction[s], line[s] = 1, fl[s]
    for i in range(s + 1, n):
        fu[i] = ub[i] if (ub[i] < fu[i - 1] or close[i - 1] > fu[i - 1]) else fu[i - 1]
        fl[i] = lb[i] if (lb[i] > fl[i - 1] or close[i - 1] < fl[i - 1]) else fl[i - 1]
        if direction[i - 1] == 1:
            direction[i] = -1 if close[i] < fl[i] else 1
        else:
            direction[i] = 1 if close[i] > fu[i] else -1
        line[i] = fl[i] if direction[i] == 1 else fu[i]
    return line, direction


def add_indicators(df, sma=20, ema=20) -> pd.DataFrame:
    x = df.copy()
    c, hi, lo, v = x["close"], x["high"], x["low"], x["volume"].fillna(0)
    sma, ema = int(sma), int(ema)
    x["SMA"] = c.rolling(sma).mean()
    x["EMA"] = c.ewm(span=ema, adjust=False, min_periods=ema).mean()
    # VWAP: session-anchored for intraday bars, rolling 20-bar otherwise
    tp = (hi + lo + c) / 3
    pv = tp * v
    if is_intraday(x.index):
        day = x.index.normalize()
        x["VWAP"] = pv.groupby(day).cumsum() / v.groupby(day).cumsum().replace(0, np.nan)
    else:
        x["VWAP"] = pv.rolling(20).sum() / v.rolling(20).sum().replace(0, np.nan)
    # RSI (Wilder)
    d = c.diff()
    gain, loss = _wilder(d.clip(lower=0), 14), _wilder((-d).clip(lower=0), 14)
    rsi = 100 - 100 / (1 + gain / loss.replace(0, np.nan))
    x["RSI"] = rsi.mask((loss == 0) & gain.notna(), 100.0)
    # MACD
    e12, e26 = c.ewm(span=12, adjust=False).mean(), c.ewm(span=26, adjust=False).mean()
    x["MACD"] = e12 - e26
    x["MACD_signal"] = x["MACD"].ewm(span=9, adjust=False).mean()
    x["MACD_hist"] = x["MACD"] - x["MACD_signal"]
    # ATR (Wilder)
    tr = pd.concat([hi - lo, (hi - c.shift()).abs(), (lo - c.shift()).abs()], axis=1).max(axis=1)
    x["ATR"] = _wilder(tr, 14)
    # Bollinger
    mid, sd = c.rolling(20).mean(), c.rolling(20).std()
    x["BB_mid"], x["BB_upper"], x["BB_lower"] = mid, mid + 2 * sd, mid - 2 * sd
    # Supertrend (ATR 10, x3)
    atr10 = _wilder(tr, 10).to_numpy(float)
    line, direction = _supertrend(hi.to_numpy(float), lo.to_numpy(float), c.to_numpy(float), atr10)
    x["Supertrend"], x["Supertrend_dir"] = line, direction
    # ADX (Wilder) with directional indices
    up, dn = hi.diff(), -lo.diff()
    plus_dm = pd.Series(np.where((up > dn) & (up > 0), up, 0.0), index=x.index)
    minus_dm = pd.Series(np.where((dn > up) & (dn > 0), dn, 0.0), index=x.index)
    atr_w = _wilder(tr, 14).replace(0, np.nan)
    x["Plus_DI"], x["Minus_DI"] = 100 * _wilder(plus_dm, 14) / atr_w, 100 * _wilder(minus_dm, 14) / atr_w
    dx = 100 * (x["Plus_DI"] - x["Minus_DI"]).abs() / (x["Plus_DI"] + x["Minus_DI"]).replace(0, np.nan)
    x["ADX"] = _wilder(dx, 14)
    # Stochastic
    ll, hh = lo.rolling(14).min(), hi.rolling(14).max()
    x["Stoch_K"] = 100 * (c - ll) / (hh - ll).replace(0, np.nan)
    x["Stoch_D"] = x["Stoch_K"].rolling(3).mean()
    # Volume
    x["Volume"], x["Volume_SMA20"] = v, v.rolling(20).mean()
    x["Relative_Volume"] = v / x["Volume_SMA20"].replace(0, np.nan)
    # Previous-session levels and classic pivots
    if is_intraday(x.index):
        day = x.index.normalize()
        agg = pd.DataFrame({"h": hi, "l": lo, "c": c}).groupby(day).agg(h=("h", "max"), l=("l", "min"), c=("c", "last")).shift(1)
        ph, pl, pc = (agg.reindex(day)[k].to_numpy() for k in ("h", "l", "c"))
        ph, pl, pc = (pd.Series(a, index=x.index) for a in (ph, pl, pc))
    else:
        ph, pl, pc = hi.shift(1), lo.shift(1), c.shift(1)
    pivot = (ph + pl + pc) / 3
    x["Prev_High"], x["Prev_Low"], x["Prev_Close"], x["Pivot"] = ph, pl, pc, pivot
    x["Pivot_R1"], x["Pivot_S1"] = 2 * pivot - pl, 2 * pivot - ph
    x["Pivot_R2"], x["Pivot_S2"] = pivot + (ph - pl), pivot - (ph - pl)
    # Swing levels (current and strictly-prior; strategies use the prior values)
    x["Support"], x["Resistance"] = lo.rolling(20).min(), hi.rolling(20).max()
    x["Support_prev"], x["Resistance_prev"] = x["Support"].shift(1), x["Resistance"].shift(1)
    return x


def level_rows(x):
    r, last = x.iloc[-1], float(x["close"].iloc[-1])
    spec = [("Resistance 2", "Pivot_R2"), ("Resistance 1", "Pivot_R1"), ("Swing resistance", "Resistance"),
            ("Pivot", "Pivot"), ("Previous close", "Prev_Close"), ("Previous high", "Prev_High"),
            ("Previous low", "Prev_Low"), ("Swing support", "Support"), ("Support 1", "Pivot_S1"),
            ("Support 2", "Pivot_S2")]
    rows = []
    for label, col in spec:
        v = fnum(r.get(col))
        if v is not None:
            rows.append({"Level": label, "Price": v, "From last": (v / last - 1) * 100 if last else None})
    return rows


def technical_read(x):
    """Factual observations from the latest bar. Returns (rows, counts)."""
    r = x.iloc[-1]
    close = float(r["close"])
    rows = []

    def add(name, value, reading, tone):
        rows.append({"Indicator": name, "Value": value, "Reading": reading, "tone": tone})

    e20 = x["close"].ewm(span=20, adjust=False, min_periods=20).mean().iloc[-1]
    e50 = x["close"].ewm(span=50, adjust=False, min_periods=50).mean().iloc[-1]
    if pd.notna(e20) and pd.notna(e50):
        if close > e20 > e50:
            add("Trend", f"EMA20 {price_str(e20)} / EMA50 {price_str(e50)}", "Price above both, short average leads", "up")
        elif close < e20 < e50:
            add("Trend", f"EMA20 {price_str(e20)} / EMA50 {price_str(e50)}", "Price below both, short average lags", "down")
        else:
            add("Trend", f"EMA20 {price_str(e20)} / EMA50 {price_str(e50)}", "Mixed: averages and price disagree", "flat")
    if pd.notna(r["Supertrend_dir"]):
        bull = r["Supertrend_dir"] > 0
        add("Supertrend", price_str(r["Supertrend"]), "Trend line is support (bullish)" if bull else "Trend line is resistance (bearish)", "up" if bull else "down")
    if pd.notna(r["RSI"]):
        v = r["RSI"]
        if v >= 70:
            add("RSI 14", f"{v:.1f}", "Overbought zone; can persist in strong trends", "flat")
        elif v <= 30:
            add("RSI 14", f"{v:.1f}", "Oversold zone; can persist in weak trends", "flat")
        elif v >= 55:
            add("RSI 14", f"{v:.1f}", "Momentum leans bullish", "up")
        elif v <= 45:
            add("RSI 14", f"{v:.1f}", "Momentum leans bearish", "down")
        else:
            add("RSI 14", f"{v:.1f}", "Neutral momentum", "flat")
    if pd.notna(r["MACD_hist"]):
        up = r["MACD_hist"] > 0
        add("MACD", f"{r['MACD']:.3f} vs {r['MACD_signal']:.3f}", "MACD above signal line" if up else "MACD below signal line", "up" if up else "down")
    if pd.notna(r["ADX"]):
        strong = r["ADX"] >= 25
        di = "up" if r["Plus_DI"] > r["Minus_DI"] else "down"
        add("ADX 14", f"{r['ADX']:.1f}", ("Strong trend, buyers ahead" if di == "up" else "Strong trend, sellers ahead") if strong else "Weak or range-bound trend", di if strong else "flat")
    if pd.notna(r["Stoch_K"]):
        k = r["Stoch_K"]
        if k >= 80:
            add("Stochastic", f"K {k:.0f}", "Near top of recent range", "flat")
        elif k <= 20:
            add("Stochastic", f"K {k:.0f}", "Near bottom of recent range", "flat")
        else:
            up = k > r["Stoch_D"] if pd.notna(r["Stoch_D"]) else None
            add("Stochastic", f"K {k:.0f}", "K above D" if up else "K below D", "up" if up else "down")
    if pd.notna(r["BB_upper"]) and r["BB_upper"] != r["BB_lower"]:
        b = (close - r["BB_lower"]) / (r["BB_upper"] - r["BB_lower"])
        add("Bollinger %B", f"{b:.2f}", "At or above upper band" if b >= 1 else ("At or below lower band" if b <= 0 else "Inside the bands"), "flat")
    if pd.notna(r["ATR"]) and close:
        add("ATR 14", f"{r['ATR']:.2f} ({r['ATR'] / close * 100:.2f}% of price)", "Typical bar range; use for stop distance", "flat")
    if pd.notna(r["Relative_Volume"]):
        rv = r["Relative_Volume"]
        add("Relative volume", f"{rv:.2f}x", "Unusually active" if rv >= 1.5 else ("Quiet" if rv < .7 else "Typical activity"), "flat")
    counts = {k: sum(1 for r_ in rows if r_["tone"] == k) for k in ("up", "down", "flat")}
    return rows, counts

# ───────────────────────────── strategy rules ─────────────────────────────
def _xa(a, b):
    return (a > b) & (a.shift(1) <= b.shift(1))


def _fmt(v, d=2):
    v = fnum(v)
    return "n/a" if v is None else f"{v:,.{d}f}"


# rule name -> (mask function(x, p), detail function(last_row, p))
ENTRY_RULES = {
    "EMA fast > EMA slow": (lambda x, p: x["Fast"] > x["Slow"], lambda r, p: f"fast {_fmt(r['Fast'])} vs slow {_fmt(r['Slow'])}"),
    "EMA fast crosses above EMA slow": (lambda x, p: _xa(x["Fast"], x["Slow"]), lambda r, p: f"fast {_fmt(r['Fast'])} vs slow {_fmt(r['Slow'])}"),
    "Price > EMA slow": (lambda x, p: x["close"] > x["Slow"], lambda r, p: f"close {_fmt(r['close'])} vs slow {_fmt(r['Slow'])}"),
    "Price > EMA20": (lambda x, p: x["close"] > x["EMA"], lambda r, p: f"close {_fmt(r['close'])} vs EMA20 {_fmt(r['EMA'])}"),
    "Price > VWAP": (lambda x, p: x["close"] > x["VWAP"], lambda r, p: f"close {_fmt(r['close'])} vs VWAP {_fmt(r['VWAP'])}"),
    "Price crosses above VWAP": (lambda x, p: _xa(x["close"], x["VWAP"]), lambda r, p: f"close {_fmt(r['close'])} vs VWAP {_fmt(r['VWAP'])}"),
    "RSI > threshold": (lambda x, p: x["RSI"] > p["rsi"], lambda r, p: f"RSI {_fmt(r['RSI'], 1)} vs {p['rsi']}"),
    "RSI < threshold": (lambda x, p: x["RSI"] < p["rsi"], lambda r, p: f"RSI {_fmt(r['RSI'], 1)} vs {p['rsi']}"),
    "RSI crosses above 30": (lambda x, p: (x["RSI"] > 30) & (x["RSI"].shift(1) <= 30), lambda r, p: f"RSI {_fmt(r['RSI'], 1)}"),
    "MACD > signal": (lambda x, p: x["MACD"] > x["MACD_signal"], lambda r, p: f"MACD {_fmt(r['MACD'], 3)} vs signal {_fmt(r['MACD_signal'], 3)}"),
    "MACD crosses above signal": (lambda x, p: _xa(x["MACD"], x["MACD_signal"]), lambda r, p: f"MACD {_fmt(r['MACD'], 3)} vs signal {_fmt(r['MACD_signal'], 3)}"),
    "Volume > average volume": (lambda x, p: x["Volume"] > x["Volume_SMA20"], lambda r, p: f"volume {_fmt(r['Volume'], 0)} vs 20-bar avg {_fmt(r['Volume_SMA20'], 0)}"),
    "Relative Volume > 1.5": (lambda x, p: x["Relative_Volume"] > p["rv"], lambda r, p: f"relative volume {_fmt(r['Relative_Volume'])}x vs {p['rv']}x"),
    "Price > Support": (lambda x, p: x["close"] > x["Support_prev"], lambda r, p: f"close {_fmt(r['close'])} vs prior 20-bar low {_fmt(r['Support_prev'])}"),
    "Price > Resistance": (lambda x, p: x["close"] > x["Resistance_prev"], lambda r, p: f"close {_fmt(r['close'])} vs prior 20-bar high {_fmt(r['Resistance_prev'])}"),
    "Supertrend bullish": (lambda x, p: x["Supertrend_dir"] > 0, lambda r, p: f"direction {_fmt(r['Supertrend_dir'], 0)}"),
    "Supertrend turns bullish": (lambda x, p: (x["Supertrend_dir"] > 0) & (x["Supertrend_dir"].shift(1) <= 0), lambda r, p: f"direction {_fmt(r['Supertrend_dir'], 0)}"),
    "ADX > 25": (lambda x, p: x["ADX"] > 25, lambda r, p: f"ADX {_fmt(r['ADX'], 1)}"),
    "Stochastic < 20": (lambda x, p: x["Stoch_K"] < 20, lambda r, p: f"%K {_fmt(r['Stoch_K'], 1)}"),
    "Close below lower Bollinger Band": (lambda x, p: x["close"] < x["BB_lower"], lambda r, p: f"close {_fmt(r['close'])} vs lower band {_fmt(r['BB_lower'])}"),
}
EXIT_RULES = {
    "EMA fast < EMA slow": (lambda x, p: x["Fast"] < x["Slow"], lambda r, p: f"fast {_fmt(r['Fast'])} vs slow {_fmt(r['Slow'])}"),
    "Price < EMA slow": (lambda x, p: x["close"] < x["Slow"], lambda r, p: f"close {_fmt(r['close'])} vs slow {_fmt(r['Slow'])}"),
    "Price < EMA20": (lambda x, p: x["close"] < x["EMA"], lambda r, p: f"close {_fmt(r['close'])} vs EMA20 {_fmt(r['EMA'])}"),
    "Price < VWAP": (lambda x, p: x["close"] < x["VWAP"], lambda r, p: f"close {_fmt(r['close'])} vs VWAP {_fmt(r['VWAP'])}"),
    "RSI > 60": (lambda x, p: x["RSI"] > 60, lambda r, p: f"RSI {_fmt(r['RSI'], 1)}"),
    "RSI > 70": (lambda x, p: x["RSI"] > 70, lambda r, p: f"RSI {_fmt(r['RSI'], 1)}"),
    "RSI < 30": (lambda x, p: x["RSI"] < 30, lambda r, p: f"RSI {_fmt(r['RSI'], 1)}"),
    "MACD < signal": (lambda x, p: x["MACD"] < x["MACD_signal"], lambda r, p: f"MACD {_fmt(r['MACD'], 3)} vs signal {_fmt(r['MACD_signal'], 3)}"),
    "Volume < average volume": (lambda x, p: x["Volume"] < x["Volume_SMA20"], lambda r, p: f"volume {_fmt(r['Volume'], 0)} vs 20-bar avg {_fmt(r['Volume_SMA20'], 0)}"),
    "Supertrend bearish": (lambda x, p: x["Supertrend_dir"] < 0, lambda r, p: f"direction {_fmt(r['Supertrend_dir'], 0)}"),
    "Price < Support": (lambda x, p: x["close"] < x["Support_prev"], lambda r, p: f"close {_fmt(r['close'])} vs prior 20-bar low {_fmt(r['Support_prev'])}"),
    "Close above Bollinger mid": (lambda x, p: x["close"] > x["BB_mid"], lambda r, p: f"close {_fmt(r['close'])} vs mid {_fmt(r['BB_mid'])}"),
}

LIBRARY = {
    "Golden Cross": dict(desc="Fast EMA crosses above the slow EMA for a trend-following entry; exits when the fast falls back below.",
                         entry=["EMA fast crosses above EMA slow"], exit=["EMA fast < EMA slow"]),
    "RSI Reversal": dict(desc="Enters when RSI recovers above 30 from oversold and exits once RSI rises above 60.",
                         entry=["RSI crosses above 30"], exit=["RSI > 60"]),
    "VWAP Reclaim": dict(desc="Enters when price moves back above VWAP. VWAP is session-anchored on intraday bars and a 20-bar rolling value otherwise.",
                         entry=["Price crosses above VWAP"], exit=["Price < VWAP"]),
    "Breakout + Volume": dict(desc="Requires a close above the prior 20-bar high together with elevated relative volume.",
                              entry=["Price > Resistance", "Relative Volume > 1.5"], exit=["Price < EMA20"]),
    "Bollinger Mean Reversion": dict(desc="Buys closes below the lower Bollinger Band and exits at the middle band.",
                                     entry=["Close below lower Bollinger Band"], exit=["Close above Bollinger mid"]),
    "Supertrend Trend Following": dict(desc="Uses a Supertrend flip to bullish as the entry and a flip to bearish as the exit.",
                                       entry=["Supertrend turns bullish"], exit=["Supertrend bearish"]),
    "MACD Crossover": dict(desc="Enters when MACD crosses above its signal line and exits when it falls below.",
                           entry=["MACD crosses above signal"], exit=["MACD < signal"]),
    "Volume Momentum": dict(desc="Requires price above EMA20 with relative volume above the chosen threshold.",
                            entry=["Price > EMA20", "Relative Volume > 1.5"], exit=["Price < EMA20"]),
}


def resolve_cfg(cfg):
    """Turn any saved config (library / advanced / legacy) into entry+exit rule lists and parameters."""
    p = {"fast": int(cfg.get("fast", 20)), "slow": int(cfg.get("slow", 50)),
         "rsi": float(cfg.get("rsi_threshold", 55)), "rv": float(cfg.get("rv_threshold", 1.5))}
    if p["fast"] >= p["slow"]:
        p["slow"] = p["fast"] + 1
    typ = cfg.get("type")
    if typ == "library":
        lib = LIBRARY.get(cfg.get("library"), LIBRARY["Golden Cross"])
        return dict(entry=lib["entry"], exit=lib["exit"], logic="AND", exit_logic="OR", params=p)
    if typ == "advanced":
        logic = cfg.get("logic", "AND")
        return dict(entry=cfg.get("entry", []), exit=cfg.get("exit", []), logic=logic,
                    exit_logic=cfg.get("exit_logic", logic), params=p)
    return dict(entry=["EMA fast > EMA slow"], exit=["EMA fast < EMA slow"], logic="AND", exit_logic="OR", params=p)


def strategy_masks(x, cfg):
    spec = resolve_cfg(cfg)
    p = spec["params"]
    x["Fast"] = x["close"].ewm(span=p["fast"], adjust=False, min_periods=p["fast"]).mean()
    x["Slow"] = x["close"].ewm(span=p["slow"], adjust=False, min_periods=p["slow"]).mean()

    def combine(names, table, logic):
        masks = [table[n][0](x, p).fillna(False).astype(bool) for n in names if n in table]
        if not masks:
            return pd.Series(False, index=x.index)
        frame = pd.concat(masks, axis=1)
        return frame.any(axis=1) if logic == "OR" else frame.all(axis=1)

    return combine(spec["entry"], ENTRY_RULES, spec["logic"]), combine(spec["exit"], EXIT_RULES, spec["exit_logic"])


def explain_strategy(x, cfg):
    """Evaluate every rule on the latest bar with the real indicator values."""
    spec = resolve_cfg(cfg)
    strategy_masks(x, cfg)  # attaches Fast/Slow
    r, out = x.iloc[-1], []
    for side, names, table in (("Entry", spec["entry"], ENTRY_RULES), ("Exit", spec["exit"], EXIT_RULES)):
        for n in names:
            if n not in table:
                continue
            try:
                met = bool(table[n][0](x, spec["params"]).iloc[-1])
                detail = table[n][1](r, spec["params"])
            except Exception:
                met, detail = False, "n/a"
            out.append({"side": side, "rule": n, "met": met, "detail": detail})
    return out


# ───────────────────────────── strategy storage ───────────────────────────
def save_strategy(name, cfg, base_id=None):
    t = now()
    old = one("SELECT version FROM strategies WHERE id=?", (base_id,)) if base_id else None
    if old:
        ver = int(old["version"]) + 1
        run("UPDATE strategies SET name=?,version=?,config=?,updated_at=? WHERE id=?", (name, ver, json.dumps(cfg), t, base_id))
        return base_id, ver
    sid = uid()
    run("INSERT INTO strategies VALUES(?,?,?,?,?,?)", (sid, name, 1, json.dumps(cfg), t, t))
    return sid, 1


def load_strategies():
    return q("SELECT * FROM strategies ORDER BY updated_at DESC")


# ───────────────────────────── back-test engine ───────────────────────────
def run_backtest(df, cfg, initial, fee_pct, slip_pct):
    """
    Honest bar-by-bar simulation
      * Signals are read at a bar's close and filled at the NEXT bar's open (no look-ahead).
      * Each trade risks a fixed quantity (allocation % of equity at entry / entry price), so a
        trade's P&L equals its real entry-to-exit P&L for both longs and shorts.
      * Stop-loss / take-profit are checked intrabar with high/low; gaps fill at the open;
        if both are touched in one bar the stop is assumed to hit first.
      * After a stop/target exit the strategy stays flat until its signal state changes.
      * Fees + slippage are charged on every entry and exit as a % of the traded notional.
    Returns (frame, trades DataFrame, metrics dict, trade list).
    """
    x = add_indicators(df, 20, 20)
    n = len(x)
    if n < 30:
        raise ValueError("At least 30 bars are required for a meaningful back-test.")
    entry, exit_ = strategy_masks(x, cfg)
    long_short = cfg.get("mode") == "Long / Short"
    alloc = min(max(float(cfg.get("allocation", 100)) / 100, 0.0), 1.0)
    stop, tgt = float(cfg.get("stop") or 0) / 100, float(cfg.get("target") or 0) / 100
    cost = (float(fee_pct) + float(slip_pct)) / 100
    o, hi, lo, c = (x[k].to_numpy(float) for k in ("open", "high", "low", "close"))
    ent, ext = entry.to_numpy(bool), exit_.to_numpy(bool)

    state, s = np.zeros(n), 0
    for i in range(n):
        if s != 1 and ent[i]:
            s = 1
        elif ext[i] and s != -1 and (s == 1 or long_short):
            s = -1 if long_short else 0
        state[i] = s

    cash, qty, entry_px, entry_i, eq_before, lock, bust = float(initial), 0.0, 0.0, -1, float(initial), None, False
    equity, posarr, trades = np.zeros(n), np.zeros(n), []

    def close_trade(i_exit, px, reason, charge_cost=True):
        nonlocal cash, qty
        fee = abs(qty) * px * cost if charge_cost else 0.0
        cash_after = cash + qty * (px - entry_px) - fee
        side = 1 if qty > 0 else -1
        trades.append({"entry_time": x.index[entry_i], "exit_time": x.index[i_exit], "side": "Long" if side > 0 else "Short",
                       "entry_price": entry_px, "exit_price": px, "return_pct": (px / entry_px - 1) * side * 100,
                       "pnl": cash_after - eq_before, "bars": i_exit - entry_i, "reason": reason})
        cash, qty = cash_after, 0.0

    for i in range(n):
        if bust:
            continue
        want = state[i - 1] if i > 0 else 0.0
        if lock is not None:
            if want == lock:
                want = 0.0
            else:
                lock = None
        have = float(np.sign(qty))
        if want != have:
            if have != 0.0:
                close_trade(i, o[i], "Signal")
            if want != 0.0:
                eq_before = cash
                notional = alloc * cash
                qty = want * notional / o[i]
                cash -= notional * cost
                entry_px, entry_i = o[i], i
        if qty != 0.0:
            side, exit_px, reason = (1 if qty > 0 else -1), None, None
            sp = entry_px * (1 - side * stop) if stop > 0 else None
            tp = entry_px * (1 + side * tgt) if tgt > 0 else None
            if side > 0:
                if sp is not None and lo[i] <= sp:
                    exit_px, reason = min(o[i], sp), "Stop-loss"
                elif tp is not None and hi[i] >= tp:
                    exit_px, reason = max(o[i], tp), "Take-profit"
            else:
                if sp is not None and hi[i] >= sp:
                    exit_px, reason = max(o[i], sp), "Stop-loss"
                elif tp is not None and lo[i] <= tp:
                    exit_px, reason = min(o[i], tp), "Take-profit"
            if exit_px is not None:
                close_trade(i, exit_px, reason)
                lock = side
            elif cash + qty * (c[i] - entry_px) <= 0:      # short squeezed beyond equity
                close_trade(i, c[i], "Liquidated", charge_cost=False)
                cash, bust = 0.0, True
        equity[i] = cash + qty * (c[i] - entry_px) if qty != 0.0 else cash
        posarr[i] = (qty * c[i] / equity[i]) if qty != 0.0 and equity[i] > 0 else 0.0
    if qty != 0.0:                                        # mark any open trade at the last close
        close_trade(n - 1, c[-1], "Open (marked to last close)", charge_cost=False)
        cash_marked = cash
        equity[-1] = cash_marked

    out = x.copy()
    out["position"], out["equity"] = posarr, equity
    out["drawdown_pct"] = (out["equity"] / out["equity"].cummax() - 1) * 100
    out["buy_hold"] = float(initial) * out["close"] / out["close"].iloc[0]
    tr = pd.DataFrame(trades)
    return out, tr, compute_metrics(out, tr, float(initial)), trades


def compute_metrics(out, tr, initial):
    n, final = len(out), float(out["equity"].iloc[-1])
    span = (out.index[-1] - out.index[0]).total_seconds()
    years = span / (365.25 * 86400)
    ppy = n / years if years > 0 else 252.0
    rets = out["equity"].pct_change().replace([np.inf, -np.inf], np.nan).dropna()
    sd = rets.std(ddof=1) if len(rets) > 1 else 0.0
    dsd = float(np.sqrt((np.minimum(rets, 0) ** 2).mean())) if len(rets) else 0.0
    cagr = ((final / initial) ** (1 / years) - 1) * 100 if years > 0.05 and final > 0 else None
    mdd = float(out["drawdown_pct"].min())
    dd_len = run_len = 0
    for v in out["drawdown_pct"]:
        run_len = run_len + 1 if v < 0 else 0
        dd_len = max(dd_len, run_len)
    m = {"ending_equity": final, "net_pnl": final - initial, "return_pct": (final / initial - 1) * 100, "cagr_pct": cagr,
         "buy_hold_pct": (float(out["close"].iloc[-1]) / float(out["close"].iloc[0]) - 1) * 100,
         "volatility_pct": float(sd * math.sqrt(ppy) * 100),
         "sharpe": float(rets.mean() / sd * math.sqrt(ppy)) if sd > 0 else 0.0,
         "sortino": float(rets.mean() / dsd * math.sqrt(ppy)) if dsd > 0 else 0.0,
         "max_drawdown_pct": mdd, "max_dd_bars": dd_len,
         "calmar": (cagr / abs(mdd)) if cagr is not None and mdd < 0 else None,
         "exposure_pct": float((out["position"] != 0).mean() * 100), "total_trades": len(tr)}
    if tr.empty:
        m.update(win_rate_pct=0.0, profit_factor=0.0, gross_profit=0.0, gross_loss=0.0, avg_trade=0.0, avg_win=0.0,
                 avg_loss=0.0, payoff=None, best_trade=0.0, worst_trade=0.0, avg_hold_days=0.0, max_win_streak=0, max_loss_streak=0)
        return m
    win, loss = tr[tr["pnl"] > 0], tr[tr["pnl"] < 0]
    gp, gl = float(win["pnl"].sum()), abs(float(loss["pnl"].sum()))

    def streak(positive):
        best = run_ = 0
        for v in tr["pnl"]:
            run_ = run_ + 1 if ((v > 0) if positive else (v <= 0)) else 0
            best = max(best, run_)
        return best

    aw = float(win["pnl"].mean()) if len(win) else 0.0
    al = float(loss["pnl"].mean()) if len(loss) else 0.0
    m.update(win_rate_pct=len(win) / len(tr) * 100, profit_factor=(gp / gl) if gl else (float("inf") if gp else 0.0),
             gross_profit=gp, gross_loss=-gl, avg_trade=float(tr["pnl"].mean()), avg_win=aw, avg_loss=al,
             payoff=(aw / abs(al)) if al else None, best_trade=float(tr["pnl"].max()), worst_trade=float(tr["pnl"].min()),
             avg_hold_days=float((tr["exit_time"] - tr["entry_time"]).dt.total_seconds().mean() / 86400),
             max_win_streak=streak(True), max_loss_streak=streak(False))
    return m

# ───────────────────────────── UI components ──────────────────────────────
def kpi(label, value, sub="", tone="flat", lead=False) -> str:
    return (f"<div class='kpi{' lead' if lead else ''}'><div class='k-label'>{h(label)}</div>"
            f"<div class='k-value'>{h(value)}</div><div class='k-sub {tone}'>{h(sub)}</div></div>")


def kpi_row(items):
    cols = st.columns(len(items))
    for col, it in zip(cols, items):
        col.markdown(kpi(**it), unsafe_allow_html=True)


def pill(kind, text) -> str:
    return f"<span class='pill {kind}'>{h(text)}</span>"


def render_table(df, fmt=None, tones=None, raw=(), max_rows=300):
    """Hand-built HTML table (version-proof, matches the theme). fmt: col->callable, tones: col->callable(v,row)."""
    fmt, tones = fmt or {}, tones or {}
    if df is None or len(df) == 0:
        st.markdown("<div class='tbl-wrap'><div style='padding:14px;color:#93A0B5'>No rows to show.</div></div>", unsafe_allow_html=True)
        return
    df = df.head(max_rows)
    cols = list(df.columns)
    numeric = {c for c in cols if pd.api.types.is_numeric_dtype(df[c]) and not pd.api.types.is_bool_dtype(df[c])}
    ths = "".join(f"<th class='{'num' if c in numeric else ''}'>{h(c)}</th>" for c in cols)
    body = []
    for _, row in df.iterrows():
        tds = []
        for c in cols:
            v = row[c]
            missing = v is None or (isinstance(v, float) and math.isnan(v))
            txt = fmt[c](v) if (c in fmt and not missing) else ("—" if missing else str(v))
            t = tones[c](v, row) if (c in tones and not missing) else None
            cls = ("num " if c in numeric else "") + (f"tone-{t}" if t else "")
            tds.append(f"<td class='{cls.strip()}'>{txt if c in raw else h(txt)}</td>")
        body.append("<tr>" + "".join(tds) + "</tr>")
    st.markdown(f"<div class='tbl-wrap'><table class='tbl'><thead><tr>{ths}</tr></thead><tbody>{''.join(body)}</tbody></table></div>",
                unsafe_allow_html=True)


def masthead():
    st.markdown(
        "<div class='mast'><div><span class='brand-name'>OOYT</span>"
        "<span class='brand-sub'>Research, back-testing and paper trading for Indian markets and crypto</span></div>"
        f"<div class='mast-right'>{datetime.now().strftime('%d %b %Y, %H:%M')}<br>Research only. No live orders are sent.</div></div>",
        unsafe_allow_html=True)


def tape():
    snaps, items = overview_snaps(), []
    for name, sym, _ in TAPE:
        s = snaps.get(sym) or {}
        if s.get("last") is None:
            continue
        ch = s.get("change")
        items.append(f"<span class='tq'><b>{h(name)}</b>{h(price_str(s['last']))} <span class='{tone_of(ch)}'>{h(pct(ch))}</span></span>")
    if items:
        track = "".join(items) * 4
        st.markdown(f"<div class='tape'><div class='tape-track'>{track}</div></div>", unsafe_allow_html=True)
    else:
        st.markdown("<div class='tape' style='padding:.6rem 0;color:#93A0B5;font-size:.85rem'>Live index quotes are unavailable right now. Check your connection and press Refresh.</div>", unsafe_allow_html=True)


# ───────────────────────────── charts ─────────────────────────────────────
PANES = ["RSI", "MACD", "Stochastic", "ADX", "ATR"]
OVERLAYS = ["SMA", "EMA", "VWAP", "Bollinger Bands", "Supertrend", "Support/Resistance", "Pivot Points"]


def rangebreaks_for(idx, interval, symbol):
    """Hide weekends, holidays and (intraday) off-hours so NSE/BSE charts have no empty gaps."""
    if not is_indian(symbol) or interval not in ("5m", "15m", "1h", "4h", "1d") or len(idx) < 3:
        return []
    rb = [dict(bounds=["sat", "mon"])]
    days = pd.DatetimeIndex(idx.normalize().unique())
    missing = [d for d in pd.date_range(days.min(), days.max(), freq="D").difference(days) if d.weekday() < 5]
    if missing:
        rb.append(dict(values=[d.strftime("%Y-%m-%d") for d in missing]))
    if interval != "1d":
        rb.append(dict(bounds=[15.5, 9.25], pattern="hour"))
    return rb


def _naive(ts):
    ts = pd.Timestamp(ts)
    return ts.tz_localize(None) if ts.tzinfo is not None else ts


def _style(fig, title, height):
    fig.update_layout(
        height=height, title=dict(text=title, x=0.0, font=dict(family=SERIF, size=22, color=C["ivory"])),
        paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
        font=dict(family=SANS, color=C["mist"], size=12), margin=dict(l=10, r=10, t=58, b=10),
        legend=dict(orientation="h", yanchor="bottom", y=1.0, xanchor="right", x=1, bgcolor="rgba(0,0,0,0)"),
        hovermode="x unified", hoverlabel=dict(bgcolor=C["raised"], bordercolor=C["line"], font=dict(color=C["ivory"])),
        dragmode="pan")
    fig.update_xaxes(showgrid=False, linecolor=C["line"], rangeslider_visible=False)
    fig.update_yaxes(gridcolor="rgba(147,160,181,0.10)", zeroline=False, linecolor=C["line"])


def price_chart(x, title, overlays, panes, interval, symbol, trades=None, key="chart"):
    if go is None:
        st.warning("Interactive charts need Plotly (pip install plotly). Showing a basic line chart instead.")
        st.line_chart(x["close"])
        return
    x = x.tail(900).copy()
    rb = rangebreaks_for(x.index, interval, symbol)
    x.index = x.index.tz_localize(None) if x.index.tz is not None else x.index
    show_vol = float(x["volume"].sum()) > 0
    panes = [p for p in panes if p in PANES]
    n_rows = 1 + int(show_vol) + len(panes)
    main = max(0.42, 1 - 0.15 * (n_rows - 1))
    heights = [main] + [(1 - main) / (n_rows - 1)] * (n_rows - 1) if n_rows > 1 else [1.0]
    fig = make_subplots(rows=n_rows, cols=1, shared_xaxes=True, vertical_spacing=0.02, row_heights=heights)
    fig.add_trace(go.Candlestick(x=x.index, open=x["open"], high=x["high"], low=x["low"], close=x["close"], name="Price",
                                 increasing_line_color=C["up"], decreasing_line_color=C["down"],
                                 increasing_fillcolor=C["up"], decreasing_fillcolor=C["down"], line=dict(width=1)), row=1, col=1)

    def line(col, name, color, row=1, dash="solid", width=1.4, series=None, **kw):
        y = series if series is not None else (x[col] if col in x else None)
        if y is not None and y.notna().any():
            fig.add_trace(go.Scatter(x=x.index, y=y, name=name, mode="lines", line=dict(color=color, width=width, dash=dash), **kw), row=row, col=1)

    for o in overlays:
        if o == "SMA":
            line("SMA", "SMA", C["gold"])
        elif o == "EMA":
            line("EMA", "EMA", C["sky"])
        elif o == "VWAP":
            line("VWAP", "VWAP", C["violet"])
        elif o == "Bollinger Bands":
            line("BB_upper", "BB upper", "#7C8CA6", width=1)
            line("BB_lower", "BB lower", "#7C8CA6", width=1, fill="tonexty", fillcolor="rgba(124,140,166,0.08)")
            line("BB_mid", "BB mid", "#7C8CA6", dash="dash", width=1)
        elif o == "Supertrend":
            line("Supertrend", "Supertrend up", C["up"], width=1.6, series=x["Supertrend"].where(x["Supertrend_dir"] > 0))
            line("Supertrend", "Supertrend down", C["down"], width=1.6, series=x["Supertrend"].where(x["Supertrend_dir"] < 0))
        elif o == "Support/Resistance":
            line("Support", "Support", C["up"], dash="dot", width=1.2)
            line("Resistance", "Resistance", C["down"], dash="dot", width=1.2)
        elif o == "Pivot Points":
            line("Pivot", "Pivot", C["gold_hi"], dash="dot", width=1)
            line("Pivot_R1", "R1", C["down"], dash="dot", width=1)
            line("Pivot_S1", "S1", C["up"], dash="dot", width=1)

    if trades:
        for side, sym_in, name in (("Long", "triangle-up", "Long entry"), ("Short", "triangle-down", "Short entry")):
            pts = [t for t in trades if t["side"] == side]
            if pts:
                fig.add_trace(go.Scatter(x=[_naive(t["entry_time"]) for t in pts], y=[t["entry_price"] for t in pts], mode="markers", name=name,
                                         marker=dict(symbol=sym_in, size=11, color=C["gold"], line=dict(color=C["ink"], width=1)),
                                         hovertemplate="%{y:,.2f}<extra>" + name + "</extra>"), row=1, col=1)
        fig.add_trace(go.Scatter(x=[_naive(t["exit_time"]) for t in trades], y=[t["exit_price"] for t in trades], mode="markers", name="Exit",
                                 marker=dict(symbol="x", size=9, color=[C["up"] if t["pnl"] > 0 else C["down"] for t in trades]),
                                 hovertemplate="%{y:,.2f}<extra>Exit</extra>"), row=1, col=1)

    r = 2
    if show_vol:
        fig.add_trace(go.Bar(x=x.index, y=x["volume"], name="Volume", showlegend=False, opacity=0.5,
                             marker_color=np.where(x["close"] >= x["open"], C["up"], C["down"]).tolist()), row=r, col=1)
        fig.update_yaxes(title_text="Volume", row=r, col=1)
        r += 1
    for p in panes:
        if p == "RSI":
            line("RSI", "RSI", C["gold"], row=r)
            for lv in (30, 70):
                fig.add_hline(y=lv, line=dict(color=C["mist"], width=1, dash="dot"), row=r, col=1)
            fig.update_yaxes(range=[0, 100], row=r, col=1)
        elif p == "MACD":
            fig.add_trace(go.Bar(x=x.index, y=x["MACD_hist"], name="Histogram", showlegend=False, opacity=0.55,
                                 marker_color=np.where(x["MACD_hist"] >= 0, C["up"], C["down"]).tolist()), row=r, col=1)
            line("MACD", "MACD", C["sky"], row=r)
            line("MACD_signal", "Signal", C["gold"], row=r)
        elif p == "Stochastic":
            line("Stoch_K", "%K", C["sky"], row=r)
            line("Stoch_D", "%D", C["gold"], row=r)
            for lv in (20, 80):
                fig.add_hline(y=lv, line=dict(color=C["mist"], width=1, dash="dot"), row=r, col=1)
            fig.update_yaxes(range=[0, 100], row=r, col=1)
        elif p == "ADX":
            line("ADX", "ADX", C["gold"], row=r)
            line("Plus_DI", "+DI", C["up"], row=r, width=1)
            line("Minus_DI", "-DI", C["down"], row=r, width=1)
        elif p == "ATR":
            line("ATR", "ATR", C["violet"], row=r)
        fig.update_yaxes(title_text=p, row=r, col=1)
        r += 1
    _style(fig, title, 520 + 130 * (n_rows - 1))
    if rb:
        fig.update_xaxes(rangebreaks=rb)
    plot(fig, key)


def equity_chart(out, key):
    if go is None:
        st.warning("Interactive charts need Plotly (pip install plotly).")
        st.line_chart(out[["equity", "buy_hold"]])
        return
    xi = out.index.tz_localize(None) if out.index.tz is not None else out.index
    fig = make_subplots(rows=2, cols=1, shared_xaxes=True, vertical_spacing=0.04, row_heights=[0.72, 0.28])
    fig.add_trace(go.Scatter(x=xi, y=out["equity"], name="Strategy", line=dict(color=C["gold"], width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=xi, y=out["buy_hold"], name="Buy and hold", line=dict(color=C["mist"], width=1.3, dash="dash")), row=1, col=1)
    fig.add_trace(go.Scatter(x=xi, y=out["drawdown_pct"], name="Drawdown %", fill="tozeroy",
                             line=dict(color=C["down"], width=1), fillcolor="rgba(226,96,111,0.22)"), row=2, col=1)
    fig.update_yaxes(title_text="Equity", row=1, col=1)
    fig.update_yaxes(title_text="Drawdown %", row=2, col=1)
    _style(fig, "Equity curve against buy and hold", 560)
    plot(fig, key)


def donut_chart(labels, values, key, title="Allocation"):
    if go is None:
        return
    palette = [C["gold"], C["sky"], C["up"], C["violet"], C["down"], "#7C8CA6", C["gold_hi"], "#4E6A8F"]
    fig = go.Figure(go.Pie(labels=labels, values=values, hole=0.62, sort=False,
                           marker=dict(colors=palette * 4, line=dict(color=C["ink"], width=2)), textinfo="percent"))
    _style(fig, title, 380)
    fig.update_layout(showlegend=True, legend=dict(orientation="v", x=1.0, y=0.5), hovermode="closest")
    plot(fig, key)


# ───────────────────────────── navigation ─────────────────────────────────
def sym_options(asset, current=None):
    if asset == "Crypto":
        base = {s: s for s in (delta_symbol_options() or ["BTCUSD", "ETHUSD"])}
    else:
        base = dict(ASSET_MAP[asset])
    if current and current not in base.values():
        base = {f"Custom: {current}": current, **base}
    return base


def open_market(asset, symbol=None, workspace="Dashboard", mode=None):
    """Callback-safe navigation (runs before widgets are instantiated on the next run)."""
    ss = st.session_state
    symbol = symbol or default_symbol(asset)
    opts = sym_options(asset, symbol)
    ss["active"], ss["asset_class"], ss["symbol"], ss["mode_label"] = True, asset, symbol, mode
    ss["asset_picker"] = asset
    ss[f"sym_{asset}"] = next((lbl for lbl, s in opts.items() if s == symbol), symbol)
    ss["workspace"], ss["nav"] = workspace, workspace


def go_home():
    st.session_state["active"] = False


def _asset_changed():
    ss = st.session_state
    ss["asset_class"] = ss["asset_picker"]
    ss["symbol"] = default_symbol(ss["asset_picker"])
    ss["mode_label"] = None


def cur():
    ss = st.session_state
    return ss["asset_class"], ss["symbol"], provider_of(ss["asset_class"])


def search_box(key, compact=False):
    return st.text_input("Search instruments", key=f"search_{key}", label_visibility="collapsed" if compact else "visible",
                         placeholder="Search by name or symbol: Reliance, NIFTY, GOLDBEES, BTCUSD")


def search_results(term, key):
    t = (term or "").strip()
    if not t:
        return
    rows = search_catalog(t)
    opts = [f"{r['name']}   ({r['symbol']}, {r['asset']})" for r in rows]
    custom = None
    if " " not in t and len(t) >= 2:
        custom = f"Use {t.upper()} as a custom Yahoo Finance symbol"
        opts.append(custom)
    if not opts:
        st.caption("No instrument matched. Try a different name or symbol.")
        return
    pick = st.selectbox("Matches", opts, key=f"match_{key}")
    if pick == custom:
        asset, symbol = "Share Investment", t.upper()
    else:
        r = rows[opts.index(pick)]
        asset, symbol = r["asset"], r["symbol"]
    btn("Open instrument", type="primary", key=f"open_{key}", on_click=open_market, kwargs=dict(asset=asset, symbol=symbol))


TILES = [
    ("Share Investment", "Stocks with price history, trend analysis and paper trades.",
     "<svg viewBox='0 0 32 32'><polyline points='3,25 12,15 18,20 29,7'/><polyline points='22,7 29,7 29,14'/></svg>"),
    ("Option Trading", "Study the underlying index and research strategies without inventing premiums.",
     "<svg viewBox='0 0 32 32'><circle cx='16' cy='16' r='12'/><polygon points='16,7 21,16 16,25 11,16'/></svg>"),
    ("Mutual Funds", "Fund NAV history and monitoring.",
     "<svg viewBox='0 0 32 32'><rect x='5' y='17' width='5' height='10'/><rect x='13' y='11' width='5' height='16'/><rect x='21' y='5' width='5' height='22'/></svg>"),
    ("ETFs", "Exchange-traded funds and market trends.",
     "<svg viewBox='0 0 32 32'><polygon points='16,4 29,10 16,16 3,10'/><polyline points='3,16 16,22 29,16'/><polyline points='3,22 16,28 29,22'/></svg>"),
    ("Crypto", "Delta Exchange markets, charts and paper trades.",
     "<svg viewBox='0 0 32 32'><polygon points='16,3 27,9.5 27,22.5 16,29 5,22.5 5,9.5'/><circle cx='16' cy='16' r='4.5'/></svg>"),
]


def home():
    masthead()
    tape()
    left, right = st.columns([3, 2])
    with left:
        st.markdown("<div class='hero'><h1>Analyse, test and paper-trade before you commit capital.</h1>"
                    "<p>Indian equities, indices, ETFs, mutual funds and crypto in one workspace. Every number comes from a "
                    "live data provider; nothing is simulated or invented.</p></div>", unsafe_allow_html=True)
    with right:
        st.markdown("<div style='height:2.2rem'></div>", unsafe_allow_html=True)
        term = search_box("home")
        search_results(term, "home")
    st.markdown("### Choose a market")
    cols = st.columns(5)
    for col, (name, desc, svg) in zip(cols, TILES):
        with col:
            st.markdown(f"<div class='tile'>{svg}<h3>{h(name)}</h3><p>{h(desc)}</p></div>", unsafe_allow_html=True)
            asset = "Indices" if name == "Option Trading" else name
            btn(f"Open {name}", key=f"tile_{name}", type="primary" if name == "Crypto" else "secondary", on_click=open_market,
                kwargs=dict(asset=asset, symbol="^NSEI" if name == "Option Trading" else None,
                            mode="Option Trading" if name == "Option Trading" else None))
    st.markdown("### Indian market overview")
    snaps = overview_snaps()
    items = []
    for name, sym, prov in TAPE[:4]:
        s = snaps.get(sym) or {}
        if s.get("last") is None:
            items.append(dict(label=name, value="Unavailable", sub="Provider did not respond"))
        else:
            items.append(dict(label=name, value=price_str(s["last"]), sub=pct(s.get("change")), tone=tone_of(s.get("change")), lead=(name == "Nifty 50")))
    kpi_row(items)
    st.markdown("### Workspaces")
    cols = st.columns(7)
    for col, ws in zip(cols, ["Portfolio", "Watchlist", "Strategy Builder", "Backtester", "Scanner", "Paper Trading", "Learn"]):
        with col:
            ss = st.session_state
            btn(ws, key=f"home_ws_{ws}", on_click=open_market,
                kwargs=dict(asset=ss.get("asset_class") or "Share Investment", symbol=ss.get("symbol"), workspace=ws))


# ───────────────────────────── shared page pieces ─────────────────────────
def instrument_head(asset, symbol, pills=""):
    mode = st.session_state.get("mode_label")
    st.markdown(f"<div class='inst-head'><span class='inst-name'>{h(label_for(asset, symbol))}</span>"
                f"<span class='inst-sym'>{h(symbol)} · {h(mode or asset)}</span>{pills}</div>", unsafe_allow_html=True)


def status_pill(df, interval):
    kind, label, detail = data_status(df, interval)
    return pill(kind, f"{label} · {detail}")


def fetch_df(asset, symbol, prov, period, interval, what="Loading market data"):
    with loading(what):
        return get_market_df(symbol, prov, period, interval)


def tf_controls(prefix, default_interval="1d", periods=None):
    c1, c2, _ = st.columns([1, 1, 3])
    interval = c1.selectbox("Timeframe", INTERVALS, index=INTERVALS.index(default_interval), key=f"{prefix}_tf")
    opts = periods or period_options(interval)
    dflt = DEFAULT_PERIOD[interval] if DEFAULT_PERIOD[interval] in opts else opts[-1]
    period = c2.selectbox("History", opts, index=opts.index(dflt), key=f"{prefix}_p_{interval}")
    return interval, period


def read_table(x):
    rows, counts = technical_read(x)
    tmap = {r["Indicator"]: r["tone"] for r in rows}
    df = pd.DataFrame([{k: r[k] for k in ("Indicator", "Value", "Reading")} for r in rows])
    render_table(df, tones={"Reading": lambda v, row: tmap.get(row["Indicator"])})
    st.caption(f"Of {len(rows)} readings: {counts['up']} bullish, {counts['down']} bearish, {counts['flat']} neutral. "
               "These describe the latest bar. They are observations, not a forecast.")


def levels_table(x):
    df = pd.DataFrame(level_rows(x))
    render_table(df, fmt={"Price": price_str, "From last": pct}, tones={"From last": lambda v, r: tone_of(v)})


def no_data(asset, symbol):
    st.warning(f"No candles were returned for {symbol} at this timeframe. Try a longer history or a daily timeframe. "
               "Intraday history is limited to about 60 days for Indian markets.")


# ───────────────────────────── dashboard ──────────────────────────────────
def render_dashboard():
    asset, symbol, prov = cur()
    interval, period = tf_controls("dash")
    try:
        df = fetch_df(asset, symbol, prov, period, interval, "Preparing market workspace")
        snap = market_snapshot(symbol, prov)
    except Exception as e:
        instrument_head(asset, symbol)
        st.error(fetch_error_message(e))
        return
    instrument_head(asset, symbol, status_pill(df, interval))
    if df.empty:
        no_data(asset, symbol)
        return
    sym = cur_symbol(asset)
    last, ch = snap.get("last"), snap.get("change")
    rng = "—" if snap.get("low") is None else f"{price_str(snap['low'])} – {price_str(snap['high'])}"
    vol = "—" if not snap.get("volume") else indian(snap["volume"], 0)
    if snap.get("bid") and snap.get("ask"):
        quote = dict(label="Bid / Ask", value=f"{price_str(snap['bid'])} / {price_str(snap['ask'])}", sub="Best available quote")
    else:
        quote = dict(label="Previous close", value=f"{sym}{price_str(snap.get('prev'))}", sub="Prior daily bar")
    kpi_row([dict(label="Last", value=f"{sym}{price_str(last)}", sub=pct(ch), tone=tone_of(ch), lead=True),
             dict(label="Day range", value=rng, sub="Latest daily bar"),
             dict(label="Volume", value=vol, sub="Latest daily bar" if prov == "yahoo" else "24 hours"),
             dict(label="Bars loaded", value=f"{len(df):,}", sub=f"{interval} candles"), quote])
    x = add_indicators(df)
    price_chart(x, f"{label_for(asset, symbol)}  ·  {interval}", ["SMA", "EMA", "Support/Resistance"], [], interval, symbol, key="dash_chart")
    a, b = st.columns([2, 3])
    with a:
        st.markdown("### Key levels")
        levels_table(x)
    with b:
        st.markdown("### Technical read")
        read_table(x)


# ───────────────────────────── analyser ───────────────────────────────────
def render_analyser():
    asset, symbol, prov = cur()
    interval, period = tf_controls("an")
    c1, c2 = st.columns(2)
    overlays = c1.multiselect("Chart overlays", OVERLAYS, default=["SMA", "EMA", "VWAP", "Support/Resistance"], key="an_over")
    panes = c2.multiselect("Indicator panes", PANES, default=["RSI", "MACD"], key="an_panes")
    a, b, _ = st.columns([1, 1, 3])
    sma = a.number_input("SMA period", 2, 400, 20, key="an_sma")
    ema = b.number_input("EMA period", 2, 400, 20, key="an_ema")
    try:
        df = fetch_df(asset, symbol, prov, period, interval)
    except Exception as e:
        st.error(fetch_error_message(e))
        return
    instrument_head(asset, symbol, status_pill(df, interval))
    if df.empty:
        no_data(asset, symbol)
        return
    x = add_indicators(df, int(sma), int(ema))
    price_chart(x, f"{label_for(asset, symbol)}  ·  {interval}", overlays, panes, interval, symbol, key="an_chart")
    a, b = st.columns([2, 3])
    with a:
        st.markdown("### Support, resistance and pivots")
        levels_table(x)
    with b:
        st.markdown("### Technical read")
        read_table(x)
    with st.expander("Indicator guide"):
        st.markdown("**SMA / EMA** smooth closing prices; the EMA weights recent bars more. **VWAP** is price weighted by volume "
                    "(reset each session on intraday charts). **RSI** is a 0–100 momentum oscillator. **MACD** is the gap between a fast "
                    "and slow EMA plus a signal line. **ATR** is typical bar range. **Bollinger Bands** are a moving average ± 2 standard "
                    "deviations. **Supertrend** is an ATR-based trend line. **ADX** measures trend strength, not direction. "
                    "**Stochastic** locates the close within its recent range. **Relative volume** compares volume with its 20-bar average.")
    with st.expander("Recent bars and indicator values"):
        cols = [c for c in ["open", "high", "low", "close", "volume", "SMA", "EMA", "VWAP", "RSI", "MACD", "MACD_signal", "ATR", "ADX", "Stoch_K", "Relative_Volume"] if c in x]
        t = x[cols].tail(200).iloc[::-1].copy()
        t.index = t.index.strftime("%Y-%m-%d %H:%M")
        wide(st.dataframe, t.round(4))
        st.download_button("Download this table (CSV)", x[cols].to_csv().encode(), file_name=f"{symbol}_{interval}_indicators.csv", mime="text/csv")


# ───────────────────────────── strategy builder ───────────────────────────
def strategy_target():
    """Choose to save as new or update an existing strategy (real version bump)."""
    rows = load_strategies()
    opts = {"Save as a new strategy": None}
    for r in rows:
        opts[f"Update “{r['name']}” (currently v{r['version']})"] = r["id"]
    pick = st.selectbox("Save to", list(opts), key="sb_target")
    return opts[pick]


def render_strategy_builder():
    mode = st.radio("Builder mode", ["Beginner", "Advanced"], horizontal=True, key="sb_mode")
    if mode == "Beginner":
        choice = st.selectbox("Starting strategy", list(LIBRARY), key="sb_lib")
        lib = LIBRARY[choice]
        st.info(lib["desc"])
        st.markdown(f"**Entry:** {' and '.join(lib['entry'])}  \n**Exit:** {' or '.join(lib['exit'])}")
        a, b, c = st.columns(3)
        fast = a.number_input("Fast EMA", 2, 200, 20, key="sb_fast")
        slow = b.number_input("Slow EMA", 3, 400, 50, key="sb_slow")
        pos = c.selectbox("Position mode", ["Long only", "Long / Short"], key="sb_pos")
        d, e, f = st.columns(3)
        stop = d.number_input("Stop-loss %", 0.0, 50.0, 0.0, step=0.5, key="sb_stop")
        tgt = e.number_input("Take-profit %", 0.0, 200.0, 0.0, step=0.5, key="sb_tgt")
        alloc = f.slider("Capital allocation %", 5, 100, 25, key="sb_alloc")
        if fast >= slow:
            st.warning("The fast EMA should be shorter than the slow EMA. The slow EMA will be adjusted to fast + 1 when tested.")
        name = st.text_input("Strategy name", value=choice, key="sb_name")
        cfg = {"type": "library", "library": choice, "fast": int(fast), "slow": int(slow), "mode": pos, "stop": float(stop), "target": float(tgt), "allocation": int(alloc)}
    else:
        name = st.text_input("Strategy name", value="My advanced strategy", key="sb_name_adv")
        a, b = st.columns(2)
        logic = a.radio("Combine entry conditions with", ["AND", "OR"], horizontal=True, key="sb_logic")
        exit_logic = b.radio("Combine exit conditions with", ["OR", "AND"], horizontal=True, key="sb_xlogic")
        entries = st.multiselect("Entry conditions", list(ENTRY_RULES), default=["EMA fast > EMA slow", "RSI > threshold"], key="sb_entries")
        exits = st.multiselect("Exit conditions", list(EXIT_RULES), default=["EMA fast < EMA slow"], key="sb_exits")
        a, b, c, d = st.columns(4)
        fast = a.number_input("Fast EMA", 2, 200, 20, key="sb_fast_a")
        slow = b.number_input("Slow EMA", 3, 400, 50, key="sb_slow_a")
        rsi = c.number_input("RSI threshold", 1.0, 99.0, 55.0, key="sb_rsi")
        rv = d.number_input("Relative-volume threshold", 0.1, 10.0, 1.5, step=0.1, key="sb_rv")
        a, b, c, d = st.columns(4)
        pos = a.selectbox("Position mode", ["Long only", "Long / Short"], key="sb_pos_a")
        stop = b.number_input("Stop-loss %", 0.0, 50.0, 0.0, step=0.5, key="sb_stop_a")
        tgt = c.number_input("Take-profit %", 0.0, 200.0, 0.0, step=0.5, key="sb_tgt_a")
        alloc = d.slider("Capital allocation %", 5, 100, 25, key="sb_alloc_a")
        st.code(("ENTER when  " + f"\n   {logic}  ".join(entries) if entries else "No entry conditions selected")
                + ("\nEXIT when   " + f"\n   {exit_logic}  ".join(exits) if exits else ""), language="text")
        cfg = {"type": "advanced", "logic": logic, "exit_logic": exit_logic, "entry": entries, "exit": exits, "fast": int(fast), "slow": int(slow),
               "rsi_threshold": float(rsi), "rv_threshold": float(rv), "mode": pos, "stop": float(stop), "target": float(tgt), "allocation": int(alloc)}
    target = strategy_target()
    ready = bool(name.strip()) and (cfg["type"] == "library" or bool(cfg["entry"]))
    if not ready:
        st.caption("Give the strategy a name and at least one entry condition to save it.")
    if st.button("Save strategy", type="primary", disabled=not ready, key="sb_save"):
        sid, ver = save_strategy(name.strip(), cfg, target)
        st.session_state["strategy_pick"] = sid
        st.success(f"Saved “{name.strip()}” as version {ver}. Open the Backtester to test it.")
    rows = load_strategies()
    if rows:
        st.markdown("### Saved strategies")
        render_table(pd.DataFrame([{"Name": r["name"], "Version": r["version"], "Type": json.loads(r["config"]).get("type", "legacy"), "Updated": r["updated_at"]} for r in rows]),
                     fmt={"Version": lambda v: f"v{v}"})
        opts = {f"{r['name']} (v{r['version']})": r["id"] for r in rows}
        c1, c2 = st.columns([3, 1])
        victim = c1.selectbox("Remove a strategy", list(opts), key="sb_del_pick")
        if c2.button("Delete", key="sb_del"):
            run("DELETE FROM strategies WHERE id=?", (opts[victim],))
            st.rerun()


# ───────────────────────────── backtester ─────────────────────────────────
def load_saved_dataset(path):
    df = pd.read_csv(path, index_col=0, parse_dates=True)
    df.index = pd.to_datetime(df.index, utc=True, errors="coerce")
    return clean_ohlcv(df[df.index.notna()])


def metric_val(m, k, kind):
    v = m.get(k)
    if v is None or (isinstance(v, float) and math.isnan(v)):
        return "—"
    if isinstance(v, float) and math.isinf(v):
        return "∞"
    return {"pct": f"{v:.2f}%", "num": f"{v:.2f}", "int": f"{int(v)}", "days": f"{v:.1f} days", "money": money(v)}[kind]


def render_bt_results(res):
    m, out, tr = res["met"], res["out"], res["tr"]
    edge = m["return_pct"] - m["buy_hold_pct"]
    kpi_row([dict(label="Ending equity", value=money(m["ending_equity"]), sub=pct(m["return_pct"]), tone=tone_of(m["return_pct"]), lead=True),
             dict(label="Net profit", value=money(m["net_pnl"]), sub=f"{pct(edge)} vs buy and hold", tone=tone_of(edge)),
             dict(label="Max drawdown", value=f"{m['max_drawdown_pct']:.2f}%", sub=f"Longest {m['max_dd_bars']} bars", tone="down"),
             dict(label="Sharpe / Sortino", value=f"{m['sharpe']:.2f} / {m['sortino']:.2f}", sub="Annualised, zero risk-free rate"),
             dict(label="Trades", value=str(m["total_trades"]), sub=f"Win rate {m['win_rate_pct']:.1f}%")])
    st.markdown("<div style='height:.7rem'></div>", unsafe_allow_html=True)
    rows = [("CAGR", metric_val(m, "cagr_pct", "pct")), ("Buy and hold", metric_val(m, "buy_hold_pct", "pct")),
            ("Volatility (annual)", metric_val(m, "volatility_pct", "pct")), ("Calmar", metric_val(m, "calmar", "num")),
            ("Exposure", metric_val(m, "exposure_pct", "pct")), ("Profit factor", metric_val(m, "profit_factor", "num")),
            ("Payoff ratio", metric_val(m, "payoff", "num")), ("Average trade", metric_val(m, "avg_trade", "money")),
            ("Average win", metric_val(m, "avg_win", "money")), ("Average loss", metric_val(m, "avg_loss", "money")),
            ("Best trade", metric_val(m, "best_trade", "money")), ("Worst trade", metric_val(m, "worst_trade", "money")),
            ("Average hold", metric_val(m, "avg_hold_days", "days")), ("Win streak", metric_val(m, "max_win_streak", "int")),
            ("Loss streak", metric_val(m, "max_loss_streak", "int")), ("Gross profit", metric_val(m, "gross_profit", "money"))]
    cols = st.columns(8)
    for i, (k, v) in enumerate(rows):
        cols[i % 8].markdown(f"<div style='margin-bottom:.8rem'><div class='k-label'>{h(k)}</div><div style='font-size:1.05rem'>{h(v)}</div></div>", unsafe_allow_html=True)
    if m["total_trades"] == 0:
        st.info("This strategy produced no trades on the selected history. Try a longer range or looser conditions.")
    equity_chart(out, "bt_equity")
    price_chart(out, f"{res['symbol']} with trades", ["EMA"], [], res["interval"], res["symbol"], trades=res["trades"], key="bt_price")
    if not tr.empty:
        st.markdown("### Trade log")
        t = tr.copy()
        t["entry_time"] = t["entry_time"].dt.strftime("%Y-%m-%d %H:%M")
        t["exit_time"] = t["exit_time"].dt.strftime("%Y-%m-%d %H:%M")
        t = t.rename(columns={"entry_time": "Entry", "exit_time": "Exit", "side": "Side", "entry_price": "Entry price", "exit_price": "Exit price",
                              "return_pct": "Return", "pnl": "P&L", "bars": "Bars", "reason": "Exit reason"})
        render_table(t.iloc[::-1], fmt={"Entry price": price_str, "Exit price": price_str, "Return": pct, "P&L": money},
                     tones={"Return": lambda v, r: tone_of(v), "P&L": lambda v, r: tone_of(v)})
        c1, c2 = st.columns(2)
        c1.download_button("Download trades (CSV)", tr.to_csv(index=False).encode(), file_name="ooyt_trades.csv", mime="text/csv")
        c2.download_button("Download equity curve (CSV)", out[["close", "equity", "buy_hold", "drawdown_pct", "position"]].to_csv().encode(),
                           file_name="ooyt_equity.csv", mime="text/csv")
    st.caption("Signals are read at a bar's close and filled at the next bar's open. Stops and targets use intrabar highs and lows; when both "
               "are touched in one bar the stop is assumed to fill first. Fees and slippage are charged on every entry and exit.")


def render_backtester():
    asset, symbol, prov = cur()
    rows = load_strategies()
    smap = {f"{r['name']}  (v{r['version']})": r for r in rows}
    if not smap:
        st.info("You have no saved strategies yet, so the default EMA 20/50 crossover is used. Build your own in Strategy Builder.")
    labels = list(smap) or ["Default EMA 20/50 crossover"]
    pre = st.session_state.get("strategy_pick")
    idx = next((i for i, r in enumerate(smap.values()) if r["id"] == pre), 0)
    pick = st.selectbox("Strategy", labels, index=idx, key="bt_strategy")
    cfg = json.loads(smap[pick]["config"]) if smap else {"fast": 20, "slow": 50, "mode": "Long only", "stop": 0, "target": 0, "allocation": 100}

    src_opts = ["Live provider history"] + (["Saved dataset"] if q("SELECT 1 FROM datasets LIMIT 1") else [])
    source = st.radio("Data", src_opts, horizontal=True, key="bt_source")
    ds_path = None
    if source == "Saved dataset":
        ds = q("SELECT * FROM datasets ORDER BY created_at DESC")
        dmap = {f"{d['name']} · {d['rows']:,} rows · {d['created_at']}": d["path"] for d in ds}
        ds_path = dmap[st.selectbox("Dataset", list(dmap), key="bt_ds")]
        interval, period = "1d", "5y"
    else:
        interval, period = tf_controls("bt", periods=None)
    a, b, c = st.columns(3)
    initial = a.number_input("Starting capital", 1000.0, 1e9, 100000.0, step=1000.0, key="bt_cap")
    fee = b.number_input("Fees % per trade side", 0.0, 5.0, 0.10, step=0.05, key="bt_fee")
    slip = c.number_input("Slippage % per trade side", 0.0, 5.0, 0.05, step=0.05, key="bt_slip")
    if st.session_state.get("mode_label") == "Option Trading":
        st.warning("Option Trading tests the underlying index only. Option premiums, expiry, implied volatility and Greeks are not simulated.")

    with st.expander("Position size calculator"):
        r1, r2, r3 = st.columns(3)
        risk = r1.number_input("Risk per trade %", 0.1, 10.0, 1.0, step=0.1, key="bt_risk")
        e_px = r2.number_input("Planned entry price", 0.0, 1e12, 0.0, key="bt_epx")
        s_px = r3.number_input("Planned stop price", 0.0, 1e12, 0.0, key="bt_spx")
        if e_px > 0 and s_px > 0 and e_px != s_px:
            cash = initial * risk / 100
            st.info(f"Maximum loss {money(cash)} · risk per unit {price_str(abs(e_px - s_px))} · quantity about {cash / abs(e_px - s_px):,.2f}. This is arithmetic, not an order recommendation.")

    # Live explanation of the strategy on the latest bar
    try:
        df = load_saved_dataset(ds_path) if ds_path else get_market_df(symbol, prov, "1y" if interval in ("1d", "1wk") else period, interval)
        if not df.empty and len(df) > 60:
            with st.expander("What is the strategy saying right now?", expanded=False):
                for e in explain_strategy(add_indicators(df), cfg):
                    st.markdown(f"{'🟢' if e['met'] else '⚪'} **{e['side']}** · {e['rule']} — {e['detail']}")
    except Exception:
        pass

    if st.button("Run backtest", type="primary", key="bt_run"):
        try:
            with loading("Running back-test"):
                df = load_saved_dataset(ds_path) if ds_path else get_market_df(symbol, prov, period, interval)
                if df.empty:
                    st.error("No historical data was returned for this selection.")
                    return
                out, tr, met, trades = run_backtest(df, cfg, float(initial), float(fee), float(slip))
            st.session_state["bt"] = dict(out=out, tr=tr, met=met, trades=trades, symbol=symbol, interval=interval, name=pick)
            st.session_state["last_backtest_metrics"] = met
        except ValueError as e:
            st.error(str(e))
        except Exception as e:
            st.error(fetch_error_message(e))
    res = st.session_state.get("bt")
    if res:
        st.markdown(f"### Results · {h(res['name'])} on {h(label_for(asset, res['symbol']))}", unsafe_allow_html=True)
        render_bt_results(res)


# ───────────────────────────── scanner ────────────────────────────────────
SCAN_RULES = {
    "Price > EMA20": lambda z: z["close"] > z["EMA"],
    "Price > VWAP": lambda z: z["close"] > z["VWAP"],
    "RSI > 55": lambda z: z["RSI"] > 55,
    "RSI < 35": lambda z: z["RSI"] < 35,
    "Relative Volume > 1.5": lambda z: z["Relative_Volume"] > 1.5,
    "MACD > signal": lambda z: z["MACD"] > z["MACD_signal"],
    "Supertrend bullish": lambda z: z["Supertrend_dir"] > 0,
    "ADX > 25": lambda z: z["ADX"] > 25,
    "Near 20-bar high": lambda z: z["close"] >= 0.98 * z["Resistance"],
}


def scan_one(row, tf, rules):
    try:
        prov = provider_of(row["asset"])
        df = fetch_market_raw(row["symbol"], prov, DEFAULT_PERIOD[tf] if tf != "1d" else "1y", tf)
        if len(df) < 60:
            return None
        x = add_indicators(df)
        z = x.iloc[-1]
        if not all(bool(SCAN_RULES[r](z)) for r in rules):
            return None
        prev = x["close"].iloc[-2]
        return {"Name": row["name"], "Symbol": row["symbol"], "asset": row["asset"], "Price": float(z["close"]), "Change": (z["close"] / prev - 1) * 100,
                "RSI": fnum(z["RSI"]), "ADX": fnum(z["ADX"]), "Rel. volume": fnum(z["Relative_Volume"]),
                "Trend": "Bullish" if z["Supertrend_dir"] > 0 else "Bearish"}
    except Exception:
        return None


def render_scanner():
    st.caption("Scans a universe on its latest completed bar. Results are observations, not predictions.")
    a, b, c = st.columns(3)
    universe = a.selectbox("Universe", ["Stocks", "Indices", "ETFs", "Mutual Funds", "Crypto"], key="sc_uni")
    tf = b.selectbox("Scan timeframe", ["1d", "1h", "15m"], key="sc_tf")
    amap = {"Stocks": "Share Investment", "Indices": "Indices", "ETFs": "ETFs", "Mutual Funds": "Mutual Funds", "Crypto": "Crypto"}
    asset = amap[universe]
    rows = ([{"name": s, "symbol": s, "asset": "Crypto"} for s in (delta_symbol_options() or ["BTCUSD", "ETHUSD"])]
            if asset == "Crypto" else [{"name": n, "symbol": s, "asset": asset} for n, s in ASSET_MAP[asset].items()])
    rows = [r for r in rows if "-" not in r["symbol"] or asset != "Crypto"] if asset == "Crypto" else rows
    top = max(5, min(100, len(rows)))
    limit = c.slider("Maximum instruments", 5, top, min(40, top), key="sc_limit") if top > 5 else len(rows)
    rules = st.multiselect("All of these must be true", list(SCAN_RULES), default=["Price > EMA20", "RSI > 55"], key="sc_rules")
    if st.button("Scan universe", type="primary", key="sc_run", disabled=not rules):
        with loading("Scanning instruments"):
            with ThreadPoolExecutor(max_workers=8) as ex:
                futs = [ex.submit(scan_one, r, tf, rules) for r in rows[:limit]]
                res = [f.result() for f in as_completed(futs)]
        st.session_state["scan"] = dict(hits=[r for r in res if r], scanned=len(rows[:limit]))
    sc = st.session_state.get("scan")
    if sc:
        hits = sorted(sc["hits"], key=lambda r: -(r["RSI"] or 0))
        st.markdown(f"### {len(hits)} of {sc['scanned']} instruments matched")
        if hits:
            df = pd.DataFrame(hits)
            render_table(df.drop(columns=["asset"]), fmt={"Price": price_str, "Change": pct, "RSI": lambda v: f"{v:.1f}", "ADX": lambda v: f"{v:.1f}", "Rel. volume": lambda v: f"{v:.2f}x"},
                         tones={"Change": lambda v, r: tone_of(v), "Trend": lambda v, r: "up" if v == "Bullish" else "down"})
            opts = {f"{r['Name']} ({r['Symbol']})": r for r in hits}
            pick = st.selectbox("Open a result in the Analyser", list(opts), key="sc_open_pick")
            r = opts[pick]
            btn("Open in Analyser", key="sc_open", on_click=open_market, kwargs=dict(asset=r["asset"], symbol=r["Symbol"], workspace="Analyser"))
        else:
            st.info("Nothing matched, or data was unavailable. Loosen the conditions or try another universe.")


# ───────────────────────────── paper trading ──────────────────────────────
def live_prices(rows):
    """rows: iterable of (symbol, asset_class) -> {symbol: last}. Parallel and failure-tolerant."""
    pairs = tuple(sorted({(s, provider_of(a)) for s, a in rows}))
    if not pairs:
        return {}
    try:
        snaps = batch_snapshots(pairs)
    except Exception:
        return {}
    return {s: (snaps.get(s) or {}).get("last") for s, _ in pairs}


def render_paper():
    asset, symbol, prov = cur()
    st.caption("Simulation only. No broker credentials or live orders are used. Crypto results are in the contract's quote currency.")
    accs = q("SELECT * FROM paper_accounts ORDER BY created_at")
    amap = {a["name"]: a["id"] for a in accs}
    acc = one("SELECT * FROM paper_accounts WHERE id=?", (amap[st.selectbox("Virtual account", list(amap), key="pp_acc")],))
    opens = q("SELECT * FROM paper_trades WHERE account_id=? AND status='OPEN' ORDER BY opened_at DESC", (acc["id"],))
    prices = live_prices([(t["symbol"], t["asset_class"]) for t in opens])
    unreal = 0.0
    for t in opens:
        p = fnum(prices.get(t["symbol"]))
        if p:
            unreal += (p - t["entry"]) * t["quantity"] * (1 if t["side"] == "Long" else -1)
    realised = acc["cash"] - acc["initial_cash"]
    kpi_row([dict(label="Account value", value=money(acc["cash"] + unreal), sub=f"{pct((acc['cash'] + unreal) / acc['initial_cash'] * 100 - 100)} since start", tone=tone_of(acc["cash"] + unreal - acc["initial_cash"]), lead=True),
             dict(label="Realised P&L", value=money(realised), sub="Closed positions, after fees", tone=tone_of(realised)),
             dict(label="Unrealised P&L", value=money(unreal), sub="Open positions at latest price", tone=tone_of(unreal)),
             dict(label="Open positions", value=str(len(opens)), sub=f"Started with {money(acc['initial_cash'], dec=0)}")])
    with st.expander("Create another virtual account"):
        nn = st.text_input("Account name", key="pp_new_name")
        nc = st.number_input("Initial cash", 1000.0, 1e9, 100000.0, step=1000.0, key="pp_new_cash")
        if st.button("Create account", key="pp_new") and nn.strip():
            if nn.strip() in amap:
                st.error("An account with that name already exists.")
            else:
                run("INSERT INTO paper_accounts VALUES(?,?,?,?,?)", (uid(), nn.strip(), nc, nc, now()))
                st.rerun()
    st.markdown(f"### Open a position in {h(label_for(asset, symbol))}", unsafe_allow_html=True)
    with st.form("pp_open"):
        a, b, c, d = st.columns(4)
        side = a.selectbox("Side", ["Long", "Short"])
        qty = b.number_input("Quantity", 0.000001, 1e9, 1.0)
        entry = c.number_input("Entry price (0 = latest)", 0.0, 1e12, 0.0)
        fees = d.number_input("Fees", 0.0, 1e9, 0.0)
        note = st.text_input("Note")
        go_ = st.form_submit_button("Open simulated position", type="primary")
    if go_:
        px = entry or fnum(market_snapshot(symbol, prov).get("last"))
        if not px:
            st.error("No valid market price was returned. Enter an entry price manually.")
        else:
            run("INSERT INTO paper_trades VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)", (uid(), acc["id"], asset, symbol, side, qty, px, None, fees, now(), None, note, "OPEN"))
            st.success(f"Opened {side.lower()} {qty:g} {symbol} at {price_str(px)}.")
            st.rerun()
    if opens:
        st.markdown("### Open positions")
        df = pd.DataFrame([{"Symbol": t["symbol"], "Side": t["side"], "Qty": t["quantity"], "Entry": t["entry"], "Last": fnum(prices.get(t["symbol"])),
                            "P&L": ((fnum(prices.get(t["symbol"])) - t["entry"]) * t["quantity"] * (1 if t["side"] == "Long" else -1)) if fnum(prices.get(t["symbol"])) else None,
                            "Opened": t["opened_at"], "Note": t["note"] or ""} for t in opens])
        render_table(df, fmt={"Qty": lambda v: f"{v:g}", "Entry": price_str, "Last": price_str, "P&L": money}, tones={"P&L": lambda v, r: tone_of(v)})
        opts = {f"{t['symbol']} · {t['side']} · {t['quantity']:g} @ {price_str(t['entry'])}": t for t in opens}
        a, b, c = st.columns([3, 1, 1])
        label = a.selectbox("Close a position", list(opts), key="pp_close_pick")
        cp = b.number_input("Exit price (0 = latest)", 0.0, 1e12, 0.0, key="pp_close_px")
        cf = c.number_input("Exit fees", 0.0, 1e9, 0.0, key="pp_close_fee")
        if st.button("Close position", key="pp_close"):
            t = opts[label]
            px = cp or fnum(prices.get(t["symbol"])) or fnum(market_snapshot(t["symbol"], provider_of(t["asset_class"])).get("last"))
            if not px:
                st.error("No valid price was returned. Enter an exit price manually.")
            else:
                pnl = (px - t["entry"]) * t["quantity"] * (1 if t["side"] == "Long" else -1) - t["fees"] - cf
                run("UPDATE paper_trades SET exit=?,closed_at=?,status='CLOSED',fees=? WHERE id=?", (px, now(), t["fees"] + cf, t["id"]))
                run("UPDATE paper_accounts SET cash=cash+? WHERE id=?", (pnl, acc["id"]))
                st.success(f"Closed at {price_str(px)}. Simulated P&L after fees: {money(pnl)}.")
                st.rerun()
    closed = q("SELECT * FROM paper_trades WHERE account_id=? AND status='CLOSED' ORDER BY closed_at DESC", (acc["id"],))
    if closed:
        st.markdown("### Closed trades")
        df = pd.DataFrame([{"Symbol": t["symbol"], "Side": t["side"], "Qty": t["quantity"], "Entry": t["entry"], "Exit": t["exit"],
                            "P&L": (t["exit"] - t["entry"]) * t["quantity"] * (1 if t["side"] == "Long" else -1) - t["fees"], "Closed": t["closed_at"]} for t in closed])
        render_table(df, fmt={"Qty": lambda v: f"{v:g}", "Entry": price_str, "Exit": price_str, "P&L": money}, tones={"P&L": lambda v, r: tone_of(v)})


# ───────────────────────────── portfolio ──────────────────────────────────
def compute_holdings(tx):
    """Average-cost method. Returns (holdings dict, realised P&L). Rows must be oldest first."""
    hold, realised = {}, 0.0
    for t in tx:
        s = t["symbol"]
        hd = hold.setdefault(s, {"qty": 0.0, "cost": 0.0, "asset": t["asset_class"]})
        if t["side"] == "BUY":
            hd["qty"] += t["quantity"]
            hd["cost"] += t["quantity"] * t["price"] + t["fees"]
        else:
            avg = hd["cost"] / hd["qty"] if hd["qty"] > 1e-12 else 0.0
            sold = min(t["quantity"], hd["qty"])
            realised += sold * (t["price"] - avg) - t["fees"]
            hd["qty"] -= sold
            hd["cost"] -= avg * sold
    return {k: v for k, v in hold.items() if v["qty"] > 1e-9}, realised


def render_portfolio():
    asset, symbol, prov = cur()
    ports = q("SELECT * FROM portfolios ORDER BY name")
    pmap = {p["name"]: p["id"] for p in ports}
    p = one("SELECT * FROM portfolios WHERE id=?", (pmap[st.selectbox("Portfolio", list(pmap), key="pf_pick")],))
    tx = q("SELECT * FROM portfolio_tx WHERE portfolio_id=? ORDER BY ts, rowid", (p["id"],))
    hold, realised = compute_holdings(tx)
    prices = live_prices([(s, v["asset"]) for s, v in hold.items()])
    rows, mv_total, cost_total = [], 0.0, 0.0
    for s, v in hold.items():
        px = fnum(prices.get(s))
        mv = px * v["qty"] if px else None
        rows.append({"Symbol": s, "Qty": v["qty"], "Avg cost": v["cost"] / v["qty"], "Last": px, "Value": mv, "P&L": (mv - v["cost"]) if mv is not None else None,
                     "Return": ((mv / v["cost"] - 1) * 100) if mv is not None and v["cost"] else None})
        cost_total += v["cost"]
        mv_total += mv if mv is not None else v["cost"]
    unreal = mv_total - cost_total
    kpi_row([dict(label="Holdings value", value=money(mv_total), sub=f"Invested {money(cost_total, dec=0)}", lead=True),
             dict(label="Unrealised P&L", value=money(unreal), sub=pct(unreal / cost_total * 100) if cost_total else "", tone=tone_of(unreal)),
             dict(label="Realised P&L", value=money(realised), sub="Average-cost method, after fees", tone=tone_of(realised)),
             dict(label="Net cash flow", value=money(p["cash"]), sub="Sells minus buys and fees")])
    st.markdown("<div style='height:.6rem'></div>", unsafe_allow_html=True)
    if rows:
        a, b = st.columns([3, 2])
        with a:
            st.markdown("### Holdings")
            render_table(pd.DataFrame(rows), fmt={"Qty": lambda v: f"{v:g}", "Avg cost": price_str, "Last": price_str, "Value": money, "P&L": money, "Return": pct},
                         tones={"P&L": lambda v, r: tone_of(v), "Return": lambda v, r: tone_of(v)})
        with b:
            donut_chart([r["Symbol"] for r in rows], [max(r["Value"] or 0, 0.0) or hold[r["Symbol"]]["cost"] for r in rows], "pf_donut", "Allocation by value")
    st.markdown("### Record a transaction")
    with st.form("pf_tx"):
        a, b, c = st.columns(3)
        sym_in = a.text_input("Symbol", symbol)
        side = b.selectbox("Side", ["BUY", "SELL"])
        ac = c.selectbox("Asset class", ASSETS, index=ASSETS.index(asset) if asset in ASSETS else 0)
        a, b, c, d = st.columns(4)
        qty = a.number_input("Quantity", 0.000001, 1e9, 1.0)
        price = b.number_input("Price", 0.000001, 1e12, 1.0)
        fees = c.number_input("Fees", 0.0, 1e9, 0.0)
        note = d.text_input("Note")
        ok = st.form_submit_button("Record transaction", type="primary")
    if ok:
        sym_in = sym_in.strip()
        owned = hold.get(sym_in, {}).get("qty", 0.0)
        if not sym_in:
            st.error("Enter a symbol.")
        elif side == "SELL" and qty > owned + 1e-9:
            st.error(f"You hold {owned:g} of {sym_in}, so you cannot sell {qty:g}.")
        else:
            sign = 1 if side == "BUY" else -1
            run("INSERT INTO portfolio_tx VALUES(?,?,?,?,?,?,?,?,?,?)", (uid(), p["id"], sym_in, ac, side, qty, price, fees, now(), note))
            run("UPDATE portfolios SET cash=cash-? WHERE id=?", (sign * qty * price + fees, p["id"]))
            st.success("Transaction recorded.")
            st.rerun()
    if tx:
        with st.expander(f"Transaction history ({len(tx)})"):
            render_table(pd.DataFrame([{"Time": t["ts"], "Symbol": t["symbol"], "Side": t["side"], "Qty": t["quantity"], "Price": t["price"], "Fees": t["fees"], "Note": t["note"] or ""} for t in reversed(tx)]),
                         fmt={"Qty": lambda v: f"{v:g}", "Price": price_str, "Fees": lambda v: f"{v:,.2f}"}, tones={"Side": lambda v, r: "up" if v == "BUY" else "down"})
    with st.expander("New portfolio"):
        nn = st.text_input("Portfolio name", key="pf_new_name")
        if st.button("Create portfolio", key="pf_new") and nn.strip():
            if nn.strip() in pmap:
                st.error("A portfolio with that name already exists.")
            else:
                run("INSERT INTO portfolios VALUES(?,?,?,?)", (uid(), nn.strip(), 0.0, now()))
                st.rerun()


# ───────────────────────────── watchlist ──────────────────────────────────
def render_watchlist():
    asset, symbol, prov = cur()
    lists = q("SELECT * FROM watchlists ORDER BY name")
    lmap = {w["name"]: w["id"] for w in lists}
    wid = lmap[st.selectbox("Watchlist", list(lmap), key="wl_pick")]
    a, b, c = st.columns([2, 2, 1])
    sym_in = a.text_input("Add symbol", value=symbol, key="wl_sym")
    ac = b.selectbox("Asset class", ASSETS, index=ASSETS.index(asset) if asset in ASSETS else 0, key="wl_ac")
    c.markdown("<div style='height:1.85rem'></div>", unsafe_allow_html=True)
    if c.button("Add", key="wl_add") and sym_in.strip():
        run("INSERT OR REPLACE INTO watchlist_items VALUES(?,?,?,?)", (wid, sym_in.strip(), ac, 0))
        st.rerun()
    items = q("SELECT * FROM watchlist_items WHERE watchlist_id=? ORDER BY position, symbol", (wid,))
    if items:
        with loading("Refreshing watchlist"):
            snaps = batch_snapshots(tuple(sorted({(i["symbol"], provider_of(i["asset_class"])) for i in items})))
        df = pd.DataFrame([{"Name": label_for(i["asset_class"], i["symbol"]), "Symbol": i["symbol"], "Class": i["asset_class"],
                            "Last": (snaps.get(i["symbol"]) or {}).get("last"), "Change": (snaps.get(i["symbol"]) or {}).get("change")} for i in items])
        render_table(df, fmt={"Last": price_str, "Change": pct}, tones={"Change": lambda v, r: tone_of(v)})
        opts = {f"{i['symbol']} ({i['asset_class']})": i for i in items}
        d1, d2, d3 = st.columns([3, 1, 1])
        pick = d1.selectbox("Selected", list(opts), key="wl_sel")
        it = opts[pick]
        d2.markdown("<div style='height:1.85rem'></div>", unsafe_allow_html=True)
        d3.markdown("<div style='height:1.85rem'></div>", unsafe_allow_html=True)
        with d2:
            btn("Open", key="wl_open", on_click=open_market, kwargs=dict(asset=it["asset_class"], symbol=it["symbol"], workspace="Analyser"))
        if d3.button("Remove", key="wl_rm"):
            run("DELETE FROM watchlist_items WHERE watchlist_id=? AND symbol=?", (wid, it["symbol"]))
            st.rerun()
    else:
        st.info("This watchlist is empty. Add a symbol above to start tracking it.")
    with st.expander("New watchlist"):
        nn = st.text_input("Watchlist name", key="wl_new_name")
        if st.button("Create watchlist", key="wl_new") and nn.strip():
            if nn.strip() in lmap:
                st.error("A watchlist with that name already exists.")
            else:
                run("INSERT INTO watchlists VALUES(?,?,?)", (uid(), nn.strip(), now()))
                st.rerun()


# ───────────────────────────── data center ────────────────────────────────
def validate_ohlcv(df):
    d = df.copy()
    d.columns = [str(c).lower() for c in d.columns]
    rep = {"rows": len(d), "columns": list(d.columns), "missing": {}, "duplicate_timestamps": 0, "invalid_ohlc": 0}
    for c in OHLCV:
        if c in d:
            rep["missing"][c] = int(pd.to_numeric(d[c], errors="coerce").isna().sum())
    if isinstance(d.index, pd.DatetimeIndex):
        rep["duplicate_timestamps"] = int(d.index.duplicated().sum())
    if all(c in d for c in ("open", "high", "low", "close")):
        o, hi, lo, cl = (pd.to_numeric(d[k], errors="coerce") for k in ("open", "high", "low", "close"))
        rep["invalid_ohlc"] = int(((hi < pd.concat([o, cl], axis=1).max(axis=1)) | (lo > pd.concat([o, cl], axis=1).min(axis=1)) | (hi < lo)).sum())
    return rep


def render_data_center():
    st.caption("Upload OHLCV data, check its quality and reuse it in the Backtester.")
    up = st.file_uploader("CSV dataset", type=["csv"], key="dc_up")
    if up:
        try:
            df = pd.read_csv(up)
        except Exception as e:
            st.error(f"Could not read that file as CSV: {e}")
            return
        wide(st.dataframe, df.head(100))
        tc = st.selectbox("Timestamp column", ["<none>"] + list(df.columns), key="dc_tc")
        if tc != "<none>":
            df = df.assign(_ts=pd.to_datetime(df[tc], errors="coerce", utc=True)).dropna(subset=["_ts"]).set_index("_ts").sort_index().drop(columns=[tc])
        rep = validate_ohlcv(df)
        bad = rep["invalid_ohlc"] + rep["duplicate_timestamps"] + sum(rep["missing"].values())
        kpi_row([dict(label="Rows", value=f"{rep['rows']:,}"), dict(label="Missing values", value=str(sum(rep["missing"].values())), tone="down" if sum(rep["missing"].values()) else "flat"),
                 dict(label="Duplicate timestamps", value=str(rep["duplicate_timestamps"])), dict(label="Invalid OHLC rows", value=str(rep["invalid_ohlc"]), tone="down" if rep["invalid_ohlc"] else "flat")])
        if bad:
            st.warning("Quality issues were found. Saving will keep the file as uploaded; the Backtester repairs highs and lows and drops rows without a close.")
        if tc == "<none>":
            st.info("Choose the timestamp column to make this dataset usable in the Backtester.")
        if st.button("Save dataset locally", type="primary", disabled=tc == "<none>", key="dc_save"):
            d = Path("ooyt_datasets")
            d.mkdir(exist_ok=True)
            fn = d / (Path(up.name).stem + "_" + datetime.now().strftime("%Y%m%d%H%M%S") + ".csv")
            df.to_csv(fn)
            run("INSERT INTO datasets VALUES(?,?,?,?,?,?,?)", (uid(), up.name, str(fn), len(df), json.dumps(list(df.columns)), json.dumps(rep), now()))
            st.success(f"Saved {fn}")
    rows = q("SELECT * FROM datasets ORDER BY created_at DESC")
    if rows:
        st.markdown("### Saved datasets")
        render_table(pd.DataFrame([{"Name": r["name"], "Rows": r["rows"], "Saved": r["created_at"], "Path": r["path"]} for r in rows]), fmt={"Rows": lambda v: f"{v:,}"})
        opts = {f"{r['name']} · {r['created_at']}": r for r in rows}
        c1, c2 = st.columns([3, 1])
        pick = c1.selectbox("Remove a dataset", list(opts), key="dc_del_pick")
        if c2.button("Delete", key="dc_del"):
            r = opts[pick]
            try:
                Path(r["path"]).unlink(missing_ok=True)
            except OSError:
                pass
            run("DELETE FROM datasets WHERE id=?", (r["id"],))
            st.rerun()


# ───────────────────────────── journal ────────────────────────────────────
def render_journal():
    asset, symbol, _ = cur()
    with st.form("jr_form"):
        sym = st.text_input("Symbol", symbol)
        a, b = st.columns(2)
        entry = a.text_area("Entry reason")
        exit_reason = b.text_area("Exit reason")
        notes = st.text_area("Notes and lessons")
        tags = st.text_input("Tags (comma separated)")
        save = st.form_submit_button("Save entry", type="primary")
    if save:
        if not (entry.strip() or exit_reason.strip() or notes.strip()):
            st.error("Write something in at least one of the text boxes first.")
        else:
            run("INSERT INTO journal VALUES(?,?,?,?,?,?,?,?,?)", (uid(), None, sym, asset, entry, exit_reason, notes, tags, now()))
            st.success("Entry saved.")
            st.rerun()
    rows = q("SELECT * FROM journal ORDER BY ts DESC")
    if rows:
        term = st.text_input("Filter entries", key="jr_filter", placeholder="Search symbol, tag or text")
        shown = [r for r in rows if not term or term.lower() in " ".join(str(r[k] or "") for k in ("symbol", "tags", "entry_reason", "exit_reason", "notes")).lower()]
        for r in shown[:60]:
            with st.expander(f"{r['ts']}  ·  {r['symbol']}  ·  {r['tags'] or 'untagged'}"):
                for lab, k in (("Entry reason", "entry_reason"), ("Exit reason", "exit_reason"), ("Notes", "notes")):
                    if r[k]:
                        st.markdown(f"**{lab}**  \n{h(r[k])}", unsafe_allow_html=True)
                if st.button("Delete entry", key=f"jr_del_{r['id']}"):
                    run("DELETE FROM journal WHERE id=?", (r["id"],))
                    st.rerun()
    else:
        st.info("Your journal is empty. Record why you entered and exited so you can review your decisions later.")


# ───────────────────────────── alerts ─────────────────────────────────────
def render_alerts():
    asset, symbol, _ = cur()
    st.caption("Alerts are checked whenever this page loads or you press Refresh. They are not background notifications.")
    with st.form("al_form"):
        a, b = st.columns(2)
        nm = a.text_input("Alert name")
        sym = b.text_input("Symbol", symbol)
        a, b, c = st.columns(3)
        ac = a.selectbox("Asset class", ASSETS, index=ASSETS.index(asset) if asset in ASSETS else 0)
        kind = b.selectbox("Condition", ["Price above", "Price below"])
        val = c.number_input("Threshold", 0.0, 1e12, 0.0)
        save = st.form_submit_button("Create alert", type="primary")
    if save:
        if not nm.strip() or not sym.strip() or val <= 0:
            st.error("Give the alert a name, a symbol and a threshold above zero.")
        else:
            run("INSERT INTO alerts VALUES(?,?,?,?,?,?,?,?)", (uid(), nm.strip(), ac, sym.strip(), kind, val, 1, None))
            st.success("Alert created.")
    rows = q("SELECT * FROM alerts ORDER BY name")
    if not rows:
        st.info("No alerts yet. Create one above.")
        return
    prices = live_prices([(a["symbol"], a["asset_class"]) for a in rows if a["active"]])
    table = []
    for a in rows:
        px = fnum(prices.get(a["symbol"])) if a["active"] else None
        hit = px is not None and ((a["kind"] == "Price above" and px > a["value"]) or (a["kind"] == "Price below" and px < a["value"]))
        if hit:
            st.warning(f"Triggered: {a['name']} — {a['symbol']} is {price_str(px)} ({a['kind'].lower()} {price_str(a['value'])})")
            run("UPDATE alerts SET last_triggered=? WHERE id=?", (now(), a["id"]))
        table.append({"Name": a["name"], "Symbol": a["symbol"], "Condition": f"{a['kind']} {price_str(a['value'])}", "Last": px, "Status": "Triggered" if hit else ("Active" if a["active"] else "Paused"),
                      "Last triggered": a["last_triggered"] or "—"})
    render_table(pd.DataFrame(table), fmt={"Last": price_str}, tones={"Status": lambda v, r: "down" if v == "Triggered" else ("up" if v == "Active" else "flat")})
    opts = {f"{a['name']} ({a['symbol']})": a for a in rows}
    c1, c2, c3 = st.columns([3, 1, 1])
    pick = opts[c1.selectbox("Manage alert", list(opts), key="al_pick")]
    c2.markdown("<div style='height:1.85rem'></div>", unsafe_allow_html=True)
    c3.markdown("<div style='height:1.85rem'></div>", unsafe_allow_html=True)
    if c2.button("Pause" if pick["active"] else "Resume", key="al_toggle"):
        run("UPDATE alerts SET active=? WHERE id=?", (0 if pick["active"] else 1, pick["id"]))
        st.rerun()
    if c3.button("Delete", key="al_del"):
        run("DELETE FROM alerts WHERE id=?", (pick["id"],))
        st.rerun()


# ───────────────────────────── analytics ──────────────────────────────────
def render_analytics():
    bt = st.session_state.get("last_backtest_metrics")
    trades = q("SELECT * FROM paper_trades")
    closed = [t for t in trades if t["status"] == "CLOSED" and t["exit"] is not None]
    if closed:
        d = pd.DataFrame([dict(t) for t in closed])
        d["pnl"] = (d["exit"] - d["entry"]) * d["quantity"] * d["side"].map({"Long": 1, "Short": -1}) - d["fees"]
        d["closed_at"] = pd.to_datetime(d["closed_at"], errors="coerce")
        d = d.sort_values("closed_at")
        wins = int((d["pnl"] > 0).sum())
        kpi_row([dict(label="Paper trades", value=str(len(trades)), sub=f"{len(closed)} closed", lead=True),
                 dict(label="Net paper P&L", value=money(d["pnl"].sum()), tone=tone_of(d["pnl"].sum())),
                 dict(label="Win rate", value=f"{wins / len(d) * 100:.1f}%", sub=f"{wins} of {len(d)} closed"),
                 dict(label="Average trade", value=money(d["pnl"].mean()), tone=tone_of(d["pnl"].mean()))])
        st.markdown("### Cumulative paper P&L")
        st.line_chart(d.set_index("closed_at")["pnl"].cumsum(), height=280)
        monthly = d.groupby(d["closed_at"].dt.to_period("M"))["pnl"].agg(["sum", "count"]).reset_index()
        monthly.columns = ["Month", "P&L", "Trades"]
        monthly["Month"] = monthly["Month"].astype(str)
        st.markdown("### By month")
        render_table(monthly.iloc[::-1], fmt={"P&L": money}, tones={"P&L": lambda v, r: tone_of(v)})
    else:
        st.info("No closed paper trades yet. Close a simulated position in Paper Trading to see performance here.")
    if bt:
        st.markdown("### Latest back-test")
        kpi_row([dict(label="Return", value=pct(bt["return_pct"]), sub=f"Buy and hold {pct(bt['buy_hold_pct'])}", tone=tone_of(bt["return_pct"]), lead=True),
                 dict(label="Max drawdown", value=f"{bt['max_drawdown_pct']:.2f}%", tone="down"),
                 dict(label="Sharpe", value=f"{bt['sharpe']:.2f}"), dict(label="Trades", value=str(bt["total_trades"]), sub=f"Win rate {bt['win_rate_pct']:.1f}%")])
    st.caption("Back-tests, paper trades and portfolio records are kept separate. Results depend on the records and market data available.")


# ───────────────────────────── learn ──────────────────────────────────────
LESSONS = {
    "SMA and EMA": "A simple moving average is the plain average of the last N closes. An exponential moving average weights recent closes more, so it turns sooner. Neither predicts prices; both describe what has already happened.",
    "VWAP": "Volume-weighted average price shows where most of the traded volume changed hands. It is most meaningful on intraday charts, where it restarts every session.",
    "RSI": "RSI ranges from 0 to 100 and compares recent gains with recent losses. Readings above 70 or below 30 are common reference zones, not guaranteed reversal points.",
    "MACD": "MACD is the difference between a fast and a slow EMA, with a signal line smoothing it. Crossovers mark changes in momentum and can whipsaw in sideways markets.",
    "ATR": "Average true range measures how far price typically moves in one bar, including gaps. It says nothing about direction, and is often used to set stop distance and position size.",
    "Bollinger Bands": "Bands sit two standard deviations either side of a 20-bar average. Touching a band is common in both trends and ranges, so context decides what it means.",
    "Supertrend": "Supertrend places an ATR-based line under price in uptrends and above it in downtrends. It follows trends well and flips repeatedly in sideways markets.",
    "ADX": "ADX measures how strong a trend is on a 0–100 scale, regardless of direction. Above about 25 is usually read as a trending market.",
    "Stochastic": "Stochastic shows where the close sits within its recent high-low range. It can stay overbought or oversold for long stretches in strong trends.",
    "Volume and relative volume": "Volume is traded quantity. Relative volume divides it by its 20-bar average, so 2x means twice the usual activity.",
    "Support and resistance": "Support and resistance are price areas where the market previously paused or reversed. Treat them as zones, not exact lines, and expect them to fail sometimes.",
    "Backtesting": "A back-test applies fixed rules to history. Look-ahead, unrealistic fills, missing data, fees and slippage can all change results, so the assumptions matter as much as the answer. Good past results do not promise future ones.",
    "Risk management": "Size positions from the loss you can accept, not from how confident you feel. A stop-loss does not cap losses when price gaps or liquidity disappears.",
}


def render_learn():
    for title, text in LESSONS.items():
        with st.expander(title):
            st.write(text)
    st.info("This section is educational. Historical relationships do not guarantee future performance.")


# ───────────────────────────── settings ───────────────────────────────────
def ping(name, fn):
    try:
        t0 = datetime.now()
        r = fn()
        ms = (datetime.now() - t0).total_seconds() * 1000
        return {"Check": name, "Result": "Working", "Detail": f"{ms:,.0f} ms" + (f" · {r}" if r else "")}
    except Exception as e:
        return {"Check": name, "Result": "Failed", "Detail": fetch_error_message(e)}


def render_settings():
    st.markdown(f"OOYT **v{APP_VERSION}** · database `{DB_PATH.resolve()}`")
    a, b = st.columns(2)
    if a.button("Clear market-data cache", key="st_clear"):
        st.cache_data.clear()
        st.success("Cache cleared.")
    if DB_PATH.exists():
        b.download_button("Download database backup", DB_PATH.read_bytes(), file_name="ooyt_data.sqlite3", mime="application/octet-stream")
    st.markdown("### System check")
    pk = [("streamlit", st.__version__), ("pandas", pd.__version__), ("numpy", np.__version__), ("plotly", "installed" if go else None), ("yfinance", "installed" if yf else None)]
    render_table(pd.DataFrame([{"Package": n, "Status": v or "Missing. Run: pip install " + n} for n, v in pk]), tones={"Status": lambda v, r: "down" if v.startswith("Missing") else "up"})
    if st.button("Test data providers", key="st_ping"):
        rows = [ping("Yahoo Finance (NIFTY 50)", lambda: f"last {price_str(snapshot_raw('^NSEI', 'yahoo').get('last'))}"),
                ping("Delta Exchange (BTCUSD)", lambda: f"last {price_str(snapshot_raw('BTCUSD', 'crypto').get('last'))}")]
        render_table(pd.DataFrame(rows), tones={"Result": lambda v, r: "up" if v == "Working" else "down"})
    with st.expander("Optional: make Streamlit's own widgets match the theme"):
        st.caption("Save this as .streamlit/config.toml next to the script, then restart.")
        st.code(THEME_TOML, language="toml")
    st.markdown("### What OOYT does and does not do")
    st.markdown("- Indian stock, index, ETF and mutual-fund catalogue with universal search and custom Yahoo symbols\n"
                "- Candlestick charts with 10+ indicators, pivots and swing levels\n"
                "- Beginner strategy library and an AND/OR rule builder with versioned saves\n"
                "- Back-tester with next-bar fills, intrabar stops, fees, slippage, Sharpe, Sortino and Calmar\n"
                "- Paper trading, portfolio with average cost, watchlists, alerts, journal, data center\n"
                "- Not included: live broker orders, and option-contract history (premiums are never fabricated)")


# ───────────────────────────── shell + routing ────────────────────────────
ROUTES = {"Dashboard": render_dashboard, "Analyser": render_analyser, "Strategy Builder": render_strategy_builder, "Backtester": render_backtester,
          "Scanner": render_scanner, "Paper Trading": render_paper, "Portfolio": render_portfolio, "Watchlist": render_watchlist,
          "Data Center": render_data_center, "Trading Journal": render_journal, "Alerts": render_alerts, "Analytics": render_analytics,
          "Learn": render_learn, "Settings": render_settings}


def footer():
    st.markdown(f"<div class='foot'>OOYT v{APP_VERSION} · Research and paper trading only · No real broker orders · Data coverage and freshness vary by provider.</div>",
                unsafe_allow_html=True)


def refresh_all():
    st.cache_data.clear()


def init_state():
    ss = st.session_state
    for k, v in (("active", False), ("asset_class", "Share Investment"), ("symbol", default_symbol("Share Investment")),
                 ("workspace", "Dashboard"), ("nav", "Dashboard"), ("mode_label", None), ("asset_picker", "Share Investment")):
        ss.setdefault(k, v)
    if ss["nav"] not in WORKSPACES:
        ss["nav"] = "Dashboard"
    if ss["asset_picker"] not in ASSETS or ss["asset_picker"] != ss["asset_class"]:
        ss["asset_picker"] = ss["asset_class"] if ss["asset_class"] in ASSETS else "Share Investment"


def _symbol_changed(labels_key, opts_key):
    ss = st.session_state
    ss["symbol"] = ss[opts_key][ss[labels_key]]


def shell():
    ss = st.session_state
    masthead()
    tape()
    c1, c2, c3, c4 = st.columns([2, 4, 1, 1])
    c1.selectbox("Market", ASSETS, key="asset_picker", on_change=_asset_changed)
    asset = ss["asset_class"]
    opts = sym_options(asset, ss["symbol"])
    skey, okey = f"sym_{asset}", f"opts_{asset}"
    ss[okey] = opts
    want = next((lbl for lbl, s in opts.items() if s == ss["symbol"]), None)
    if want is None:
        want = next(iter(opts))
        ss["symbol"] = opts[want]
    ss[skey] = want
    c2.selectbox("Instrument", list(opts), key=skey, on_change=_symbol_changed, args=(skey, okey),
                 format_func=lambda lbl: lbl if asset == "Crypto" else f"{lbl}   ({opts[lbl]})")
    c3.markdown("<div style='height:1.85rem'></div>", unsafe_allow_html=True)
    c4.markdown("<div style='height:1.85rem'></div>", unsafe_allow_html=True)
    with c3:
        btn("Home", key="go_home", on_click=go_home)
    with c4:
        if btn("Refresh", key="do_refresh"):
            refresh_all()
            st.rerun()
    with st.expander("Search all instruments"):
        term = search_box("shell", compact=True)
        search_results(term, "shell")
    st.radio("Workspace", WORKSPACES, key="nav", horizontal=True, label_visibility="collapsed")
    ss["workspace"] = ss["nav"]
    st.caption(f"{ss['nav']} · Source: {source_name(asset)} · Public data may be delayed or limited · No live orders")
    try:
        ROUTES[ss["nav"]]()
    except Exception as e:  # last-resort guard so one bad widget never blanks the whole app
        st.error(f"Something went wrong in {ss['nav']}: {type(e).__name__}: {e}")
    footer()


def main():
    st.set_page_config(page_title="OOYT", page_icon="◆", layout="wide", initial_sidebar_state="collapsed")
    st.markdown(f"<style>{CSS.strip()}</style>", unsafe_allow_html=True)
    if "db_ready" not in st.session_state:
        init_db()
        st.session_state["db_ready"] = True
    init_state()
    if st.session_state["active"]:
        shell()
    else:
        home()
        footer()


if not os.environ.get("OOYT_NO_AUTORUN"):
    main()

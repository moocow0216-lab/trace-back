"""每天由 GitHub Actions 執行：從 SoSoValue 抓美國比特幣現貨 ETF 流入，存成 data/etf.json。
金鑰放在 GitHub 的 Secrets（名稱 SOSOVALUE_API_KEY），不會出現在程式碼裡。"""
import datetime, json, os, sys, time, urllib.parse, urllib.request

BASE = "https://openapi.sosovalue.com/openapi/v1"
KEY = os.environ.get("SOSOVALUE_API_KEY", "").strip()
OUT = os.path.join(os.path.dirname(__file__), "..", "data", "etf.json")

if not KEY:
    sys.exit("找不到 SOSOVALUE_API_KEY，請到 Settings → Secrets and variables → Actions 新增。")


def get(path, params=None):
    url = BASE + path + ("?" + urllib.parse.urlencode(params) if params else "")
    req = urllib.request.Request(url, headers={"x-soso-api-key": KEY, "Accept": "application/json", "User-Agent": "infinite-void-updater"})
    with urllib.request.urlopen(req, timeout=30) as r:
        payload = json.load(r)
    if isinstance(payload, dict) and "code" in payload:
        if payload["code"] != 0:
            raise RuntimeError(f"SoSoValue 回傳錯誤：{payload.get('message')}")
        return payload.get("data")
    return payload


def as_date(v):
    if isinstance(v, (int, float)):
        return datetime.datetime.fromtimestamp(v / 1000 if v > 1e11 else v, datetime.timezone.utc).date().isoformat()
    return str(v)[:10]


def num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


rows = get("/etfs/summary-history", {"symbol": "BTC", "country_code": "US", "limit": 60}) or []
daily = sorted(({
    "date": as_date(r.get("date")),
    "net": num(r.get("total_net_inflow")),
    "traded": num(r.get("total_value_traded")),
    "assets": num(r.get("total_net_assets")),
    "cum": num(r.get("cum_net_inflow")),
} for r in rows if r.get("date") is not None), key=lambda x: x["date"])
daily = [d for d in daily if d["net"] is not None]
if not daily:
    sys.exit("SoSoValue 沒有回傳每日資料，這次先不更新。")

# 各檔 ETF 最新一天（免費方案每分鐘 20 次，所以每次間隔 3.5 秒）
funds = {"date": daily[-1]["date"], "rows": []}
try:
    time.sleep(3.5)
    tickers = get("/etfs", {"symbol": "BTC", "country_code": "US"}) or []
    for t in tickers[:15]:
        tk = t.get("ticker") if isinstance(t, dict) else t
        if not tk:
            continue
        time.sleep(3.5)
        hist = get(f"/etfs/{urllib.parse.quote(tk)}/history", {"limit": 3}) or []
        for h in hist:
            if as_date(h.get("date")) == funds["date"] and num(h.get("net_inflow")) is not None:
                funds["rows"].append({"ticker": tk, "net": num(h.get("net_inflow"))})
                break
except Exception as e:  # 各檔明細失敗不影響總額
    print("各檔明細抓取失敗：", e)

new = {"source": "SoSoValue", "daily": daily, "funds": funds if funds["rows"] else None}
try:
    with open(OUT, encoding="utf-8") as f:
        old = json.load(f)
except Exception:
    old = {}
if {k: old.get(k) for k in ("source", "daily", "funds")} == new:
    print("資料沒有變動，不需要提交。")
    sys.exit(0)

new["updated"] = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
with open(OUT, "w", encoding="utf-8") as f:
    json.dump(new, f, ensure_ascii=False, indent=1)
print(f"已更新：最新一日 {daily[-1]['date']} 淨流入 {daily[-1]['net']:,.0f} 美元，共 {len(daily)} 天。")

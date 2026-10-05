"""由 GitHub Actions 定時執行，抓美國比特幣現貨 ETF 每日流入，存成 data/etf.json。

資料來源（自動選擇）：
1. 有設定 SOSOVALUE_API_KEY（GitHub Secrets）就用 SoSoValue API。
2. 沒有金鑰、或 SoSoValue 失敗，就改抓 Farside Investors 的公開表格（不需要金鑰）。
"""
import datetime, html.parser, json, os, sys, time, urllib.parse, urllib.request

OUT = os.path.join(os.path.dirname(__file__), "..", "data", "etf.json")
KEY = os.environ.get("SOSOVALUE_API_KEY", "").strip()
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36"


def num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


# ---------- SoSoValue ----------
def soso_get(path, params=None):
    url = "https://openapi.sosovalue.com/openapi/v1" + path + ("?" + urllib.parse.urlencode(params) if params else "")
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


def from_sosovalue():
    rows = soso_get("/etfs/summary-history", {"symbol": "BTC", "country_code": "US", "limit": 60}) or []
    daily = sorted(({"date": as_date(r.get("date")), "net": num(r.get("total_net_inflow")), "traded": num(r.get("total_value_traded")),
                     "assets": num(r.get("total_net_assets")), "cum": num(r.get("cum_net_inflow"))}
                    for r in rows if r.get("date") is not None), key=lambda x: x["date"])
    daily = [d for d in daily if d["net"] is not None]
    if not daily:
        raise RuntimeError("SoSoValue 沒有回傳每日資料")
    funds = {"date": daily[-1]["date"], "rows": []}
    try:
        time.sleep(3.5)
        for t in (soso_get("/etfs", {"symbol": "BTC", "country_code": "US"}) or [])[:15]:
            tk = t.get("ticker") if isinstance(t, dict) else t
            if not tk:
                continue
            time.sleep(3.5)
            for h in soso_get(f"/etfs/{urllib.parse.quote(tk)}/history", {"limit": 3}) or []:
                if as_date(h.get("date")) == funds["date"] and num(h.get("net_inflow")) is not None:
                    funds["rows"].append({"ticker": tk, "net": num(h.get("net_inflow"))})
                    break
    except Exception as e:
        print("各檔明細抓取失敗：", e)
    return {"source": "SoSoValue", "daily": daily, "funds": funds if funds["rows"] else None}


# ---------- Farside（不需要金鑰） ----------
class Tables(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.tables, self.row, self.cell, self.in_cell = [], None, "", False

    def handle_starttag(self, tag, attrs):
        if tag == "table":
            self.tables.append([])
        elif tag == "tr" and self.tables:
            self.row = []
        elif tag in ("td", "th") and self.row is not None:
            self.in_cell, self.cell = True, ""

    def handle_endtag(self, tag):
        if tag in ("td", "th") and self.in_cell:
            self.row.append(" ".join(self.cell.split()))
            self.in_cell = False
        elif tag == "tr" and self.row is not None and self.tables:
            if self.row:
                self.tables[-1].append(self.row)
            self.row = None

    def handle_data(self, data):
        if self.in_cell:
            self.cell += data


def farside_num(s):
    s = s.replace(",", "").strip()
    if s in ("", "-", "—"):
        return None
    neg = s.startswith("(") and s.endswith(")")
    v = num(s.strip("()"))
    return None if v is None else (-v if neg else v)


def from_farside():
    req = urllib.request.Request("https://farside.co.uk/btc/", headers={"User-Agent": UA, "Accept": "text/html", "Accept-Language": "en-US,en;q=0.9"})
    with urllib.request.urlopen(req, timeout=30) as r:
        page = r.read().decode("utf-8", "replace")
    p = Tables()
    p.feed(page)
    for table in p.tables:
        head_i = next((i for i, row in enumerate(table) if row and row[0].strip().lower() == "date" and any(c.strip().lower() == "total" for c in row)), None)
        if head_i is None:
            continue
        head = table[head_i]
        tot_i = [c.strip().lower() for c in head].index("total")
        daily, last_row = [], None
        for row in table[head_i + 1:]:
            if len(row) <= tot_i:
                continue
            try:
                d = datetime.datetime.strptime(row[0].strip(), "%d %b %Y").date().isoformat()
            except ValueError:
                continue                       # 跳過 Total／Average／Maximum 這類統計列
            tot = farside_num(row[tot_i])
            if tot is None:
                continue
            daily.append({"date": d, "net": tot * 1e6})
            last_row = (d, row)
        if not daily:
            continue
        daily.sort(key=lambda x: x["date"])
        daily = daily[-60:]
        funds = None
        if last_row:
            d, row = last_row
            rows = [{"ticker": head[i].strip(), "net": farside_num(row[i]) * 1e6} for i in range(1, tot_i) if farside_num(row[i]) is not None]
            funds = {"date": d, "rows": rows} if rows else None
        return {"source": "Farside Investors", "daily": daily, "funds": funds}
    raise RuntimeError("Farside 頁面裡找不到 ETF 流入表格")


# ---------- 主程式 ----------
new, errors = None, []
if KEY:
    try:
        new = from_sosovalue()
    except Exception as e:
        errors.append(f"SoSoValue：{e}")
if new is None:
    try:
        new = from_farside()
    except Exception as e:
        errors.append(f"Farside：{e}")
if new is None:
    sys.exit("兩個資料來源都失敗，這次不更新。\n" + "\n".join(errors))
for e in errors:
    print("提醒：", e)

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
print(f"已更新（{new['source']}）：最新一日 {new['daily'][-1]['date']} 淨流入 {new['daily'][-1]['net']:,.0f} 美元，共 {len(new['daily'])} 天。")

"""即時加密貨幣新聞收集器（由 GitHub Actions 每分鐘左右執行一次）。

指定優先來源：CoinDesk、金十數據、區塊客、CoinGecko
其他來源：Cointelegraph、Decrypt、The Block、Bitcoin.com、動區動趨、鏈新聞、Google 新聞（中文）
英文與簡體中文會自動翻成繁體中文。新聞會累積保留（最多 300 則），最新的排最前面。
用法：python update_news.py 輸出檔 [上一版檔案]
"""
import datetime, email.utils, hashlib, html, json, os, re, sys, time, urllib.parse, urllib.request
import xml.etree.ElementTree as ET

OUT = sys.argv[1] if len(sys.argv) > 1 else "news.json"
PREV = sys.argv[2] if len(sys.argv) > 2 else OUT
KEEP = 300
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36"
TPE = datetime.timezone(datetime.timedelta(hours=8))


def fetch(url, headers=None, timeout=20):
    h = {"User-Agent": UA, "Accept": "*/*", "Accept-Language": "zh-TW,zh;q=0.9,en;q=0.8"}
    h.update(headers or {})
    with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=timeout) as r:
        return r.read().decode("utf-8", "replace")


def strip(s):
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


def to_ms(s):
    if not s:
        return None
    s = s.strip()
    try:
        return int(email.utils.parsedate_to_datetime(s).timestamp() * 1000)
    except Exception:
        pass
    try:
        d = datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))
        if d.tzinfo is None:
            d = d.replace(tzinfo=datetime.timezone.utc)
        return int(d.timestamp() * 1000)
    except Exception:
        return None


def item(title, link, ts, src, lang, summary="", pri=False):
    title = strip(title)
    if not title:
        return None
    key = re.sub(r"\W+", "", title.lower())[:80]
    return {"id": hashlib.sha1(key.encode()).hexdigest()[:14], "te": title, "se": strip(summary)[:300], "u": link or "",
            "ts": ts or int(time.time() * 1000), "src": src, "lang": lang, "pri": pri}


def rss(url, src, lang, pri=False, google=False):
    text = fetch(url).lstrip("\ufeff")
    root = ET.fromstring(text)
    out = []
    atom = "{http://www.w3.org/2005/Atom}"
    nodes = list(root.iter("item")) + list(root.iter(atom + "entry"))
    for n in nodes[:40]:
        g = lambda tag: (n.findtext(tag) or n.findtext(atom + tag) or "")
        title, s = g("title"), src
        link = g("link")
        if not link:
            le = n.find(atom + "link")
            link = le.get("href") if le is not None else ""
        if google:
            se = n.find("source")
            m = re.match(r"^(.*)\s+-\s+([^-]{1,40})$", strip(title))
            if se is not None and se.text:
                s = strip(se.text)
            elif m:
                s = m.group(2)
            if m:
                title = m.group(1)
        ts = to_ms(g("pubDate") or n.findtext("{http://purl.org/dc/elements/1.1/}date") or g("published") or g("updated"))
        summ = "" if google else (g("description") or g("summary"))
        it = item(title, link.strip(), ts, s, lang, summ, pri)
        if it:
            out.append(it)
    return out


def gnews(q, src=None, pri=False):
    url = "https://news.google.com/rss/search?q=" + urllib.parse.quote(q) + "&hl=zh-TW&gl=TW&ceid=TW:zh-Hant"
    items = rss(url, src or "Google 新聞", "zh-TW", pri, google=True)
    if src:  # 指定網站的搜尋結果，來源統一顯示成那個網站
        for it in items:
            it["src"] = src
    return items


CRYPTO = re.compile(r"比特币|比特幣|以太坊|加密货币|加密貨幣|加密资产|数字货币|数字资产|稳定币|穩定幣|币安|幣安|Binance|Coinbase|OKX|Bitget|"
                    r"\bBTC\b|\bETH\b|\bSOL\b|\bXRP\b|\bBNB\b|\bDOGE\b|狗狗币|Solana|USDT|USDC|Tether|泰达币|区块链|區塊鏈|链上|鏈上|"
                    r"Web3|DeFi|NFT|MicroStrategy|Strategy公司|灰度|Grayscale|Circle|Hyperliquid|山寨币|代币|代幣|挖矿|矿企|减半", re.I)


def jin10():
    raw = fetch("https://flash-api.jin10.com/get_flash_list?channel=-8200&vip=1",
                {"x-app-id": "bVBF4FyRTn5NJF5n", "x-version": "1.0.0", "Origin": "https://www.jin10.com", "Referer": "https://www.jin10.com/"})
    data = json.loads(raw).get("data") or []
    out = []
    for d in data:
        if d.get("type") == 1:
            continue
        content = strip((d.get("data") or {}).get("content") or "")
        if not content or not CRYPTO.search(content):
            continue
        m = re.match(r"^【(.*?)】(.*)$", content)
        title, summ = (m.group(1), m.group(2)) if m else (content[:60] + ("…" if len(content) > 60 else ""), content if len(content) > 60 else "")
        ts = None
        try:
            ts = int(datetime.datetime.strptime(d.get("time", ""), "%Y-%m-%d %H:%M:%S").replace(tzinfo=TPE).timestamp() * 1000)
        except Exception:
            pass
        it = item(title, f"https://flash.jin10.com/detail/{d.get('id')}" if d.get("id") else "https://www.jin10.com/", ts, "金十數據", "zh-CN", summ, True)
        if it:
            out.append(it)
    return out


def coingecko():
    try:
        data = json.loads(fetch("https://api.coingecko.com/api/v3/news", {"Accept": "application/json"})).get("data") or []
        out = []
        for d in data[:30]:
            ts = d.get("updated_at") or d.get("created_at")
            ts = int(ts) * 1000 if isinstance(ts, (int, float)) and ts < 1e11 else to_ms(str(ts)) if ts else None
            it = item(d.get("title"), d.get("url"), ts, "CoinGecko", "en", d.get("description") or "", True)
            if it:
                out.append(it)
        if out:
            return out
    except Exception as e:
        print("CoinGecko API：", e)
    return gnews("site:coingecko.com when:7d", "CoinGecko", True)


def blockcast():
    try:
        out = rss("https://blockcast.it/feed/", "區塊客", "zh-TW", True)
        if out:
            return out
    except Exception as e:
        print("區塊客 RSS：", e)
    return gnews("site:blockcast.it when:3d", "區塊客", True)


SOURCES = [
    ("CoinDesk", lambda: rss("https://www.coindesk.com/arc/outboundfeeds/rss/", "CoinDesk", "en", True)),
    ("金十數據", jin10),
    ("區塊客", blockcast),
    ("CoinGecko", coingecko),
    ("Cointelegraph", lambda: rss("https://cointelegraph.com/rss", "Cointelegraph", "en")),
    ("Decrypt", lambda: rss("https://decrypt.co/feed", "Decrypt", "en")),
    ("The Block", lambda: rss("https://www.theblock.co/rss.xml", "The Block", "en")),
    ("Bitcoin.com 新聞", lambda: rss("https://news.bitcoin.com/feed/", "Bitcoin.com 新聞", "en")),
    ("動區動趨", lambda: rss("https://www.blocktempo.com/feed/", "動區動趨", "zh-TW")),
    ("鏈新聞", lambda: rss("https://abmedia.io/feed", "鏈新聞", "zh-TW")),
    ("Google 新聞", lambda: gnews("(比特幣 OR 加密貨幣 OR 以太坊 OR 虛擬貨幣) when:1d")),
]


def translate(text, sl):
    if not text:
        return ""
    url = "https://translate.googleapis.com/translate_a/single?client=gtx&sl=" + sl + "&tl=zh-TW&dt=t&q=" + urllib.parse.quote(text)
    try:
        j = json.loads(fetch(url, timeout=15))
        return "".join(x[0] for x in j[0] if x and x[0]).strip()
    except Exception:
        return ""


try:
    with open(PREV, encoding="utf-8") as f:
        prev = json.load(f)
except Exception:
    prev = {}
old = {x["id"]: x for x in prev.get("items", [])}

status, fresh = {}, []
for name, fn in SOURCES:
    try:
        got = fn()
        status[name] = {"ok": True, "count": len(got)}
        fresh += got
    except Exception as e:
        status[name] = {"ok": False, "error": str(e)[:120]}
        print(f"{name} 失敗：{e}")

now = int(time.time() * 1000)
merged = dict(old)
for it in fresh:
    if it["ts"] > now + 10 * 60000:
        it["ts"] = now
    o = merged.get(it["id"])
    if o:  # 已經有了：保留翻譯，優先來源標記取聯集
        o["pri"] = o.get("pri") or it["pri"]
        continue
    it["seen"] = now
    merged[it["id"]] = it

# 翻譯：繁中原文直接用；英文、簡中翻成繁中（每次最多 60 則，避免被限流）
budget = 60
for it in sorted(merged.values(), key=lambda x: -x["ts"]):
    if it.get("t"):
        continue
    if it["lang"] == "zh-TW":
        it["t"], it["s"] = it["te"], it.get("se", "")
        continue
    if budget <= 0:
        continue
    budget -= 1
    sl = "zh-CN" if it["lang"] == "zh-CN" else "en"
    zt = translate(it["te"], sl)
    if zt:
        it["t"] = zt
        it["s"] = translate(it.get("se", ""), sl) if it.get("se") else ""
        time.sleep(0.3)

items = sorted(merged.values(), key=lambda x: -x["ts"])[:KEEP]
for it in items:  # 還沒翻成功的先用原文
    it.setdefault("t", "")
data = {"updated": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"), "sources": status, "items": items}
if [(x["id"], x.get("t")) for x in items] == [(x["id"], x.get("t")) for x in prev.get("items", [])]:
    print("沒有新新聞")
    sys.exit(0)
os.makedirs(os.path.dirname(os.path.abspath(OUT)), exist_ok=True)
with open(OUT, "w", encoding="utf-8") as f:
    json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
new_n = sum(1 for x in items if x["id"] not in old)
print(f"已更新：共 {len(items)} 則，新增 {new_n} 則；" + "、".join(f"{k}{'✓' if v['ok'] else '✗'}" for k, v in status.items()))

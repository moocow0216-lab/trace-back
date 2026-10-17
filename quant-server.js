'use strict';
/*
 * 合約量化進場：雲端掃描伺服器
 * - 每 10 秒掃描幣安 USDT 永續合約，找出「價格平穩但五項指標異常」的訊號
 * - 每分鐘用 1 分鐘 K 線、每 3 秒用最新成交價追蹤每一筆訊號的浮盈浮虧
 * - 可以從網頁觸發回測，回測的單也會繼續追蹤 7 天
 * - 所有資料存在 data/state.json，網頁透過 /api/state 讀取，所以每台裝置看到的都一樣
 * 需要 Node.js 18 以上，不需要安裝任何套件。
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = +process.env.PORT || 8787;
const HOST = process.env.HOST || '127.0.0.1';          // 預設只聽本機，由 Caddy 轉 HTTPS 進來
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const ADMIN_KEY = (process.env.ADMIN_KEY || '').trim();
const BF = process.env.BINANCE_FAPI || 'https://fapi.binance.com';
const BS = process.env.BINANCE_API || 'https://api.binance.com';
const FILE = path.join(DATA_DIR, 'state.json');
const HOUR = 3600000, TRACK_MAX = 168 * HOUR;
fs.mkdirSync(DATA_DIR, { recursive: true });

const sleep = ms => new Promise(r => setTimeout(r, ms));
const r5 = x => Math.round(x * 1e5) / 1e5;
const log = (...a) => console.log(new Date().toISOString(), ...a);

/* ---------------- 狀態與存檔 ---------------- */
const DEF_SET = { flat: 2, range: 6, minVol: 500, win: 4, sens: 1, minN: 2, logic: 'follow', everyS: 10 };
const DEF_TRADE = { tp: 250, sl: 250, lev: 100, hold: 24, exit: 'lock' };
const DEF_NOTIFY = { webhook: '', name: '', enabled: true, entry: true, exit: true };
const DEF_EQ = { mode: 'fixed', amt: 0.3, fee: 0.05, max: 0 };
const DEF_BX = { key: '', secret: '', notify: true, liq: true, liqPct: 3 };
const DEF_LT = { on: false, margin: 0.3, lev: 100, mode: 'CROSS', maxOpen: 0, dayLoss: 20, startCap: 0, startAt: 0 };   // startCap＝0 代表等偵測到帳戶資金再開始算   // 自動下單（預設暫停）   // Bitunix 唯讀 API 金鑰（只存在這台伺服器）            // 資金模擬：每筆保證金、手續費、最多同時持倉
const DEF_REP = { cap: 100, btN: 50, days: 14, next: 0 };                   // 雙週結算：每期本金、回測幣數、幾天一期、下次結算時間
let ST = { cards: [], bt: { at: 0, coins: 0, trades: [] }, set: { ...DEF_SET }, trade: { ...DEF_TRADE }, notify: { ...DEF_NOTIFY }, eq: { ...DEF_EQ }, rep: { ...DEF_REP }, reports: [], bx: { ...DEF_BX }, users: [], sessions: [], lt: { ...DEF_LT }, ltTrades: [] };
try {
  const j = JSON.parse(fs.readFileSync(FILE, 'utf8'));
  ST = { cards: j.cards || [], bt: j.bt || ST.bt, set: { ...DEF_SET, ...(j.set || {}) }, trade: { ...DEF_TRADE, ...(j.trade || {}) }, notify: { ...DEF_NOTIFY, ...(j.notify || {}) }, eq: { ...DEF_EQ, ...(j.eq || {}) }, rep: { ...DEF_REP, ...(j.rep || {}) }, reports: j.reports || [], bx: { ...DEF_BX, ...(j.bx || {}) }, users: j.users || [], sessions: j.sessions || [], lt: { ...DEF_LT, ...(j.lt || {}), on: false }, ltTrades: j.ltTrades || [] };   // 伺服器重開後自動交易一律先暫停
  log(`讀入存檔：${ST.cards.length} 張卡片、${ST.bt.trades.length} 筆回測`);
} catch (e) { log('沒有存檔，從頭開始'); }
let CV = Date.now(), BV = Date.now();                  // 卡片、回測各自的版本號，沒變就不用重傳
let dirty = false;
const touchCards = () => { CV++; dirty = true; };
const touchBT = () => { BV++; dirty = true; };
function save() {
  if (!dirty) return; dirty = false;
  const tmp = FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(ST), { mode: 0o600 });   // 裡面有 Discord Webhook 和 Bitunix 金鑰，只給自己讀
  fs.renameSync(tmp, FILE);
}
setInterval(() => { try { save(); } catch (e) { log('存檔失敗', e.message); } }, 10000);
for (const sig of ['SIGINT', 'SIGTERM']) process.on(sig, () => { dirty = true; try { save(); } catch (e) {} process.exit(0); });

/* ---------------- 幣安限速 ---------------- */
const RL = { win: [], oi: [], pause: 0 };
const BUDGET = 1800;                                    // 每分鐘 2400 的上限，留一點緩衝
function weight(url) {
  if (!url.startsWith(BF)) return 0;
  if (url.includes('/futures/data/')) return -1;
  const m = url.match(/[?&]limit=(\d+)/), lim = m ? +m[1] : 500;
  if (url.includes('/klines')) return lim < 100 ? 1 : lim < 500 ? 2 : lim <= 1000 ? 5 : 10;
  if (url.includes('/ticker/24hr')) return url.includes('symbol=') ? 1 : 40;
  if (url.includes('/ticker/price')) return url.includes('symbol=') ? 1 : 2;
  if (url.includes('/exchangeInfo')) return 1;
  return 5;
}
async function gate(url) {
  const w = weight(url); if (!w) return;
  for (;;) {
    const now = Date.now();
    if (now < RL.pause) { await sleep(Math.min(5000, RL.pause - now)); continue; }
    if (w < 0) { RL.oi = RL.oi.filter(t => now - t < 300000); if (RL.oi.length < 900) { RL.oi.push(now); return; } }
    else { RL.win = RL.win.filter(x => now - x[0] < 60000); if (RL.win.reduce((a, x) => a + x[1], 0) + w <= BUDGET) { RL.win.push([now, w]); return; } }
    await sleep(300);
  }
}
async function getJSON(url, retry = true) {
  await gate(url);
  const r = await fetch(url, { signal: AbortSignal.timeout(15000) });
  if (r.status === 429 || r.status === 418) {
    const ra = +r.headers.get('retry-after');
    RL.pause = Math.max(RL.pause, Date.now() + (ra > 0 ? ra * 1000 : r.status === 418 ? 180000 : 60000));
    log('幣安限速', r.status, '暫停到', new Date(RL.pause).toISOString());
    if (retry) return getJSON(url, false);
    const e = new Error('HTTP ' + r.status); e.rate = true; throw e;
  }
  if (r.status === 451 || r.status === 403) throw new Error(`幣安拒絕這台主機的 IP（HTTP ${r.status}），請換到日本、新加坡、香港等地區的主機`);
  if (!r.ok) throw new Error('HTTP ' + r.status);
  return r.json();
}

/* ---------------- 幣安資料 ---------------- */
function spotOf(sym, set) {
  if (set.has(sym)) return sym;
  const m = sym.match(/^(1000000|100000|10000|1000|1M)(.+)$/);
  return m && set.has(m[2]) ? m[2] : null;
}
const BN = {
  meta: null,
  async universe() {
    if (!BN.meta || Date.now() - BN.meta.at > HOUR) {
      const [info, spot] = await Promise.all([getJSON(BF + '/fapi/v1/exchangeInfo'), getJSON(BS + '/api/v3/ticker/price').catch(() => [])]);
      BN.meta = { at: Date.now(), ok: new Set(info.symbols.filter(s => s.contractType === 'PERPETUAL' && s.quoteAsset === 'USDT' && s.status === 'TRADING').map(s => s.symbol)), ss: new Set(spot.map(s => s.symbol)) };
    }
    const tick = await getJSON(BF + '/fapi/v1/ticker/24hr');
    return tick.filter(t => BN.meta.ok.has(t.symbol)).map(t => {
      const last = +t.lastPrice, hi = +t.highPrice, lo = +t.lowPrice;
      return { sym: t.symbol, id: t.symbol, last, chg: +t.priceChangePercent, amp: lo > 0 ? (hi - lo) / lo * 100 : 0, qv: +t.quoteVolume, spot: spotOf(t.symbol, BN.meta.ss) };
    });
  },
  async fut(id, tf, n, end) {
    const k = await getJSON(`${BF}/fapi/v1/klines?symbol=${id}&interval=${tf}&limit=${n}${end ? '&endTime=' + end : ''}`);
    return k.map(r => ({ t: +r[0], o: +r[1], h: +r[2], l: +r[3], c: +r[4], qv: +r[7], d: 2 * +r[10] - +r[7] }));
  },
  async spot(id, tf, n) {
    if (!id) return null;
    const k = await getJSON(`${BS}/api/v3/klines?symbol=${id}&interval=${tf}&limit=${n}`);
    return k.map(r => ({ t: +r[0], d: 2 * +r[10] - +r[7] }));
  },
  async oi(id, tf, n) {
    const r = await getJSON(`${BF}/futures/data/openInterestHist?symbol=${id}&period=${tf}&limit=${Math.min(500, n)}`);
    return r.map(x => ({ t: +x.timestamp, v: +x.sumOpenInterestValue }));
  }
};
function mergeBars(old, fresh, N) {
  if (!old) return fresh;
  const m = new Map(old.map(b => [b.t, b])); fresh.forEach(b => m.set(b.t, b));
  return [...m.values()].sort((a, b) => a.t - b.t).slice(-N);
}

/* ---------------- 指標與判斷（跟網頁同一套） ---------------- */
const SENS = [{ sum: 2.0, bar: 2.5 }, { sum: 2.5, bar: 3.0 }, { sum: 3.0, bar: 3.5 }];
function median(s) { const n = s.length; return n % 2 ? s[(n - 1) / 2] : (s[n / 2 - 1] + s[n / 2]) / 2; }
function rz(x, arr) {
  const s = arr.filter(Number.isFinite).sort((a, b) => a - b);
  if (s.length < 24) return NaN;
  const med = median(s), mad = median(s.map(v => Math.abs(v - med)).sort((a, b) => a - b));
  let sd = 1.4826 * mad;
  if (!(sd > 0)) { const m = s.reduce((a, b) => a + b, 0) / s.length; sd = Math.sqrt(s.reduce((a, b) => a + (b - m) ** 2, 0) / s.length); }
  if (!(sd > 0)) return 0;
  return Math.max(-20, Math.min(20, (x - med) / sd));
}
function sumFeat(d, W) {
  const n = d.length; if (n < W + 30) return null;
  const cur = d.slice(n - W); if (cur.some(x => !Number.isFinite(x))) return null;
  const v = cur.reduce((a, b) => a + b, 0), base = [];
  for (let i = W; i <= n - W; i++) { let s = 0, ok = true; for (let j = i - W; j < i; j++) { if (!Number.isFinite(d[j])) { ok = false; break; } s += d[j]; } if (ok) base.push(s); }
  return { v, z: rz(v, base) };
}
function barFeat(d, W) {
  const n = d.length; if (n < W + 30) return null;
  const base = d.slice(0, n - W); let best = null;
  for (let i = n - W; i < n; i++) { if (!Number.isFinite(d[i])) continue; const z = rz(d[i], base); if (!best || Math.abs(z) > Math.abs(best.z)) best = { v: d[i], z }; }
  return best && Number.isFinite(best.z) ? best : null;
}
function oiFeat(v, W) {
  const n = v.length; if (n < W + 30 || !(v[n - 1 - W] > 0)) return null;
  const cur = v[n - 1] / v[n - 1 - W] - 1, base = [];
  for (let i = W; i < n - W; i++) if (v[i - W] > 0) base.push(v[i] / v[i - W] - 1);
  return { v: cur, z: rz(cur, base) };
}
const IND = [
  { k: 'fcvd', n: '合約 CVD', w: 1, bar: false },
  { k: 'oi', n: '未平倉合約', w: 1, bar: false },
  { k: 'scvd', n: '現貨 CVD', w: 1.5, bar: false },
  { k: 'sbar', n: '現貨 Delta Bars', w: 0.75, bar: true },
  { k: 'fbar', n: '合約 Delta Bars', w: 0.75, bar: true }
];
function detect(fd, oiv, sd, W) {
  const S = ST.set, th = SENS[S.sens] || SENS[1];
  const F = { fcvd: sumFeat(fd, W), oi: oiv ? oiFeat(oiv, W) : null, scvd: sd ? sumFeat(sd, W) : null, sbar: sd ? barFeat(sd, W) : null, fbar: barFeat(fd, W) };
  let score = 0, abN = 0;
  const ind = IND.map(I => {
    const f = F[I.k]; const ok = f && Number.isFinite(f.z);
    const ab = !!(ok && Math.abs(f.z) >= (I.bar ? th.bar : th.sum));
    let dir = 0;
    if (ab) { abN++; dir = I.k === 'oi' ? (f.v > 0 && F.fcvd ? Math.sign(F.fcvd.v) : 0) : Math.sign(f.v); score += I.w * dir; }
    return { k: I.k, n: I.n, v: ok ? f.v : null, z: ok ? f.z : null, ab, dir };
  });
  if (abN < S.minN) return null;
  let dir = score >= 1 ? 1 : score <= -1 ? -1 : 0;
  if (!dir) return null;
  if (S.logic === 'absorb') dir = -dir;
  return { dir, score: Math.round(Math.abs(score) * 100) / 100, abN, ind };
}
const amt = v => { const a = Math.abs(v); return a >= 1e8 ? (a / 1e8).toFixed(2) + ' 億' : a >= 1e4 ? (a / 1e4).toFixed(a >= 1e6 ? 0 : 1) + ' 萬' : a.toFixed(a >= 100 ? 0 : 2); };
const spct = v => (v > 0 ? '+' : v < 0 ? '−' : '') + Math.abs(v).toFixed(2) + '%';
const zs = z => (z > 0 ? '+' : z < 0 ? '−' : '') + Math.abs(z).toFixed(1);
function reason(r) {
  const parts = r.ind.filter(i => i.ab).map(i => {
    const z = `（z ${zs(i.z)}）`;
    if (i.k === 'fcvd') return `合約主動${i.v > 0 ? '買' : '賣'}超 ${amt(i.v)}${z}`;
    if (i.k === 'scvd') return `現貨主動${i.v > 0 ? '買' : '賣'}超 ${amt(i.v)}${z}`;
    if (i.k === 'oi') return `持倉${i.v > 0 ? '增加' : '減少'} ${(Math.abs(i.v) * 100).toFixed(2)}%${z}`;
    if (i.k === 'sbar') return `現貨單根${i.v > 0 ? '買' : '賣'}方爆量 ${amt(i.v)}${z}`;
    return `合約單根${i.v > 0 ? '買' : '賣'}方爆量 ${amt(i.v)}${z}`;
  });
  let s = `近 ${r.win} 小時價格只動 ${spct(r.pc)}（24 小時 ${spct(r.chg)}），但${parts.join('、')}。`;
  const oi = r.ind.find(i => i.k === 'oi');
  if (oi && oi.ab && oi.v < 0) s += '持倉減少代表有人平倉離場，這項不計方向。';
  if (r.logic === 'absorb') s += r.dir > 0 ? '主動賣盤被掛單接走、價格跌不下去，依吸收反轉判斷偏多。' : '主動買盤被掛單壓住、價格漲不上去，依吸收反轉判斷偏空。';
  else s += r.dir > 0 ? '主動買盤趁橫盤進場，跟隨資金方向偏多。' : '主動賣盤趁橫盤出貨，跟隨資金方向偏空。';
  return s;
}

/* ---------------- 浮盈浮虧軌跡（網頁用同一套格式重算成功率） ---------------- */
function extend(tr, bars) {
  for (const b of bars) {
    const f = tr.dir > 0 ? b.h / tr.entry - 1 : 1 - b.l / tr.entry;
    const a = tr.dir > 0 ? 1 - b.l / tr.entry : b.h / tr.entry - 1;
    const nf = f > tr.fav + 1e-9, na = a > tr.adv + 1e-9;
    if (nf || na) { tr.fav = Math.max(tr.fav, f); tr.adv = Math.max(tr.adv, a); tr.recs.push([b.t, r5(tr.fav), r5(tr.adv), nf && na ? 1 : 0]); }
    tr.end = b.t;
  }
}
function hourClose(tr, c, bars, step) {
  tr.hc = tr.hc || [];
  for (const b of bars) {
    if (!Number.isFinite(b.c)) continue;
    const k = Math.floor((b.t - c.et) / HOUR);
    if (k >= 0 && k < 168) {
      tr.hh = tr.hh || []; tr.hl = tr.hl || [];
      const hi = r5(b.h / c.entry - 1), lo = r5(b.l / c.entry - 1);
      for (let q = tr.hh.length; q < k; q++) { tr.hh[q] = null; tr.hl[q] = null; }
      tr.hh[k] = Number.isFinite(tr.hh[k]) ? Math.max(tr.hh[k], hi) : hi;
      tr.hl[k] = Number.isFinite(tr.hl[k]) ? Math.min(tr.hl[k], lo) : lo;
    }
    const h = Math.floor((b.t + step - c.et) / HOUR);
    if (h >= 1 && h <= 168 && !Number.isFinite(tr.hc[h - 1])) { for (let q = 0; q < h - 1; q++) if (tr.hc[q] === undefined) tr.hc[q] = null; tr.hc[h - 1] = r5(b.c / c.entry - 1); }
  }
}
// 這筆單在伺服器設定的 ±範圍下是否還沒碰到成功線或失敗線（用來決定重複訊號要不要合併）
function stillOpen(c) {
  const T = ST.trade, tp = T.tp / 100 / T.lev, sl = T.sl / 100 / T.lev, tr = c.trk;
  if (!tr) return true;
  const fav = Math.max(tr.fav || 0, ...(tr.lv || []).map(p => p[1])), adv = Math.max(tr.adv || 0, ...(tr.lv || []).map(p => p[2]));
  return fav < tp && adv < sl;
}

/* ---------------- 判斷一筆單有沒有結單（跟網頁同一套規則） ---------------- */
function evalTrade(c) {
  const T = ST.trade, tr = c.trk || c;
  let recs = tr.recs || [];
  const lv = (tr.lv || []).filter(p => !tr.end || p[0] >= tr.end + (tr.step || 60000));
  if (lv.length) {
    recs = recs.slice(); let cf = recs.length ? recs[recs.length - 1][1] : 0, ca = recs.length ? recs[recs.length - 1][2] : 0;
    for (const p of lv) if (p[1] > cf || p[2] > ca) { cf = Math.max(cf, p[1]); ca = Math.max(ca, p[2]); recs.push([p[0], cf, ca, 0]); }
  }
  const tp = T.tp / 100 / T.lev, sl = T.sl / 100 / T.lev, lim = c.et + T.hold * HOUR, step = tr.step || 60000;
  const done = !!(tr.end && tr.end + step >= lim);
  const hcAt = () => { const h = tr.hc && tr.hc[T.hold - 1]; return Number.isFinite(h) ? c.dir * h * T.lev * 100 : null; };
  for (let i = 0; i < recs.length; i++) {
    const r = recs[i];
    if (r[0] >= lim) break;
    const hT = r[1] >= tp, hL = r[2] >= sl;
    if (hL) return { st: hT && r[3] ? 'amb' : 'fail', at: r[0], exitAt: r[0], pnl: -T.sl };
    if (hT) {
      if (T.exit === 'fixed') return { st: 'win', at: r[0], exitAt: r[0], pnl: T.tp, how: 'fixed' };
      if (tr.hl && !tr.noHL) {
        const H0 = Math.floor((r[0] - c.et) / HOUR), nH = Math.min(T.hold, tr.hl.length);
        for (let h = H0 + 1; h < nH; h++) {
          const lo = c.dir > 0 ? tr.hl[h] : -tr.hh[h];
          if (Number.isFinite(lo) && lo <= tp) return { st: 'win', at: r[0], exitAt: c.et + h * HOUR, pnl: T.tp, how: 'lock' };
        }
      }
      if (done) { const v = hcAt(); return { st: 'win', at: r[0], exitAt: lim, pnl: v === null ? T.tp : Math.max(T.tp, v), how: 'hold' }; }
      return { st: 'win', at: r[0], open: true };      // 達標後持有中，還沒結單
    }
  }
  if (!done) return { st: 'open', open: true };
  const v = hcAt();
  return { st: 'timeout', at: lim, exitAt: lim, pnl: v === null ? 0 : v };
}
const isLive = c => !!evalTrade(c).open;
// 已經結單的卡片先標記為「通知過」，避免改設定或重開伺服器時一次跳出一堆結單訊息
function markSettledNotified() { for (const c of ST.cards) if (c.et && !isLive(c)) c.nx = 1; }
markSettledNotified();

/* ---------------- Discord 通知（Webhook） ---------------- */
// Webhook 網址長這樣：https://discord.com/api/webhooks/數字/一長串英數字
const DC_RE = /^https:\/\/(?:(?:canary|ptb)\.)?discord(?:app)?\.com\/api\/webhooks\/\d+\/[\w-]+$/;
const DC_OK = u => DC_RE.test(u) || (process.env.DC_TEST === '1' && /^http:\/\/127\.0\.0\.1:\d+\/api\/webhooks\//.test(u));
const DC = { q: [], busy: false };
function dcSend(content, cfg = ST.notify) {
  if (!cfg.webhook) return Promise.resolve(false);
  return new Promise(ok => { DC.q.push({ content, cfg, ok }); dcRun(); });
}
async function dcRun() {
  if (DC.busy) return; DC.busy = true;
  while (DC.q.length) {
    const m = DC.q.shift();
    let sent = false;
    for (let tries = 0; tries < 3 && !sent; tries++) {
      try {
        const r = await fetch(m.cfg.webhook, {
          method: 'POST', headers: { 'Content-Type': 'application/json' }, signal: AbortSignal.timeout(15000),
          body: JSON.stringify({ content: m.content.slice(0, 1900), username: '合約量化進場', allowed_mentions: { parse: [] } })
        });
        if (r.status === 429) { const j = await r.json().catch(() => ({})); await sleep(Math.ceil((+j.retry_after || 2) * 1000) + 200); continue; }   // Discord 限速，等一下再送
        if (!r.ok) { log('Discord 傳送失敗', r.status, (await r.text().catch(() => '')).slice(0, 200)); break; }
        sent = true;
      } catch (e) { log('Discord 傳送失敗', e.message); await sleep(2000); }
    }
    m.ok(sent);
    await sleep(800);
  }
  DC.busy = false;
}
const TZ = 8 * HOUR;                                    // 訊息裡的時間用台北時間
const p2 = x => String(x).padStart(2, '0');
const tw = t => { const d = new Date(t + TZ); return `${p2(d.getUTCMonth() + 1)}/${p2(d.getUTCDate())} ${p2(d.getUTCHours())}:${p2(d.getUTCMinutes())}`; };
const fpx = p => { if (!(p > 0)) return '—'; const d = p >= 1000 ? 2 : p >= 10 ? 3 : p >= 1 ? 4 : Math.min(10, Math.max(4, 3 - Math.floor(Math.log10(p)))); return p.toFixed(d + 1); };
const durTxt = ms => { const m = Math.round(ms / 60000); return m < 60 ? m + ' 分' : m < 1440 ? (m / 60).toFixed(1) + ' 小時' : (m / 1440).toFixed(1) + ' 天'; };
const mdEsc = s => String(s).replace(/[*_~`|>\\]/g, c => '\\' + c);
function notifyEntry(c) {
  const N = ST.notify, T = ST.trade; if (!N.enabled || !N.entry) return;
  const tpPx = c.entry * (1 + c.dir * T.tp / 100 / T.lev), slPx = c.entry * (1 - c.dir * T.sl / 100 / T.lev);
  const ab = (c.ind || []).filter(i => i.ab).map(i => `${i.n} z${i.z > 0 ? '+' : ''}${i.z.toFixed(1)}`).join('、');
  dcSend(`${c.dir > 0 ? '🟢 **做多**' : '🔴 **做空**'} **${mdEsc(c.sym)}**（數據異常 ${c.abN}/5）\n` +
    `進場 **${fpx(c.entry)}**・${T.lev}x\n達標 ${fpx(tpPx)}（+${T.tp}%）\n失敗 ${fpx(slPx)}（−${T.sl}%）\n` +
    `${ab ? '異常：' + mdEsc(ab) + '\n' : ''}時間 ${tw(c.et)}（台北）\n-# 統計訊號，只供參考，不是投資建議`);
}
function notifyExit(c, E) {
  const N = ST.notify, T = ST.trade; if (!N.enabled || !N.exit) return;
  const head = E.st === 'win' ? '✅ **成功**' : E.st === 'timeout' ? '⏱ **逾時**' : '❌ **失敗**';
  const how = E.how === 'lock' ? '（跑回達標線，保本鎖利出場）' : E.how === 'hold' ? `（持有到 ${T.hold} 小時到期）` : E.st === 'amb' ? '（同一根 K 棒兩邊都碰到，保守算失敗）' : '';
  const pnl = (E.pnl > 0 ? '+' : E.pnl < 0 ? '−' : '') + Math.abs(E.pnl).toFixed(0) + '%';
  dcSend(`${head} ${c.dir > 0 ? '做多' : '做空'} **${mdEsc(c.sym)}** **${pnl}**${how}\n` +
    `進場 ${fpx(c.entry)}（${tw(c.et)}）\n持有 ${durTxt((E.exitAt || Date.now()) - c.et)}・${T.lev}x`);
}
function checkExits() {
  let ch = false;
  for (const c of ST.cards) {
    if (!c.et || c.nx) continue;
    const E = evalTrade(c);
    if (E.open) continue;
    c.nx = 1; ch = true;
    notifyExit(c, E);
  }
  if (ch) touchCards();
}

/* ---------------- 掃描 ---------------- */
const SCAN = { running: false, last: 0, dur: 0, total: 0, flatN: 0, done: 0, todo: 0, found: 0, err: '' };
const CACHE = new Map();
async function getData(u, N) {
  const now = Date.now();
  let c = CACHE.get(u.id);
  if (!c || now - c.full > HOUR) c = { full: now, k: null, sp: null, oi: null, oiAt: 0 };
  const inc = !!c.k;
  c.k = mergeBars(inc ? c.k : null, await BN.fut(u.id, '1h', inc ? 3 : N), N);
  if (now - c.oiAt > 300000) { c.oi = await BN.oi(u.id, '1h', N).catch(() => c.oi); c.oiAt = now; }
  if (u.spot) c.sp = mergeBars(inc ? c.sp : null, await BN.spot(u.spot, '1h', inc && c.sp ? 3 : N).catch(() => []), N);
  CACHE.set(u.id, c);
  return { k: c.k, oi: c.oi, sp: c.sp && c.sp.length ? c.sp : null };
}
async function analyze(u) {
  const N = 168, W = ST.set.win;
  const { k, oi, sp } = await getData(u, N);
  const n = k.length; if (n < W + 31) return null;
  const pc = (k[n - 1].c / k[n - 1 - W].c - 1) * 100;
  if (Math.abs(pc) > ST.set.flat) return null;
  const D = detect(k.map(x => x.d), oi ? oi.map(x => x.v) : null, sp ? sp.map(x => x.d) : null, W);
  if (!D) return null;
  return Object.assign({ sym: u.sym, pid: u.id, spot: u.spot, src: 'binance', last: k[n - 1].c, chg: u.chg, amp: u.amp, qv: u.qv, pc, win: W, logic: ST.set.logic, unitOk: true }, D);
}
function addCard(r) {
  const now = Date.now();
  r.why = reason(r);
  // 同一個幣還有單沒結單 → 不開新單。同方向就更新一下「最後偵測」的數字；反方向直接忽略
  const live = ST.cards.find(c => c.sym === r.sym && c.et && isLive(c));
  if (live) {
    if (live.dir === r.dir) {
      const { entry, et, id, t0, ...rest } = r;
      Object.assign(live, rest, now - live.t >= 300000 ? { t: now, hits: (live.hits || 1) + 1 } : {});
      touchCards();
    }
    return;
  }
  const c = Object.assign(r, { id: r.sym + '-' + now, t0: now, t: now, hits: 1, entry: r.last, et: now });
  log('新訊號', r.sym, r.dir > 0 ? '做多' : '做空', r.abN + '/5');
  ST.cards.unshift(c);
  ST.cards = ST.cards.slice(0, 300);
  touchCards();
  notifyEntry(c);
  ltOpen(c);
}
async function scan() {
  if (SCAN.running) return; SCAN.running = true;
  const t0 = Date.now(); SCAN.err = ''; SCAN.done = 0; SCAN.found = 0;
  try {
    const uni = await BN.universe(), S = ST.set;
    const flat = uni.filter(u => Math.abs(u.chg) <= S.flat && u.amp <= S.range && u.qv >= S.minVol * 1e4).sort((a, b) => b.qv - a.qv);
    SCAN.total = uni.length; SCAN.flatN = flat.length; SCAN.todo = flat.length;
    let idx = 0;
    const worker = async () => { while (idx < flat.length) { const u = flat[idx++]; try { const r = await analyze(u); if (r) { SCAN.found++; addCard(r); } } catch (e) {} SCAN.done++; } };
    await Promise.all(Array.from({ length: 8 }, worker));
  } catch (e) { SCAN.err = e.message; log('掃描失敗', e.message); }
  SCAN.last = Date.now(); SCAN.dur = SCAN.last - t0; SCAN.running = false;
}

/* ---------------- 追蹤 ---------------- */
async function trackCard(c, now) {
  if (!c.trk) c.trk = { dir: c.dir, entry: c.entry, recs: [], fav: 0, adv: 0, end: 0, step: 60000, cur: c.entry };
  const tr = c.trk;
  if (tr.end && tr.end - c.et >= TRACK_MAX) return false;
  const from = tr.end ? tr.end + 60000 : Math.floor(c.et / 60000) * 60000 + 60000;
  if (now - from < 60000) return false;
  const lim = Math.min(1000, Math.ceil((now - from) / 60000) + 1);
  const k = await getJSON(`${BF}/fapi/v1/klines?symbol=${c.pid}&interval=1m&startTime=${from}&limit=${lim}`);
  const bars = k.map(r => ({ t: +r[0], h: +r[2], l: +r[3], c: +r[4] }));
  if (!bars.length) return false;
  if (!tr.curAt || now >= tr.curAt) { tr.cur = bars[bars.length - 1].c; tr.curAt = now; }
  const closed = bars.filter(b => b.t + 60000 <= now && b.t - c.et < TRACK_MAX);
  extend(tr, closed); hourClose(tr, c, closed, 60000);
  if (tr.lv) tr.lv = tr.lv.filter(p => p[0] >= tr.end + 60000);
  return true;
}
async function trackBT(t, now) {
  if (now - t.et > TRACK_MAX + 900000) return false;
  const from = (t.end || t.et - 900000) + 900000;
  if (from - t.et >= TRACK_MAX || now - from < 900000 * 2) return false;
  const k = await getJSON(`${BF}/fapi/v1/klines?symbol=${t.pid}&interval=15m&startTime=${from}&limit=${Math.min(1000, Math.ceil((now - from) / 900000) + 1)}`);
  const bars = k.map(r => ({ t: +r[0], h: +r[2], l: +r[3], c: +r[4] })).filter(b => b.t + 900000 <= now && b.t - t.et < TRACK_MAX);
  if (!bars.length) return false;
  const last = t.recs.length ? t.recs[t.recs.length - 1] : null;
  t.fav = last ? last[1] : 0; t.adv = last ? last[2] : 0;
  extend(t, bars); hourClose(t, t, bars, 900000);
  delete t.fav; delete t.adv;
  return true;
}
let tracking = false;
async function trackAll() {
  if (tracking) return; tracking = true;
  const now = Date.now(); let c1 = false, c2 = false;
  for (const c of ST.cards.slice()) { if (c.et && c.entry) try { if (await trackCard(c, now)) c1 = true; } catch (e) {} }
  for (const t of ST.bt.trades) try { if (await trackBT(t, now)) c2 = true; } catch (e) {}
  if (c1) touchCards(); if (c2) touchBT();
  checkExits();
  tracking = false;
}
// 每 3 秒抓一次全市場最新價，記下還沒被 1 分鐘 K 線涵蓋的極值點
const PX = { at: 0, map: {} };
async function pollPx() {
  try {
    const list = await getJSON(BF + '/fapi/v1/ticker/price');
    const t = Date.now(), m = {}; list.forEach(x => { m[x.symbol] = +x.price; });
    PX.at = t; PX.map = m;
    let ch = false;
    for (const c of ST.cards) {
      if (!c.et || !c.entry || t - c.et > TRACK_MAX) continue;
      const px = m[c.pid]; if (!(px > 0)) continue;
      c.px = px; c.pxAt = t;
      if (!c.trk) c.trk = { dir: c.dir, entry: c.entry, recs: [], fav: 0, adv: 0, end: 0, step: 60000, cur: c.entry };
      const tr = c.trk; tr.lv = tr.lv || [];
      const f = c.dir > 0 ? px / c.entry - 1 : 1 - px / c.entry, a = -f;
      const mf = tr.lv.reduce((x, p) => Math.max(x, p[1]), tr.fav || 0), ma = tr.lv.reduce((x, p) => Math.max(x, p[2]), tr.adv || 0);
      if (f > mf + 1e-9 || a > ma + 1e-9) { tr.lv.push([t, r5(f), r5(a)]); if (tr.lv.length > 400) tr.lv = tr.lv.slice(-400); ch = true; }
    }
    if (ch) touchCards();
    checkExits();
    await ltManage();
  } catch (e) {}
}

/* ---------------- 回測 ---------------- */
const BTP = { run: false, stop: false, done: 0, total: 0, found: 0, skipped: 0, msg: '', at: 0 };
const BTC = new Map();
const tailN = (arr, per, max) => arr && arr.length ? Math.min(max, Math.ceil((Date.now() - arr[arr.length - 1].t) / per) + 2) : max;
async function btBase(u) {
  let c = BTC.get(u.id);
  if (c && Date.now() - c.at > 6 * HOUR) c = null;
  if (!c) c = { k: await BN.fut(u.id, '1h', 500), at: Date.now() };
  else c.k = mergeBars(c.k, await BN.fut(u.id, '1h', tailN(c.k, HOUR, 500)), 500);
  BTC.set(u.id, c); return c;
}
async function btExtra(u, c) {
  await Promise.all([
    (async () => { c.oi = c.oi ? mergeBars(c.oi, await BN.oi(u.id, '1h', tailN(c.oi, HOUR, 500)).catch(() => []), 500) : await BN.oi(u.id, '1h', 500).catch(() => null); })(),
    (async () => { if (!u.spot) { c.sp = null; return; } c.sp = c.sp ? mergeBars(c.sp, await BN.spot(u.spot, '1h', tailN(c.sp, HOUR, 500)).catch(() => []), 500) : await BN.spot(u.spot, '1h', 500).catch(() => null); })()
  ]);
}
async function btBars(u, c, start) {
  const P15 = 900000, page = 1000 * P15;
  const get = (from, lim) => getJSON(`${BF}/fapi/v1/klines?symbol=${u.id}&interval=15m&startTime=${from}&limit=${lim}`).then(r => r.map(x => ({ t: +x[0], h: +x[2], l: +x[3], c: +x[4] })));
  if (c.b15 && c.b15.length && c.b15[0].t <= start) {
    const n = tailN(c.b15, P15, 1000);
    if (n < 1000) { c.b15 = mergeBars(c.b15, await get(c.b15[c.b15.length - 1].t, n), 4000); return; }
  }
  const pages = [];
  for (let f = start; f < Date.now(); f += page) pages.push(get(f, 1000));
  c.b15 = (await Promise.all(pages)).flat().sort((a, b) => a.t - b.t);
}
async function backtest(N) {
  if (BTP.run) return;
  Object.assign(BTP, { run: true, stop: false, done: 0, total: 0, found: 0, skipped: 0, msg: '取得合約清單…' });
  const S = ST.set, W = S.win, trades = [];
  try {
    const uni = await BN.universe();
    const list = uni.sort((a, b) => b.qv - a.qv).slice(0, N || uni.length);
    BTP.total = list.length; BTP.msg = '';
    const one = async u => {
      const c = await btBase(u), k = c.k, n = k.length; if (n < 200) return;
      const cand = [];
      for (let i = 168; i <= n - 2; i++) {
        let hi = -Infinity, lo = Infinity, qv = 0;
        for (let j = i - 23; j <= i; j++) { hi = Math.max(hi, k[j].h); lo = Math.min(lo, k[j].l); qv += k[j].qv; }
        const chg = (k[i].c / k[i - 23].o - 1) * 100, amp = (hi - lo) / lo * 100, pc = (k[i].c / k[i - W].c - 1) * 100;
        if (Math.abs(chg) > S.flat || amp > S.range || qv < S.minVol * 1e4 || Math.abs(pc) > S.flat) continue;
        cand.push({ i, chg, pc });
      }
      if (!cand.length) return;
      await btExtra(u, c);
      const t0 = k[0].t, fd = k.map(x => x.d), oiv = new Array(n).fill(NaN), sdv = c.sp ? new Array(n).fill(NaN) : null;
      if (c.oi) c.oi.forEach(o => { const i = Math.floor((o.t - 1 - t0) / HOUR); if (i >= 0 && i < n) oiv[i] = o.v; });
      if (c.sp) { const m = new Map(k.map((x, i) => [x.t, i])); c.sp.forEach(s => { if (m.has(s.t)) sdv[m.get(s.t)] = s.d; }); }
      const sig = [];
      for (const { i, chg, pc } of cand) {
        const D = detect(fd.slice(i - 167, i + 1), c.oi ? oiv.slice(i - 167, i + 1) : null, sdv ? sdv.slice(i - 167, i + 1) : null, W);
        if (D) sig.push({ i, D, chg, pc });
      }
      if (!sig.length) return;
      await btBars(u, c, k[168].t + HOUR);
      const now = Date.now(), bars = c.b15.filter(b => b.t + 900000 <= now);
      let free = 0;                                     // 上一筆單結單的時間；結單前同一個幣不開新單
      for (const { i, D, chg, pc } of sig) {
        const et = k[i].t + HOUR;
        if (et < free) continue;
        const tr = { id: 'bt-' + u.id + '-' + et, bt: 1, sym: u.sym, pid: u.id, spot: u.spot, src: 'binance', dir: D.dir, abN: D.abN, et, entry: k[i].c, recs: [], fav: 0, adv: 0, end: 0, step: 900000 };
        const seg = bars.filter(b => b.t >= et && b.t - et < TRACK_MAX);
        extend(tr, seg); hourClose(tr, tr, seg, 900000);
        delete tr.fav; delete tr.adv;
        Object.assign(tr, { ind: D.ind.map(x => ({ k: x.k, n: x.n, v: x.v === null ? null : (x.k === 'oi' ? r5(x.v) : Math.round(x.v)), z: x.z === null ? null : Math.round(x.z * 100) / 100, ab: x.ab })), chg, pc, win: W, logic: S.logic, unitOk: true, last: k[i].c });
        tr.why = reason(tr);
        trades.push(tr); BTP.found++;
        const E = evalTrade(tr);
        free = E.open ? Infinity : E.exitAt;
      }
    };
    let idx = 0;
    const worker = async () => {
      while (idx < list.length && !BTP.stop) {
        const u = list[idx++];
        try { await Promise.race([one(u), new Promise((_, no) => setTimeout(() => no(new Error('timeout')), 90000))]); }
        catch (e) { if (e.message === 'timeout') BTP.skipped++; }
        BTP.done++;
      }
    };
    await Promise.all(Array.from({ length: 6 }, worker));
    trades.sort((a, b) => b.et - a.et);
    ST.bt = { at: Date.now(), coins: BTP.done, trades: trades.slice(0, 4000) };
    touchBT();
    BTP.msg = BTP.stop ? `已手動停止，回測了 ${BTP.done}／${BTP.total} 個幣` : '';
    log('回測完成', BTP.done, '個幣', trades.length, '筆');
  } catch (e) { BTP.msg = '回測失敗：' + e.message; log(BTP.msg); }
  BTP.run = false; BTP.at = Date.now();
}

/* ---------------- 雙週結算報告 ---------------- */
// 把某一段期間「進場」的單，用固定本金照時間順序模擬一次；期末還沒出場的單，用結算當下的現價平倉
function simReport(list, start, end, cap) {
  const T = ST.trade, Q = ST.eq, feeR = Q.fee / 100;
  const tr = list.filter(c => c.et >= start && c.et < end && c.entry > 0).map(c => {
    const E = evalTrade(c);
    let xt = E.open ? 0 : E.exitAt, pnl = E.pnl, marked = false;
    if (E.open || !xt || xt > end) {
      // 期末還沒出場：歷史期間用那筆單自己記錄的「期末那個小時的收盤價」，最近一期用現價
      const h = Math.floor((end - c.et) / HOUR), hv = c.hc && h >= 1 ? c.hc[h - 1] : null, px = PX.map[c.pid];
      const cur = Number.isFinite(hv) && end < Date.now() - 2 * HOUR ? c.dir * hv * T.lev * 100 : px > 0 ? c.dir * (px / c.entry - 1) * T.lev * 100 : 0;
      pnl = E.st === 'win' ? Math.max(T.tp, cur) : cur; xt = end; marked = true;
    }
    if (xt <= c.et) xt = c.et + 1;                    // 進場同一刻就出場的單，出場要排在進場之後
    return { c, st: E.st, et: c.et, xt, pnl: Number.isFinite(pnl) ? pnl : 0, marked };
  });
  const ev = [];
  tr.forEach(t => { ev.push({ t: t.et, k: 0, x: t }); ev.push({ t: t.xt, k: 1, x: t }); });
  ev.sort((a, b) => a.t - b.t || b.k - a.k);
  let eq = cap, used = 0, open = 0, peak = cap, mdd = 0, low = cap, fees = 0;
  const R = { n: 0, skipped: 0, win: 0, fail: 0, timeout: 0, marked: 0, longN: 0, longPl: 0, shortN: 0, shortPl: 0 };
  const curve = [[start, cap]];
  for (const e of ev) {
    const t = e.x;
    if (e.k === 0) {
      const m = Q.mode === 'pct' ? eq * Q.amt / 100 : Q.amt;
      if (eq <= 0 || (Q.max && open >= Q.max) || used + m > eq) { t.skip = true; R.skipped++; continue; }
      t.m = m; used += m; open++; R.n++;
    } else {
      if (t.skip || !t.m) continue;
      const fee = t.m * T.lev * feeR * 2, pl = t.m * t.pnl / 100 - fee;
      eq += pl; fees += fee; used -= t.m; open--;
      if (t.marked) R.marked++; else if (t.st === 'win') R.win++; else if (t.st === 'timeout') R.timeout++; else R.fail++;
      if (t.c.dir > 0) { R.longN++; R.longPl += pl; } else { R.shortN++; R.shortPl += pl; }
      peak = Math.max(peak, eq); low = Math.min(low, eq); mdd = Math.max(mdd, peak > 0 ? (peak - eq) / peak : 0);
      curve.push([e.t, Math.round(eq * 100) / 100]);
    }
  }
  const step = Math.max(1, Math.ceil(curve.length / 150));             // 曲線最多存 150 個點
  const done = R.win + R.fail + R.timeout;
  return Object.assign(R, {
    cap, endCap: Math.round(eq * 100) / 100, pnl: Math.round((eq - cap) * 100) / 100, ret: Math.round((eq / cap - 1) * 10000) / 100,
    rate: done ? Math.round(R.win / done * 1000) / 10 : null, fees: Math.round(fees * 100) / 100, mdd: Math.round(mdd * 1000) / 10,
    low: Math.round(low * 100) / 100, longPl: Math.round(R.longPl * 100) / 100, shortPl: Math.round(R.shortPl * 100) / 100,
    curve: curve.filter((_, i) => i % step === 0 || i === curve.length - 1)
  });
}
const REP = { busy: false, msg: '' };
let RV = Date.now();
async function settle(manual) {
  if (REP.busy) return; REP.busy = true; REP.msg = '結算中：先回測這一期…';
  try {
    while (BTP.run) await sleep(2000);                 // 有回測正在跑就等它跑完
    const end = Date.now(), start = end - ST.rep.days * 24 * HOUR;
    await backtest(ST.rep.btN);
    const r = {
      id: end, start, end, manual: !!manual, cfg: { ...ST.eq, ...ST.trade, cap: ST.rep.cap, btN: ST.rep.btN },
      bt: simReport(ST.bt.trades, start, end, ST.rep.cap), live: simReport(ST.cards, start, end, ST.rep.cap)
    };
    ST.reports.unshift(r); ST.reports = ST.reports.slice(0, 60);
    if (!manual) ST.rep.next = end + ST.rep.days * 24 * HOUR;
    RV++; dirty = true;
    log('結算完成', `回測 ${r.bt.endCap}U（${r.bt.n} 筆）`, `即時 ${r.live.endCap}U（${r.live.n} 筆）`);
    const sg = v => (v > 0 ? '+' : v < 0 ? '−' : '') + Math.abs(v).toFixed(2);
    if (ST.notify.enabled) dcSend(`📊 **雙週結算**（${tw(start)} ～ ${tw(end)}，每期本金 ${ST.rep.cap}U）\n` +
      `回測：${r.bt.endCap}U（**${sg(r.bt.pnl)}U**，${sg(r.bt.ret)}%），${r.bt.n} 筆，成功率 ${r.bt.rate ?? '—'}%\n` +
      `即時：${r.live.endCap}U（**${sg(r.live.pnl)}U**，${sg(r.live.ret)}%），${r.live.n} 筆，成功率 ${r.live.rate ?? '—'}%`);
    REP.msg = '';
  } catch (e) { REP.msg = '結算失敗：' + e.message; log(REP.msg); }
  REP.busy = false;
}
/* 歷史結算：一次往回抓很多期（例如 15 期 × 14 天 ≈ 7 個月），每期一樣用固定本金
   注意：幣安的持倉歷史只保留 30 天，所以更早的期間只用其他四項指標判斷 */
async function getRange(base, per, from, to) {
  const pages = [];
  for (let f = from; f < to; f += 1000 * per) pages.push(getJSON(`${base}&startTime=${f}&limit=1000`).catch(() => []));
  const m = new Map();
  (await Promise.all(pages)).flat().forEach(r => m.set(+r[0], r));
  return [...m.values()].sort((a, b) => a[0] - b[0]);
}
async function historyReports(periods) {
  if (REP.busy) throw new Error('正在結算中，請稍等');
  REP.busy = true;
  try {
    while (BTP.run) await sleep(2000);
    const D = ST.rep.days * 24 * HOUR, live = ST.reports.filter(r => !r.hist).sort((a, b) => a.start - b.start);
    const anchor = live.length ? live[0].start : Date.now();          // 接在第一期正式結算之前，避免重疊
    const t0 = anchor - periods * D, from = t0 - 8 * 24 * HOUR;       // 多抓 8 天當作比較基準
    const S = ST.set, W = S.win, cap = ST.rep.cap, now = Date.now();
    const uni = await BN.universe();
    const list = uni.sort((a, b) => b.qv - a.qv).slice(0, ST.rep.btN || uni.length);
    const trades = []; let idx = 0, done = 0;
    const one = async u => {
      const kr = await getRange(`${BF}/fapi/v1/klines?symbol=${u.id}&interval=1h`, HOUR, from, anchor);
      const k = kr.map(r => ({ t: +r[0], o: +r[1], h: +r[2], l: +r[3], c: +r[4], qv: +r[7], d: 2 * +r[10] - +r[7] }));
      const n = k.length; if (n < 200) return;
      const sr = u.spot ? await getRange(`${BS}/api/v3/klines?symbol=${u.spot}&interval=1h`, HOUR, from, anchor) : [];
      const sm = new Map(sr.map(r => [+r[0], 2 * +r[10] - +r[7]]));
      const fd = k.map(x => x.d), sdv = sr.length ? k.map(x => sm.has(x.t) ? sm.get(x.t) : NaN) : null;
      const sig = [];
      for (let i = 168; i <= n - 2; i++) {
        if (k[i].t + HOUR < t0) continue;
        let hi = -Infinity, lo = Infinity, qv = 0;
        for (let j = i - 23; j <= i; j++) { hi = Math.max(hi, k[j].h); lo = Math.min(lo, k[j].l); qv += k[j].qv; }
        const chg = (k[i].c / k[i - 23].o - 1) * 100, amp = (hi - lo) / lo * 100, pc = (k[i].c / k[i - W].c - 1) * 100;
        if (Math.abs(chg) > S.flat || amp > S.range || qv < S.minVol * 1e4 || Math.abs(pc) > S.flat) continue;
        const Dt = detect(fd.slice(i - 167, i + 1), null, sdv ? sdv.slice(i - 167, i + 1) : null, W);
        if (Dt) sig.push({ i, D: Dt });
      }
      if (!sig.length) return;
      const br = await getRange(`${BF}/fapi/v1/klines?symbol=${u.id}&interval=15m`, 900000, k[sig[0].i].t + HOUR, now);
      const bars = br.map(x => ({ t: +x[0], h: +x[2], l: +x[3], c: +x[4] })).filter(b => b.t + 900000 <= now);
      let free = 0;
      for (const { i, D: Dt } of sig) {
        const et = k[i].t + HOUR; if (et < free) continue;
        const tr = { bt: 1, sym: u.sym, pid: u.id, dir: Dt.dir, abN: Dt.abN, et, entry: k[i].c, recs: [], fav: 0, adv: 0, end: 0, step: 900000 };
        const seg = bars.filter(b => b.t >= et && b.t - et < TRACK_MAX);
        extend(tr, seg); hourClose(tr, tr, seg, 900000);
        delete tr.fav; delete tr.adv;
        trades.push(tr);
        const E = evalTrade(tr); free = E.open ? Infinity : E.exitAt;
      }
    };
    const worker = async () => {
      while (idx < list.length) {
        const u = list[idx++];
        try { await Promise.race([one(u), new Promise((_, no) => setTimeout(() => no(new Error('timeout')), 240000))]); } catch (e) {}
        done++; REP.msg = `歷史回測中：${done}／${list.length} 個幣，已找到 ${trades.length} 筆訊號…（大約 5～10 分鐘）`;
      }
    };
    await Promise.all(Array.from({ length: 4 }, worker));
    const out = [];
    for (let p = 0; p < periods; p++) {
      const start = t0 + p * D, end = start + D;
      out.push({ id: end, start, end, hist: true, cfg: { ...ST.eq, ...ST.trade, cap, btN: ST.rep.btN, noOI: end < now - 30 * 24 * HOUR }, bt: simReport(trades, start, end, cap), live: null });
    }
    ST.reports = ST.reports.filter(r => !r.hist).concat(out).sort((a, b) => b.end - a.end).slice(0, 80);
    if (!live.length) ST.rep.next = anchor + D;                       // 下一次正式結算接在歷史的後面
    RV++; dirty = true; REP.msg = '';
    log('歷史結算完成', periods, '期', trades.length, '筆');
  } catch (e) { REP.msg = '歷史結算失敗：' + e.message; log(REP.msg); }
  REP.busy = false;
}
// 每分鐘檢查一次；第一次啟動時馬上結算一期（回測剛好就是最近 14 天），之後每 14 天一次
setInterval(() => { if (!REP.busy && Date.now() >= (ST.rep.next || 0)) settle(false); }, 60000);

/* ---------------- Bitunix 持倉（唯讀） ---------------- */
// 簽名：digest = SHA256(nonce + timestamp + apiKey + 排序後的 query 參數 + body)；sign = SHA256(digest + secret)
const BXAPI = process.env.BITUNIX_API || 'https://fapi.bitunix.com';
const sha = x => crypto.createHash('sha256').update(x, 'utf8').digest('hex');
async function bxGet(path, params = {}, cfg = ST.bx) {
  const keys = Object.keys(params).sort();
  const qs = keys.map(k => k + params[k]).join(''), url = BXAPI + path + (keys.length ? '?' + keys.map(k => `${k}=${encodeURIComponent(params[k])}`).join('&') : '');
  const nonce = crypto.randomBytes(16).toString('hex'), ts = String(Date.now());
  const sign = sha(sha(nonce + ts + cfg.key + qs) + cfg.secret);
  const r = await fetch(url, { headers: { 'api-key': cfg.key, nonce, timestamp: ts, sign, language: 'en-US', 'Content-Type': 'application/json' }, signal: AbortSignal.timeout(15000) });
  const j = await r.json().catch(() => ({}));
  if (!r.ok || j.code !== 0) throw new Error(j.msg ? `Bitunix：${j.msg}（${j.code}）` : 'Bitunix HTTP ' + r.status);
  return j.data;
}
const BX = { pos: [], acct: null, at: 0, err: '', seeded: false, warned: {} };
const num = v => { const n = +v; return Number.isFinite(n) ? n : 0; };
const bxEquity = () => { const A = BX.acct; return A ? A.avail + A.frozen + A.margin + A.cross + A.iso : 0; };
async function bxPoll() {
  const C = ST.bx; if (!C.key || !C.secret) { BX.pos = []; BX.acct = null; BX.err = ''; return; }
  try {
    const data = await bxGet('/api/v1/futures/position/get_pending_positions');
    const acct = await bxGet('/api/v1/futures/account', { marginCoin: 'USDT' }).catch(() => null);
    const pos = (Array.isArray(data) ? data : []).map(p => ({
      id: String(p.positionId), sym: p.symbol, dir: p.side === 'LONG' ? 1 : -1, qty: num(p.qty), lev: num(p.leverage), mode: p.marginMode,
      entry: num(p.avgOpenPrice), margin: num(p.margin), upnl: num(p.unrealizedPNL), rpnl: num(p.realizedPNL), fee: num(p.fee), funding: num(p.funding),
      liq: num(p.liqPrice), ctime: num(p.ctime), mtime: num(p.mtime), pmode: p.positionMode
    }));
    const prev = new Map(BX.pos.map(p => [p.id, p])), now = new Map(pos.map(p => [p.id, p]));
    if (BX.seeded && C.notify && ST.notify.enabled) {                 // 第一次讀到的持倉不算「新開倉」
      const botPos = p => ST.ltTrades.some(t => t.positionId === p.id || (t.sym === p.sym && t.dir === p.dir && Date.now() - t.et < 60000));   // 自動交易的單另外通知
      for (const p of pos) if (!prev.has(p.id) && !botPos(p)) dcSend(`📥 **Bitunix 開倉** ${p.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(p.sym)}**\n開倉價 ${fpx(p.entry)}・${p.lev}x ${p.mode === 'CROSS' ? '全倉' : '逐倉'}・數量 ${p.qty}・保證金 ${p.margin.toFixed(2)}U${p.liq > 0 ? `\n強平價 ${fpx(p.liq)}` : ''}`);
      for (const p of BX.pos) if (!now.has(p.id) && !botPos(p)) dcSend(`📤 **Bitunix 平倉** ${p.dir > 0 ? '做多' : '做空'} **${mdEsc(p.sym)}**\n開倉價 ${fpx(p.entry)}・${p.lev}x\n平倉前最後一次讀到的未實現損益 **${p.upnl >= 0 ? '+' : '−'}${Math.abs(p.upnl).toFixed(2)}U**（實際以交易所為準）`);
    }
    if (C.liq && ST.notify.enabled) for (const p of pos) {           // 現價離強平價太近就提醒（30 分鐘最多一次）
      const px = PX.map[p.sym]; if (!(px > 0 && p.liq > 0)) continue;
      const d = Math.abs(px - p.liq) / px * 100;
      if (d <= C.liqPct && Date.now() - (BX.warned[p.id] || 0) > 30 * 60000) {
        BX.warned[p.id] = Date.now();
        dcSend(`⚠️ **快爆倉了** ${p.dir > 0 ? '做多' : '做空'} **${mdEsc(p.sym)}**：現價 ${fpx(px)}，強平價 ${fpx(p.liq)}，只差 **${d.toFixed(2)}%**`);
      }
    }
    BX.pos = pos; BX.at = Date.now(); BX.err = ''; BX.seeded = true;
    await ltReconcile(pos);
    if (acct) { const a = Array.isArray(acct) ? acct[0] : acct; BX.acct = a ? { avail: num(a.available), frozen: num(a.frozen), margin: num(a.margin), cross: num(a.crossUnrealizedPNL), iso: num(a.isolationUnrealizedPNL), bonus: num(a.bonus) } : null; }
    const eqNow = bxEquity();
    if (!(ST.lt.startCap > 0) && eqNow > 0) {           // 第一次看到帳戶有錢：實盤統計就從這個金額、這個時間開始
      ST.lt.startCap = Math.round(eqNow * 100) / 100; ST.lt.startAt = Date.now(); touchLT();
      dcSend(`💰 偵測到 Bitunix 帳戶資金 **${ST.lt.startCap}U**，實盤統計從現在開始計算`);
    }
  } catch (e) { BX.err = e.message; }
}
setInterval(bxPoll, 10000); setTimeout(bxPoll, 3000);

/* ================= 自動下單（Bitunix 實盤） =================
   • 新訊號出現時，用市價開倉；開倉單同時帶交易所止損（失敗線），伺服器掛掉也有保護
   • 伺服器每 3 秒看一次價格：碰到成功線＝保本鎖利（或固定出場）；跑回成功線、持有到期、碰到失敗線就平倉
   • 每 10 秒對一次交易所持倉：手動平倉、部分平倉、交易所止損、強平都會被記錄下來
   • 預設暫停；單日虧損超過上限自動暫停；伺服器重開也會先暫停 */
const LT = { pairs: new Map(), pairsAt: 0, lev: {}, busy: new Set(), msg: '', dayHit: '' };
let LTV = Date.now();
const touchLT = () => { LTV++; dirty = true; };
async function bxPost(path, body, cfg = ST.bx) {
  const b = JSON.stringify(body), nonce = crypto.randomBytes(16).toString('hex'), ts = String(Date.now());
  const sign = sha(sha(nonce + ts + cfg.key + b) + cfg.secret);
  const r = await fetch(BXAPI + path, { method: 'POST', headers: { 'api-key': cfg.key, nonce, timestamp: ts, sign, language: 'en-US', 'Content-Type': 'application/json' }, body: b, signal: AbortSignal.timeout(15000) });
  const j = await r.json().catch(() => ({}));
  if (!r.ok || j.code !== 0) throw new Error(j.msg ? `${j.msg}（${j.code}）` : 'HTTP ' + r.status);
  return j.data;
}
async function ltPair(sym) {
  if (Date.now() - LT.pairsAt > HOUR || !LT.pairs.size) {
    const r = await fetch(BXAPI + '/api/v1/futures/market/trading_pairs', { signal: AbortSignal.timeout(15000) }).then(x => x.json());
    if (r && r.code === 0 && Array.isArray(r.data)) { LT.pairs = new Map(r.data.map(x => [x.symbol, x])); LT.pairsAt = Date.now(); }
  }
  return LT.pairs.get(sym) || null;
}
const fl = (v, d) => { const m = 10 ** d; return Math.floor(v * m + 1e-9) / m; };
const pxStr = (v, d) => (+v).toFixed(Math.max(0, Math.min(10, d)));
const ltOpenTrades = () => ST.ltTrades.filter(t => t.status === 'open');
function ltNet(t) { return (t.realized || 0) - Math.abs(t.fee || 0) + (t.funding || 0); }   // 已實現損益－手續費＋資金費
async function ltOpen(c) {
  const C = ST.lt;
  if (!C.on || !ST.bx.key || !ST.bx.secret || LT.busy.has(c.sym)) return;
  LT.busy.add(c.sym);
  try {
    if (C.maxOpen && ltOpenTrades().length >= C.maxOpen) { LT.msg = `已達最多同時持倉 ${C.maxOpen} 筆，${c.sym} 這次不下單`; return; }
    if (BX.pos.some(p => p.sym === c.sym) || ltOpenTrades().some(t => t.sym === c.sym)) return;   // 這個幣已經有倉位
    const pr = await ltPair(c.sym);
    if (!pr) { LT.msg = `Bitunix 沒有 ${c.sym}，略過`; return; }
    if (pr.symbolStatus !== 'OPEN') { LT.msg = `${c.sym} 在 Bitunix 暫停交易，略過`; return; }
    const px = PX.map[c.sym] || c.last, lev = Math.max(1, Math.min(C.lev, +pr.maxLeverage || C.lev));
    if (BX.acct && BX.acct.avail < C.margin * 1.2) { LT.msg = `可用餘額不足（${BX.acct.avail.toFixed(2)}U），${c.sym} 不下單`; return; }
    const qty = fl(C.margin * lev / px, +pr.basePrecision || 0);
    if (!(qty > 0) || qty < +pr.minTradeVolume) { LT.msg = `${c.sym} 用 ${C.margin}U×${lev}x 買不到最小下單量（${pr.minTradeVolume}），略過`; dcSend(`⏭️ ${mdEsc(c.sym)} 下單量太小，略過（最小 ${pr.minTradeVolume}，需要的保證金比 ${C.margin}U 多）`); return; }
    const key = C.mode + lev;
    if (LT.lev[c.sym] !== key) {
      await bxPost('/api/v1/futures/account/change_margin_mode', { marginMode: C.mode, symbol: c.sym, marginCoin: 'USDT' }).catch(() => {});
      await bxPost('/api/v1/futures/account/change_leverage', { symbol: c.sym, leverage: lev, marginCoin: 'USDT' });
      LT.lev[c.sym] = key;
    }
    const T = ST.trade, slPx = px * (1 - c.dir * T.sl / 100 / lev), qp = +pr.quotePrecision || 4;
    const base = { symbol: c.sym, qty: String(qty), side: c.dir > 0 ? 'BUY' : 'SELL', tradeSide: 'OPEN', orderType: 'MARKET', clientId: 'q' + Date.now().toString(36) };
    let o, exSL = true;
    try { o = await bxPost('/api/v1/futures/trade/place_order', { ...base, slPrice: pxStr(slPx, qp), slStopType: 'MARK_PRICE', slOrderType: 'MARKET' }); }
    catch (e) {                                       // 帶止損失敗就改成不帶，止損改由伺服器監控
      if (!/sl|stop|price/i.test(e.message)) throw e;
      exSL = false; o = await bxPost('/api/v1/futures/trade/place_order', base);
    }
    await sleep(1500);
    const ps = await bxGet('/api/v1/futures/position/get_pending_positions', { symbol: c.sym }).catch(() => []);
    const p = (ps || []).find(x => (x.side === 'LONG') === (c.dir > 0));
    const t = {
      id: 'lt-' + Date.now(), sym: c.sym, dir: c.dir, card: c.id, abN: c.abN, et: Date.now(), lev,
      entry: p ? num(p.avgOpenPrice) : px, qty: p ? num(p.qty) : qty, qty0: p ? num(p.qty) : qty, margin: p ? num(p.margin) : C.margin, m0: p ? num(p.margin) || C.margin : C.margin,
      positionId: p ? String(p.positionId) : '', orderId: o && o.orderId, status: 'open', realized: 0, fee: p ? num(p.fee) : 0, funding: 0, closes: [], locked: false, fav: 0, adv: 0, exSL, prec: +pr.basePrecision || 0, minQty: +pr.minTradeVolume || 0
    };
    ST.ltTrades.unshift(t); ST.ltTrades = ST.ltTrades.slice(0, 2000); touchLT();
    log('自動開倉', c.sym, c.dir > 0 ? '做多' : '做空', qty, '@', t.entry);
    dcSend(`🤖 **自動開倉** ${c.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(c.sym)}**\n成交價 ${fpx(t.entry)}・${lev}x 全倉・數量 ${t.qty}・保證金約 ${t.margin.toFixed(2)}U\n${exSL ? `交易所止損 ${fpx(slPx)}（−${T.sl}%）` : '⚠️ 交易所止損沒設成功，改由伺服器監控'}`);
  } catch (e) { LT.msg = `${c.sym} 自動下單失敗：${e.message}`; log(LT.msg); dcSend(`❗ **自動下單失敗** ${mdEsc(c.sym)}：${mdEsc(e.message)}`); }
  finally { LT.busy.delete(c.sym); }
}
// 平倉：pct＝1 全部（閃電平倉）；其他比例用市價平倉單
async function ltClosePos(positionId, pct, reason) {
  const p = BX.pos.find(x => x.id === positionId);
  if (!p) throw new Error('找不到這筆持倉，可能已經平倉了');
  const t = ST.ltTrades.find(x => x.status === 'open' && x.positionId === positionId);
  if (t) { t.pendReason = reason; t.pendAt = Date.now(); }
  if (pct >= 0.999) { await bxPost('/api/v1/futures/trade/flash_close_position', { positionId }); return 'full'; }
  const pr = await ltPair(p.sym), prec = pr ? +pr.basePrecision || 0 : (t ? t.prec : 0), minQ = pr ? +pr.minTradeVolume || 0 : 0;
  let q = fl(p.qty * pct, prec);
  if (!(q > 0) || q < minQ) throw new Error(`這個比例平倉數量太小（最少 ${minQ}）`);
  if (p.qty - q < minQ) { await bxPost('/api/v1/futures/trade/flash_close_position', { positionId }); return 'full'; }
  const body = p.pmode === 'HEDGE'
    ? { symbol: p.sym, qty: String(q), side: p.dir > 0 ? 'BUY' : 'SELL', tradeSide: 'CLOSE', positionId, orderType: 'MARKET' }      // 官方文件：雙向持倉平多用 BUY＋CLOSE
    : { symbol: p.sym, qty: String(q), side: p.dir > 0 ? 'SELL' : 'BUY', orderType: 'MARKET', reduceOnly: true };
  await bxPost('/api/v1/futures/trade/place_order', body);
  await sleep(1500);                                  // 安全檢查：倉位如果反而變大，代表方向錯了，立刻全平並暫停
  const ps = await bxGet('/api/v1/futures/position/get_pending_positions', { symbol: p.sym }).catch(() => null);
  const n = ps && ps.find(x => String(x.positionId) === positionId);
  if (n && num(n.qty) > p.qty + 1e-12) {
    await bxPost('/api/v1/futures/trade/flash_close_position', { positionId }).catch(() => {});
    ST.lt.on = false; touchLT();
    dcSend(`🚨 **部分平倉異常**：${mdEsc(p.sym)} 倉位變大，已全部平倉並暫停自動交易，請檢查交易所`);
    throw new Error('部分平倉後倉位變大，已緊急全部平倉並暫停自動交易');
  }
  return 'part';
}
// 每 3 秒：照規則管理自動開的單
async function ltManage() {
  const T = ST.trade, now = Date.now();
  for (const t of ltOpenTrades()) {
    const px = PX.map[t.sym]; if (!(px > 0) || !t.positionId || t.closing) continue;
    const roe = t.dir * (px / t.entry - 1) * t.lev * 100;
    t.cur = px; t.roe = roe; t.fav = Math.max(t.fav || 0, roe); t.adv = Math.min(t.adv || 0, roe);
    let why = '';
    if (roe <= -T.sl) why = 'fail';
    else if (roe >= T.tp) { if (T.exit === 'fixed') why = 'win'; else if (!t.locked) { t.locked = true; touchLT(); dcSend(`🔒 **達標鎖利** ${mdEsc(t.sym)}：浮盈 +${roe.toFixed(0)}%，之後跑回 +${T.tp}% 就平倉`); } }
    else if (t.locked && roe < T.tp) why = 'lock';
    if (!why && now - t.et >= T.hold * HOUR) why = 'timeout';
    if (!why) continue;
    t.closing = true;
    try { await ltClosePos(t.positionId, 1, why); }
    catch (e) { dcSend(`❗ **自動平倉失敗** ${mdEsc(t.sym)}：${mdEsc(e.message)}`); }
    t.closing = false;
  }
}
// 每 10 秒：跟交易所的持倉對帳
async function ltReconcile(pos) {
  const byId = new Map(pos.map(p => [p.id, p])); let ch = false;
  for (const t of ltOpenTrades()) {
    let p = t.positionId ? byId.get(t.positionId) : pos.find(x => x.sym === t.sym && x.dir === t.dir);
    if (p && !t.positionId) { t.positionId = p.id; t.entry = p.entry; t.qty = t.qty0 = p.qty; t.m0 = p.margin || t.m0; ch = true; }
    if (p) {
      if (p.qty < t.qty - 1e-12) {                    // 部分平倉（網站或交易所 App）
        const pnl = p.rpnl - (t.realized || 0);
        t.closes.push({ t: Date.now(), qty: t.qty - p.qty, pnl, by: t.pendReason || 'manual' });
        dcSend(`✂️ **部分平倉** ${mdEsc(t.sym)}：平掉 ${(t.qty - p.qty).toPrecision(6)}，這次已實現 ${pnl >= 0 ? '+' : '−'}${Math.abs(pnl).toFixed(2)}U`);
        t.pendReason = '';
      }
      Object.assign(t, { qty: p.qty, realized: p.rpnl, fee: p.fee, funding: p.funding, upnl: p.upnl, margin: p.margin || t.margin, liq: p.liq }); ch = true;
      continue;
    }
    if (!t.positionId && Date.now() - t.et < 60000) continue;
    // 倉位不見了＝已平倉：去歷史持倉拿最後的結果
    let h = null;
    try { const r = await bxGet('/api/v1/futures/position/get_history_positions', t.positionId ? { positionId: t.positionId } : { symbol: t.sym, limit: 5 }); h = (r && r.positionList || []).find(x => !t.positionId || String(x.positionId) === t.positionId) || null; } catch (e) {}
    const reason = t.pendReason || (h && num(h.liqQty) > 0 ? 'liq' : 'exchange');
    if (h) Object.assign(t, { realized: num(h.realizedPNL), fee: num(h.fee), funding: num(h.funding), closePx: num(h.closePrice) });
    const prevPart = t.closes.reduce((a, c) => a + c.pnl, 0);
    t.closes.push({ t: Date.now(), qty: t.qty, pnl: (t.realized || 0) - prevPart, by: reason });
    Object.assign(t, { status: 'closed', exitAt: Date.now(), reason, qty: 0, upnl: 0 }); ch = true;
    const net = ltNet(t), nm = { win: '✅ 達標出場', lock: '🔒 保本鎖利出場', fail: '❌ 失敗線出場', timeout: '⏱ 持有到期出場', manual: '🖐 手動平倉', all: '🛑 一鍵全部平倉', liq: '💥 強平', exchange: '📤 交易所平倉（止損或在 App 平倉）' }[reason] || reason;
    dcSend(`${nm} **${mdEsc(t.sym)}** ${t.dir > 0 ? '做多' : '做空'}\n淨損益 **${net >= 0 ? '+' : '−'}${Math.abs(net).toFixed(2)}U**（${(net / (t.m0 || ST.lt.margin) * 100).toFixed(0)}%）・持有 ${durTxt(Date.now() - t.et)}${t.closePx ? `・平倉均價 ${fpx(t.closePx)}` : ''}`);
  }
  // 單日虧損上限（台北時間每天 00:00 重算）
  const day = new Date(Date.now() + TZ).toISOString().slice(0, 10), d0 = Date.parse(day + 'T00:00:00Z') - TZ;
  let dayPnl = 0;
  for (const t of ST.ltTrades) { for (const c of t.closes || []) if (c.t >= d0) dayPnl += c.pnl; if (t.status === 'open') dayPnl += t.upnl || 0; }
  LT.dayPnl = dayPnl;
  if (ST.lt.on && ST.lt.dayLoss > 0 && dayPnl <= -ST.lt.dayLoss && LT.dayHit !== day) {
    LT.dayHit = day; ST.lt.on = false; ch = true;
    dcSend(`🛑 **今天虧損 ${dayPnl.toFixed(2)}U，超過上限 ${ST.lt.dayLoss}U，自動交易已暫停**（已開的單照常管理，可以在網站重新開始）`);
  }
  if (ch) touchLT();
}

/* ---------------- 匯入（網頁的「匯出紀錄」檔） ---------------- */
function importData(data) {
  const inCards = Array.isArray(data.quantCards) ? data.quantCards : [];
  const inBT = data.quantBT && Array.isArray(data.quantBT.trades) ? data.quantBT : { trades: [] };
  const cm = new Map(ST.cards.map(c => [c.id, c]));
  inCards.forEach(c => { if (!c || !c.id) return; const o = cm.get(c.id); if (!o || (c.t || 0) > (o.t || 0) || ((c.trk && c.trk.end) || 0) > ((o.trk && o.trk.end) || 0)) cm.set(c.id, c); });
  ST.cards = [...cm.values()].sort((a, b) => (b.t || 0) - (a.t || 0)).slice(0, 300);
  const bm = new Map(ST.bt.trades.map(t => [t.id, t]));
  inBT.trades.forEach(t => { if (!t || !t.id) return; const o = bm.get(t.id); if (!o || (t.end || 0) > (o.end || 0)) bm.set(t.id, t); });
  ST.bt = { at: Math.max(ST.bt.at || 0, inBT.at || 0), coins: Math.max(ST.bt.coins || 0, inBT.coins || 0), trades: [...bm.values()].sort((a, b) => b.et - a.et).slice(0, 4000) };
  touchCards(); touchBT();
  return { cards: ST.cards.length, trades: ST.bt.trades.length };
}

/* ---------------- HTTP API ---------------- */
function send(res, code, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(code, {
    'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store',
    'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type, X-Key, Authorization', 'Access-Control-Allow-Methods': 'GET, POST, OPTIONS'
  });
  res.end(body);
}
/* ---------------- 登入：Bitunix UID ＋ 密碼 ---------------- */
// 密碼用 scrypt 加鹽雜湊後才存；登入憑證只存雜湊；同一個 IP 連續輸錯 5 次鎖 15 分鐘
const SESSION_DAYS = 30;
const hashPw = (pw, salt = crypto.randomBytes(16).toString('hex')) => ({ salt, hash: crypto.scryptSync(pw, salt, 64).toString('hex') });
const pwOk = (u, pw) => { const h = crypto.scryptSync(pw, u.salt, 64); const a = Buffer.from(u.hash, 'hex'); return a.length === h.length && crypto.timingSafeEqual(a, h); };
const tokHash = t => crypto.createHash('sha256').update(t).digest('hex');
const FAILS = new Map();
const ipOf = req => String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
function locked(ip) { const f = FAILS.get(ip); return f && f.n >= 5 && Date.now() - f.t < 15 * 60000; }
function failed(ip) { const f = FAILS.get(ip); FAILS.set(ip, { n: f && Date.now() - f.t < 15 * 60000 ? f.n + 1 : 1, t: Date.now() }); }
function newSession(u) {
  const token = crypto.randomBytes(32).toString('hex'), now = Date.now();
  ST.sessions = ST.sessions.filter(x => x.exp > now).slice(-200);
  ST.sessions.push({ h: tokHash(token), uid: u.uid, exp: now + SESSION_DAYS * 24 * HOUR });
  u.last = now; dirty = true;
  return token;
}
function who(req) {                                   // 回傳登入的使用者（沒登入回 null）
  const m = String(req.headers.authorization || '').match(/^Bearer\s+([0-9a-f]{64})$/i); if (!m) return null;
  const h = tokHash(m[1]), s = ST.sessions.find(x => x.h === h && x.exp > Date.now()); if (!s) return null;
  return ST.users.find(u => u.uid === s.uid) || null;
}
const validUid = x => /^\d{4,20}$/.test(String(x || ''));
const validPw = x => typeof x === 'string' && x.length >= 8 && x.length <= 128;
function keyOk(req) {
  if (!ADMIN_KEY) return false;
  const k = Buffer.from(String(req.headers['x-key'] || '')), a = Buffer.from(ADMIN_KEY);
  return k.length === a.length && crypto.timingSafeEqual(k, a);
}
function readBody(req, max = 30e6) {
  return new Promise((ok, no) => {
    let n = 0; const parts = [];
    req.on('data', d => { n += d.length; if (n > max) { no(new Error('資料太大')); req.destroy(); } else parts.push(d); });
    req.on('end', () => { try { ok(parts.length ? JSON.parse(Buffer.concat(parts).toString('utf8')) : {}); } catch (e) { no(new Error('JSON 格式錯誤')); } });
    req.on('error', no);
  });
}
const pick = (o, keys) => Object.fromEntries(keys.filter(k => o[k] !== undefined).map(k => [k, o[k]]));
http.createServer(async (req, res) => {
  try {
    if (req.method === 'OPTIONS') return send(res, 204, {});
    const u = new URL(req.url, 'http://x');
    if (req.method === 'GET' && u.pathname === '/api/ping') return send(res, 200, { ok: true, time: Date.now() });
    if (req.method === 'GET' && u.pathname === '/api/auth') return send(res, 200, { needSetup: !ST.users.length });
    if (req.method === 'POST' && ['/api/login', '/api/setup', '/api/logout'].includes(u.pathname)) {
      const ip = ipOf(req), b = await readBody(req, 1e5);
      if (u.pathname === '/api/logout') { const m = String(req.headers.authorization || '').match(/^Bearer\s+(\w+)$/); if (m) { const h = tokHash(m[1]); ST.sessions = ST.sessions.filter(x => x.h !== h); dirty = true; } return send(res, 200, { ok: true }); }
      if (locked(ip)) return send(res, 429, { error: '輸錯太多次，請 15 分鐘後再試' });
      if (u.pathname === '/api/setup') {                // 第一次使用：用管理金鑰建立第一個管理員帳號
        if (ST.users.length) return send(res, 400, { error: '已經設定過了，請直接登入' });
        if (!keyOk({ headers: { 'x-key': b.key } })) { failed(ip); return send(res, 401, { error: '管理金鑰不對' }); }
        if (!validUid(b.uid)) return send(res, 400, { error: 'UID 應該是 4～20 位數字' });
        if (!validPw(b.password)) return send(res, 400, { error: '密碼至少 8 個字' });
        const usr = { uid: String(b.uid), role: 'admin', ...hashPw(b.password), created: Date.now() };
        ST.users.push(usr); log('建立管理員帳號', usr.uid);
        return send(res, 200, { token: newSession(usr), uid: usr.uid, role: usr.role });
      }
      const usr = ST.users.find(x => x.uid === String(b.uid || ''));
      if (!usr || !validPw(b.password) || !pwOk(usr, b.password)) { failed(ip); return send(res, 401, { error: 'UID 或密碼不對' }); }
      FAILS.delete(ip);
      return send(res, 200, { token: newSession(usr), uid: usr.uid, role: usr.role });
    }
    const me = who(req), admin = keyOk(req) || (me && me.role === 'admin');
    if (u.pathname.startsWith('/api/') && !me && !keyOk(req)) return send(res, 401, { error: '請先登入', needLogin: true, needSetup: !ST.users.length });
    if (req.method === 'GET' && u.pathname === '/api/me') return send(res, 200, { uid: me ? me.uid : '管理金鑰', role: admin ? 'admin' : 'viewer' });
    if (req.method === 'GET' && u.pathname === '/api/users') {
      if (!admin) return send(res, 403, { error: '只有管理員可以看' });
      return send(res, 200, { users: ST.users.map(x => ({ uid: x.uid, role: x.role, created: x.created, last: x.last || 0, sessions: ST.sessions.filter(s => s.uid === x.uid && s.exp > Date.now()).length })) });
    }
    if (req.method === 'GET' && u.pathname === '/api/state') {
      const out = {
        time: Date.now(), cv: CV, bv: BV, set: ST.set, trade: ST.trade, canWrite: !!ADMIN_KEY,
        scan: { ...SCAN, pause: RL.pause }, bt: { at: ST.bt.at, coins: ST.bt.coins, n: ST.bt.trades.length }, btp: BTP,
        notify: { enabled: ST.notify.enabled, entry: ST.notify.entry, exit: ST.notify.exit, hasHook: !!ST.notify.webhook, name: ST.notify.name },
        eq: ST.eq, rep: { ...ST.rep, busy: REP.busy, msg: REP.msg }, rv: RV,
        bx: { set: !!(ST.bx.key && ST.bx.secret), notify: ST.bx.notify, liq: ST.bx.liq, liqPct: ST.bx.liqPct, at: BX.at, err: BX.err, acct: BX.acct,
          pos: BX.pos.map(p => ({ ...p, px: PX.map[p.sym] || null, sig: !!ST.cards.find(c => c.sym === p.sym && c.dir === p.dir && c.et && isLive(c)), bot: !!ST.ltTrades.find(t => t.status === 'open' && t.positionId === p.id) })) },
        lt: { cfg: ST.lt, msg: LT.msg, dayPnl: LT.dayPnl || 0, v: LTV }
      };
      if (+u.searchParams.get('cv') !== CV) out.cards = ST.cards;
      if (+u.searchParams.get('bv') !== BV) out.trades = ST.bt.trades;
      if (+u.searchParams.get('rv') !== RV) out.reports = ST.reports;
      if (+u.searchParams.get('lv') !== LTV) out.ltTrades = ST.ltTrades.map(({ closing, ...t }) => t);
      return send(res, 200, out);
    }
    if (req.method === 'POST' && u.pathname.startsWith('/api/')) {
      if (!admin) return send(res, 403, { error: '這個帳號沒有修改權限（需要管理員）' });
      const b = await readBody(req);
      if (u.pathname === '/api/users') {               // 後台：新增帳號／改密碼／改權限
        if (!validUid(b.uid)) return send(res, 400, { error: 'UID 應該是 4～20 位數字' });
        let usr = ST.users.find(x => x.uid === String(b.uid));
        if (!usr) { if (!validPw(b.password)) return send(res, 400, { error: '新帳號要設定密碼，至少 8 個字' }); usr = { uid: String(b.uid), role: 'viewer', created: Date.now() }; ST.users.push(usr); }
        if (b.password) { if (!validPw(b.password)) return send(res, 400, { error: '密碼至少 8 個字' }); Object.assign(usr, hashPw(b.password)); ST.sessions = ST.sessions.filter(s => s.uid !== usr.uid || (me && s.uid === me.uid)); }
        if (b.role === 'admin' || b.role === 'viewer') {
          if (b.role === 'viewer' && usr.role === 'admin' && ST.users.filter(x => x.role === 'admin').length <= 1) return send(res, 400, { error: '至少要留一個管理員' });
          usr.role = b.role;
        }
        dirty = true; return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/users/delete') {
        const usr = ST.users.find(x => x.uid === String(b.uid)); if (!usr) return send(res, 404, { error: '找不到這個帳號' });
        if (usr.role === 'admin' && ST.users.filter(x => x.role === 'admin').length <= 1) return send(res, 400, { error: '至少要留一個管理員' });
        ST.users = ST.users.filter(x => x !== usr); ST.sessions = ST.sessions.filter(s => s.uid !== usr.uid); dirty = true;
        return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/users/kick') { ST.sessions = ST.sessions.filter(s => s.uid !== String(b.uid)); dirty = true; return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/settings') {
        if (b.set) Object.assign(ST.set, pick(b.set, Object.keys(DEF_SET)));
        if (b.trade) Object.assign(ST.trade, pick(b.trade, Object.keys(DEF_TRADE)));
        if (b.eq) Object.assign(ST.eq, pick(b.eq, Object.keys(DEF_EQ)));
        if (b.rep) { const r = pick(b.rep, ['cap', 'btN']); if (r.cap > 0) ST.rep.cap = +r.cap; if (r.btN >= 0) ST.rep.btN = +r.btN; }
        dirty = true; CACHE.clear();
        if (b.trade) { markSettledNotified(); touchCards(); }   // 改了浮盈／槓桿，結果會重算；已結單的不要再發一次通知
        return send(res, 200, { ok: true, set: ST.set, trade: ST.trade, eq: ST.eq, rep: ST.rep });
      }
      if (u.pathname === '/api/backtest') { backtest(Math.max(0, +b.n || 0)); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/backtest/stop') { BTP.stop = true; return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/cards/delete') { ST.cards = ST.cards.filter(c => c.id !== b.id); touchCards(); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/import') return send(res, 200, { ok: true, ...importData(b) });
      if (u.pathname === '/api/check') return send(res, 200, { ok: true });
      if (u.pathname === '/api/bitunix') {
        const C = ST.bx;
        if (b.clear) { Object.assign(C, DEF_BX); BX.pos = []; BX.acct = null; BX.seeded = false; dirty = true; return send(res, 200, { ok: true }); }
        if (typeof b.key === 'string' && b.key.trim() && typeof b.secret === 'string' && b.secret.trim()) {
          const cfg = { ...C, key: b.key.trim(), secret: b.secret.trim() };
          try { await bxGet('/api/v1/futures/position/get_pending_positions', {}, cfg); }        // 先試一次，金鑰對了才存
          catch (e) { return send(res, 400, { error: e.message + '。請確認金鑰、密鑰沒有複製錯，而且 API 有綁定這台伺服器的 IP' }); }
          const changed = C.key !== cfg.key;
          C.key = cfg.key; C.secret = cfg.secret; BX.seeded = false; BX.pos = []; BX.acct = null;
          if (changed) { ST.lt.on = false; ST.lt.startCap = 0; ST.lt.startAt = Date.now(); LT.lev = {}; touchLT(); }   // 換帳號：先暫停，統計等讀到新帳戶的資金再開始
        }
        for (const k of ['notify', 'liq']) if (typeof b[k] === 'boolean') C[k] = b[k];
        if (+b.liqPct > 0) C.liqPct = +b.liqPct;
        dirty = true; bxPoll();
        return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/lt/config') {
        const C = ST.lt;
        if (typeof b.on === 'boolean') {
          if (b.on && !(ST.bx.key && ST.bx.secret)) return send(res, 400, { error: '請先設定 Bitunix API 金鑰（要開交易權限）' });
          C.on = b.on; dcSend(b.on ? '▶️ **自動交易已開始**' : '⏸ **自動交易已暫停**（已開的單照常管理）');
        }
        if (+b.margin > 0) C.margin = +b.margin;
        if (+b.lev >= 1 && +b.lev <= 125) C.lev = Math.round(+b.lev);
        if (+b.maxOpen >= 0) C.maxOpen = Math.round(+b.maxOpen);
        if (+b.dayLoss >= 0) C.dayLoss = +b.dayLoss;
        if (b.reset) { const e = bxEquity(); C.startAt = Date.now(); C.startCap = e > 0 ? Math.round(e * 100) / 100 : 0; }   // 用目前帳戶權益重新起算
        touchLT(); return send(res, 200, { ok: true, cfg: C });
      }
      if (u.pathname === '/api/lt/testOpen' && process.env.LT_TEST === '1') { await ltOpen({ id: 'test', sym: b.sym, dir: b.dir || 1, abN: 2, last: 1 }); return send(res, 200, { ok: true, msg: LT.msg }); }
      if (u.pathname === '/api/lt/close') {
        const pct = Math.min(1, Math.max(0.01, +b.pct || 1));
        try { const r = await ltClosePos(String(b.positionId), pct, 'manual'); setTimeout(bxPoll, 1500); return send(res, 200, { ok: true, r }); }
        catch (e) { return send(res, 400, { error: e.message }); }
      }
      if (u.pathname === '/api/lt/closeAll') {
        if (b.pause) ST.lt.on = false;
        for (const t of ltOpenTrades()) { t.pendReason = 'all'; t.pendAt = Date.now(); }
        try { await bxPost('/api/v1/futures/trade/close_all_position', {}); }
        catch (e) { return send(res, 400, { error: '一鍵平倉失敗：' + e.message }); }
        touchLT(); dcSend(`🛑 **一鍵全部平倉**${b.pause ? '，並暫停自動交易' : ''}`); setTimeout(bxPoll, 1500);
        return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/report/history') { if (REP.busy) return send(res, 409, { error: '正在結算中，請稍等' }); historyReports(Math.min(26, Math.max(1, +b.periods || 15))); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/report/settle') { if (REP.busy) return send(res, 409, { error: '正在結算中，請稍等' }); settle(true); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/notify') {
        const N = ST.notify;
        if (typeof b.webhook === 'string' && b.webhook.trim()) {
          const url = b.webhook.trim().replace(/\?.*$/, '');
          if (!DC_OK(url)) return send(res, 400, { error: 'Webhook 網址格式不對，應該是 https://discord.com/api/webhooks/ 開頭' });
          const r = await fetch(url, { signal: AbortSignal.timeout(15000) }).catch(() => null);   // 先確認這個 Webhook 真的存在
          const j = r ? await r.json().catch(() => ({})) : {};
          if (!r || !r.ok) return send(res, 400, { error: 'Discord 找不到這個 Webhook，可能被刪掉了或網址複製不完整' });
          N.webhook = url; N.name = j.name || 'Webhook';
        }
        for (const k of ['enabled', 'entry', 'exit']) if (typeof b[k] === 'boolean') N[k] = b[k];
        if (b.clear) Object.assign(N, DEF_NOTIFY);
        dirty = true;
        return send(res, 200, { ok: true, name: N.name });
      }
      if (u.pathname === '/api/notify/test') {
        const ok = await dcSend('🔔 **合約量化進場**：通知測試成功！之後每次有新訊號進場、結單，都會傳到這個頻道。');
        return ok ? send(res, 200, { ok: true }) : send(res, 400, { error: '傳送失敗，請確認 Webhook 網址有儲存成功' });
      }
    }
    send(res, 404, { error: 'not found' });
  } catch (e) { send(res, 500, { error: e.message }); }
}).listen(PORT, HOST, () => log(`伺服器啟動：http://${HOST}:${PORT}（${ADMIN_KEY ? '已設定' : '沒有設定'}管理金鑰）`));

/* ---------------- 主迴圈 ---------------- */
(async () => {
  try { await getJSON(BF + '/fapi/v1/ping'); log('幣安連線正常'); }
  catch (e) { log('連不到幣安：', e.message); }
  for (;;) {
    if (!BTP.run) await scan();
    await sleep(Math.max(3, ST.set.everyS || 10) * 1000);
  }
})();
setInterval(trackAll, 60000); setTimeout(trackAll, 5000);
setInterval(pollPx, 3000);

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
let ST = { cards: [], bt: { at: 0, coins: 0, trades: [] }, set: { ...DEF_SET }, trade: { ...DEF_TRADE } };
try {
  const j = JSON.parse(fs.readFileSync(FILE, 'utf8'));
  ST = { cards: j.cards || [], bt: j.bt || ST.bt, set: { ...DEF_SET, ...(j.set || {}) }, trade: { ...DEF_TRADE, ...(j.trade || {}) } };
  log(`讀入存檔：${ST.cards.length} 張卡片、${ST.bt.trades.length} 筆回測`);
} catch (e) { log('沒有存檔，從頭開始'); }
let CV = Date.now(), BV = Date.now();                  // 卡片、回測各自的版本號，沒變就不用重傳
let dirty = false;
const touchCards = () => { CV++; dirty = true; };
const touchBT = () => { BV++; dirty = true; };
function save() {
  if (!dirty) return; dirty = false;
  const tmp = FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(ST));
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
const COOL = HOUR;
function addCard(r) {
  const now = Date.now();
  r.why = reason(r);
  const i = ST.cards.findIndex(c => c.sym === r.sym && c.dir === r.dir && now - c.t < COOL && stillOpen(c));
  if (i >= 0 && now - ST.cards[i].t < 300000) { Object.assign(ST.cards[i], r); touchCards(); return; }   // 5 分鐘內重複：只更新數字
  let c;
  if (i >= 0) { c = Object.assign(ST.cards[i], r, { t: now, hits: (ST.cards[i].hits || 1) + 1 }); ST.cards.splice(i, 1); }
  else { c = Object.assign(r, { id: r.sym + '-' + now, t0: now, t: now, hits: 1, entry: r.last, et: now }); log('新訊號', r.sym, r.dir > 0 ? '做多' : '做空', r.abN + '/5'); }
  ST.cards.unshift(c);
  ST.cards = ST.cards.slice(0, 300);
  touchCards();
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
      const sig = []; let next = 0;
      for (const { i, chg, pc } of cand) {
        if (k[i].t < next) continue;
        const D = detect(fd.slice(i - 167, i + 1), c.oi ? oiv.slice(i - 167, i + 1) : null, sdv ? sdv.slice(i - 167, i + 1) : null, W);
        if (!D) continue;
        sig.push({ i, D, chg, pc }); next = k[i].t + 12 * HOUR;
      }
      if (!sig.length) return;
      await btBars(u, c, k[168].t + HOUR);
      const now = Date.now(), bars = c.b15.filter(b => b.t + 900000 <= now);
      for (const { i, D, chg, pc } of sig) {
        const et = k[i].t + HOUR;
        const tr = { id: 'bt-' + u.id + '-' + et, bt: 1, sym: u.sym, pid: u.id, spot: u.spot, src: 'binance', dir: D.dir, abN: D.abN, et, entry: k[i].c, recs: [], fav: 0, adv: 0, end: 0, step: 900000 };
        const seg = bars.filter(b => b.t >= et && b.t - et < TRACK_MAX);
        extend(tr, seg); hourClose(tr, tr, seg, 900000);
        delete tr.fav; delete tr.adv;
        Object.assign(tr, { ind: D.ind.map(x => ({ k: x.k, n: x.n, v: x.v === null ? null : (x.k === 'oi' ? r5(x.v) : Math.round(x.v)), z: x.z === null ? null : Math.round(x.z * 100) / 100, ab: x.ab })), chg, pc, win: W, logic: S.logic, unitOk: true, last: k[i].c });
        tr.why = reason(tr);
        trades.push(tr); BTP.found++;
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
    'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type, X-Key', 'Access-Control-Allow-Methods': 'GET, POST, OPTIONS'
  });
  res.end(body);
}
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
    if (req.method === 'GET' && u.pathname === '/api/state') {
      const out = {
        time: Date.now(), cv: CV, bv: BV, set: ST.set, trade: ST.trade, canWrite: !!ADMIN_KEY,
        scan: { ...SCAN, pause: RL.pause }, bt: { at: ST.bt.at, coins: ST.bt.coins, n: ST.bt.trades.length }, btp: BTP
      };
      if (+u.searchParams.get('cv') !== CV) out.cards = ST.cards;
      if (+u.searchParams.get('bv') !== BV) out.trades = ST.bt.trades;
      return send(res, 200, out);
    }
    if (req.method === 'POST' && u.pathname.startsWith('/api/')) {
      if (!ADMIN_KEY) return send(res, 403, { error: '伺服器沒有設定管理金鑰，不能修改' });
      if (!keyOk(req)) return send(res, 401, { error: '管理金鑰不對' });
      const b = await readBody(req);
      if (u.pathname === '/api/settings') {
        if (b.set) Object.assign(ST.set, pick(b.set, Object.keys(DEF_SET)));
        if (b.trade) Object.assign(ST.trade, pick(b.trade, Object.keys(DEF_TRADE)));
        dirty = true; CACHE.clear();
        return send(res, 200, { ok: true, set: ST.set, trade: ST.trade });
      }
      if (u.pathname === '/api/backtest') { backtest(Math.max(0, +b.n || 0)); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/backtest/stop') { BTP.stop = true; return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/cards/delete') { ST.cards = ST.cards.filter(c => c.id !== b.id); touchCards(); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/import') return send(res, 200, { ok: true, ...importData(b) });
      if (u.pathname === '/api/check') return send(res, 200, { ok: true });
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

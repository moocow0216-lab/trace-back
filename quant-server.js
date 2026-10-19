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
const DEF_TRADE = { tp: 250, sl: 250, lev: 100, hold: 24, exit: 'lock', step: 50 };   // step：達標後浮盈每多幾 %，鎖利線就往上調一格（0＝固定鎖在達標線）
// 鎖利線：最高浮盈 peak（%）→ 鎖在哪裡（%）。例：達標 250、間距 50 → 最高 260 鎖 250、最高 300 鎖 300、最高 349 鎖 300
const lockAt = (peak, T = ST.trade) => (T.step > 0 && peak > T.tp ? T.tp + Math.floor((peak - T.tp) / T.step + 1e-9) * T.step : T.tp);
const DEF_NOTIFY = { webhook: '', name: '', enabled: true, entry: true, exit: true };
const DEF_EQ = { mode: 'fixed', amt: 0.3, fee: 0.05, max: 0 };
const DEF_BX = { key: '', secret: '', notify: true, liq: true, liqPct: 3 };
const DEF_LT = { on: false, margin: 0.3, lev: 100, mode: 'CROSS', maxOpen: 0, dayLoss: 20, startCap: 0, startAt: 0, budget: 0, sl: 250, step: 50, hold: 168 };   // sl：浮虧多少 % 平倉；step：鎖利線每多幾 % 上調；hold：最長持有（小時）——每個帳號自己設定   // budget：投入資金（0＝整個合約帳戶）   // startCap＝0 代表等偵測到帳戶資金再開始算   // 自動下單（預設暫停）   // Bitunix 唯讀 API 金鑰（只存在這台伺服器）            // 資金模擬：每筆保證金、手續費、最多同時持倉
const DEF_REP = { cap: 100, btN: 50, days: 14, next: 0 };                   // 雙週結算：每期本金、回測幣數、幾天一期、下次結算時間
let ST = { cards: [], bt: { at: 0, coins: 0, trades: [] }, set: { ...DEF_SET }, trade: { ...DEF_TRADE }, google: { clientId: '' }, eq: { ...DEF_EQ }, rep: { ...DEF_REP }, reports: [], users: [], sessions: [], accts: {}, owner: '' };
try {
  const j = JSON.parse(fs.readFileSync(FILE, 'utf8'));
  ST = { cards: j.cards || [], bt: j.bt || ST.bt, set: { ...DEF_SET, ...(j.set || {}) }, trade: { ...DEF_TRADE, ...(j.trade || {}) }, google: { clientId: '', ...(j.google || {}) }, eq: { ...DEF_EQ, ...(j.eq || {}) }, rep: { ...DEF_REP, ...(j.rep || {}) }, reports: j.reports || [], users: j.users || [], sessions: j.sessions || [], aws: j.aws || {}, accts: j.accts || {}, owner: j.owner || '' };
  // 舊版（只有一個帳號）：原本的 Bitunix 金鑰、自動交易、實盤紀錄、Discord 搬到擁有者（第一個管理員）的帳號底下
  if (!j.accts && (j.bx || j.lt || j.ltTrades || j.notify)) {
    const a = ST.users.find(u => u.role === 'admin'), uid = a ? a.uid : '__owner';
    ST.accts[uid] = { bx: j.bx || {}, lt: j.lt || {}, ltTrades: j.ltTrades || [], notify: j.notify || {} };
    if (a) ST.owner = a.uid;
    log('舊存檔搬到帳號', uid);
  }
  for (const A of Object.values(ST.accts)) {        // 補齊欄位；伺服器重開後每個帳號的自動交易一律先暫停
    A.bx = { ...DEF_BX, ...(A.bx || {}) }; A.lt = { ...DEF_LT, sl: ST.trade.sl, step: ST.trade.step, hold: ST.trade.hold, ...(A.lt || {}), on: false };   // 舊帳號沒有個人參數：沿用原本的共用設定 A.notify = { ...DEF_NOTIFY, ...(A.notify || {}) }; A.ltTrades = A.ltTrades || [];
    if (A.lt.startCap === 100 && !A.ltTrades.length) { A.lt.startCap = 0; A.lt.startAt = 0; }   // 舊版預設把起始本金寫死成 100U
  }
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
      // 鎖利：只有逐小時的最高、最低價，同一小時裡先高還是先低不知道 → 保守算法：
      //   先用「這小時開始前」的鎖利線檢查最低價；沒碰到，再把這小時的最高價算進去，若最低價低於新的鎖利線，就當作先衝高再跑回、以新鎖利線出場
      let lockP = T.tp;
      if (tr.hl && !tr.noHL) {
        const H0 = Math.floor((r[0] - c.et) / HOUR), nH = Math.min(T.hold, tr.hl.length), R = f => f * T.lev * 100;
        const hiAt = h => (c.dir > 0 ? tr.hh[h] : -tr.hl[h]), loAt = h => (c.dir > 0 ? tr.hl[h] : -tr.hh[h]);
        let pk = R(r[1]); if (Number.isFinite(hiAt(H0))) pk = Math.max(pk, R(hiAt(H0)));   // 達標那一小時：只把最高價算進去（最低價可能在達標之前）
        for (let h = H0 + 1; h < nH; h++) {
          const lo = loAt(h), hi = hiAt(h); if (!Number.isFinite(lo)) continue;
          const l0 = lockAt(pk); if (R(lo) <= l0) return { st: 'win', at: r[0], exitAt: c.et + h * HOUR, pnl: l0, how: 'lock' };
          if (Number.isFinite(hi)) pk = Math.max(pk, R(hi));
          const l1 = lockAt(pk); if (R(lo) <= l1) return { st: 'win', at: r[0], exitAt: c.et + (h + 1) * HOUR, pnl: l1, how: 'lock' };
        }
        lockP = lockAt(pk);
      }
      if (done) { const v = hcAt(); return { st: 'win', at: r[0], exitAt: lim, pnl: v === null ? lockP : Math.max(lockP, v), how: 'hold' }; }
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
function dcSend(content, cfg) {
  if (!cfg || !cfg.webhook) return Promise.resolve(false);
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
  const T = ST.trade;
  const tpPx = c.entry * (1 + c.dir * T.tp / 100 / T.lev), slPx = c.entry * (1 - c.dir * T.sl / 100 / T.lev);
  const ab = (c.ind || []).filter(i => i.ab).map(i => `${i.n} z${i.z > 0 ? '+' : ''}${i.z.toFixed(1)}`).join('、');
  dcAll(X => `📡 **訊號**｜${c.dir > 0 ? '🟢 **做多**' : '🔴 **做空**'} **${mdEsc(c.sym)}**（數據異常 ${c.abN}/5）\n` +
    `進場 **${fpx(c.entry)}**・${T.lev}x\n達標 ${fpx(tpPx)}（+${T.tp}%）\n失敗 ${fpx(slPx)}（−${T.sl}%）\n` +
    `${ab ? '異常：' + mdEsc(ab) + '\n' : ''}時間 ${tw(c.et)}（台北）\n-# 訊號模擬：用幣安訊號價、${T.lev}x 計算，不是你的實際倉位${X.A.lt.on ? '；實際下單看 🤖 實盤通知' : ''}`, N => N.enabled && N.entry);
}
function notifyExit(c, E) {
  const T = ST.trade;
  const head = E.st === 'win' ? '✅ **成功**' : E.st === 'timeout' ? '⏱ **逾時**' : '❌ **失敗**';
  const how = E.how === 'lock' ? `（跑回鎖利線 +${E.pnl}% 出場）` : E.how === 'hold' ? `（持有到 ${T.hold} 小時到期）` : E.st === 'amb' ? '（同一根 K 棒兩邊都碰到，保守算失敗）' : '';
  const pnl = (E.pnl > 0 ? '+' : E.pnl < 0 ? '−' : '') + Math.abs(E.pnl).toFixed(0) + '%';
  dcAll(`📡 **訊號模擬結果**｜${head} ${c.dir > 0 ? '做多' : '做空'} **${mdEsc(c.sym)}** **${pnl}**${how}\n` +
    `訊號價 ${fpx(c.entry)}（${tw(c.et)}）\n持有 ${durTxt((E.exitAt || Date.now()) - c.et)}・${T.lev}x\n-# 這是訊號的模擬結果，不代表交易所的倉位已經平倉`, N => N.enabled && N.exit);
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
  for (const X of allX()) if (X.A.lt.on) ltOpen(X, c);   // 每個「開始交易」的帳號各自用自己的金鑰下單
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
    dcAll(`📊 **雙週結算**（${tw(start)} ～ ${tw(end)}，每期本金 ${ST.rep.cap}U）\n` +
      `回測：${r.bt.endCap}U（**${sg(r.bt.pnl)}U**，${sg(r.bt.ret)}%），${r.bt.n} 筆，成功率 ${r.bt.rate ?? '—'}%\n` +
      `即時：${r.live.endCap}U（**${sg(r.live.pnl)}U**，${sg(r.live.ret)}%），${r.live.n} 筆，成功率 ${r.live.rate ?? '—'}%`, N => N.enabled);
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

/* ---------------- 多帳號：每個登入帳號各自的 Bitunix API、自動交易、實盤紀錄、Discord ----------------
   ST.accts[uid] = { bx, lt, ltTrades, notify }（會存檔）；X = 帳號執行中的暫存（持倉、帳戶資金、下單鎖、版本號）
   新註冊的帳號一開始全部是空的；訊號、回測、掃描條件、浮盈／鎖利規則大家共用 */
const RT = new Map();
const OWNER_UID = '852639358';                         // 內建的擁有者帳號：永遠是管理員，不能被降級或刪除（密碼不寫在程式裡，repo 是公開的）
function ownerUid() {                                  // 擁有者＝這台伺服器的主人（AWS 提醒、用管理金鑰登入都算他的）
  if (ST.users.some(u => u.uid === OWNER_UID)) return OWNER_UID;
  if (ST.owner && ST.users.some(u => u.uid === ST.owner)) return ST.owner;
  const a = ST.users.find(u => u.role === 'admin'); return a ? a.uid : '__owner';
}
function ctx(uid) {
  uid = String(uid || ownerUid());
  if (!ST.accts[uid]) { ST.accts[uid] = { bx: { ...DEF_BX }, lt: { ...DEF_LT }, ltTrades: [], notify: { ...DEF_NOTIFY } }; dirty = true; }
  let X = RT.get(uid);
  if (!X) { X = { uid, BX: { pos: [], acct: null, at: 0, err: '', seeded: false, warned: {} }, LT: { lev: {}, busy: new Set(), msg: '', dayHit: '', dayPnl: 0 }, v: Date.now(), polling: false, managing: false }; RT.set(uid, X); }
  X.A = ST.accts[uid];
  return X;
}
const allX = () => Object.keys(ST.accts).map(ctx);
{ const o = ST.users.find(u => u.uid === OWNER_UID); if (o) { o.role = 'admin'; ST.owner = OWNER_UID; } }
// 這個帳號實盤用的規則：成功線、出場方式跟大家一樣；浮虧失敗線、鎖利上調間距、最長持有用自己的設定
const TT = X => ({ ...ST.trade, sl: X.A.lt.sl, step: X.A.lt.step, hold: X.A.lt.hold });
const hasKey = X => !!(X.A.bx.key && X.A.bx.secret);
const dcX = (X, msg) => dcSend(msg, X.A.notify);                // 只傳到這個帳號自己的 Discord
function dcAll(content, ok = () => true) {             // 大家共用的通知（訊號、數據公布、結算）：每個帳號自己的 Discord 各傳一次，同一個 Webhook 不重複
  const seen = new Set();
  for (const X of allX()) {
    const N = X.A.notify; if (!N.webhook || !ok(N) || seen.has(N.webhook)) continue;
    seen.add(N.webhook); dcSend(typeof content === 'function' ? content(X) : content, N);
  }
}

/* ---------------- Bitunix 持倉 ---------------- */
// 簽名：digest = SHA256(nonce + timestamp + apiKey + 排序後的 query 參數 + body)；sign = SHA256(digest + secret)
const BXAPI = process.env.BITUNIX_API || 'https://fapi.bitunix.com';
const sha = x => crypto.createHash('sha256').update(x, 'utf8').digest('hex');
async function bxGet(path, params, cfg) {              // cfg 一定要指定是哪個帳號的金鑰，不能有預設值
  if (!cfg || !cfg.key) throw new Error('沒有指定 Bitunix 金鑰');
  params = params || {};
  const keys = Object.keys(params).sort();
  const qs = keys.map(k => k + params[k]).join(''), url = BXAPI + path + (keys.length ? '?' + keys.map(k => `${k}=${encodeURIComponent(params[k])}`).join('&') : '');
  const nonce = crypto.randomBytes(16).toString('hex'), ts = String(Date.now());
  const sign = sha(sha(nonce + ts + cfg.key + qs) + cfg.secret);
  const r = await fetch(url, { headers: { 'api-key': cfg.key, nonce, timestamp: ts, sign, language: 'en-US', 'Content-Type': 'application/json' }, signal: AbortSignal.timeout(15000) });
  const j = await r.json().catch(() => ({}));
  if (!r.ok || j.code !== 0) throw new Error(j.msg ? `Bitunix：${j.msg}（${j.code}）` : 'Bitunix HTTP ' + r.status);
  return j.data;
}
// 持倉方向：雙向持倉回傳 LONG／SHORT，單向持倉可能回傳 BUY／SELL，兩種都要認得
const sideDir = v => { const x = String(v || '').toUpperCase(); return x === 'LONG' || x === 'BUY' ? 1 : x === 'SHORT' || x === 'SELL' ? -1 : 0; };
const num = v => { const n = +v; return Number.isFinite(n) ? n : 0; };
const bxEquity = X => { const A = X.BX.acct; return A ? A.avail + A.frozen + A.margin + A.cross + A.iso : 0; };
const bxMapPos = data => (Array.isArray(data) ? data : []).map(p => ({
  id: String(p.positionId), sym: p.symbol, dir: sideDir(p.side), side: p.side, qty: num(p.qty), lev: num(p.leverage), mode: p.marginMode,
  entry: num(p.avgOpenPrice), margin: num(p.margin), upnl: num(p.unrealizedPNL), rpnl: num(p.realizedPNL), fee: num(p.fee), funding: num(p.funding),
  liq: num(p.liqPrice), ctime: num(p.ctime), mtime: num(p.mtime), pmode: p.positionMode
}));
async function bxPoll(X) {
  const C = X.A.bx, BX = X.BX, N = X.A.notify;
  if (!hasKey(X)) { BX.pos = []; BX.acct = null; BX.err = ''; return; }
  try {
    const data = await bxGet('/api/v1/futures/position/get_pending_positions', {}, C);
    const acct = await bxGet('/api/v1/futures/account', { marginCoin: 'USDT' }, C).catch(() => null);
    const pos = bxMapPos(data);
    const prev = new Map(BX.pos.map(p => [p.id, p])), now = new Map(pos.map(p => [p.id, p]));
    if (BX.seeded && C.notify && N.enabled) {                       // 第一次讀到的持倉不算「新開倉」
      const botPos = p => X.A.ltTrades.some(t => t.positionId === p.id || (t.sym === p.sym && t.dir === p.dir && Date.now() - t.et < 60000));   // 自動交易的單另外通知
      for (const p of pos) if (!prev.has(p.id) && !botPos(p)) dcX(X, `📥 **Bitunix 開倉** ${p.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(p.sym)}**\n開倉價 ${fpx(p.entry)}・${p.lev}x ${p.mode === 'CROSS' ? '全倉' : '逐倉'}・數量 ${p.qty}・保證金 ${p.margin.toFixed(2)}U${p.liq > 0 ? `\n強平價 ${fpx(p.liq)}` : ''}`);
      for (const p of BX.pos) if (!now.has(p.id) && !botPos(p)) dcX(X, `📤 **Bitunix 平倉** ${p.dir > 0 ? '做多' : '做空'} **${mdEsc(p.sym)}**\n開倉價 ${fpx(p.entry)}・${p.lev}x\n平倉前最後一次讀到的未實現損益 **${p.upnl >= 0 ? '+' : '−'}${Math.abs(p.upnl).toFixed(2)}U**（實際以交易所為準）`);
    }
    if (C.liq && N.enabled) for (const p of pos) {                  // 現價離強平價太近就提醒（30 分鐘最多一次）
      const px = PX.map[p.sym]; if (!(px > 0 && p.liq > 0)) continue;
      const d = Math.abs(px - p.liq) / px * 100;
      if (d <= C.liqPct && Date.now() - (BX.warned[p.id] || 0) > 30 * 60000) {
        BX.warned[p.id] = Date.now();
        dcX(X, `⚠️ **快爆倉了** ${p.dir > 0 ? '做多' : '做空'} **${mdEsc(p.sym)}**：現價 ${fpx(px)}，強平價 ${fpx(p.liq)}，只差 **${d.toFixed(2)}%**`);
      }
    }
    BX.pos = pos; BX.at = Date.now(); BX.err = ''; BX.seeded = true;
    await ltReconcile(X, pos);
    if (acct) { const a = Array.isArray(acct) ? acct[0] : acct; BX.acct = a ? { avail: num(a.available), frozen: num(a.frozen), margin: num(a.margin), cross: num(a.crossUnrealizedPNL), iso: num(a.isolationUnrealizedPNL), bonus: num(a.bonus) } : null; }
    const L = X.A.lt, eqNow = bxEquity(X);
    if (!(L.startCap > 0) && L.budget > 0) { L.startCap = L.budget; L.startAt = L.startAt || Date.now(); touchLT(X); }
    else if (!(L.startCap > 0) && eqNow >= 1) {          // 第一次看到帳戶有 1U 以上：實盤統計就從這個金額、這個時間開始（零頭不算，避免一直重複通知）
      L.startCap = Math.round(eqNow * 100) / 100; L.startAt = Date.now(); touchLT(X);
      dcX(X, `💰 偵測到 Bitunix 帳戶資金 **${L.startCap}U**，實盤統計從現在開始計算`);
    }
  } catch (e) { BX.err = e.message; }
}
async function bxPollOne(X) { if (X.polling) return; X.polling = true; try { await bxPoll(X); } finally { X.polling = false; } }
async function bxPollAll() { for (const X of allX()) if (hasKey(X) || X.BX.pos.length) await bxPollOne(X); }   // 一個帳號一個帳號輪流讀，不會同時打太多請求
setInterval(bxPollAll, 10000); setTimeout(bxPollAll, 3000);

/* ================= 自動下單（Bitunix 實盤，每個帳號各自下單） =================
   • 新訊號出現時，每個「開始交易」的帳號各自用自己的金鑰市價開倉；開倉單同時帶交易所止損（失敗線）
   • 伺服器每 3 秒看一次價格：碰到成功線＝開始鎖利（或固定出場），之後浮盈每多 step% 鎖利線上調一格；跑回鎖利線、持有到期、碰到失敗線就平倉
   • 每 10 秒對一次交易所持倉：手動平倉、部分平倉、交易所止損、強平都會被記錄下來
   • 預設暫停；單日虧損超過上限自動暫停；伺服器重開也會先暫停 */
const LTP = { pairs: new Map(), pairsAt: 0 };          // Bitunix 交易對清單：公開資料，大家共用
const touchLT = X => { X.v++; dirty = true; };
async function bxPost(path, body, cfg) {
  if (!cfg || !cfg.key) throw new Error('沒有指定 Bitunix 金鑰');
  const b = JSON.stringify(body), nonce = crypto.randomBytes(16).toString('hex'), ts = String(Date.now());
  const sign = sha(sha(nonce + ts + cfg.key + b) + cfg.secret);
  const r = await fetch(BXAPI + path, { method: 'POST', headers: { 'api-key': cfg.key, nonce, timestamp: ts, sign, language: 'en-US', 'Content-Type': 'application/json' }, body: b, signal: AbortSignal.timeout(15000) });
  const j = await r.json().catch(() => ({}));
  if (!r.ok || j.code !== 0) throw new Error(j.msg ? `${j.msg}（${j.code}）` : 'HTTP ' + r.status);
  return j.data;
}
async function ltPair(sym) {
  if (Date.now() - LTP.pairsAt > HOUR || !LTP.pairs.size) {
    const r = await fetch(BXAPI + '/api/v1/futures/market/trading_pairs', { signal: AbortSignal.timeout(15000) }).then(x => x.json());
    if (r && r.code === 0 && Array.isArray(r.data)) { LTP.pairs = new Map(r.data.map(x => [x.symbol, x])); LTP.pairsAt = Date.now(); }
  }
  return LTP.pairs.get(sym) || null;
}
const fl = (v, d) => { const m = 10 ** d; return Math.floor(v * m + 1e-9) / m; };
const pxStr = (v, d) => (+v).toFixed(Math.max(0, Math.min(10, d)));
const ltOpenTrades = X => X.A.ltTrades.filter(t => t.status === 'open');
function ltNet(t) { return (t.realized || 0) - Math.abs(t.fee || 0) + (t.funding || 0); }   // 已實現損益－手續費＋資金費
// 這組自動交易目前「自己的」資金：起始投入＋從起算時間開始所有單的淨損益（持有中的含未實現）
function ltBotEq(X) {
  const C = X.A.lt; let e = C.startCap || 0, used = 0;
  for (const t of X.A.ltTrades) { if (t.et < (C.startAt || 0)) continue; e += ltNet(t) + (t.status === 'open' ? (t.upnl || 0) : 0); if (t.status === 'open') used += t.margin || t.m0 || 0; }
  return { eq: e, used, free: e - used };
}
async function ltOpen(X, c) {
  const C = X.A.lt, K = X.A.bx, LT = X.LT, BX = X.BX;
  if (!C.on || !hasKey(X) || LT.busy.has(c.sym)) return;
  LT.busy.add(c.sym);
  try {
    if (C.maxOpen && ltOpenTrades(X).length >= C.maxOpen) { LT.msg = `已達最多同時持倉 ${C.maxOpen} 筆，${c.sym} 這次不下單`; return; }
    if (BX.pos.some(p => p.sym === c.sym) || ltOpenTrades(X).some(t => t.sym === c.sym)) return;   // 這個幣已經有倉位
    const pr = await ltPair(c.sym);
    if (!pr) { LT.msg = `Bitunix 沒有 ${c.sym}，略過`; return; }
    if (pr.symbolStatus !== 'OPEN') { LT.msg = `${c.sym} 在 Bitunix 暫停交易，略過`; return; }
    const px = PX.map[c.sym] || c.last, lev = Math.max(1, Math.min(C.lev, +pr.maxLeverage || C.lev));
    if (BX.acct && BX.acct.avail < C.margin * 1.2) { LT.msg = `可用餘額不足（${BX.acct.avail.toFixed(2)}U），${c.sym} 不下單`; return; }
    if (C.budget > 0) {                                // 只用你設定的投入資金，不碰帳戶裡其他的錢
      const B = ltBotEq(X);
      if (B.eq <= 0) { C.on = false; touchLT(X); dcX(X, `🛑 **投入資金 ${C.budget}U 已經用完**（目前 ${B.eq.toFixed(2)}U），自動交易已暫停`); return; }
      if (B.free < C.margin * 1.2) { LT.msg = `投入資金剩 ${B.free.toFixed(2)}U 可用（設定 ${C.budget}U），${c.sym} 不下單`; return; }
    }
    const qty = fl(C.margin * lev / px, +pr.basePrecision || 0);
    if (!(qty > 0) || qty < +pr.minTradeVolume) { LT.msg = `${c.sym} 用 ${C.margin}U×${lev}x 買不到最小下單量（${pr.minTradeVolume}），略過`; dcX(X, `⏭️ ${mdEsc(c.sym)} 下單量太小，略過（最小 ${pr.minTradeVolume}，需要的保證金比 ${C.margin}U 多）`); return; }
    const key = C.mode + lev;
    if (LT.lev[c.sym] !== key) {
      await bxPost('/api/v1/futures/account/change_margin_mode', { marginMode: C.mode, symbol: c.sym, marginCoin: 'USDT' }, K).catch(() => {});
      await bxPost('/api/v1/futures/account/change_leverage', { symbol: c.sym, leverage: lev, marginCoin: 'USDT' }, K);
      LT.lev[c.sym] = key;
    }
    const T = TT(X), slPx = px * (1 - c.dir * T.sl / 100 / lev), qp = +pr.quotePrecision || 4;
    const base = { symbol: c.sym, qty: String(qty), side: c.dir > 0 ? 'BUY' : 'SELL', tradeSide: 'OPEN', orderType: 'MARKET', clientId: 'q' + Date.now().toString(36) };
    let o, exSL = true;
    try { o = await bxPost('/api/v1/futures/trade/place_order', { ...base, slPrice: pxStr(slPx, qp), slStopType: 'MARK_PRICE', slOrderType: 'MARKET' }, K); }
    catch (e) {                                       // 帶止損失敗就改成不帶，止損改由伺服器監控
      if (!/sl|stop|price/i.test(e.message)) throw e;
      exSL = false; o = await bxPost('/api/v1/futures/trade/place_order', base, K);
    }
    await sleep(1500);
    const ps = await bxGet('/api/v1/futures/position/get_pending_positions', { symbol: c.sym }, K).catch(() => []);
    const p = (ps || []).find(x => sideDir(x.side) === c.dir);
    const t = {
      id: 'lt-' + Date.now(), sym: c.sym, dir: c.dir, card: c.id, abN: c.abN, et: Date.now(), lev,
      entry: p ? num(p.avgOpenPrice) : px, qty: p ? num(p.qty) : qty, qty0: p ? num(p.qty) : qty, margin: p ? num(p.margin) : C.margin, m0: p ? num(p.margin) || C.margin : C.margin,
      positionId: p ? String(p.positionId) : '', orderId: o && o.orderId, status: 'open', realized: 0, fee: p ? num(p.fee) : 0, funding: 0, closes: [], locked: false, fav: 0, adv: 0, exSL, prec: +pr.basePrecision || 0, minQty: +pr.minTradeVolume || 0
    };
    X.A.ltTrades.unshift(t); X.A.ltTrades = X.A.ltTrades.slice(0, 2000); touchLT(X);
    log('自動開倉', X.uid, c.sym, c.dir > 0 ? '做多' : '做空', qty, '@', t.entry);
    dcX(X, `🤖 **自動開倉** ${c.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(c.sym)}**\n成交價 ${fpx(t.entry)}・${lev}x 全倉・數量 ${t.qty}・保證金約 ${t.margin.toFixed(2)}U\n${exSL ? `交易所止損 ${fpx(slPx)}（−${T.sl}%）` : '⚠️ 交易所止損沒設成功，改由伺服器監控'}`);
  } catch (e) { LT.msg = `${c.sym} 自動下單失敗：${e.message}`; log(X.uid, LT.msg); dcX(X, `❗ **自動下單失敗** ${mdEsc(c.sym)}：${mdEsc(e.message)}`); }
  finally { LT.busy.delete(c.sym); }
}
// 平倉：pct＝1 全部（閃電平倉）；其他比例用市價平倉單
function closeBody(p, q) {
  return p.pmode === 'HEDGE'
    ? { symbol: p.sym, qty: String(q), side: p.dir > 0 ? 'BUY' : 'SELL', tradeSide: 'CLOSE', positionId: p.id, orderType: 'MARKET' }   // 官方文件：雙向持倉平多用 BUY＋CLOSE
    : { symbol: p.sym, qty: String(q), side: p.dir > 0 ? 'SELL' : 'BUY', orderType: 'MARKET', reduceOnly: true };
}
async function fullClose(X, p, onlyThis) {             // 三種方法依序試，前一種失敗才用下一種；onlyThis＝只能動這一筆（不用整個幣種全平，免得平到同幣種的手動單）
  const K = X.A.bx, errs = [];
  try { await bxPost('/api/v1/futures/trade/flash_close_position', { positionId: p.id }, K); return; } catch (e) { errs.push('閃電平倉：' + e.message); }
  if (!onlyThis) try { await bxPost('/api/v1/futures/trade/close_all_position', { symbol: p.sym }, K); return; } catch (e) { errs.push('單幣全平：' + e.message); }
  try { await bxPost('/api/v1/futures/trade/place_order', closeBody(p, p.qty), K); return; } catch (e) { errs.push('市價平倉：' + e.message); }
  throw new Error(errs.join('；'));
}
async function ltClosePos(X, positionId, pct, reason) {
  const K = X.A.bx, p = X.BX.pos.find(x => x.id === positionId);
  if (!p) throw new Error('找不到這筆持倉，可能已經平倉了');
  const t = X.A.ltTrades.find(x => x.status === 'open' && x.positionId === positionId);
  if (t) { t.pendReason = reason; t.pendAt = Date.now(); }
  if (pct >= 0.999) { await fullClose(X, p); return 'full'; }
  const pr = await ltPair(p.sym), prec = pr ? +pr.basePrecision || 0 : (t ? t.prec : 0), minQ = pr ? +pr.minTradeVolume || 0 : 0;
  let q = fl(p.qty * pct, prec);
  if (!(q > 0) || q < minQ) throw new Error(`這個比例平倉數量太小（最少 ${minQ}）`);
  if (p.qty - q < minQ) { await fullClose(X, p); return 'full'; }
  await bxPost('/api/v1/futures/trade/place_order', closeBody(p, q), K);
  await sleep(1500);                                  // 安全檢查：倉位如果反而變大，代表方向錯了，立刻全平並暫停
  const ps = await bxGet('/api/v1/futures/position/get_pending_positions', { symbol: p.sym }, K).catch(() => null);
  const n = ps && ps.find(x => String(x.positionId) === positionId);
  if (n && num(n.qty) > p.qty + 1e-12) {
    await bxPost('/api/v1/futures/trade/flash_close_position', { positionId }, K).catch(() => {});
    X.A.lt.on = false; touchLT(X);
    dcX(X, `🚨 **部分平倉異常**：${mdEsc(p.sym)} 倉位變大，已全部平倉並暫停自動交易，請檢查交易所`);
    throw new Error('部分平倉後倉位變大，已緊急全部平倉並暫停自動交易');
  }
  return 'part';
}
// 每 3 秒：照規則管理每個帳號自動開的單（帳號之間互不影響，一個帳號出錯不會卡住其他帳號）
async function ltManage() { for (const X of allX()) { if (X.managing || !ltOpenTrades(X).length) continue; X.managing = true; try { await ltManageX(X); } catch (e) { log('管理自動單失敗', X.uid, e.message); } finally { X.managing = false; } } }
async function ltManageX(X) {
  const T = TT(X), now = Date.now();
  for (const t of ltOpenTrades(X)) {
    const px = PX.map[t.sym]; if (!(px > 0) || !t.positionId || t.closing) continue;
    const roe = t.dir * (px / t.entry - 1) * t.lev * 100;
    t.cur = px; t.roe = roe; t.fav = Math.max(t.fav || 0, roe); t.adv = Math.min(t.adv || 0, roe);
    let why = '';
    if (roe <= -T.sl) why = 'fail';
    else if (T.exit === 'fixed') { if (roe >= T.tp) why = 'win'; }
    else if (t.fav >= T.tp) {                            // 鎖利：最高浮盈每多 step%，鎖利線就往上調一格，只升不降
      const lv = Math.max(lockAt(t.fav, T), t.lockLv || 0);
      if (!t.locked) { t.locked = true; touchLT(X); dcX(X, `🤖 **實盤**｜🔒 **達標鎖利** ${mdEsc(t.sym)}（${t.lev}x）：浮盈 +${roe.toFixed(0)}%，鎖利線 **+${lv}%**${T.step > 0 ? `\n之後浮盈每多 ${T.step}% 鎖利線就往上調一次，跑回鎖利線就平倉` : `，之後跑回 +${lv}% 就平倉`}`); }
      else if (lv > (t.lockLv || T.tp)) { touchLT(X); dcX(X, `🤖 **實盤**｜🔒 **鎖利上調** ${mdEsc(t.sym)}：浮盈 +${roe.toFixed(0)}%，鎖利線調到 **+${lv}%**`); }
      t.lockLv = lv;
      if (roe < lv) why = 'lock';
    }
    if (!why && now - t.et >= T.hold * HOUR) why = 'timeout';
    if (!why) continue;
    t.closing = true;
    try { await ltClosePos(X, t.positionId, 1, why); }
    catch (e) { dcX(X, `❗ **自動平倉失敗** ${mdEsc(t.sym)}：${mdEsc(e.message)}`); }
    t.closing = false;
  }
}
// 每 10 秒：跟交易所的持倉對帳
async function ltReconcile(X, pos) {
  const K = X.A.bx, TR = X.A.ltTrades, byId = new Map(pos.map(p => [p.id, p])); let ch = false;
  // 修正舊版的錯：方向判斷錯誤時，倉位明明還在卻被當成已平倉 → 找回來重新追蹤
  for (const t of TR) {
    if (t.status !== 'closed' || t.reason !== 'exchange' || t.positionId || Date.now() - t.et > 7 * 24 * HOUR) continue;
    const p = pos.find(x => x.sym === t.sym && x.dir === t.dir && Math.abs((x.ctime || 0) - t.et) < 5 * 60000 && !TR.some(o => o.status === 'open' && o.positionId === x.id));
    if (!p) continue;
    Object.assign(t, { status: 'open', reason: '', exitAt: 0, positionId: p.id, entry: p.entry, qty: p.qty, qty0: p.qty, m0: p.margin || t.m0, lev: p.lev || t.lev, closes: (t.closes || []).slice(0, -1) });
    ch = true; log('找回被誤判平倉的單', X.uid, t.sym);
  }
  for (const t of ltOpenTrades(X)) {
    let p = t.positionId ? byId.get(t.positionId) : pos.find(x => x.sym === t.sym && x.dir === t.dir && Math.abs((x.ctime || 0) - t.et) < 5 * 60000);   // 只認自動下單那一刻開的倉，手動開的不算
    if (p && !t.positionId) { t.positionId = p.id; t.entry = p.entry; t.qty = t.qty0 = p.qty; t.m0 = p.margin || t.m0; ch = true; }
    if (p) {
      if (p.qty < t.qty - 1e-12) {                    // 部分平倉（網站或交易所 App）
        const pnl = p.rpnl - (t.realized || 0);
        t.closes.push({ t: Date.now(), qty: t.qty - p.qty, pnl, by: t.pendReason || 'manual' });
        dcX(X, `✂️ **部分平倉** ${mdEsc(t.sym)}：平掉 ${(t.qty - p.qty).toPrecision(6)}，這次已實現 ${pnl >= 0 ? '+' : '−'}${Math.abs(pnl).toFixed(2)}U`);
        t.pendReason = '';
      }
      Object.assign(t, { qty: p.qty, realized: p.rpnl, fee: p.fee, funding: p.funding, upnl: p.upnl, margin: p.margin || t.margin, liq: p.liq }); ch = true;
      continue;
    }
    if (!t.positionId && Date.now() - t.et < 60000) continue;
    // 倉位不見了＝已平倉：去歷史持倉拿最後的結果
    let h = null;
    try { const r = await bxGet('/api/v1/futures/position/get_history_positions', t.positionId ? { positionId: t.positionId } : { symbol: t.sym, limit: 5 }, K); h = (r && r.positionList || []).find(x => !t.positionId || String(x.positionId) === t.positionId) || null; } catch (e) {}
    const reason = t.pendReason || (h && num(h.liqQty) > 0 ? 'liq' : 'exchange');
    if (h) Object.assign(t, { realized: num(h.realizedPNL), fee: num(h.fee), funding: num(h.funding), closePx: num(h.closePrice) });
    const prevPart = t.closes.reduce((a, c) => a + c.pnl, 0);
    t.closes.push({ t: Date.now(), qty: t.qty, pnl: (t.realized || 0) - prevPart, by: reason });
    Object.assign(t, { status: 'closed', exitAt: Date.now(), reason, qty: 0, upnl: 0 }); ch = true;
    const net = ltNet(t), nm = '🤖 **實盤平倉**｜' + ({ win: '✅ 達標出場', lock: `🔒 鎖利出場（鎖利線 +${t.lockLv || ST.trade.tp}%）`, fail: '❌ 失敗線出場', timeout: '⏱ 持有到期出場', manual: '🖐 手動平倉', all: '🛑 一鍵平倉（自動單）', liq: '💥 強平', exchange: '📤 交易所平倉（止損或在 App 平倉）' }[reason] || reason);
    dcX(X, `${nm} **${mdEsc(t.sym)}** ${t.dir > 0 ? '做多' : '做空'}\n淨損益 **${net >= 0 ? '+' : '−'}${Math.abs(net).toFixed(2)}U**（${(net / (t.m0 || X.A.lt.margin) * 100).toFixed(0)}%）・持有 ${durTxt(Date.now() - t.et)}${t.closePx ? `・平倉均價 ${fpx(t.closePx)}` : ''}`);
  }
  // 單日虧損上限（台北時間每天 00:00 重算）
  const L = X.A.lt, LT = X.LT, day = new Date(Date.now() + TZ).toISOString().slice(0, 10), d0 = Date.parse(day + 'T00:00:00Z') - TZ;
  let dayPnl = 0;
  for (const t of TR) { for (const c of t.closes || []) if (c.t >= d0) dayPnl += c.pnl; if (t.status === 'open') dayPnl += t.upnl || 0; }
  LT.dayPnl = dayPnl;
  if (L.on && L.dayLoss > 0 && dayPnl <= -L.dayLoss && LT.dayHit !== day) {
    LT.dayHit = day; L.on = false; ch = true;
    dcX(X, `🛑 **今天虧損 ${dayPnl.toFixed(2)}U，超過上限 ${L.dayLoss}U，自動交易已暫停**（已開的單照常管理，可以在網站重新開始）`);
  }
  if (ch) touchLT(X);
}

/* ---------------- 📅 數據公布（經濟數據行事曆，來源：Forex Factory 公開 JSON） ----------------
   只看美國（USD）的高影響數據；公布前 30 分鐘、公布時各發一次 Discord，之後讀到實際值再補一次 */
const ECO = { list: [], at: 0, err: '', sent: {} };
const ECO_ZH = [
  [/core cpi/i, '核心 CPI（消費者物價）'], [/\bcpi\b/i, 'CPI（消費者物價指數）'], [/core pce/i, '核心 PCE 物價'], [/\bpce\b/i, 'PCE 物價'],
  [/core ppi/i, '核心 PPI（生產者物價）'], [/\bppi\b/i, 'PPI（生產者物價指數）'], [/non-farm|nonfarm/i, '非農就業人數'], [/unemployment rate/i, '失業率'],
  [/unemployment claims/i, '初領失業金人數'], [/average hourly earnings/i, '平均時薪'], [/federal funds rate/i, '聯準會利率決議'], [/fomc statement/i, 'FOMC 聲明'],
  [/fomc press conference/i, 'FOMC 記者會'], [/fomc meeting minutes/i, 'FOMC 會議紀要'], [/fed chair|powell/i, '聯準會主席談話'], [/advance gdp|prelim gdp|final gdp|\bgdp\b/i, 'GDP（國內生產毛額）'],
  [/retail sales/i, '零售銷售'], [/ism manufacturing/i, 'ISM 製造業指數'], [/ism services/i, 'ISM 服務業指數'], [/jolts/i, 'JOLTS 職缺'],
  [/consumer confidence/i, '消費者信心'], [/prelim uom|uom consumer sentiment/i, '密大消費者信心'], [/adp/i, 'ADP 就業人數'], [/durable goods/i, '耐久財訂單']
];
const ecoZh = t => { for (const [re, zh] of ECO_ZH) if (re.test(t)) return zh + (/(m\/m)/i.test(t) ? '（月增）' : /(y\/y)/i.test(t) ? '（年增）' : /(q\/q)/i.test(t) ? '（季增）' : ''); return t; };
async function ecoGet(urls) {
  for (const url of urls) {
    try {
      const r = await fetch(url, { signal: AbortSignal.timeout(15000), headers: { 'User-Agent': 'Mozilla/5.0' } });
      if (!r.ok) throw new Error('HTTP ' + r.status);
      return await r.json();
    } catch (e) { ECO.err = e.message; }
  }
  return null;
}
async function ecoFetch() {                           // 本週＋下週
  const base = process.env.ECO_URL ? [process.env.ECO_URL] : null;
  const wk = await ecoGet(base || ['https://nfs.faireconomy.media/ff_calendar_thisweek.json', 'https://cdn-nfs.faireconomy.media/ff_calendar_thisweek.json']);
  const nx = await ecoGet(base ? [base[0].replace('thisweek', 'nextweek')] : ['https://nfs.faireconomy.media/ff_calendar_nextweek.json', 'https://cdn-nfs.faireconomy.media/ff_calendar_nextweek.json']);
  if (!wk && !nx) return;
  const m = new Map();
  for (const e of [].concat(wk || [], nx || [])) {
    if (e.country !== 'USD' || (e.impact !== 'High' && e.impact !== 'Medium')) continue;   // 清單顯示高、中影響；Discord 只通知高影響
    const t = Date.parse(e.date); if (!Number.isFinite(t)) continue;
    const id = e.title + '|' + e.date;
    m.set(id, { id, t, imp: e.impact === 'High' ? 'H' : 'M', title: e.title, zh: ecoZh(e.title), forecast: e.forecast || '', previous: e.previous || '', actual: e.actual || '' });
  }
  ECO.list = [...m.values()].sort((a, b) => a.t - b.t);
  ECO.at = Date.now(); ECO.err = wk ? '' : ECO.err; ECO.hasNext = !!nx;
}
function ecoTick() {
  const now = Date.now(), fv = e => `${e.forecast ? `預測 ${e.forecast}` : ''}${e.forecast && e.previous ? '・' : ''}${e.previous ? `前值 ${e.previous}` : ''}`;
  for (const e of ECO.list) {
    if (e.imp !== 'H') continue;
    const k = e.id;
    if (e.t - now <= 30 * 60000 && e.t > now && !ECO.sent[k + 'pre']) { ECO.sent[k + 'pre'] = 1; dcAll(`📅 **數據即將公布**（30 分鐘後，${tw(e.t)} 台北）\n🇺🇸 **${mdEsc(e.zh)}**${fv(e) ? '\n' + fv(e) : ''}\n高影響數據，公布前後波動可能很大`, N => N.enabled); }
    if (now >= e.t && now - e.t < 10 * 60000 && !ECO.sent[k + 'now']) { ECO.sent[k + 'now'] = 1; dcAll(`📊 **數據公布中** 🇺🇸 **${mdEsc(e.zh)}**（${tw(e.t)} 台北）${fv(e) ? '\n' + fv(e) : ''}${e.actual ? `\n實際 **${e.actual}**` : ''}`, N => N.enabled); if (e.actual) ECO.sent[k + 'act'] = 1; }
    if (e.actual && now >= e.t && now - e.t < 6 * HOUR && !ECO.sent[k + 'act'] && ECO.sent[k + 'now']) { ECO.sent[k + 'act'] = 1; dcAll(`📊 **數據已公布** 🇺🇸 **${mdEsc(e.zh)}**：實際 **${e.actual}**${fv(e) ? '（' + fv(e) + '）' : ''}`, N => N.enabled); }
  }
}
// 每 30 分鐘抓一次（公布時間前後改成每 5 分鐘，才拿得到實際值）；每 30 秒檢查要不要發通知
setTimeout(ecoFetch, 4000);
setInterval(() => { const now = Date.now(), near = ECO.list.some(e => e.imp === 'H' && Math.abs(e.t - now) < 30 * 60000); if (now - ECO.at > (near ? 5 : 30) * 60000) ecoFetch(); }, 60000);
setInterval(ecoTick, 30000);

/* ---------------- 🐋 鯨魚大單（伺服器用 WebSocket 收幣安逐筆成交，網頁只來讀結果） ----------------
   幣安 2026/03 起合約 WebSocket 分成 /public、/market、/private，aggTrade 在 /market；舊的 /ws 網址連得上但收不到成交。
   Node 20 沒有內建 WebSocket 用戶端，所以自己寫一個最小的（只做這裡需要的：連線、收文字訊息、回 pong、送訂閱）。 */
const tls = require('tls'), net = require('net');
const { EventEmitter } = require('events');
class MiniWS extends EventEmitter {
  constructor(url) {
    super();
    const u = new URL(url), sec = u.protocol === 'wss:', port = +u.port || (sec ? 443 : 80);
    const key = crypto.randomBytes(16).toString('base64');
    this.accept = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
    this.open = false; this.closed = false; this.buf = Buffer.alloc(0); this.frag = null;
    const s = this.sock = sec ? tls.connect({ host: u.hostname, port, servername: u.hostname }) : net.connect({ host: u.hostname, port });
    s.setNoDelay(true);
    s.setTimeout(20000, () => this.kill('連線逾時'));          // 只管握手階段，連上後改由外面的看門狗判斷
    s.once(sec ? 'secureConnect' : 'connect', () => s.write(`GET ${u.pathname}${u.search} HTTP/1.1\r\nHost: ${u.host}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: ${key}\r\nSec-WebSocket-Version: 13\r\nUser-Agent: quant-server\r\n\r\n`));
    s.on('data', d => { try { this.onData(d); } catch (e) { this.kill('解析失敗：' + e.message); } });
    s.on('error', e => this.kill(e.message));
    s.on('close', () => this.kill('連線中斷'));
  }
  onData(d) {
    this.buf = this.buf.length ? Buffer.concat([this.buf, d]) : d;
    if (!this.open) {
      const i = this.buf.indexOf('\r\n\r\n');
      if (i < 0) { if (this.buf.length > 16384) this.kill('握手失敗'); return; }
      const head = this.buf.subarray(0, i).toString('latin1'); this.buf = this.buf.subarray(i + 4);
      const st = head.match(/^HTTP\/1\.[01] (\d+)/);
      if (!st || st[1] !== '101') return this.kill('握手失敗（' + (st ? 'HTTP ' + st[1] : head.slice(0, 40)) + '）');
      const acc = head.match(/sec-websocket-accept:\s*(\S+)/i);
      if (!acc || acc[1] !== this.accept) return this.kill('握手驗證失敗');
      this.open = true; this.sock.setTimeout(0); this.emit('open');
    }
    while (!this.closed) {
      const b = this.buf; if (b.length < 2) return;
      const fin = b[0] & 0x80, op = b[0] & 0x0f, masked = b[1] & 0x80;
      let len = b[1] & 0x7f, off = 2;
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (b.length < 10) return; len = Number(b.readBigUInt64BE(2)); off = 10; }
      if (len > 16 * 1024 * 1024) return this.kill('訊息太大');
      let mk = null; if (masked) { if (b.length < off + 4) return; mk = b.subarray(off, off + 4); off += 4; }
      if (b.length < off + len) return;
      let p = b.subarray(off, off + len); this.buf = b.subarray(off + len);
      if (mk) { p = Buffer.from(p); for (let j = 0; j < p.length; j++) p[j] ^= mk[j & 3]; }
      if (op === 8) { this.frame(8, p.subarray(0, 2)); return this.kill('幣安關閉連線'); }
      if (op === 9) { this.frame(10, p); continue; }        // 幣安每 3 分鐘 ping 一次，要回 pong
      if (op === 10) continue;
      if (op === 0) { if (!this.frag) continue; this.frag.push(Buffer.from(p)); if (fin) { const all = Buffer.concat(this.frag); this.frag = null; this.emit('message', all.toString('utf8')); } continue; }
      if (op === 1 || op === 2) { if (fin) this.emit('message', p.toString('utf8')); else this.frag = [Buffer.from(p)]; }
    }
  }
  frame(op, payload = Buffer.alloc(0)) {                // 用戶端送出的資料一定要加遮罩
    if (!this.open || this.sock.destroyed) return;
    const n = payload.length, mk = crypto.randomBytes(4);
    let h;
    if (n < 126) h = Buffer.from([0x80 | op, 0x80 | n]);
    else if (n < 65536) { h = Buffer.alloc(4); h[0] = 0x80 | op; h[1] = 0x80 | 126; h.writeUInt16BE(n, 2); }
    else { h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 0x80 | 127; h.writeBigUInt64BE(BigInt(n), 2); }
    const p = Buffer.from(payload); for (let j = 0; j < n; j++) p[j] ^= mk[j & 3];
    this.sock.write(Buffer.concat([h, mk, p]));
  }
  send(text) { this.frame(1, Buffer.from(text, 'utf8')); }
  kill(why) { if (this.closed) return; this.closed = true; this.open = false; try { this.sock.destroy(); } catch (e) {} this.emit('close', why); }
}

const WH_WS = (process.env.BINANCE_WS || 'wss://fstream.binance.com/market').replace(/\/+$/, '');
const WH_BASE = ['BTCUSDT', 'ETHUSDT', 'SOLUSDT', 'BNBUSDT', 'XRPUSDT', 'DOGEUSDT', 'ADAUSDT', 'AVAXUSDT', 'LINKUSDT', 'SUIUSDT', 'LTCUSDT', 'TRXUSDT', 'HYPEUSDT'];   // 網站幣種選單上的幣，24 小時一直收
const WH_KEEP = 60 * 60000, WH_MIN = 250000, WH_EXTRA = 10, WH_IDLE = 15 * 60000;
const WH = { ws: null, open: false, connAt: 0, msgAt: 0, retry: 0, err: '', subs: new Set(), d: new Map(), want: new Map(), id: 1, downAt: 0, gaps: [], timer: null };
function whData(sym) {
  let d = WH.d.get(sym);
  if (!d) { d = { since: WH.open ? Date.now() : 0, trades: [], bk: new Map(), lastId: 0, last: 0, ratio: [], ratioAt: 0, ratioBusy: false }; WH.d.set(sym, d); }
  return d;
}
function whSyms() { return [...new Set([...WH_BASE, ...WH.want.keys()])]; }
function whConnect() {
  clearTimeout(WH.timer); WH.timer = null;
  const syms = whSyms(); WH.subs = new Set(syms);
  let ws;
  try { ws = new MiniWS(`${WH_WS}/stream?streams=${syms.map(s => s.toLowerCase() + '@aggTrade').join('/')}`); }
  catch (e) { WH.err = e.message; WH.retry++; WH.timer = setTimeout(whConnect, Math.min(60, 2 * WH.retry) * 1000); return; }
  WH.ws = ws;
  ws.on('open', () => {
    const now = Date.now();
    WH.open = true; WH.connAt = now; WH.msgAt = now; WH.retry = 0; WH.err = '';
    if (WH.downAt) { WH.gaps.push([WH.downAt, now]); WH.downAt = 0; }
    for (const s of syms) { const d = whData(s); if (!d.since) d.since = now; }
    log('鯨魚大單：已連上幣安 WebSocket，', syms.length, '個幣');
  });
  ws.on('message', txt => {
    WH.msgAt = Date.now();
    let m; try { m = JSON.parse(txt); } catch (e) { return; }
    const t = m && m.data;
    if (!t || t.e !== 'aggTrade') return;
    whIngest(String(t.s), t);
  });
  ws.on('close', why => {
    if (WH.ws !== ws) return;
    if (WH.open) { WH.downAt = Date.now(); log('鯨魚大單：WebSocket 斷線，', why); }
    WH.ws = null; WH.open = false; WH.err = why; WH.retry++;
    WH.timer = setTimeout(whConnect, Math.min(60, 2 * WH.retry) * 1000);   // 2、4、6…最多 60 秒後重連
  });
}
function whIngest(sym, r) {
  const d = WH.d.get(sym); if (!d) return;
  const id = +r.a, t = +r.T, p = +r.p, q = +r.q, v = p * q, sell = !!r.m;
  if (!(id > d.lastId) || !Number.isFinite(v)) return;
  d.lastId = id; d.last = t;
  const k = Math.floor(t / 60000) * 60000;
  let b = d.bk.get(k); if (!b) { b = [0, 0]; d.bk.set(k, b); }
  b[sell ? 1 : 0] += v;
  if (v >= WH_MIN) d.trades.push({ id, t, p, q, v, sell });
}
function whSub(method, syms) {
  if (!WH.open || !syms.length) return;
  WH.ws.send(JSON.stringify({ method, params: syms.map(s => s.toLowerCase() + '@aggTrade'), id: WH.id++ }));
  for (const s of syms) method === 'SUBSCRIBE' ? WH.subs.add(s) : WH.subs.delete(s);
}
function whPrune() {
  const now = Date.now(), cut = now - WH_KEEP;
  for (const d of WH.d.values()) {
    if (d.trades.length && d.trades[0].t < cut) d.trades = d.trades.filter(x => x.t >= cut);
    for (const k of d.bk.keys()) if (k < cut - 60000) d.bk.delete(k);
  }
  WH.gaps = WH.gaps.filter(g => g[1] >= cut);
  const drop = [];                                       // 自己輸入的幣：15 分鐘沒人看就停止收集
  for (const [s, at] of WH.want) if (now - at > WH_IDLE && !WH_BASE.includes(s)) { WH.want.delete(s); WH.d.delete(s); drop.push(s); }
  whSub('UNSUBSCRIBE', drop.filter(s => WH.subs.has(s)));
  if (WH.open && now - WH.msgAt > 90000) WH.ws.kill('90 秒沒有收到成交');      // 13 個主流幣同時 90 秒沒成交，代表連線卡住了
  if (WH.open && now - WH.connAt > 23 * HOUR) WH.ws.kill('定期重連');           // 幣安 24 小時會強制斷線，提前自己重連
}
function whWant(sym) {
  const now = Date.now();
  if (WH_BASE.includes(sym)) return whData(sym);
  if (!WH.want.has(sym) && WH.want.size >= WH_EXTRA) {   // 太多自己輸入的幣：把最久沒人看的那個停掉
    const old = [...WH.want.entries()].sort((a, b) => a[1] - b[1])[0][0];
    WH.want.delete(old); WH.d.delete(old); whSub('UNSUBSCRIBE', [old]);
  }
  WH.want.set(sym, now);
  const d = whData(sym);
  if (!WH.subs.has(sym)) whSub('SUBSCRIBE', [sym]);
  return d;
}
async function whRatio(sym, d) {
  if (d.ratioBusy || Date.now() - d.ratioAt < 60000) return;
  d.ratioBusy = true;
  try {
    const rows = await getJSON(`${BF}/futures/data/topLongShortPositionRatio?symbol=${sym}&period=5m&limit=12`);
    d.ratio = rows.map(r => ({ t: +r.timestamp, r: +r.longShortRatio, L: +r.longAccount, S: +r.shortAccount }));
  } catch (e) {}
  d.ratioAt = Date.now(); d.ratioBusy = false;
}
function whOut(sym, after) {
  const d = whWant(sym); whRatio(sym, d);
  const full = !(after > 0) || after > d.lastId;      // 第一次或幣安重新編號：整包重傳；之後只傳新的大單
  return {
    sym, live: WH.open, err: WH.open ? '' : WH.err, since: d.since, last: d.last, aid: d.lastId, full,
    trades: full ? d.trades : d.trades.filter(x => x.id > after),
    bk: [...d.bk.entries()].map(([k, b]) => [k, Math.round(b[0]), Math.round(b[1])]),
    ratio: d.ratio, gaps: WH.gaps
  };
}
setInterval(whPrune, 15000);
setTimeout(whConnect, 2000);

/* ---------------- 💰 AWS 帳單提醒（傳到 Discord） ----------------
   伺服器沒有 AWS 帳號權限，讀不到真正的帳單，所以是用「主機建立日」推算：
   Lightsail $5 方案從建立起大約 90 天免費 → 結束前 7 天、前 1 天、結束當天各提醒一次；之後每月 1 號提醒一次。 */
const DEF_AWS = { on: true, created: 0, auto: true, price: 5, sent: {} };
ST.aws = { ...DEF_AWS, ...(ST.aws || {}) };
const AWS_FREE_DAYS = 90, DAY = 24 * HOUR;
function awsDetect() {                                  // 主機第一次開機時 cloud-init 會建立這個資料夾，它的建立時間≈主機建立日
  for (const p of ['/var/lib/cloud/instance', '/etc/machine-id']) {
    try { const t = fs.statSync(p).birthtimeMs; if (t > Date.UTC(2024, 0, 1) && t <= Date.now()) return Math.round(t); } catch (e) {}
  }
  return 0;
}
if (ST.aws.auto) { const t = awsDetect(); if (t && t !== ST.aws.created) { ST.aws.created = t; dirty = true; } }
const twDate = t => { const d = new Date(t + TZ); return `${d.getUTCFullYear()}/${p2(d.getUTCMonth() + 1)}/${p2(d.getUTCDate())}`; };
function awsPlan(now = Date.now()) {                   // 列出所有提醒時間點（台北時間早上 10 點送）
  const A = ST.aws, ev = [], at10 = t => { const d = new Date(t + TZ); return Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate(), 10) - TZ; };
  const end = A.created ? A.created + AWS_FREE_DAYS * DAY : 0;
  if (end) {
    ev.push({ k: 'free-7', at: at10(end - 7 * DAY), win: 6 * DAY, msg: `💰 **AWS 帳單提醒**｜Lightsail 免費期剩 **${Math.max(1, Math.ceil((end - now) / DAY))} 天**\n預計 **${twDate(end)}** 結束，之後每月約 **$${A.price} 美元**（雪梨主機＋固定 IP）。\n還要繼續跑就不用做任何事；不用了請到 Lightsail 把**主機和固定 IP 都刪掉**（只刪主機，固定 IP 還是會收錢）。` });
    ev.push({ k: 'free-1', at: at10(end - DAY), win: DAY - HOUR, msg: `💰 **AWS 帳單提醒**｜Lightsail 免費期**明天**（${twDate(end)}）結束\n之後每月約 **$${A.price} 美元**。不用了請今天把主機和固定 IP 都刪掉。` });
    ev.push({ k: 'free-0', at: Math.max(end, at10(end)), win: 3 * DAY, msg: `💰 **AWS 帳單提醒**｜Lightsail 免費期已結束，從今天開始計費（每月約 **$${A.price} 美元**）\n之後每月 1 號會提醒一次。實際金額請以 AWS Billing 為準。` });
  }
  const d = new Date(now + TZ), m1 = Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), 1, 10) - TZ;
  if (!end || m1 >= end + DAY) ev.push({ k: 'm-' + twDate(m1).slice(0, 7), at: m1, win: 3 * DAY, msg: `💰 **AWS 帳單提醒**｜${d.getUTCMonth() + 1} 月\nLightsail 雪梨主機這個月約 **$${A.price} 美元**（流量超過方案額度才會多收）。\n建議到 AWS Billing 看一下上個月的帳單；不用了請把**主機和固定 IP 都刪掉**。` });
  return { end, ev };
}
function awsTick() {
  const A = ST.aws, OX = ctx(ownerUid()), ON = OX.A.notify; if (!A.on || !ON.enabled || !ON.webhook) return;   // 帳單只跟擁有者有關
  const now = Date.now(), { ev } = awsPlan(now);
  if (!A.sent.hello) {
    A.sent.hello = now; dirty = true;
    const { end, next } = awsNext();
    dcX(OX, `💰 **AWS 帳單提醒已開啟**\n${end ? `Lightsail 免費期預計到 **${twDate(end)}**（主機建立日 ${twDate(A.created)} ＋ 90 天）` : '還不知道主機建立日，請到網站「☁ 雲端伺服器」填寫'}\n${next ? `下一次提醒：${tw(next)}（台北）` : ''}\n-# 伺服器讀不到真正的帳單，日期是推算的；實際金額以 AWS Billing 為準`);
  }
  for (const e of ev) {
    if (A.sent[e.k] || now < e.at) continue;
    A.sent[e.k] = now; dirty = true;                     // 錯過太久（例如伺服器當時沒開）就不補發舊的
    if (now - e.at <= e.win) dcX(OX, e.msg);
  }
}
function awsNext() {                                    // 給網頁顯示「下一次提醒」
  const now = Date.now(), { end, ev } = awsPlan(now), A = ST.aws;
  const nx = ev.filter(e => !A.sent[e.k] && e.at > now).map(e => e.at);
  const d = new Date(now + TZ), m2 = Date.UTC(d.getUTCFullYear(), d.getUTCMonth() + 1, 1, 10) - TZ;
  if (!end || m2 >= end + DAY) nx.push(m2);
  return { end, next: nx.length ? Math.min(...nx) : 0 };
}
let AWS_T = setTimeout(awsTick, 60000);
setInterval(awsTick, 10 * 60000);

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
/* ---------------- 帳號綁定：Google 信箱＋手機號碼，綁好才能用網站 ----------------
   有設定 Google 用戶端 ID：用 Google 登入按鈕驗證信箱（伺服器向 Google 確認）；還沒設定：先手動輸入 Gmail。
   手機號碼目前只檢查格式（簡訊驗證碼要接付費簡訊服務）。同一個信箱、同一支手機只能綁一個帳號。 */
const GOOGLE_INFO = process.env.GOOGLE_TOKENINFO || 'https://oauth2.googleapis.com/tokeninfo';
const gClient = () => process.env.GOOGLE_CLIENT_ID || ST.google.clientId || '';
const normPhone = x => {
  let v = String(x || '').replace(/[\s\-()（）]/g, '');
  if (/^09\d{8}$/.test(v)) v = '+886' + v.slice(1);                   // 台灣手機 09xx → +8869xx
  else if (/^8869\d{8}$/.test(v)) v = '+' + v;
  else if (/^\+8860?9\d{8}$/.test(v)) v = '+8869' + v.slice(-8);
  return /^\+[1-9]\d{7,14}$/.test(v) ? v : '';
};
const needBind = usr => !!usr && !(usr.bind && usr.bind.email && usr.bind.phone);
const bindOut = usr => (usr && usr.bind ? { email: usr.bind.email, phone: usr.bind.phone, google: !!usr.bind.google, at: usr.bind.at } : null);
async function googleEmail(cred, cid) {               // 向 Google 確認登入憑證是真的、是發給我們網站的、信箱已驗證
  const r = await fetch(GOOGLE_INFO + '?id_token=' + encodeURIComponent(cred), { signal: AbortSignal.timeout(15000) }).catch(() => null);
  const j = r && r.ok ? await r.json().catch(() => null) : null;
  if (!j || j.aud !== cid || !['accounts.google.com', 'https://accounts.google.com'].includes(j.iss) || String(j.email_verified) !== 'true' || !(+j.exp * 1000 > Date.now()) || !j.email) return '';
  return String(j.email).toLowerCase();
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
        if (ST.accts.__owner && !ST.accts[usr.uid]) { ST.accts[usr.uid] = ST.accts.__owner; delete ST.accts.__owner; RT.delete('__owner'); }   // 還沒建帳號前存的資料交給第一個管理員
        ST.owner = usr.uid; dirty = true;
        return send(res, 200, { token: newSession(usr), uid: usr.uid, role: usr.role });
      }
      const usr = ST.users.find(x => x.uid === String(b.uid || ''));
      if (!usr || !validPw(b.password) || !pwOk(usr, b.password)) { failed(ip); return send(res, 401, { error: 'UID 或密碼不對' }); }
      FAILS.delete(ip);
      return send(res, 200, { token: newSession(usr), uid: usr.uid, role: usr.role });
    }
    const me = who(req), admin = keyOk(req) || (me && me.role === 'admin');
    if (u.pathname.startsWith('/api/') && !me && !keyOk(req)) return send(res, 401, { error: '請先登入', needLogin: true, needSetup: !ST.users.length });
    if (me && needBind(me) && u.pathname !== '/api/me' && u.pathname !== '/api/bind') return send(res, 403, { error: '請先綁定 Google 信箱和手機號碼', needBind: true });
    const X = ctx(me ? me.uid : ownerUid());          // 這次請求的「自己」：每個帳號只看得到、改得到自己的 Bitunix／自動交易／Discord（用管理金鑰登入＝擁有者）
    if (req.method === 'GET' && u.pathname === '/api/me') return send(res, 200, { uid: me ? me.uid : '管理金鑰', role: admin ? 'admin' : 'viewer', owner: X.uid === ownerUid(), needBind: needBind(me), bind: bindOut(me), google: gClient() });
    if (req.method === 'GET' && u.pathname === '/api/users') {
      if (!admin) return send(res, 403, { error: '只有管理員可以看' });
      return send(res, 200, { users: ST.users.map(x => { const A = ST.accts[x.uid]; return { uid: x.uid, role: x.role, created: x.created, last: x.last || 0, sessions: ST.sessions.filter(s => s.uid === x.uid && s.exp > Date.now()).length,
        api: !!(A && A.bx.key), auto: !!(A && A.lt.on), open: A ? A.ltTrades.filter(t => t.status === 'open').length : 0, owner: x.uid === ownerUid(), bind: bindOut(x) }; }), google: gClient(), googleEnv: !!process.env.GOOGLE_CLIENT_ID });   // 只給管理員看「有沒有設」，不會給金鑰
    }
    if (req.method === 'GET' && u.pathname === '/api/users/view') {      // 管理員查看某個帳號的狀況：只能看，沒有任何能動倉位或資金的東西，也不會給金鑰
      if (!admin) return send(res, 403, { error: '只有管理員可以看' });
      const usr = ST.users.find(x => x.uid === String(u.searchParams.get('uid') || ''));
      if (!usr) return send(res, 404, { error: '找不到這個帳號' });
      const out = { uid: usr.uid, role: usr.role, owner: usr.uid === ownerUid(), bind: bindOut(usr), last: usr.last || 0, created: usr.created || 0 };
      if (!ST.accts[usr.uid]) return send(res, 200, { ...out, api: false, empty: true });
      const V = ctx(usr.uid), L = V.A.lt, TR = V.A.ltTrades.filter(t => t.et >= (L.startAt || 0));
      const done = TR.filter(t => t.status === 'closed'), net = done.reduce((a, t) => a + ltNet(t), 0);
      return send(res, 200, {
        ...out, api: hasKey(V), err: V.BX.err, at: V.BX.at, acctEq: bxEquity(V), bot: ltBotEq(V), dayPnl: V.LT.dayPnl || 0, msg: V.LT.msg, hook: !!V.A.notify.webhook,
        lt: { on: L.on, budget: L.budget, margin: L.margin, lev: L.lev, dayLoss: L.dayLoss, sl: L.sl, step: L.step, hold: L.hold, startCap: L.startCap, startAt: L.startAt },
        pos: V.BX.pos.map(p => ({ sym: p.sym, dir: p.dir, lev: p.lev, qty: p.qty, entry: p.entry, px: PX.map[p.sym] || null, upnl: p.upnl, margin: p.margin, liq: p.liq, ctime: p.ctime, bot: !!V.A.ltTrades.find(t => t.status === 'open' && t.positionId === p.id) })),
        stats: { n: done.length, win: done.filter(t => ltNet(t) > 0).length, net, fee: TR.reduce((a, t) => a + Math.abs(t.fee || 0), 0) },
        trades: V.A.ltTrades.slice(0, 30).map(t => ({ sym: t.sym, dir: t.dir, lev: t.lev, et: t.et, exitAt: t.exitAt || 0, status: t.status, reason: t.reason || '', net: ltNet(t), upnl: t.upnl || 0, m0: t.m0 || 0 }))
      });
    }
    if (req.method === 'GET' && u.pathname === '/api/whale') {          // 🐋 鯨魚大單：?sym=BTCUSDT&a=上次收到的最後一筆成交編號
      const sym = String(u.searchParams.get('sym') || 'BTCUSDT').toUpperCase();
      if (!/^[A-Z0-9]{2,30}USDT$/.test(sym)) return send(res, 400, { error: '幣種格式不對' });
      if (!WH_BASE.includes(sym) && !WH.want.has(sym) && BN.meta && !BN.meta.ok.has(sym)) return send(res, 400, { error: `幣安沒有 ${sym} 永續合約` });
      return send(res, 200, whOut(sym, +u.searchParams.get('a') || 0));
    }
    if (req.method === 'GET' && u.pathname === '/api/state') {
      const out = {
        time: Date.now(), ver: '2026-10-19b', cv: CV, bv: BV, set: ST.set, trade: ST.trade, canWrite: !!ADMIN_KEY,
        scan: { ...SCAN, pause: RL.pause }, bt: { at: ST.bt.at, coins: ST.bt.coins, n: ST.bt.trades.length }, btp: BTP,
        notify: { enabled: X.A.notify.enabled, entry: X.A.notify.entry, exit: X.A.notify.exit, hasHook: !!X.A.notify.webhook, name: X.A.notify.name },
        me: { uid: me ? me.uid : '管理金鑰', admin, owner: X.uid === ownerUid() },
        eq: ST.eq, rep: { ...ST.rep, busy: REP.busy, msg: REP.msg }, rv: RV,
        bx: { set: hasKey(X), notify: X.A.bx.notify, liq: X.A.bx.liq, liqPct: X.A.bx.liqPct, at: X.BX.at, err: X.BX.err, acct: X.BX.acct,
          pos: X.BX.pos.map(p => ({ ...p, px: PX.map[p.sym] || null, sig: !!ST.cards.find(c => c.sym === p.sym && c.dir === p.dir && c.et && isLive(c)), bot: !!X.A.ltTrades.find(t => t.status === 'open' && t.positionId === p.id) })) },
        eco: { list: ECO.list.filter(e => e.t > Date.now() - 7 * 24 * HOUR), at: ECO.at, err: ECO.err, hasNext: !!ECO.hasNext },
        lt: { cfg: X.A.lt, msg: X.LT.msg, dayPnl: X.LT.dayPnl || 0, v: X.v, bot: ltBotEq(X), acctEq: bxEquity(X) },
        aws: !(X.uid === ownerUid()) ? null : { on: ST.aws.on, created: ST.aws.created, auto: ST.aws.auto, price: ST.aws.price, detected: awsDetect(), ...awsNext() }
      };
      if (+u.searchParams.get('cv') !== CV) out.cards = ST.cards;
      if (+u.searchParams.get('bv') !== BV) out.trades = ST.bt.trades;
      if (+u.searchParams.get('rv') !== RV) out.reports = ST.reports;
      if (+u.searchParams.get('lv') !== X.v) out.ltTrades = X.A.ltTrades.map(({ closing, ...t }) => t);
      return send(res, 200, out);
    }
    if (req.method === 'POST' && u.pathname.startsWith('/api/')) {
      // 個人設定：每個帳號都能改「自己的」；其他（掃描條件、浮盈規則、回測、帳號管理、AWS）只有管理員能改
      const PERSONAL = ['/api/bind', '/api/bitunix', '/api/lt/config', '/api/lt/testOpen', '/api/lt/close', '/api/lt/closeAll', '/api/notify', '/api/notify/test'];
      if (!PERSONAL.includes(u.pathname) && !admin) return send(res, 403, { error: '這個設定只有管理員可以改' });
      const b = await readBody(req);
      if (u.pathname === '/api/users') {               // 後台：新增帳號／改密碼／改權限
        if (!validUid(b.uid)) return send(res, 400, { error: 'UID 應該是 4～20 位數字' });
        let usr = ST.users.find(x => x.uid === String(b.uid));
        if (!usr) { if (!validPw(b.password)) return send(res, 400, { error: '新帳號要設定密碼，至少 8 個字' }); usr = { uid: String(b.uid), role: 'viewer', created: Date.now() }; ST.users.push(usr); }
        if (b.password) { if (!validPw(b.password)) return send(res, 400, { error: '密碼至少 8 個字' }); Object.assign(usr, hashPw(b.password)); ST.sessions = ST.sessions.filter(s => s.uid !== usr.uid || (me && s.uid === me.uid)); }
        if (b.unbind) { delete usr.bind; ST.sessions = ST.sessions.filter(s => s.uid !== usr.uid); }   // 重設綁定：對方下次登入要重新綁定
        if (b.role === 'admin' || b.role === 'viewer') {
          if (b.role === 'viewer' && usr.uid === ownerUid()) return send(res, 400, { error: '擁有者帳號一定是管理員' });
          if (b.role === 'viewer' && usr.role === 'admin' && ST.users.filter(x => x.role === 'admin').length <= 1) return send(res, 400, { error: '至少要留一個管理員' });
          usr.role = b.role;
        }
        dirty = true; return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/bind') {
        if (!me) return send(res, 400, { error: '用管理金鑰登入不需要綁定' });
        if (!needBind(me)) return send(res, 400, { error: '這個帳號已經綁定過了，要更換請找管理員重設' });
        const phone = normPhone(b.phone);
        if (!phone) return send(res, 400, { error: '手機號碼格式不對（台灣手機請填 09 開頭的 10 碼，其他國家請加 + 和國碼）' });
        const cid = gClient(); let email = '', google = false;
        if (cid) {
          if (!b.credential) return send(res, 400, { error: '請按「使用 Google 帳號登入」驗證信箱' });
          email = await googleEmail(String(b.credential), cid); google = true;
          if (!email) return send(res, 400, { error: 'Google 驗證失敗，請重新按一次 Google 按鈕' });
        } else {
          email = String(b.email || '').trim().toLowerCase();
          if (!/^[a-z0-9.+_-]{3,64}@(gmail|googlemail)\.com$/.test(email)) return send(res, 400, { error: '請輸入 Google 信箱（@gmail.com）' });
        }
        const dup = ST.users.find(x => x !== me && x.bind && (x.bind.email === email || x.bind.phone === phone));
        if (dup) return send(res, 400, { error: dup.bind.email === email ? '這個 Google 信箱已經綁定別的帳號了' : '這支手機號碼已經綁定別的帳號了' });
        me.bind = { email, phone, google, at: Date.now() }; dirty = true;
        log('帳號綁定', me.uid, email, google ? '（Google 驗證）' : '（手動輸入）');
        return send(res, 200, { ok: true, bind: bindOut(me) });
      }
      if (u.pathname === '/api/google') {             // 管理員設定 Google 用戶端 ID（空白＝改回手動輸入 Gmail）
        const id = String(b.clientId || '').trim();
        if (id && !/^[\w-]+\.apps\.googleusercontent\.com$/.test(id)) return send(res, 400, { error: '格式不對，應該是 xxxx.apps.googleusercontent.com' });
        ST.google.clientId = id; dirty = true; return send(res, 200, { ok: true, google: gClient() });
      }
      if (u.pathname === '/api/users/delete') {
        const usr = ST.users.find(x => x.uid === String(b.uid)); if (!usr) return send(res, 404, { error: '找不到這個帳號' });
        if (usr.uid === ownerUid()) return send(res, 400, { error: '擁有者帳號不能刪除' });
        if (usr.role === 'admin' && ST.users.filter(x => x.role === 'admin').length <= 1) return send(res, 400, { error: '至少要留一個管理員' });
        const UA = ST.accts[usr.uid], nOpen = UA ? UA.ltTrades.filter(t => t.status === 'open').length : 0;
        if (nOpen) return send(res, 400, { error: `這個帳號還有 ${nOpen} 筆自動單持倉，刪掉的話就沒有人管理了。請對方先平倉，或先讓他按「暫停交易」並等持倉結束` });
        ST.users = ST.users.filter(x => x !== usr); ST.sessions = ST.sessions.filter(s => s.uid !== usr.uid);
        delete ST.accts[usr.uid]; RT.delete(usr.uid); dirty = true;            // 他的金鑰、紀錄、Webhook 一起刪掉
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
        const C = X.A.bx, BX = X.BX;
        if (b.clear) {
          if (ltOpenTrades(X).length) return send(res, 400, { error: `還有 ${ltOpenTrades(X).length} 筆自動單持倉，刪掉金鑰就沒辦法管理了，請先平倉` });
          Object.assign(C, DEF_BX); X.A.lt.on = false; BX.pos = []; BX.acct = null; BX.seeded = false; touchLT(X); return send(res, 200, { ok: true });
        }
        if (typeof b.key === 'string' && b.key.trim() && typeof b.secret === 'string' && b.secret.trim()) {
          const cfg = { ...C, key: b.key.trim(), secret: b.secret.trim() };
          try { await bxGet('/api/v1/futures/position/get_pending_positions', {}, cfg); }        // 先試一次，金鑰對了才存
          catch (e) { return send(res, 400, { error: e.message + '。請確認金鑰、密鑰沒有複製錯，而且 API 有綁定這台伺服器的 IP' }); }
          const other = Object.entries(ST.accts).find(([id, A]) => id !== X.uid && A.bx.key === cfg.key);
          if (other) return send(res, 400, { error: '這組 API 已經有別的帳號在用了。同一個 Bitunix 帳戶只能給一個人自動交易，不然會互相下單、互相平倉' });
          const changed = C.key !== cfg.key;
          if (changed && ltOpenTrades(X).length) return send(res, 400, { error: `還有 ${ltOpenTrades(X).length} 筆自動單持倉，換金鑰就沒辦法管理了，請先平倉` });
          C.key = cfg.key; C.secret = cfg.secret; BX.seeded = false; BX.pos = []; BX.acct = null;
          if (changed) { X.A.lt.on = false; X.A.lt.startCap = 0; X.A.lt.startAt = Date.now(); X.LT.lev = {}; touchLT(X); }   // 換帳號：先暫停，統計等讀到新帳戶的資金再開始
        }
        for (const k of ['notify', 'liq']) if (typeof b[k] === 'boolean') C[k] = b[k];
        if (+b.liqPct > 0) C.liqPct = +b.liqPct;
        dirty = true; bxPollOne(X);
        return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/lt/config') {
        const C = X.A.lt;
        if (typeof b.on === 'boolean') {
          if (b.on && !hasKey(X)) return send(res, 400, { error: '請先設定你自己的 Bitunix API 金鑰（要開交易權限）' });
          C.on = b.on; dcX(X, b.on ? '▶️ **自動交易已開始**' : '⏸ **自動交易已暫停**（已開的單照常管理）');
        }
        if (+b.margin > 0) C.margin = +b.margin;
        if (+b.lev >= 1 && +b.lev <= 125) C.lev = Math.round(+b.lev);
        if (+b.maxOpen >= 0) C.maxOpen = Math.round(+b.maxOpen);
        if (+b.dayLoss >= 0) C.dayLoss = +b.dayLoss;
        if (b.budget !== undefined && +b.budget >= 0) {
          const e = bxEquity(X);
          if (+b.budget > 0 && !hasKey(X)) return send(res, 400, { error: '請先設定 Bitunix API，才知道合約帳戶有多少資金' });
          if (+b.budget > 0 && !(e > 0)) return send(res, 400, { error: '還沒讀到合約帳戶的資金，請等 10 秒再試' });
          if (+b.budget > e + 1e-9) return send(res, 400, { error: `投入資金不能大於合約帳戶目前的資金 ${e.toFixed(2)}U` });
          C.budget = +b.budget;
        }
        let rule = false;                                // 個人的出場規則
        if (b.sl !== undefined) { const v = +b.sl; if (!(v >= 10 && v <= 1000)) return send(res, 400, { error: '浮虧 % 要在 10～1000 之間' }); C.sl = v; rule = true; }
        if (b.step !== undefined) { const v = +b.step; if (!(v >= 0 && v <= 1000)) return send(res, 400, { error: '鎖利線上調要在 0～1000 之間' }); C.step = v; rule = true; }
        if (b.hold !== undefined) { const v = +b.hold; if (!(v >= 1 && v <= 720)) return send(res, 400, { error: '持有時間要在 1 小時～30 天之間' }); C.hold = v; rule = true; }
        if (+b.lev >= 1 && +b.lev <= 125) rule = true;
        if (rule && X.uid === ownerUid()) {             // 擁有者的設定也拿來當「訊號模擬、回測、Discord 訊號通知」的共用規則
          Object.assign(ST.trade, { sl: C.sl, step: C.step, hold: C.hold, lev: C.lev });
          CACHE.clear(); markSettledNotified(); touchCards();
        }
        if (b.reset) { const e = bxEquity(X); C.startAt = Date.now(); C.startCap = C.budget > 0 ? C.budget : e > 0 ? Math.round(e * 100) / 100 : 0; }   // 有設投入資金就用它，沒有就用目前帳戶權益
        touchLT(X); return send(res, 200, { ok: true, cfg: C });
      }
      if (u.pathname === '/api/lt/testOpen' && process.env.LT_TEST === '1') { await ltOpen(X, { id: 'test', sym: b.sym, dir: b.dir || 1, abN: 2, last: 1 }); return send(res, 200, { ok: true, msg: X.LT.msg }); }
      if (u.pathname === '/api/lt/close') {
        const pct = Math.min(1, Math.max(0.01, +b.pct || 1));
        try { const r = await ltClosePos(X, String(b.positionId), pct, 'manual'); setTimeout(() => bxPollOne(X), 1500); return send(res, 200, { ok: true, r }); }
        catch (e) { return send(res, 400, { error: e.message }); }
      }
      if (u.pathname === '/api/lt/closeAll') {
        // 只平自動下單的倉位：手動開的單（含「符合訊號」）一律不動
        if (!hasKey(X)) return send(res, 400, { error: '還沒設定 Bitunix API 金鑰' });
        if (b.pause) X.A.lt.on = false;
        let pos = X.BX.pos;
        try { pos = bxMapPos(await bxGet('/api/v1/futures/position/get_pending_positions', {}, X.A.bx)); } catch (e) {}   // 先重新讀一次，剛開的自動單也平得到
        const open = ltOpenTrades(X), ids = new Set(open.map(t => t.positionId).filter(Boolean));
        const mine = pos.filter(p => ids.has(p.id) || open.some(t => !t.positionId && t.sym === p.sym && t.dir === p.dir && Math.abs((p.ctime || 0) - t.et) < 5 * 60000));
        for (const t of open) { t.pendReason = 'all'; t.pendAt = Date.now(); }
        let ok = 0; const fails = [];
        for (const p of mine) {
          try { await fullClose(X, p, true); ok++; } catch (e2) { fails.push(`${p.sym}（${e2.message}）`); }
          await sleep(300);
        }
        const nMan = pos.length - mine.length;
        touchLT(X); setTimeout(() => bxPollOne(X), 1500);
        dcX(X, `🛑 **一鍵平倉（自動單）**：成功 ${ok} 筆${fails.length ? `，失敗 ${fails.length} 筆：${mdEsc(fails.join('、'))}` : ''}${nMan ? `；手動單 ${nMan} 筆沒有動` : ''}${b.pause ? '，並暫停自動交易' : ''}`);
        if (fails.length) return send(res, 400, { error: `平倉成功 ${ok} 筆，失敗 ${fails.length} 筆：${fails.join('、')}` });
        return send(res, 200, { ok: true, n: ok });
      }
      if (u.pathname === '/api/report/history') { if (REP.busy) return send(res, 409, { error: '正在結算中，請稍等' }); historyReports(Math.min(26, Math.max(1, +b.periods || 15))); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/report/settle') { if (REP.busy) return send(res, 409, { error: '正在結算中，請稍等' }); settle(true); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/notify') {
        const N = X.A.notify;                          // 每個帳號自己的 Discord，自己決定開不開
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
      if (u.pathname === '/api/aws') {                 // 💰 AWS 帳單提醒：開關、主機建立日（auto＝自動偵測）
        const A = ST.aws;
        if (typeof b.on === 'boolean') { A.on = b.on; if (b.on) delete A.sent.hello; }
        if (b.created === 'auto') { A.auto = true; A.created = awsDetect() || A.created; }
        else if (b.created !== undefined) {
          const t = +b.created;
          if (!(t > Date.UTC(2020, 0, 1) && t <= Date.now() + DAY)) return send(res, 400, { error: '日期不對' });
          A.auto = false; A.created = t;
        }
        if (b.created !== undefined) { for (const k of Object.keys(A.sent)) if (k.startsWith('free-')) delete A.sent[k]; delete A.sent.hello; }   // 改了日期：免費期提醒重新算
        if (b.price !== undefined) { const v = +b.price; if (!(v > 0 && v < 1000)) return send(res, 400, { error: '金額不對' }); A.price = v; }
        dirty = true; clearTimeout(AWS_T); AWS_T = setTimeout(awsTick, 8000);   // 連續改好幾次只發一則確認
        return send(res, 200, { ok: true, ...awsNext() });
      }
      if (u.pathname === '/api/notify/test') {
        const ok = await dcX(X, '🔔 **合約量化進場**：通知測試成功！之後每次有新訊號進場、結單，都會傳到這個頻道。');
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

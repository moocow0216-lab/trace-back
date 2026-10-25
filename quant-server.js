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
const os = require('os');
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
const DEF_SET = { flat: 2, range: 6, minVol: 500, win: 4, sens: 1, zSum: 5, zBar: 5, minN: 2, logic: 'follow', everyS: 10, btcF: 1, btcMode: '24h', btcWith: 2, btcAgainst: 4 };   // btcF：進場前先看 BTC 方向；順勢至少 btcWith 項異常、逆勢至少 btcAgainst 項
const DEF_TRADE = { tp: 250, sl: 250, lev: 100, hold: 24, exit: 'lock', step: 50 };   // step：達標後浮盈每多幾 %，鎖利線就往上調一格（0＝固定鎖在達標線）
// 鎖利線：最高浮盈 peak（%）→ 鎖在哪裡（%）。例：達標 250、間距 50 → 最高 260 鎖 250、最高 300 鎖 300、最高 349 鎖 300
const lockAt = (peak, T = ST.trade) => (T.step > 0 && peak > T.tp ? T.tp + Math.floor((peak - T.tp) / T.step + 1e-9) * T.step : T.tp);
const DEF_NOTIFY = { webhook: '', name: '', enabled: true, entry: true, exit: true };
const DEF_EQ = { mode: 'fixed', amt: 0.3, fee: 0.05, max: 0 };
const DEF_BX = { key: '', secret: '', notify: true, liq: true, liqPct: 3 };
const RESUME = [];                                       // 🔄 重開前在跑的帳號
const DEF_LT = { on: false, sp: false, budgetAt: 0, wd: 0, spWd: 0, spLev: null, spMargin: null, spBudget: 0, spStartAt: 0, spDayLoss: null, spTp: null, spStep: null, spSl: null, spHold: null, margin: 0.3, lev: 100, mode: 'CROSS', maxOpen: 0, dayLoss: 20, startCap: 0, startAt: 0, budget: 0, tp: 250, sl: 250, step: 50, hold: 168, btcF: 1 };   // tp：浮盈達到幾 % 開始鎖利（每個帳號自己設）   // btcF：自己要不要用 BTC 方向過濾（預設開）   // sl：浮虧多少 % 平倉；step：鎖利線每多幾 % 上調；hold：最長持有（小時）——每個帳號自己設定   // budget：投入資金（0＝整個合約帳戶）   // startCap＝0 代表等偵測到帳戶資金再開始算   // 自動下單（預設暫停）   // Bitunix 唯讀 API 金鑰（只存在這台伺服器）            // 資金模擬：每筆保證金、手續費、最多同時持倉
const DEF_REP = { cap: 100, btN: 50, days: 14, next: 0 };                   // 雙週結算：每期本金、回測幣數、幾天一期、下次結算時間
let ST = { cards: [], bt: { at: 0, coins: 0, trades: [] }, set: { ...DEF_SET }, trade: { ...DEF_TRADE }, google: { clientId: '' }, eq: { ...DEF_EQ }, rep: { ...DEF_REP }, reports: [], users: [], sessions: [], accts: {}, owner: '' };
try {
  const j = JSON.parse(fs.readFileSync(FILE, 'utf8'));
  ST = { cards: j.cards || [], bt: j.bt || ST.bt, set: { ...DEF_SET, ...(j.set || {}) }, trade: { ...DEF_TRADE, ...(j.trade || {}) }, google: { clientId: '', ...(j.google || {}) }, eq: { ...DEF_EQ, ...(j.eq || {}) }, rep: { ...DEF_REP, ...(j.rep || {}) }, reports: j.reports || [], users: j.users || [], sessions: j.sessions || [], aws: j.aws || {}, accts: j.accts || {}, owner: j.owner || '', bstat: j.bstat || null, hb: j.hb || '', ecoDay: j.ecoDay || '', tool: j.tool || null, alive: j.alive || 0, boots: j.boots || [], exit: j.exit || null, hb2: j.hb2 || null, lastErr: j.lastErr || null };
  // 舊版（只有一個帳號）：原本的 Bitunix 金鑰、自動交易、實盤紀錄、Discord 搬到擁有者（第一個管理員）的帳號底下
  if (!j.accts && (j.bx || j.lt || j.ltTrades || j.notify)) {
    const a = ST.users.find(u => u.role === 'admin'), uid = a ? a.uid : '__owner';
    ST.accts[uid] = { bx: j.bx || {}, lt: j.lt || {}, ltTrades: j.ltTrades || [], notify: j.notify || {} };
    if (a) ST.owner = a.uid;
    log('舊存檔搬到帳號', uid);
  }
  for (const [uid, A] of Object.entries(ST.accts)) if (A.lt && (A.lt.on || A.lt.sp)) RESUME.push({ uid, on: !!A.lt.on, sp: !!A.lt.sp });   // 🔄 重開前在跑的帳號：約 1 分鐘後自動恢復
  for (const A of Object.values(ST.accts)) {        // 補齊欄位；伺服器重開後每個帳號的自動交易先暫停，約 1 分鐘後再自動恢復（見下面）
    A.bx = { ...DEF_BX, ...(A.bx || {}) }; A.lt = { ...DEF_LT, sl: ST.trade.sl, step: ST.trade.step, hold: ST.trade.hold, ...(A.lt || {}), on: false, sp: false };
    for (const [k, f] of [['spLev', 'lev'], ['spMargin', 'margin'], ['spDayLoss', 'dayLoss'], ['spTp', 'tp'], ['spStep', 'step'], ['spSl', 'sl'], ['spHold', 'hold']]) if (A.lt[k] == null) A.lt[k] = A.lt[f];   // 🗡 特級交易設定：第一次照抄一般交易   // 舊帳號沒有個人參數：沿用原本的共用設定 A.notify = { ...DEF_NOTIFY, ...(A.notify || {}) }; A.ltTrades = A.ltTrades || [];
    if (A.lt.budget > 0 && A.lt.startCap !== A.lt.budget) A.lt.startCap = A.lt.budget;   // 投入資金＝起始本金（盈虧紀錄保留：100U 虧到 98U，改成 50U 就是 48U）
    A.lt.spStartAt = 0;                                // 🗡 特級交易一樣：盈虧從第一筆特級單開始算，改投入資金不歸零
    if (A.lt.startCap === 100 && !A.ltTrades.length) { A.lt.startCap = 0; A.lt.startAt = 0; }   // 舊版預設把起始本金寫死成 100U
  }
  log(`讀入存檔：${ST.cards.length} 張卡片、${ST.bt.trades.length} 筆回測`);
} catch (e) { log('沒有存檔，從頭開始'); }
let CV = Date.now(), BV = Date.now();                  // 卡片、回測各自的版本號，沒變就不用重傳
let dirty = false;
const touchCards = () => { CV++; dirty = true; };
const touchBT = () => { BV++; dirty = true; };
// 🔒 存檔時把 Bitunix 金鑰和 Discord Webhook 加密（AES-256-GCM）；解密的鑰匙放在 data/secret.key（權限 600），
//    所以 state.json 或備份檔被複製走，也看不到金鑰。secret.key 不見的話，大家要重新輸入 API。
const KEYFILE = path.join(path.dirname(FILE), 'secret.key');
let SKEY = null;
try { SKEY = Buffer.from(fs.readFileSync(KEYFILE, 'utf8').trim(), 'hex'); if (SKEY.length !== 32) SKEY = null; } catch (e) {}
if (!SKEY) { SKEY = crypto.randomBytes(32); fs.writeFileSync(KEYFILE, SKEY.toString('hex'), { mode: 0o600 }); log('建立新的加密鑰匙', KEYFILE); }
function enc(v) {
  if (!v || String(v).startsWith('enc1:')) return v;
  const iv = crypto.randomBytes(12), c = crypto.createCipheriv('aes-256-gcm', SKEY, iv), d = Buffer.concat([c.update(String(v), 'utf8'), c.final()]);
  return 'enc1:' + Buffer.concat([iv, c.getAuthTag(), d]).toString('base64');
}
function dec(v) {
  if (!v || !String(v).startsWith('enc1:')) return v;
  const b = Buffer.from(String(v).slice(5), 'base64'), dc = crypto.createDecipheriv('aes-256-gcm', SKEY, b.subarray(0, 12));
  dc.setAuthTag(b.subarray(12, 28)); return Buffer.concat([dc.update(b.subarray(28)), dc.final()]).toString('utf8');
}
function snapshot() {                                  // 要寫進檔案的內容：金鑰、Webhook 加密
  const accts = {};
  for (const [id, A] of Object.entries(ST.accts)) accts[id] = { ...A, bx: { ...A.bx, key: enc(A.bx.key), secret: enc(A.bx.secret) }, notify: { ...A.notify, webhook: enc(A.notify.webhook) } };
  return JSON.stringify({ ...ST, accts });
}
function save() {
  if (!dirty) return; dirty = false;
  const tmp = FILE + '.tmp';
  fs.writeFileSync(tmp, snapshot(), { mode: 0o600 });   // 只給自己讀
  fs.renameSync(tmp, FILE);
}
// 讀檔時解密；解不開（secret.key 換了）就清掉，請那個帳號重新輸入
for (const [id, A] of Object.entries(ST.accts)) {
  for (const [o, k] of [[A.bx, 'key'], [A.bx, 'secret'], [A.notify, 'webhook']]) {
    try { o[k] = dec(o[k]); } catch (e) { o[k] = ''; log('金鑰解不開，已清除，請重新輸入', id, k); }
  }
}
if (Object.keys(ST.accts).length) dirty = true;   // 開機後馬上用加密格式重存一次（舊的明文存檔會被換掉）

// ===== 🗂 每天自動備份（保留 7 天，金鑰一樣是加密的） =====
const BACKUP_DIR = path.join(path.dirname(FILE), 'backups');
function backupTick() {
  try {
    const day = new Date(Date.now() + 8 * 3600000).toISOString().slice(0, 10), f = path.join(BACKUP_DIR, `state-${day}.json`);
    if (fs.existsSync(f)) return;
    fs.mkdirSync(BACKUP_DIR, { recursive: true, mode: 0o700 });
    fs.writeFileSync(f, snapshot(), { mode: 0o600 });
    const old = fs.readdirSync(BACKUP_DIR).filter(x => /^state-\d{4}-\d{2}-\d{2}\.json$/.test(x)).sort().slice(0, -7);
    for (const x of old) fs.unlinkSync(path.join(BACKUP_DIR, x));
    log('每日備份', f, old.length ? `，刪掉 ${old.length} 個舊備份` : '');
  } catch (e) { log('備份失敗', e.message); }
}
setTimeout(backupTick, 5 * 60000); setInterval(backupTick, 6 * HOUR);   // 每 6 小時看一次，當天還沒備份就備份
setInterval(() => { try { save(); } catch (e) { log('存檔失敗', e.message); } }, 10000);
for (const sig of ['SIGINT', 'SIGTERM']) process.on(sig, () => { dirty = true; ST.alive = Date.now(); ST.exit = { t: Date.now(), how: sig }; try { save(); } catch (e) {} process.exit(0); });   // 正常關機（更新、重開）：留紀錄
const hbNow = () => { const m = process.memoryUsage(); return { t: Date.now(), rss: Math.round(m.rss / 1048576), heap: Math.round(m.heapUsed / 1048576), free: Math.round(os.freemem() / 1048576), total: Math.round(os.totalmem() / 1048576), load: +os.loadavg()[0].toFixed(2) }; };
setInterval(() => { ST.alive = Date.now(); ST.hb2 = hbNow(); dirty = true; }, 60000);   // 💓 心跳：重開時用來判斷停機多久、停機前的記憶體
// 🛡 當機保護：有錯誤沒接住時記下來、繼續運作，不要整個程式當掉（當掉會被系統重開，所有人的自動交易都會暫停）
const ERRN = { at: 0 };
function onCrash(kind, e) {
  const msg = String((e && (e.stack || e.message)) || e).slice(0, 700); log('⚠️ ' + kind, msg);
  ST.lastErr = { t: Date.now(), kind, msg: msg.slice(0, 400) }; dirty = true;   // 留給下次停機的原因分析
  if (Date.now() - ERRN.at > 10 * 60000) { ERRN.at = Date.now(); try { dcX(ctx(ownerUid()), `⚠️ **伺服器發生錯誤**（已經擋下來，程式繼續運作；10 分鐘內同類錯誤只通知一次）\n\`\`\`${msg.slice(0, 600)}\`\`\``); } catch (x) {} }
}
process.on('unhandledRejection', e => onCrash('沒有接住的錯誤', e));
process.on('uncaughtException', e => onCrash('程式錯誤', e));
// 🔄 重開後自動恢復：先等 1 分鐘讀好持倉和行情，之後一律恢復重開前在跑的交易（擁有者要求：每次停機都自動開始）
//    停機超過 5 分鐘、或 30 分鐘內重開 3 次以上：另外分析停機原因，發到擁有者的 Discord
{ const now = Date.now(), a0 = ST.alive || 0, down = a0 ? now - a0 : Infinity, ex = ST.exit, hb = ST.hb2, err = ST.lastErr;   // 剛重開時先把停機前的資料存起來（之後心跳會覆蓋）
  ST.boots = (ST.boots || []).filter(t => now - t < 30 * 60000).concat(now); ST.exit = null; dirty = true;
  const loop = ST.boots.length >= 3, mins = isFinite(down) ? Math.max(1, Math.round(down / 60000)) : null;
  setTimeout(() => {
    for (const r of RESUME) {
      const X = ctx(r.uid); if (!hasKey(X)) continue;
      const parts = [r.on ? '自動交易' : '', r.sp && toolOkUid(r.uid) ? '🗡 特級交易' : ''].filter(Boolean); if (!parts.length) continue;
      if (r.on) X.A.lt.on = true;
      if (r.sp && toolOkUid(r.uid)) X.A.lt.sp = true;
      X.LT.pause = null; touchLT(X); log('重開後自動恢復', r.uid, parts.join('、'));
      dcX(X, `🔄 **伺服器重新啟動，已自動恢復${parts.join('和')}**${mins ? `（停機約 ${mins} 分鐘）` : ''}`);
    }
  }, 60000);
  setImmediate(() => { for (const r of RESUME) { const X = ctx(r.uid); X.LT.pause = { t: now, why: '伺服器重新啟動，約 1 分鐘後自動恢復' }; } });
  if (!isFinite(down) || down > 5 * 60000 || loop) setTimeout(() => {   // 🔎 停機原因分析
    const L = [], up = os.uptime() * 1000;
    L.push(ex && ex.t >= a0 - 120000 ? `✅ 關機方式：**正常關機**（收到 ${ex.how}，例如你更新或重開伺服器）` : '❗ 關機方式：**沒有正常關機的紀錄**，代表程式是被強制關掉或當掉的');
    L.push(isFinite(down) && up < down + 60000 ? `❗ 主機：**整台主機在 ${Math.round(up / 60000)} 分鐘前重新開機**（可能是 AWS 維護、主機當機或被重開）` : `✅ 主機：沒有重新開機（已經開了 ${Math.round(up / 3600000)} 小時）`);
    if (hb) { const low = hb.free < Math.max(80, hb.total * 0.08); L.push(`${low ? '❗' : '✅'} 停機前的記憶體：程式用了 ${hb.rss}MB，主機剩 **${hb.free}MB**／${hb.total}MB${low ? '（偏低，很可能是記憶體不足被系統關掉）' : ''}・負載 ${hb.load}`); }
    if (err && (!a0 || err.t >= a0 - 30 * 60000)) L.push(`❗ 停機前 30 分鐘內最後一個錯誤（${err.kind}）：\n\`\`\`${err.msg.slice(0, 300)}\`\`\``);
    const nowHb = hbNow(); L.push(`📊 現在：程式用了 ${nowHb.rss}MB，主機剩 ${nowHb.free}MB／${nowHb.total}MB`);
    const head = loop ? `🔎 **伺服器 30 分鐘內重開了 ${ST.boots.length} 次**` : `🔎 **伺服器停機${mins ? ` ${mins} 分鐘` : '（沒有上次運作的紀錄）'}**`;
    dcX(ctx(ownerUid()), `${head}，交易已照常自動恢復。停機原因分析：\n${L.join('\n')}\n-# 如果看不懂，把這則訊息貼給 Claude`);
    log('停機原因分析', L.join(' / '));
  }, 70000);
}

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
  const S = ST.set, th = { sum: +S.zSum > 0 ? +S.zSum : 5, bar: +S.zBar > 0 ? +S.zBar : 5 };   // z 值門檻：擁有者在掃描條件自己設（累積型／單根型）
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
// 🔄 反手：同一個幣出現反方向訊號，舊訊號在 flipAt 那一刻用當時價格 flipPx 結束（之前已經結單的就照原本的結果）
function evalTrade(c) {
  const E = evalTrade1(c);
  if (!c.flipAt || (!E.open && (E.exitAt || 0) <= c.flipAt)) return E;
  const pnl = Math.round(c.dir * (c.flipPx / c.entry - 1) * ST.trade.lev * 1000) / 10;
  return { st: E.st === 'win' ? 'win' : 'timeout', at: E.st === 'win' ? E.at : c.flipAt, exitAt: c.flipAt, pnl, how: 'flip' };
}
function evalTrade1(c) {
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
const DC = { q: [], busy: false, st: new Map() };        // st：每個 Webhook 最後一次的傳送結果（給網站顯示，不存檔）
const dcErr = (status, txt) => status === 404 ? 'Webhook 不存在（可能被刪掉了），請到 Discord 重新複製網址' : status === 401 || status === 403 ? 'Webhook 網址無效，請重新複製' : status === 400 ? `Discord 拒收這則訊息（${String(txt).slice(0, 80)}）` : `Discord 回應錯誤 ${status}`;
function dcStat(url) { const x = url && DC.st.get(url); return x ? { ok: x.ok, at: x.at, err: x.err || '' } : null; }
function dcSend(content, cfg, force) {
  if (!cfg || !cfg.webhook) return Promise.resolve(false);
  const x = DC.st.get(cfg.webhook);
  if (!force && x && x.pauseTo > Date.now()) return Promise.resolve(false);   // 這個網址連續失敗：暫停 5 分鐘，不要卡住別人的通知（測試訊息不受限）
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
          method: 'POST', headers: { 'Content-Type': 'application/json' }, signal: AbortSignal.timeout(8000),
          body: JSON.stringify({ content: m.content.slice(0, 1900), username: '合約量化進場', allowed_mentions: { parse: [] } })
        });
        if (r.status === 429) { const j = await r.json().catch(() => ({})); await sleep(Math.ceil((+j.retry_after || 2) * 1000) + 200); continue; }   // Discord 限速，等一下再送
        if (!r.ok) { const tx = (await r.text().catch(() => '')).slice(0, 200); log('Discord 傳送失敗', r.status, tx); m.err = dcErr(r.status, tx); break; }
        sent = true;
      } catch (e) {
        log('Discord 傳送失敗', e.message); const to = /timeout|abort/i.test(e.name + e.message);
        m.err = to ? '連不到 Discord（逾時）' : `連不到 Discord（${e.message}）`;
        if (to) break;                                 // 逾時代表整個連不上：不重試，免得卡住其他人的通知
        await sleep(1500);
      }
    }
    { const prev = DC.st.get(m.cfg.webhook) || {}, fails = sent ? 0 : (prev.fails || 0) + 1;
      DC.st.set(m.cfg.webhook, { ok: sent, at: Date.now(), err: sent ? '' : (m.err || '傳送失敗'), fails, pauseTo: fails >= 3 ? Date.now() + 5 * 60000 : 0 }); }
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
  const bt = c.btcD !== undefined ? `\nBTC ${c.btcD > 0 ? '偏多' : c.btcD < 0 ? '偏空' : '讀不到'}${c.btcChg !== null && c.btcChg !== undefined ? `（${c.btcChg > 0 ? '+' : ''}${c.btcChg}%）` : ''}・${c.btcD === c.dir ? '順勢' : '逆勢'}（需要 ${c.btcNeed} 項，${c.btcPass === false ? '**沒過 BTC 過濾**，有開過濾的人不會下單' : '有過 BTC 過濾'}）` : '';
  dcAll(`📡 **訊號**｜${c.dir > 0 ? '🟢 **做多**' : '🔴 **做空**'} **${mdEsc(c.sym)}**（數據異常 ${c.abN}/5）${bt}\n` +   // 只發訊號本身；模擬倉的達標價、失敗價不發
    `訊號價 **${fpx(c.entry)}**\n${ab ? '異常：' + mdEsc(ab) + '\n' : ''}時間 ${tw(c.et)}（台北）`, (N, X) => N.enabled && N.entry && !(X.A.lt.btcF && c.btcPass === false));
}
function notifyExit(c, E) {
  const T = ST.trade;
  const head = E.how === 'flip' ? '🔄 **反手**' : E.st === 'win' ? '✅ **成功**' : E.st === 'timeout' ? '⏱ **逾時**' : '❌ **失敗**';
  const how = E.how === 'flip' ? '（出現反方向訊號，用當時價格結束）' : E.how === 'lock' ? `（跑回鎖利線 +${E.pnl}% 出場）` : E.how === 'hold' ? `（持有到 ${T.hold} 小時到期）` : E.st === 'amb' ? '（同一根 K 棒兩邊都碰到，保守算失敗）' : '';
  const pnl = (E.pnl > 0 ? '+' : E.pnl < 0 ? '−' : '') + Math.abs(E.pnl).toFixed(0) + '%';
  return;                                             // 模擬倉的結果不發 Discord（使用者要求）；網站上的卡片、歷史紀錄照常顯示
  dcAll(`📡 **訊號模擬結果**｜${head} ${c.dir > 0 ? '做多' : '做空'} **${mdEsc(c.sym)}** **${pnl}**${how}\n` +
    `訊號價 ${fpx(c.entry)}（${tw(c.et)}）\n持有 ${durTxt((E.exitAt || Date.now()) - c.et)}・${T.lev}x\n-# 這是訊號的模擬結果，不代表交易所的倉位已經平倉`, (N, X) => N.enabled && N.exit && !(X.A.lt.btcF && c.btcPass === false));
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
const SCAN = { running: false, last: 0, dur: 0, total: 0, flatN: 0, done: 0, todo: 0, found: 0, err: '', btc: null, btcSkip: 0 };
/* ---------------- 🧭 BTC 方向過濾：進場前先看 BTC 往哪走 ----------------
   順勢（訊號方向跟 BTC 一樣）至少 btcWith 項異常；逆勢至少 btcAgainst 項。讀不到 BTC 資料時保守處理：兩個方向都要用逆勢的門檻。
   判斷方式：24h＝現價比 24 小時前；day＝現價比今天開盤（台北 08:00）；4h＝現價比 4 小時前 */
const BTCL = { k: [], at: 0, busy: false };
const btcRef = (k, t, mode) => {                       // k：BTC 1 小時 K 線（陣列或「開盤時間→K 棒」的 Map）；t：判斷的時間點 → 參考價（多久以前的價格）
  const get = t0 => (k instanceof Map ? k.get(t0) : k.find(x => x.t === t0));
  if (mode === 'day') { const b = get(Math.floor((t - 1) / (24 * HOUR)) * 24 * HOUR); return b ? b.o : null; }
  const back = mode === '4h' ? 4 : 24, b = get(Math.floor(t / HOUR) * HOUR - (back + 1) * HOUR);   // 這根 K 棒的收盤＝back 小時前的價格
  return b ? b.c : null;
};
function btcDirFrom(px, ref) { if (!(px > 0 && ref > 0)) return { d: 0, chg: null }; const chg = (px / ref - 1) * 100; return { d: chg > 0 ? 1 : chg < 0 ? -1 : 0, chg: Math.round(chg * 100) / 100 }; }
async function btcRefresh() {                          // 即時用：每 5 分鐘抓一次 BTC 1 小時 K 線
  if (BTCL.busy || Date.now() - BTCL.at < 5 * 60000) return; BTCL.busy = true;
  try { BTCL.k = await BN.fut('BTCUSDT', '1h', 60); BTCL.at = Date.now(); } catch (e) {}
  BTCL.busy = false;
}
function btcNow() {
  const px = PX.map.BTCUSDT || (BTCL.k.length ? BTCL.k[BTCL.k.length - 1].c : 0), now = Date.now();
  return { ...btcDirFrom(px, btcRef(BTCL.k, now, ST.set.btcMode)), mode: ST.set.btcMode, px };
}
const btcNeed = (dir, bd, S = ST.set) => (!S.btcF ? S.minN : bd === 0 ? Math.max(S.btcWith, S.btcAgainst) : dir === bd ? S.btcWith : S.btcAgainst);
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
  {                                                    // 🧭 BTC 方向過濾：訊號照樣產生，記下有沒有過；開著過濾的帳號才擋（不通知、不下單、不算成功率）
    const B = btcNow(), need = btcNeed(r.dir, B.d, { ...ST.set, btcF: 1 });
    r.btcD = B.d; r.btcChg = B.chg; r.btcNeed = need; r.btcPass = r.abN >= need;
  }
  r.why = reason(r);
  // 同一個幣還有單沒結單 → 不開新單。同方向就更新一下「最後偵測」的數字；反方向直接忽略
  const live = ST.cards.find(c => c.sym === r.sym && c.et && isLive(c));
  if (live && live.dir !== r.dir) {                    // 🔄 反方向訊號：舊訊號用現價結束，接著開新訊號（實盤也跟著反手）
    live.flipAt = now; live.flipPx = PX.map[live.pid] || r.last; live.flipTo = r.dir;
    log('反手', r.sym, live.dir > 0 ? '多→空' : '空→多');
    touchCards();
  } else if (live) {
    if (live.dir === r.dir) {
      // 原本沒過 BTC 過濾、這次異常項數夠了：開著過濾的帳號現在才進場（沒開過濾的帳號當初就進了）
      const late = live.btcPass === false && r.btcPass;
      const { entry, et, id, t0, btcPass, ...rest } = r;
      if (late) { live.btcPass = true; live.btcLate = now; }
      for (const X of allX()) {                          // 開著過濾、現在才通過的帳號：走反手流程（手上有反方向的自動單就先平掉）
        if (!X.A.lt.on) continue;
        const F = X.LT.flipTry || (X.LT.flipTry = {});
        if (late && X.A.lt.btcF) { F[live.sym] = now; ltFlipOpen(X, live); continue; }
        // 補反手：之前沒反手成功（例如當時沒過 BTC 過濾），這個訊號又出現、而且對這個帳號有過 → 補做反手；同一個幣 10 分鐘最多試一次
        const pass = !(X.A.lt.btcF && live.btcPass === false);
        if (pass && now - (F[live.sym] || 0) > 10 * 60000 && ltOpenTrades(X).some(t => t.sym === live.sym && t.dir !== live.dir && t.positionId)) { F[live.sym] = now; log('補反手', X.uid, live.sym); ltFlipOpen(X, live); }
      }
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
  if (c.btcPass === false) SCAN.btcSkip++;
  notifyEntry(c);
  for (const X of allX()) if (X.A.lt.on) ltFlipOpen(X, c);   // 每個「開始交易」的帳號各自用自己的金鑰下單（手上有反方向的自動單就先反手平倉）
}
async function scan() {
  if (SCAN.running) return; SCAN.running = true;
  await btcRefresh(); SCAN.btc = btcNow();              // 每個帳號自己決定要不要過濾，BTC 方向一律更新
  const t0 = Date.now(); SCAN.err = ''; SCAN.done = 0; SCAN.found = 0;
  try {
    const uni = await BN.universe(), S = ST.set;
    const flat = uni.filter(u => Math.abs(u.chg) <= S.flat && u.amp <= S.range && u.qv >= S.minVol * 1e4).sort((a, b) => b.qv - a.qv);
    SCAN.total = uni.length; SCAN.flatN = flat.length; SCAN.todo = flat.length;
    let idx = 0;
    const worker = async () => { while (idx < flat.length) { const u = flat[idx++]; try { const r = await analyze(u); if (r) { SCAN.found++; addCard(r); } } catch (e) {} SCAN.done++; } };
    await Promise.all(Array.from({ length: 8 }, worker));
    SCAN.okAt = Date.now();
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
    // BTC 1 小時 K 線：用來判斷每一筆訊號當下 BTC 的方向（每種判斷方式都記下來，之後換方式也能比較）
    const bk = (await btBase({ id: 'BTCUSDT', sym: 'BTCUSDT' })).k, bpx = new Map(bk.map(x => [x.t, x.c]));
    const btcAt = (et, mode) => btcDirFrom(bpx.get(et - HOUR), btcRef(bk, et, mode));
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
      // 兩條路線各自算「上一筆結單前同一個幣不開新單」：c0＝沒有 BTC 過濾、c1＝有 BTC 過濾
      let free0 = 0, free1 = 0;
      for (const { i, D, chg, pc } of sig) {
        const et = k[i].t + HOUR, B = btcAt(et, S.btcMode), need = btcNeed(D.dir, B.d, { ...S, btcF: 1 });
        const in0 = et >= free0, in1 = D.abN >= need && et >= free1;
        if (!in0 && !in1) continue;
        const tr = { id: 'bt-' + u.id + '-' + et, bt: 1, sym: u.sym, pid: u.id, spot: u.spot, src: 'binance', dir: D.dir, abN: D.abN, et, entry: k[i].c, recs: [], fav: 0, adv: 0, end: 0, step: 900000,
          btcD: B.d, btcChg: B.chg, btcNeed: need, btcMode: S.btcMode, c0: in0, c1: in1 };
        const seg = bars.filter(b => b.t >= et && b.t - et < TRACK_MAX);
        extend(tr, seg); hourClose(tr, tr, seg, 900000);
        delete tr.fav; delete tr.adv;
        Object.assign(tr, { ind: D.ind.map(x => ({ k: x.k, n: x.n, v: x.v === null ? null : (x.k === 'oi' ? r5(x.v) : Math.round(x.v)), z: x.z === null ? null : Math.round(x.z * 100) / 100, ab: x.ab })), chg, pc, win: W, logic: S.logic, unitOk: true, last: k[i].c });
        tr.why = reason(tr);
        trades.push(tr); BTP.found++;
        const E = evalTrade(tr), x = E.open ? Infinity : E.exitAt;
        if (in0) free0 = x; if (in1) free1 = x;
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
    ST.bt = { at: Date.now(), coins: BTP.done, trades: trades.slice(0, 6000), cfg: { mode: S.btcMode, w: S.btcWith, a: S.btcAgainst, minN: S.minN } };
    touchBT(); BTCMP.key = '';
    BTP.msg = BTP.stop ? `已手動停止，回測了 ${BTP.done}／${BTP.total} 個幣` : '';
    log('回測完成', BTP.done, '個幣', trades.length, '筆');
  } catch (e) { BTP.msg = '回測失敗：' + e.message; log(BTP.msg); }
  BTP.run = false; BTP.at = Date.now();
}

// 目前使用的回測紀錄：開著 BTC 過濾就用 c1 那條，關掉就用 c0 那條（舊版回測沒有標記，兩條都算）
const btActive = () => ST.bt.trades.filter(t => (ST.set.btcF ? t.c1 : t.c0) !== false);
// 🧭 有／沒有 BTC 過濾的比較：同一次回測、同一組浮盈規則，用固定本金照時間順序模擬
const BTCMP = { key: '', v: null };
function btCompare() {
  const T = ST.trade, key = BV + '|' + JSON.stringify(T) + '|' + JSON.stringify(ST.eq) + '|' + ST.rep.cap;
  if (BTCMP.key === key) return BTCMP.v;
  const all = ST.bt.trades.filter(t => t.c0 !== undefined); let v = null;
  if (all.length) {
    const start = Math.min(...all.map(t => t.et)), end = Date.now() + 1, cap = ST.rep.cap;
    const one = list => {
      const r = simReport(list, start, end, cap), E = list.map(t => evalTrade(t));
      const done = E.filter(e => !e.open), w = done.filter(e => e.st === 'win').length;
      const sum = done.reduce((a, e) => a + (Number.isFinite(e.pnl) ? e.pnl : 0), 0);
      return { n: list.length, long: list.filter(t => t.dir > 0).length, short: list.filter(t => t.dir < 0).length, done: done.length, win: w,
        rate: done.length ? Math.round(w / done.length * 1000) / 10 : null, sum: Math.round(sum), avg: done.length ? Math.round(sum / done.length * 10) / 10 : null,
        endCap: r.endCap, pnl: r.pnl, ret: r.ret, mdd: r.mdd, fees: r.fees, longPl: r.longPl, shortPl: r.shortPl, taken: r.n, skipped: r.skipped };
    };
    const off = all.filter(t => t.c0), on = all.filter(t => t.c1);
    v = { start, end: end - 1, at: ST.bt.at, coins: ST.bt.coins, cfg: ST.bt.cfg || null, off: one(off), on: one(on),
      cut: { n: off.filter(t => !t.c1).length, long: off.filter(t => !t.c1 && t.dir > 0).length, short: off.filter(t => !t.c1 && t.dir < 0).length },
      bySide: { with: one(on.filter(t => t.btcD === t.dir)), against: one(on.filter(t => t.btcD !== t.dir)) } };
  }
  BTCMP.key = key; BTCMP.v = v; return v;
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
      id: end, start, end, manual: !!manual, cfg: { ...ST.eq, ...ST.trade, btc: ST.set.btcF ? { mode: ST.set.btcMode, w: ST.set.btcWith, a: ST.set.btcAgainst } : null, cap: ST.rep.cap, btN: ST.rep.btN },
      bt: simReport(btActive(), start, end, ST.rep.cap), live: simReport(ST.cards.filter(c => !(ST.set.btcF && c.btcPass === false)), start, end, ST.rep.cap)
    };
    ST.reports.unshift(r); ST.reports = ST.reports.slice(0, 60);
    if (!manual) ST.rep.next = end + ST.rep.days * 24 * HOUR;
    RV++; dirty = true;
    log('結算完成', `回測 ${r.bt.endCap}U（${r.bt.n} 筆）`, `即時 ${r.live.endCap}U（${r.live.n} 筆）`);
    const sg = v => (v > 0 ? '+' : v < 0 ? '−' : '') + Math.abs(v).toFixed(2);
    if (false) dcAll(`📊 **雙週結算**（${tw(start)} ～ ${tw(end)}，每期本金 ${ST.rep.cap}U）\n` +
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
    // 🧭 BTC 方向過濾：跟即時進場用同一套規則（BTC 1 小時 K 線多抓 2 天，才算得到最前面的 24 小時漲跌）
    const bkm = new Map((await getRange(`${BF}/fapi/v1/klines?symbol=BTCUSDT&interval=1h`, HOUR, from - 2 * 24 * HOUR, anchor)).map(r => [+r[0], { t: +r[0], o: +r[1], c: +r[4] }]));
    const btcAt = et => { const b = bkm.get(et - HOUR); return btcDirFrom(b ? b.c : 0, btcRef(bkm, et, S.btcMode)); };
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
        const B = S.btcF ? btcAt(et) : null;
        if (B && Dt.abN < btcNeed(Dt.dir, B.d)) continue;      // 沒過 BTC 過濾：不進場，也不擋後面的訊號
        const tr = { bt: 1, sym: u.sym, pid: u.id, dir: Dt.dir, abN: Dt.abN, et, entry: k[i].c, recs: [], fav: 0, adv: 0, end: 0, step: 900000, btcD: B ? B.d : undefined };
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
      out.push({ id: end, start, end, hist: true, cfg: { ...ST.eq, ...ST.trade, btc: ST.set.btcF ? { mode: ST.set.btcMode, w: ST.set.btcWith, a: ST.set.btcAgainst } : null, cap, btN: ST.rep.btN, noOI: end < now - 30 * 24 * HOUR }, bt: simReport(trades, start, end, cap), live: null });
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
const OWNER_UID = '852639358';
const VER = '2026-10-25c';                         // 內建的擁有者帳號：永遠是管理員，不能被降級或刪除（密碼不寫在程式裡，repo 是公開的）
function ownerUid() {                                  // 擁有者＝這台伺服器的主人（AWS 提醒、用管理金鑰登入都算他的）；轉讓後存在 ST.owner
  if (ST.owner && ST.users.some(u => u.uid === ST.owner)) return ST.owner;
  if (ST.users.some(u => u.uid === OWNER_UID)) return OWNER_UID;
  if (ST.owner && ST.users.some(u => u.uid === ST.owner)) return ST.owner;
  const a = ST.users.find(u => u.role === 'admin'); return a ? a.uid : '__owner';
}
function ctx(uid) {
  uid = String(uid || ownerUid());
  if (!ST.accts[uid]) { ST.accts[uid] = { bx: { ...DEF_BX }, lt: { ...DEF_LT }, ltTrades: [], notify: { ...DEF_NOTIFY } }; dirty = true; }
  { const L = ST.accts[uid].lt; for (const [k, f] of [['spLev', 'lev'], ['spMargin', 'margin'], ['spDayLoss', 'dayLoss'], ['spTp', 'tp'], ['spStep', 'step'], ['spSl', 'sl'], ['spHold', 'hold']]) if (L[k] == null) L[k] = L[f]; }
  let X = RT.get(uid);
  if (!X) { X = { uid, BX: { pos: [], acct: null, at: 0, err: '', seeded: false, warned: {} }, LT: { lev: {}, busy: new Set(), msg: '', dayHit: '', dayPnl: 0 }, v: Date.now(), polling: false, managing: false }; RT.set(uid, X); }
  X.A = ST.accts[uid];
  return X;
}
const allX = () => Object.keys(ST.accts).map(ctx);
{ if (!ST.owner && ST.users.some(u => u.uid === OWNER_UID)) ST.owner = OWNER_UID; const o = ST.users.find(u => u.uid === ownerUid()); if (o) o.role = 'admin'; }
// 這個帳號實盤用的規則：成功線、出場方式跟大家一樣；浮虧失敗線、鎖利上調間距、最長持有用自己的設定
const TT = X => ({ ...ST.trade, tp: X.A.lt.tp || ST.trade.tp, sl: X.A.lt.sl, step: X.A.lt.step, hold: X.A.lt.hold });
const TS = X => { const L = X.A.lt; return { ...ST.trade, exit: 'lock', tp: L.spTp || L.tp, sl: L.spSl || L.sl, step: L.spStep ?? L.step, hold: L.spHold || L.hold, lev: L.spLev || L.lev }; };   // 🗡 特級交易自己的出場規則
const TRule = (X, t) => (t && t.src === 'tool' ? TS(X) : TT(X));
const hasKey = X => !!(X.A.bx.key && X.A.bx.secret);
const dcX = (X, msg) => dcSend(msg, X.A.notify);                // 只傳到這個帳號自己的 Discord
function dcAll(content, ok = () => true) {             // 大家共用的通知（訊號、數據公布、結算）：每個帳號自己的 Discord 各傳一次，同一個 Webhook 不重複
  const seen = new Set();
  for (const X of allX()) {
    const N = X.A.notify; if (!N.webhook || !ok(N, X) || seen.has(N.webhook)) continue;
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
const msT = v => (v > 0 && v < 1e12 ? v * 1000 : v);   // 交易所回傳的時間有時是秒、有時是毫秒，統一成毫秒
const bxMapPos = data => (Array.isArray(data) ? data : []).map(p => ({
  id: String(p.positionId), sym: p.symbol, dir: sideDir(p.side), side: p.side, qty: num(p.qty), lev: num(p.leverage), mode: p.marginMode,
  entry: num(p.avgOpenPrice), margin: num(p.margin), upnl: num(p.unrealizedPNL), rpnl: num(p.realizedPNL), fee: num(p.fee), funding: num(p.funding),
  liq: num(p.liqPrice), ctime: msT(num(p.ctime)), mtime: msT(num(p.mtime)), pmode: p.positionMode
}));
async function bxPoll(X) {
  const C = X.A.bx, BX = X.BX, N = X.A.notify;
  if (!hasKey(X)) { BX.pos = []; BX.acct = null; BX.err = ''; return; }
  try {
    const data = await bxGet('/api/v1/futures/position/get_pending_positions', {}, C);
    const acct = await bxGet('/api/v1/futures/account', { marginCoin: 'USDT' }, C).catch(() => null);
    const pos = bxMapPos(data);
    const prev = new Map(BX.pos.map(p => [p.id, p])), now = new Map(pos.map(p => [p.id, p]));
    if (false && BX.seeded && C.notify && N.enabled) {              // 手動單的開倉／平倉不發 Discord（使用者要求）；自動單另外有 🤖 通知
      const botPos = p => X.A.ltTrades.some(t => t.positionId === p.id || (t.sym === p.sym && t.dir === p.dir && Date.now() - t.et < 60000));   // 自動交易的單另外通知
      for (const p of pos) if (!prev.has(p.id) && !botPos(p)) dcX(X, `📥 **Bitunix 開倉** ${p.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(p.sym)}**\n開倉價 ${fpx(p.entry)}・${p.lev}x ${p.mode === 'CROSS' ? '全倉' : '逐倉'}・數量 ${p.qty}・保證金 ${p.margin.toFixed(2)}U${p.liq > 0 ? `\n強平價 ${fpx(p.liq)}` : ''}`);
      for (const p of BX.pos) if (!now.has(p.id) && !botPos(p)) dcX(X, `📤 **Bitunix 平倉** ${p.dir > 0 ? '做多' : '做空'} **${mdEsc(p.sym)}**\n開倉價 ${fpx(p.entry)}・${p.lev}x\n平倉前最後一次讀到的未實現損益 **${p.upnl >= 0 ? '+' : '−'}${Math.abs(p.upnl).toFixed(2)}U**（實際以交易所為準）`);
    }
    if (C.liq && N.enabled) for (const p of pos) {                  // 現價離強平價太近就提醒（30 分鐘最多一次）；只提醒自動單，手動單不發
      if (!X.A.ltTrades.some(t => t.status === 'open' && t.positionId === p.id)) continue;
      const px = PX.map[p.sym]; if (!(px > 0 && p.liq > 0)) continue;
      const d = Math.abs(px - p.liq) / px * 100;
      if (d <= C.liqPct && Date.now() - (BX.warned[p.id] || 0) > 30 * 60000) {
        BX.warned[p.id] = Date.now();
        dcX(X, `⚠️ **快爆倉了** ${p.dir > 0 ? '做多' : '做空'} **${mdEsc(p.sym)}**：現價 ${fpx(px)}，強平價 ${fpx(p.liq)}，只差 **${d.toFixed(2)}%**`);
      }
    }
    BX.pos = pos; BX.at = Date.now(); BX.err = ''; BX.seeded = true;
    if (Date.now() - (BX.tpslAt || 0) > 30000) {       // 手動單在交易所設的止盈止損（只讀，給網站的部位工具用），每 30 秒讀一次
      BX.tpslAt = Date.now(); const m = new Map();
      const syms = [...new Set(pos.filter(p => !X.A.ltTrades.some(t => t.status === 'open' && t.positionId === p.id)).map(p => p.sym))];
      for (const sym of syms) {
        try {
          const L = await bxGet('/api/v1/futures/tpsl/get_pending_orders', { symbol: sym }, C);
          for (const o of Array.isArray(L) ? L : (L && (L.orderList || L.list)) || []) {
            const id = String(o.positionId || ''); if (!id) continue;
            const r = m.get(id) || {}; if (+o.tpPrice > 0) r.tp = +o.tpPrice; if (+o.slPrice > 0) r.sl = +o.slPrice; m.set(id, r);
          }
        } catch (e) {}
      }
      BX.tpsl = m;
    }
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
// 算進實盤統計的單：起算之後開的，加上起算那時還開著、或起算之後才平倉的（不然重新起算後，原本開著的單會被漏掉）
const inStat = (t, startAt) => t.et >= (startAt || 0) || t.status === 'open' || (t.exitAt || 0) >= (startAt || 0);
function ltNet(t) { return (t.realized || 0) - Math.abs(t.fee || 0) + (t.funding || 0); }   // 已實現損益－手續費＋資金費
// 這組自動交易目前「自己的」資金：起始投入＋從起算時間開始所有單的淨損益（持有中的含未實現）
function ltBudMax(X, sp) {                             // 💰 這一邊的投入資金最多能設多少：改完後「一般目前＋特級目前」不能超過帳戶（另一邊不限制投入資金就不檢查）
  const C = X.A.lt, a = bxEquity(X), N = ltBotEq(X), S = ltSpEq(X);
  const pnlN = N.eq - ((C.startCap || 0) - (C.wd || 0)), pnlS = S.eq - ((C.spBudget || 0) - (C.spWd || 0));
  const other = sp ? (C.budget > 0 ? Math.max(0, N.eq) : null) : (C.spBudget > 0 && toolOkUid(X.uid) ? Math.max(0, S.eq) : null);
  if (other === null || !(a > 0)) return null;
  return { max: Math.floor((a - other - (sp ? pnlS : pnlN)) * 100) / 100, acct: a, other };
}
function ltBudEq(X) {                                 // 一般交易的投入資金：起始本金就是投入資金，盈虧從開始統計那時候一直算（跟統計、資金曲線同一套）
  return { ...ltBotEq(X), at: X.A.lt.startAt || 0 };
}
function ltSpEq(X) {                                  // 🗡 特級交易的資金：投入資金（起始本金）＋特級的盈虧 − 收回的
  const C = X.A.lt; let e = (C.spBudget || 0) - (C.spWd || 0), used = 0;
  for (const t of X.A.ltTrades) { if (t.src !== 'tool' || !inStat(t, C.spStartAt)) continue; e += ltNet(t) + (t.status === 'open' ? (t.upnl || 0) : 0); if (t.status === 'open') used += t.margin || t.m0 || 0; }
  return { eq: e, used, free: e - used };
}
function ltBotEq(X) {                                 // 一般自動交易的資金（不含 🗡 特級交易）：起始本金＋盈虧 − 收回的
  const C = X.A.lt; let e = (C.startCap || 0) - (C.wd || 0), used = 0;
  for (const t of X.A.ltTrades) { if (t.src === 'tool' || !inStat(t, C.startAt)) continue; e += ltNet(t) + (t.status === 'open' ? (t.upnl || 0) : 0); if (t.status === 'open') used += t.margin || t.m0 || 0; }
  return { eq: e, used, free: e - used };
}
// 📅 有美國高影響數據公布的那一天（台北時間 00:00–23:59）整天不開新單、不反手；已開的單照常管理
const twDay = t => new Date(t + TZ).toISOString().slice(0, 10);
const ecoToday = (t = Date.now()) => ECO.list.filter(e => e.imp === 'H' && twDay(e.t) === twDay(t));
const ecoBlock = (t = Date.now()) => ecoToday(t)[0] || null;
const ecoNames = L => L.map(e => `${e.zh || e.title} ${tw(e.t).slice(-5)}`).join('、');
function ecoDayTick() {                               // 這種日子一開始就在 Discord 通知一次
  const L = ecoToday(), day = twDay(Date.now());
  if (!L.length || ST.ecoDay === day) return;
  ST.ecoDay = day; dirty = true;
  dcAll(`📅 **今天（${day.slice(5).replace('-', '/')}）有美國重要數據：${mdEsc(ecoNames(L))}**\n自動交易今天整天不開新單、也不反手；已經開著的單照常管理（鎖利、失敗線、到期）。`, N => N.enabled);
}
setInterval(ecoDayTick, 60000); setTimeout(ecoDayTick, 90000);
const toolOkUid = uid => uid === ownerUid() || ST.tool.grants.includes(uid);   // 🗡 有特級咒具權限
async function ltOpen(X, c) {
  const C = X.A.lt, K = X.A.bx, LT = X.LT, BX = X.BX, sp = c.src === 'tool';
  const M = sp ? C.spMargin || C.margin : C.margin, LV = sp ? C.spLev || C.lev : C.lev, BUD = sp ? C.spBudget : C.budget, NM = sp ? '特級交易' : '自動交易';   // 🗡 特級交易用自己的設定（先替換再插入，避免這行也被換掉）   // sp：🗡 特級交易（特級咒具的訊號）
  if (!(sp ? C.sp && toolOkUid(X.uid) : C.on) || !hasKey(X) || LT.busy.has(c.sym)) return;
  if (!sp && C.btcF && c.btcPass === false) { LT.msg = `${c.sym} 沒過 BTC 方向過濾（${c.abN} 項，需要 ${c.btcNeed} 項），不下單`; return; }
  { const L = ecoToday(); if (L.length) { LT.msg = `今天有美國重要數據（${ecoNames(L)}），整天不開新單：${c.sym} 略過`; return; } }
  LT.busy.add(c.sym);
  try {
    if (C.maxOpen && ltOpenTrades(X).length >= C.maxOpen) { LT.msg = `已達最多同時持倉 ${C.maxOpen} 筆，${c.sym} 這次不下單`; return; }
    if (BX.pos.some(p => p.sym === c.sym && p.dir === c.dir) || ltOpenTrades(X).some(t => t.sym === c.sym && t.dir === c.dir)) return;   // 這個幣已經有同方向的倉位：不加碼（雙向持倉下會被交易所合成一個倉位，分不清是誰的）
    { const opp = BX.pos.filter(p => p.sym === c.sym && p.dir !== c.dir), oppT = ltOpenTrades(X).some(t => t.sym === c.sym && t.dir !== c.dir);
      if (opp.length || oppT) {                        // 有反方向的倉位（另一套系統的單或手動單）：只有「雙向持倉」才能多空雙開，單向持倉下反方向的單會把原本的倉位抵銷掉
        const hedge = opp.length > 0 && opp.every(p => String(p.pmode || '').toUpperCase() === 'HEDGE');
        if (!hedge) { LT.msg = `${c.sym} 已經有反方向的倉位，帳戶${opp.length ? '是單向持倉' : '的持倉模式還讀不到'}，不能多空雙開，這次不下單（要雙開請到 Bitunix 改成「雙向持倉」）`; return; }
      }
    }
    const pr = await ltPair(c.sym);
    if (!pr) { LT.msg = `Bitunix 沒有 ${c.sym}，略過`; return; }
    if (pr.symbolStatus !== 'OPEN') { LT.msg = `${c.sym} 在 Bitunix 暫停交易，略過`; return; }
    const px = PX.map[c.sym] || c.last, lev = Math.max(1, Math.min(LV, +pr.maxLeverage || LV));
    if (BX.acct && BX.acct.avail < M * 1.2) { LT.msg = `可用餘額不足（${BX.acct.avail.toFixed(2)}U），${c.sym} 不下單`; return; }
    if (BUD > 0) {                                // 只用你設定的投入資金，不碰帳戶裡其他的錢
      const B = sp ? ltSpEq(X) : ltBudEq(X);
      if (B.eq <= 0) { if (sp) C.sp = false; else C.on = false; LT.pause = { t: Date.now(), why: `${sp ? '特級交易的' : ''}投入資金用完` }; touchLT(X); dcX(X, `🛑 **${sp ? '🗡 特級交易的' : ''}投入資金 ${BUD}U 已經用完**（目前 ${B.eq.toFixed(2)}U），${NM}已暫停`); return; }
      if (B.free < M * 1.2) { LT.msg = `投入資金剩 ${B.free.toFixed(2)}U 可用（設定 ${BUD}U），${c.sym} 不下單`; return; }
    }
    const qty = fl(M * lev / px, +pr.basePrecision || 0);
    if (!(qty > 0) || qty < +pr.minTradeVolume) { LT.msg = `${c.sym} 用 ${M}U×${lev}x 買不到最小下單量（${pr.minTradeVolume}），略過`; dcX(X, `⏭️ ${mdEsc(c.sym)} 下單量太小，略過（最小 ${pr.minTradeVolume}，需要的保證金比 ${M}U 多）`); return; }
    const key = C.mode + lev;
    if (LT.lev[c.sym] !== key) {
      await bxPost('/api/v1/futures/account/change_margin_mode', { marginMode: C.mode, symbol: c.sym, marginCoin: 'USDT' }, K).catch(() => {});
      await bxPost('/api/v1/futures/account/change_leverage', { symbol: c.sym, leverage: lev, marginCoin: 'USDT' }, K);
      LT.lev[c.sym] = key;
    }
    // 失敗線用「設定的槓桿」換算價格（例如 100x、−250% ＝ 價格反向 2.5%）；幣只支援 50x 時實際虧損是 −125%，但跟訊號模擬同一個價格出場
    const T = sp ? TS(X) : TT(X), slPx = px * (1 - c.dir * T.sl / 100 / LV), qp = +pr.quotePrecision || 4;
    const base = { symbol: c.sym, qty: String(qty), side: c.dir > 0 ? 'BUY' : 'SELL', tradeSide: 'OPEN', orderType: 'MARKET', clientId: 'q' + Date.now().toString(36) };
    let o, exSL = true;
    try { o = await bxPost('/api/v1/futures/trade/place_order', { ...base, slPrice: pxStr(slPx, qp), slStopType: 'MARK_PRICE', slOrderType: 'MARKET' }, K); }
    catch (e) {                                       // 帶止損失敗就改成不帶，止損改由伺服器監控
      if (!/sl|stop|price/i.test(e.message)) throw e;
      exSL = false; o = await bxPost('/api/v1/futures/trade/place_order', base, K);
    }
    let p = null;                                      // 交易所處理需要時間：最多重試 6 次（約 9 秒）拿到這筆倉位的編號，沒有編號伺服器就管不到它
    for (let k = 0; k < 6 && !p; k++) { await sleep(1500); const ps = await bxGet('/api/v1/futures/position/get_pending_positions', { symbol: c.sym }, K).catch(() => []); p = (ps || []).find(x => sideDir(x.side) === c.dir) || null; }
    if (!p) log('開倉後查不到倉位編號，之後對帳時再認領', X.uid, c.sym);
    const t = {
      id: 'lt-' + Date.now(), sym: c.sym, dir: c.dir, card: c.id, abN: c.abN, et: Date.now(), lev,
      entry: p ? num(p.avgOpenPrice) : px, qty: p ? num(p.qty) : qty, qty0: p ? num(p.qty) : qty, margin: p ? num(p.margin) : M, m0: p ? num(p.margin) || M : M,
      positionId: p ? String(p.positionId) : '', orderId: o && o.orderId, status: 'open', ruleLev: LV, src: sp ? 'tool' : '', ttype: c.ttype || '', tpair: c.tpair || '', realized: 0, fee: p ? num(p.fee) : 0, funding: 0, closes: [], locked: false, fav: 0, adv: 0, exSL, prec: +pr.basePrecision || 0, minQty: +pr.minTradeVolume || 0
    };
    X.A.ltTrades.unshift(t); X.A.ltTrades = X.A.ltTrades.slice(0, 2000); touchLT(X);
    log('自動開倉', X.uid, c.sym, c.dir > 0 ? '做多' : '做空', qty, '@', t.entry);
    dcX(X, `${sp ? `🗡 **特級交易開倉**（${({ zh: '莊家進場', crt: (c.tpair === 'h4' ? 'H4' : 'H1') + ' CRT 進場', hunt: '獵殺進場' })[c.ttype] || ''}・${c.tpair === 'h4' ? '4H→15 分' : '1H→5 分'}）` : '🤖 **自動開倉**'} ${c.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(c.sym)}**\n成交價 ${fpx(t.entry)}・${lev}x 全倉・數量 ${t.qty}・保證金約 ${t.margin.toFixed(2)}U\n${exSL ? `交易所止損 ${fpx(slPx)}（−${pctK(T.sl, lev / LV)}%）` : '⚠️ 交易所止損沒設成功，改由伺服器監控'}\n出場規則：浮盈 **+${pctK(T.tp, lev / LV)}%** 開始鎖利、浮虧 **−${pctK(T.sl, lev / LV)}%** 停損${lev !== LV ? `\n-# 這個幣最高 ${lev}x，你設 ${LV}x：停利停損按 ${lev}÷${LV} 縮小（你的 +${T.tp}%／−${T.sl}%），出場價格不變` : ''}`);
  } catch (e) { LT.msg = `${c.sym} 自動下單失敗：${e.message}`; log(X.uid, LT.msg); dcX(X, `❗ **自動下單失敗** ${mdEsc(c.sym)}：${mdEsc(e.message)}`); }
  finally { LT.busy.delete(c.sym); }
}
// 🛡 把交易所上的止損改成目前設定的浮虧 %：先改「持倉止損」，沒有的話就新掛一張；舊的止損單取消掉
async function ltSyncSL(X, kind) {                     // kind：'n'＝只同步一般、'sp'＝只同步特級、不給＝全部（每筆照自己的規則）
  const K = X.A.bx, T = kind === 'sp' ? TS(X) : TT(X), ok = [], bad = [], skip = [];
  for (const t of ltOpenTrades(X)) {
    if (!t.positionId || (kind === 'sp' && t.src !== 'tool') || (kind === 'n' && t.src === 'tool')) continue;
    const T = TRule(X, t);
    const rl = t.ruleLev || t.lev, slPx = t.entry * (1 - t.dir * T.sl / 100 / rl), px = PX.map[t.sym];
    if (px > 0 && t.dir * (px - slPx) <= 0) { skip.push(t.sym); continue; }     // 現價已經超過新的止損：伺服器下一輪就會平倉，不用掛
    const pr = await ltPair(t.sym).catch(() => null), sp = pxStr(slPx, pr ? +pr.quotePrecision || 4 : 6);
    const body = { symbol: t.sym, positionId: t.positionId, slPrice: sp, slStopType: 'MARK_PRICE' };
    let oid = null;
    try { oid = (await bxPost('/api/v1/futures/tpsl/position/modify_order', body, K) || {}).orderId; }
    catch (e1) {
      try { oid = (await bxPost('/api/v1/futures/tpsl/position/place_order', body, K) || {}).orderId; }
      catch (e2) { bad.push(`${t.sym}（${e2.message}）`); continue; }
    }
    try {                                              // 其他價格不一樣的止損單取消，免得舊的比較近先觸發
      const L = await bxGet('/api/v1/futures/tpsl/get_pending_orders', { symbol: t.sym, positionId: t.positionId, limit: 20 }, K);
      for (const o of Array.isArray(L) ? L : []) if (o.slPrice && String(o.id) !== String(oid) && Math.abs(+o.slPrice / slPx - 1) > 1e-6) await bxPost('/api/v1/futures/tpsl/cancel_order', { symbol: t.sym, orderId: String(o.id) }, K).catch(() => {});
    } catch (e) {}
    t.slPx = slPx; t.exSL = true; ok.push(t.sym);
    await sleep(250);
  }
  touchLT(X);
  if (ok.length || bad.length) dcX(X, `🛡 **${kind === 'sp' ? '🗡 特級交易的' : ''}交易所止損已改成 −${T.sl}%**（槓桿開不到 ${T.lev}x 的幣按比例縮小）：成功 ${ok.length} 筆${bad.length ? `，失敗 ${bad.length} 筆：${mdEsc(bad.join('、'))}` : ''}${skip.length ? `；${skip.join('、')} 已經超過新的止損，伺服器會直接平倉` : ''}\n-# 改失敗的單，伺服器還是會照 −${T.sl}% 幫你平倉`);
}
// 🔄 反手：手上有這個幣「反方向」的自動單 → 先市價平掉、確認倉位消失，再照新訊號開倉（手動單不動）
// 幣開不到你設定的槓桿：停利、停損、鎖利間距都按「實際槓桿 ÷ 設定槓桿」縮小（出場價格不變），通知裡顯示這筆單真正的報酬率
const rk = (t, rl) => (t.lev > 0 && rl > 0 ? t.lev / rl : 1);
const pctK = (v, k) => { const x = v * k; return Math.abs(x - Math.round(x)) < 0.05 ? String(Math.round(x)) : x.toFixed(1); };
async function ltFlipOpen(X, c) {
  const sp = c.src === 'tool', LT = X.LT, opp = ltOpenTrades(X).filter(t => t.sym === c.sym && t.dir !== c.dir && t.positionId && (sp ? t.src === 'tool' : t.src !== 'tool'));   // 🗡 特級只反手特級自己的單
  if (sp && !(X.A.lt.sp && toolOkUid(X.uid))) return;
  if (!opp.length) return ltOpen(X, c);
  if (!sp && X.A.lt.btcF && c.btcPass === false) { LT.msg = `${c.sym} 出現反方向訊號，但沒過 BTC 方向過濾，維持原本的單`; return; }
  if (ecoBlock()) { LT.msg = `${c.sym} 出現反方向訊號，但今天有美國重要數據，維持原本的單`; return; }
  if (LT.flip && LT.flip.has(c.sym)) return;
  (LT.flip = LT.flip || new Set()).add(c.sym);
  try {
    for (const t of opp) {
      t.closing = true;                                // 不讓每 3 秒的管理同時去平這一筆
      try { await ltClosePos(X, t.positionId, 1, 'flip'); }
      catch (e) { t.closing = false; dcX(X, `❗ **反手失敗** ${mdEsc(c.sym)}：原本的${t.dir > 0 ? '多單' : '空單'}平不掉（${mdEsc(e.message)}），不開新單`); return; }
    }
    const ids = new Set(opp.map(t => t.positionId)), still = () => X.BX.pos.some(p => ids.has(p.id)) || ltOpenTrades(X).some(t => ids.has(t.positionId));
    for (let i = 0; i < 8; i++) {                      // 等交易所確認「被反手的那幾筆」真的平掉了（最多約 12 秒）；雙開時這個幣可能還有另一套系統的倉位，不算
      await sleep(1500); await bxPollOne(X);
      if (!still()) break;
    }
    for (const t of opp) t.closing = false;
    if (X.BX.pos.some(p => ids.has(p.id))) { dcX(X, `❗ **反手**：${mdEsc(c.sym)} 原本的倉位還在，這次不開新單，請到交易所確認`); return; }
    if (X.BX.pos.some(p => p.sym === c.sym && p.dir === c.dir)) {   // 雙開時：這個幣已經有同方向的倉位（另一套系統或手動單），平掉就好，不再加開
      dcX(X, `🔄 **${c.src === 'tool' ? '🗡 特級交易' : ''}反手** ${mdEsc(c.sym)}：原本的${opp[0].dir > 0 ? '多單' : '空單'}已平倉；這個幣已經有${c.dir > 0 ? '多單' : '空單'}（另一套系統或手動單），不再加開`); return;
    }
    dcX(X, `🔄 **${c.src === 'tool' ? '🗡 特級交易' : ''}反手** ${mdEsc(c.sym)}：原本的${opp[0].dir > 0 ? '多單' : '空單'}已平倉，改${c.dir > 0 ? '做多' : '做空'}`);
    await ltOpen(X, c);
  } finally { LT.flip.delete(c.sym); }
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
    X.A.lt.on = false; X.A.lt.sp = false; X.LT.pause = { t: Date.now(), why: `部分平倉異常（${p.sym}）` }; touchLT(X);
    dcX(X, `🚨 **部分平倉異常**：${mdEsc(p.sym)} 倉位變大，已全部平倉並暫停自動交易，請檢查交易所`);
    throw new Error('部分平倉後倉位變大，已緊急全部平倉並暫停自動交易');
  }
  return 'part';
}
// 每 3 秒：照規則管理每個帳號自動開的單（帳號之間互不影響，一個帳號出錯不會卡住其他帳號）
async function ltManage() { for (const X of allX()) { if (X.managing || !ltOpenTrades(X).length) continue; X.managing = true; try { await ltManageX(X); } catch (e) { log('管理自動單失敗', X.uid, e.message); } finally { X.managing = false; } } }
async function ltManageX(X) {
  const now = Date.now();
  for (const t of ltOpenTrades(X)) {
    const T = TRule(X, t);                             // 🗡 特級交易用自己的停損、鎖利、持有天數
    const px = PX.map[t.sym]; if (!(px > 0) || !t.positionId || t.closing || (X.LT.flip && X.LT.flip.has(t.sym))) continue;
    const rl = t.ruleLev || t.lev;                     // 規則用的槓桿：新單＝你設定的槓桿（跟訊號模擬一致）；更新前開的舊單照原本的實際槓桿
    const roe = t.dir * (px / t.entry - 1) * rl * 100;
    t.cur = px; t.roe = roe; t.fav = Math.max(t.fav || 0, roe); t.adv = Math.min(t.adv || 0, roe);
    let why = '';
    if (roe <= -T.sl) why = 'fail';
    else if (T.exit === 'fixed') { if (roe >= T.tp) why = 'win'; }
    else if (t.fav >= T.tp) {                            // 鎖利：最高浮盈每多 step%，鎖利線就往上調一格，只升不降
      const lv = Math.max(lockAt(t.fav, T), t.lockLv || 0);
      const k = rk(t, rl), kn = k !== 1 ? `\n-# ${t.lev}x 的幣：你的 +${lv}% 按 ${t.lev}÷${rl} 縮小` : '';   // 通知裡顯示這筆單真正的報酬率
      if (!t.locked) { t.locked = true; touchLT(X); dcX(X, `${t.src === 'tool' ? '🗡 **特級交易**' : '🤖 **實盤**'}｜🔒 **達標鎖利** ${mdEsc(t.sym)}（${t.lev}x）：浮盈 +${pctK(roe, k)}%，鎖利線 **+${pctK(lv, k)}%**${T.step > 0 ? `\n之後浮盈每多 ${pctK(T.step, k)}% 鎖利線就往上調一次，跑回鎖利線就平倉` : `，之後跑回 +${pctK(lv, k)}% 就平倉`}${kn}`); }
      else if (lv > (t.lockLv || T.tp)) { touchLT(X); dcX(X, `${t.src === 'tool' ? '🗡 **特級交易**' : '🤖 **實盤**'}｜🔒 **鎖利上調** ${mdEsc(t.sym)}（${t.lev}x）：浮盈 +${pctK(roe, k)}%，鎖利線調到 **+${pctK(lv, k)}%**${kn}`); }
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
  // 交易所偶爾回傳不完整的持倉清單，舊版會把還開著的自動單誤記成「交易所平倉」→ 倉位變成「手動單」、伺服器不再管理。只要倉位還在就接回來
  for (const t of TR) {
    if (t.status !== 'closed' || t.reason !== 'exchange' || Date.now() - t.et > 7 * 24 * HOUR) continue;
    const free = x => !TR.some(o => o.status === 'open' && o.positionId === x.id);
    const p = t.positionId ? pos.find(x => x.id === t.positionId && free(x))
      : pos.find(x => x.sym === t.sym && x.dir === t.dir && free(x) && Math.abs(x.entry / t.entry - 1) < 0.002 && (!(x.ctime > 0) || Math.abs(x.ctime - t.et) < 5 * 60000));
    if (!p) continue;
    Object.assign(t, { status: 'open', reason: '', exitAt: 0, positionId: p.id, entry: p.entry, qty: p.qty, qty0: Math.max(t.qty0 || 0, p.qty), m0: p.margin || t.m0, lev: p.lev || t.lev, closes: (t.closes || []).slice(0, -1), miss: 0 });
    ch = true; log('找回被誤判平倉的自動單', X.uid, t.sym);
    dcX(X, `🔧 **找回自動單** ${mdEsc(t.sym)} ${t.dir > 0 ? '做多' : '做空'}：這筆單之前被誤記成已平倉，其實還開著，伺服器已經重新接管（鎖利、停損、到期照常）`);
  }
  for (const t of ltOpenTrades(X)) {
    let p = t.positionId ? byId.get(t.positionId) : pos.find(x => x.sym === t.sym && x.dir === t.dir && Math.abs((x.ctime || 0) - t.et) < 5 * 60000);   // 只認自動下單那一刻開的倉，手動開的不算
    if (p && !t.positionId) { t.positionId = p.id; t.entry = p.entry; t.qty = t.qty0 = p.qty; t.m0 = p.margin || t.m0; ch = true; }
    if (p) t.miss = 0;
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
    // 倉位不見了：去歷史持倉確認。是我們自己平的、或歷史紀錄查得到這筆，才算平倉；不然要連續 3 次（約 30 秒）都不見才算（交易所偶爾回傳不完整的清單）
    t.miss = (t.miss || 0) + 1;
    let h = null;
    try { const r = await bxGet('/api/v1/futures/position/get_history_positions', t.positionId ? { positionId: t.positionId } : { symbol: t.sym, limit: 5 }, K); h = (r && r.positionList || []).find(x => !t.positionId || String(x.positionId) === t.positionId) || null; } catch (e) {}
    if (!t.pendReason && !(t.positionId && h) && t.miss < 3) { ch = true; continue; }
    const reason = t.pendReason || (h && num(h.liqQty) > 0 ? 'liq' : 'exchange');
    if (h) Object.assign(t, { realized: num(h.realizedPNL), fee: num(h.fee), funding: num(h.funding), closePx: num(h.closePrice) });
    const prevPart = t.closes.reduce((a, c) => a + c.pnl, 0);
    t.closes.push({ t: Date.now(), qty: t.qty, pnl: (t.realized || 0) - prevPart, by: reason });
    Object.assign(t, { status: 'closed', exitAt: Date.now(), reason, qty: 0, upnl: 0 }); ch = true;
    const net = ltNet(t), nm = (t.src === 'tool' ? '🗡 **特級交易平倉**｜' : '🤖 **實盤平倉**｜') + ({ win: '✅ 達標出場', lock: `🔒 鎖利出場（鎖利線 +${pctK(t.lockLv || TRule(X, t).tp, rk(t, t.ruleLev || t.lev))}%）`, fail: '❌ 失敗線出場', timeout: '⏱ 持有到期出場', manual: '🖐 手動平倉', all: '🛑 一鍵平倉（自動單）', flip: '🔄 反手平倉', liq: '💥 強平', exchange: '📤 交易所平倉（止損或在 App 平倉）' }[reason] || reason);
    dcX(X, `${nm} **${mdEsc(t.sym)}** ${t.dir > 0 ? '做多' : '做空'}\n淨損益 **${net >= 0 ? '+' : '−'}${Math.abs(net).toFixed(2)}U**（${(net / (t.m0 || X.A.lt.margin) * 100).toFixed(0)}%）・持有 ${durTxt(Date.now() - t.et)}${t.closePx ? `・平倉均價 ${fpx(t.closePx)}` : ''}`);
  }
  // 🔍 第二層判斷：沒被管理的倉位，如果其實是伺服器開的，就自動接回管理（每筆倉位每 5 分鐘檢查一次）
  //    ① 跟訊號卡片同幣、同方向，開倉時間跟卡片進場時間差 20 秒內（人看到通知再手動跟單通常要更久，不會被誤接）
  //    ② 交易所的開倉訂單有伺服器下單時加的標記（q 開頭的 clientId），手動在 App 下的單沒有
  const OC = X.LT.orphan || (X.LT.orphan = {});
  for (const p of pos) {
    if (TR.some(t => t.status === 'open' && (t.positionId === p.id || t.sym === p.sym))) continue;
    if (!(p.ctime > 0) || Date.now() - (OC[p.id] || 0) < 5 * 60000) continue;
    OC[p.id] = Date.now();
    let why = '';
    const card = ST.cards.find(c => c.sym === p.sym && c.dir === p.dir && c.et && (Math.abs(p.ctime - c.et) <= 20000 || (c.btcLate && Math.abs(p.ctime - c.btcLate) <= 30000)));
    if (card) why = `跟訊號卡片同時進場（${tw(card.et)}）`;
    if (!why) {
      try {
        const r = await bxGet('/api/v1/futures/trade/get_history_orders', { symbol: p.sym, limit: 20 }, K);
        const L0 = Array.isArray(r) ? r : (r && (r.orderList || r.list)) || [];
        if (L0.find(o => /^q[0-9a-z]{6,}$/.test(String(o.clientId || o.clientOrderId || '')) && sideDir(o.side) === p.dir && Math.abs(msT(num(o.ctime)) - p.ctime) <= 60000)) why = '開倉訂單有伺服器下單的標記';
      } catch (e) {}
    }
    if (!why) continue;
    const C = X.A.lt, px = PX.map[p.sym] || p.entry, roe = p.dir * (px / p.entry - 1) * C.lev * 100;
    const t = {
      id: 'lt-found-' + Date.now(), sym: p.sym, dir: p.dir, card: card ? card.id : '', abN: card ? card.abN : 0, et: p.ctime, lev: p.lev,
      entry: p.entry, qty: p.qty, qty0: p.qty, margin: p.margin, m0: p.margin || C.margin, positionId: p.id, orderId: '', status: 'open', ruleLev: C.lev,
      realized: p.rpnl || 0, fee: p.fee || 0, funding: p.funding || 0, closes: [], locked: false, fav: Math.max(0, roe), adv: Math.min(0, roe), exSL: false, found: Date.now(), prec: 0, minQty: 0
    };
    const pr = await ltPair(p.sym).catch(() => null); if (pr) { t.prec = +pr.basePrecision || 0; t.minQty = +pr.minTradeVolume || 0; }
    TR.unshift(t); ch = true; log('偵測到伺服器開的單，自動接回', X.uid, p.sym, why);
    const T = TT(X), k = rk(t, C.lev);
    dcX(X, `🔧 **偵測到伺服器開的單** ${p.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(p.sym)}**（${p.lev}x）\n${why}，但之前沒被記到，已經自動接回管理\n浮盈 **+${pctK(T.tp, k)}%** 開始鎖利、浮虧 **−${pctK(T.sl, k)}%** 停損、持有 ${T.hold} 小時到期`);
    setTimeout(() => ltSyncSL(X).catch(e => log('補掛止損失敗', X.uid, e.message)), 500);
  }
  // 單日虧損上限（台北時間每天 00:00 重算）
  const L = X.A.lt, LT = X.LT, day = new Date(Date.now() + TZ).toISOString().slice(0, 10), d0 = Date.parse(day + 'T00:00:00Z') - TZ;
  let dayPnl = 0, spDay = 0;
  for (const t of TR) { let v = 0; for (const c of t.closes || []) if (c.t >= d0) v += c.pnl; if (t.status === 'open') v += t.upnl || 0; if (t.src === 'tool') spDay += v; else dayPnl += v; }
  LT.dayPnl = dayPnl; LT.spDayPnl = spDay;
  if (L.sp && L.spDayLoss > 0 && spDay <= -L.spDayLoss && LT.spDayHit !== day) {   // 🗡 特級交易自己的單日虧損上限
    LT.spDayHit = day; L.sp = false; LT.pause = { t: Date.now(), why: '特級交易超過單日虧損上限' }; ch = true;
    dcX(X, `🛑 **🗡 特級交易今天虧損 ${spDay.toFixed(2)}U，超過上限 ${L.spDayLoss}U，特級交易已暫停**（已開的單照常管理，可以在網站重新開始）`);
  }
  if (L.on && L.dayLoss > 0 && dayPnl <= -L.dayLoss && LT.dayHit !== day) {
    LT.dayHit = day; L.on = false; LT.pause = { t: Date.now(), why: '超過單日虧損上限' }; ch = true;
    dcX(X, `🛑 **今天虧損 ${dayPnl.toFixed(2)}U，超過上限 ${L.dayLoss}U，自動交易已暫停**（已開的單照常管理，可以在網站重新開始）`);
  }
  if (ch) touchLT(X);
}

/* ================= 🗡 特級咒具：莊家進場、H4/H1 CRT 進場、獵殺進場 =================
   移植自擁有者的兩套 TradingView 指標（只有這三種進場；BigBeluga 的清算熱力圖沒有用到）。
   兩組週期：4H→15 分、1H→5 分。每根小週期 K 棒收盤後，掃描成交額前 N 個幣，出現進場就記下來、傳 Discord。
   莊家淨額：原指標用 1 分 K 的漲跌方向推估主動買賣；這裡改用幣安直接給的主動買入成交額（主動買 − 主動賣），更準但數字會跟 TradingView 有些差 */
const DEF_TOOL = { pw: null, grants: [], hooks: {}, px: {}, set: { n: 30, h4: true, h1: true, zh: true, crt: true, hunt: true }, sigs: [], seen: {}, scan: { at: 0, coins: 0, err: '', n: 0 } };
ST.tool = { ...DEF_TOOL, ...(ST.tool || {}) }; ST.tool.set = { ...DEF_TOOL.set, ...(ST.tool.set || {}) }; ST.tool.scan = { ...DEF_TOOL.scan };
let TOOLV = 1;
const TOOL_P = { h4: { ltf: '15m', lms: 15 * 60000, htf: '4h', hms: 4 * HOUR, slotH: 4, maxSlot: 5, name: '4H→15 分', crt: 'H4' }, h1: { ltf: '5m', lms: 5 * 60000, htf: '1h', hms: HOUR, slotH: 1, maxSlot: 23, name: '1H→5 分', crt: 'H1' } };
const toolUsers = () => [ownerUid(), ...ST.tool.grants.filter(u => ST.users.some(x => x.uid === u))];
const toolOk = (me, owner) => owner || !!(me && ST.tool.grants.includes(me.uid));
async function toolKl(sym, iv, limit, ms) {           // 只要已經收盤的 K 棒
  const r = await getJSON(`${BF}/fapi/v1/klines?symbol=${sym}&interval=${iv}&limit=${limit}`);
  return (Array.isArray(r) ? r : []).map(x => ({ t: +x[0], o: +x[1], h: +x[2], l: +x[3], c: +x[4], qv: +x[7], tb: +x[10] })).filter(b => b.t + ms <= Date.now());
}
// CHoCH／BOS（照指標的 f_leg／f_structure）：每根 K 棒有沒有看漲、看跌結構突破
function toolStruct(B, len) {
  const n = B.length, bull = new Array(n).fill(false), bear = new Array(n).fill(false), tagB = new Array(n).fill(''), tagS = new Array(n).fill('');
  let leg = 0, prevLeg = 0, swH = NaN, swL = NaN, hX = false, lX = false, bias = 0, pH = NaN, pL = NaN;
  for (let i = 0; i < n; i++) {
    if (i >= len) {                                    // high[len] 跟最近 len 根（不含它）比
      let mh = -Infinity, ml = Infinity; for (let k = i - len + 1; k <= i; k++) { if (B[k].h > mh) mh = B[k].h; if (B[k].l < ml) ml = B[k].l; }
      if (B[i - len].h > mh) leg = 0; else if (B[i - len].l < ml) leg = 1;
    }
    if (i > 0 && leg !== prevLeg) { if (leg === 1) { swL = B[i - len].l; lX = false; } else { swH = B[i - len].h; hX = false; } }
    prevLeg = leg;
    const c = B[i].c, cp = i ? B[i - 1].c : NaN;
    const up = !isNaN(swH) && !isNaN(pH) && c > swH && cp <= pH, dn = !isNaN(swL) && !isNaN(pL) && c < swL && cp >= pL;   // ta.crossover／crossunder
    if (up && !hX) { bull[i] = true; hX = true; tagB[i] = bias === -1 ? 'CHoCH' : 'BOS'; bias = 1; }
    if (dn && !lX) { bear[i] = true; lX = true; tagS[i] = bias === 1 ? 'CHoCH' : 'BOS'; bias = -1; }
    pH = swH; pL = swL;
  }
  return { bull, bear, tagB, tagS };
}
function toolAtr(B, len) {                            // ta.atr（RMA）
  const out = new Array(B.length).fill(NaN); let rma = NaN, sum = 0;
  for (let i = 0; i < B.length; i++) {
    const b = B[i], tr = i ? Math.max(b.h - b.l, Math.abs(b.h - B[i - 1].c), Math.abs(b.l - B[i - 1].c)) : b.h - b.l;
    if (i < len) { sum += tr; if (i === len - 1) rma = sum / len; } else rma = (rma * (len - 1) + tr) / len;
    out[i] = rma;
  }
  return out;
}
// 🎯 獵殺進場（天神下凡）：同一天（UTC）連續兩根 4H／1H：前跌後漲且後低破前低＝看漲窗口；前漲後跌且後高破前高＝看跌窗口 → 窗口內出現同方向 CHoCH/BOS，下一根標示進場
function toolHunt(L, P, sb, ib) {
  const out = []; let day = [], curDay = null, acc = null, win = { dir: 0, trig: false }, pend = null;
  for (let i = 0; i < L.length; i++) {
    const b = L[i], slot = Math.floor(new Date(b.t).getUTCHours() / P.slotH) + 1, dayId = Math.floor(b.t / 86400000);
    if (!acc || slot !== acc.slot || dayId !== acc.day) {
      if (acc && dayId !== acc.day && win.dir && !win.trig) win = { dir: 0, trig: false };   // 新的一天：還沒觸發的窗口取消
      if (acc) {
        if (acc.day !== curDay) { day = []; curDay = acc.day; }
        day.push(acc);
        const n = day.length;
        if (n >= 2) {
          const p = day[n - 2], q = day[n - 1];
          if (q.slot === p.slot + 1 && q.slot <= P.maxSlot) {
            const lp = p.c < p.o && q.c > q.o && q.l < p.l, sp = p.c > p.o && q.c < q.o && q.h > p.h;
            if (lp || sp) win = { dir: lp ? 1 : -1, trig: false };
          }
        }
      }
      acc = { o: b.o, h: b.h, l: b.l, c: b.c, slot, day: dayId };
    } else { acc.h = Math.max(acc.h, b.h); acc.l = Math.min(acc.l, b.l); acc.c = b.c; }
    if (win.dir && !win.trig) {
      const brk = win.dir === 1 ? (sb.bull[i] || ib.bull[i]) : (sb.bear[i] || ib.bear[i]);
      if (brk) { win.trig = true; pend = { dir: win.dir, i, tag: win.dir === 1 ? (ib.tagB[i] || sb.tagB[i]) : (ib.tagS[i] || sb.tagS[i]) }; }
    }
    if (pend && i === pend.i + 1) { out.push({ i, dir: pend.dir, tag: pend.tag }); pend = null; }
  }
  return out;
}
// 💰 莊家進場：大週期 K 棒收跌但淨額為正＝吸貨背離、收漲但淨額為負＝出貨背離 → 小週期同方向 CHoCH/BOS（Internal）進場；反向結構出現就取消背離；每個背離只進場一次
function toolZh(L, P, ib) {
  const out = []; let acc = null, setup = 0, used = false;
  for (let i = 0; i < L.length; i++) {
    const b = L[i], hs = Math.floor(b.t / P.hms) * P.hms; let bull = false, bear = false;
    if (!acc || hs !== acc.t) {
      if (acc && acc.full) { if (acc.c < acc.o && acc.net > 0) bull = true; if (acc.c > acc.o && acc.net < 0) bear = true; }
      acc = { t: hs, o: b.o, c: b.c, net: 0, full: b.t === hs };   // 資料開頭不完整的那根大週期不判斷
    }
    acc.net += 2 * b.tb - b.qv; acc.c = b.c;
    if (bull) { setup = 1; used = false; acc.div = 1; }
    if (bear) { setup = -1; used = false; }
    const bB = ib.bull[i], bS = ib.bear[i];
    if (setup === 1 && !used && bB) { out.push({ i, dir: 1, tag: ib.tagB[i] }); used = true; }
    if (setup === -1 && !used && bS) { out.push({ i, dir: -1, tag: ib.tagS[i] }); used = true; }
    if ((setup === 1 && bS) || (setup === -1 && bB)) { setup = 0; used = false; }
  }
  return out;
}
// 🕯 H4/H1 CRT 進場：大週期掃前一根高低點再收回（嚴格：前一根顏色相反）→ 之後第 1～2 根大週期內，小週期結構轉向（武裝）後回踩 FVG，風險距離 ≥ 0.3 ATR → 進場；止盈＝盈虧比 1:1
function toolCrt(L, H, P, sb, ib, atr) {
  const st = []; let dir = 0, ci = -1, top = NaN, bot = NaN;
  for (let j = 0; j < H.length; j++) {
    if (j >= 1) {
      const a = H[j - 1], b = H[j];
      if (b.l < a.l && b.c > a.l && b.c > b.o && a.c < a.o) { dir = 1; ci = j; top = Math.max(a.h, b.h); bot = a.l; }
      if (b.h > a.h && b.c < a.h && b.c < b.o && a.c > a.o) { dir = -1; ci = j; top = a.h; bot = Math.min(a.l, b.l); }
    }
    st.push({ dir, ci, top, bot });
  }
  const out = []; let bias = 0, la = false, sa = false, bz = [], sz = [], k = -1;
  for (let i = 0; i < L.length; i++) {
    const b = L[i], ct = b.t + P.lms;
    while (k + 1 < H.length && H[k + 1].t + P.hms <= ct) k++;   // 這根小 K 收盤時，已經收盤的最後一根大週期（等同 lookahead_off）
    const S = k >= 0 ? st[k] : null, since = S && S.ci >= 0 ? k - S.ci : NaN, act = !!(S && S.dir && since >= 1 && since <= 2), cdir = act ? S.dir : 0;
    const anyB = sb.bull[i] || ib.bull[i], anyS = sb.bear[i] || ib.bear[i];
    if (anyB) { bias = 1; la = true; sa = false; }
    if (anyS) { bias = -1; sa = true; la = false; }
    if (anyB) bz = []; if (anyS) sz = [];
    if (i >= 2) {
      const p1 = L[i - 1], p2 = L[i - 2], d = (p1.c - p1.o) / (p1.o * 100);
      if (b.l > p2.h && p1.c > p2.h && d > 0) { bz.unshift({ top: b.l, bot: p2.h, i }); if (bz.length > 5) bz.pop(); }
      if (b.h < p2.l && p1.c < p2.l && -d > 0) { sz.unshift({ top: p2.l, bot: b.h, i }); if (sz.length > 5) sz.pop(); }
    }
    bz = bz.filter(z => !(b.c < z.bot)); sz = sz.filter(z => !(b.c > z.top));
    const bh = Math.max(b.o, b.c), bl = Math.min(b.o, b.c), hit = Z => Z.some(z => z.i !== i && b.h >= z.bot && b.l <= z.top && !(bl <= z.bot && bh >= z.top));
    const lh = hit(bz), sh = hit(sz), A = atr[i];
    if (la && bias === 1 && lh && cdir === 1 && b.c - S.bot >= 0.3 * A) { out.push({ i, dir: 1, sl: S.bot, tp: b.c + (b.c - S.bot) }); la = false; }
    if (sa && bias === -1 && sh && cdir === -1 && S.top - b.c >= 0.3 * A) { out.push({ i, dir: -1, sl: S.top, tp: b.c - (S.top - b.c) }); sa = false; }
  }
  return out;
}
const TOOLU = { at: 0, list: [] };
async function toolUniverse(n) {                       // 成交額前 N 個 USDT 永續（每小時更新一次）
  if (Date.now() - TOOLU.at > HOUR || !TOOLU.list.length) {
    const r = await getJSON(`${BF}/fapi/v1/ticker/24hr`);
    TOOLU.list = (Array.isArray(r) ? r : []).filter(x => /USDT$/.test(x.symbol) && !x.symbol.includes('_')).sort((a, b) => +b.quoteVolume - +a.quoteVolume).map(x => x.symbol); TOOLU.at = Date.now();
  }
  return TOOLU.list.slice(0, n);
}
function toolNotify(s) {
  const P = TOOL_P[s.pair], nm = { zh: '莊家進場', crt: `${P.crt} CRT 進場`, hunt: '獵殺進場' }[s.type];
  const msg = `🗡 **特級咒具**｜${s.dir > 0 ? '🟢 **做多**' : '🔴 **做空**'} **${mdEsc(s.sym)}**・**${nm}**（${P.name}）\n進場時間 ${tw(s.t)}（台北）・價格 ${fpx(s.px)}${s.tag ? `・${s.tag}` : ''}${s.type === 'crt' ? `\n止損 ${fpx(s.sl)}・止盈 ${fpx(s.tp)}（盈虧比 1:1）` : ''}`;
  const seen = new Set();
  for (const uid of toolUsers()) { let h = ''; try { h = dec(ST.tool.hooks[uid] || ''); } catch (e) {} if (!h || seen.has(h)) continue; seen.add(h); dcSend(msg, { webhook: h }); }
}
/* ---------- 🗡 特級咒具回測：三種進場 × 兩組週期，用「我的設定」的出場規則（停損、開始鎖利、鎖利上調、持有天數、槓桿）、每筆保證金、初始資金、手續費全部算進去 ---------- */
const TBT = { run: false, done: 0, total: 0, msg: '' };
async function toolKlRange(sym, iv, ms, from, to) {     // 分段抓一段期間的 K 線（只要已收盤的）
  const out = []; let s0 = from;
  while (s0 < to) {
    const r = await getJSON(`${BF}/fapi/v1/klines?symbol=${sym}&interval=${iv}&startTime=${s0}&limit=1500`);
    if (!Array.isArray(r) || !r.length) break;
    for (const x of r) { const t = +x[0]; if (t + ms <= Date.now() && (!out.length || t > out[out.length - 1].t)) out.push({ t, o: +x[1], h: +x[2], l: +x[3], c: +x[4], qv: +x[7], tb: +x[10] }); }
    const last = +r[r.length - 1][0]; if (r.length < 1500 || last + ms >= to) break; s0 = last + ms;
  }
  return out;
}
// 一筆單的出場：K 棒內的走法——收漲的 K 棒當作「開→低→高→收」、收跌的當作「開→高→低→收」，照順序檢查停損、鎖利、最高浮盈；到期用收盤價
function toolExit(B, i0, d, e, T, lev, lms) {
  const roe = p => d * (p / e - 1) * lev * 100, et = B[i0].t + lms, holdMs = (T.hold || 168) * HOUR;
  let peak = 0, locked = false;
  for (let i = i0 + 1; i < B.length; i++) {
    const b = B[i], tEnd = b.t + lms, path = b.c >= b.o ? [b.o, b.l, b.h, b.c] : [b.o, b.h, b.l, b.c];
    for (const p of path) {
      const r = roe(p);
      if (!locked && r <= -T.sl) return { t: tEnd, roe: -T.sl, how: 'fail' };
      if (locked) { const lv = lockAt(peak, T); if (r <= lv) return { t: tEnd, roe: lv, how: 'lock' }; }
      if (r > peak) peak = r;
      if (!locked && peak >= T.tp) locked = true;
    }
    if (tEnd - et >= holdMs) return { t: tEnd, roe: roe(b.c), how: 'hold' };
  }
  const z = B[B.length - 1]; return { t: z.t + lms, roe: roe(z.c), how: 'open' };
}
async function toolBacktest(X, cfg) {
  const S = ST.tool.set, days = [7, 14, 30].includes(+cfg.days) ? +cfg.days : 14, n = Math.max(5, Math.min(50, Math.round(+cfg.n || S.n || 30)));
  const L0 = X.A.lt, T = TS(X), lev = L0.spLev || L0.lev || 100, m = L0.spMargin || L0.margin || 0.3, cap0 = L0.spBudget > 0 ? L0.spBudget : 100, fee = ((ST.eq && ST.eq.fee) ?? 0.05) / 100;
  const start = Date.now() - days * 24 * HOUR, warm = 2 * 24 * HOUR, pairs = ['h4', 'h1'].filter(p => S[p]);
  const syms = await toolUniverse(n); TBT.total = syms.length * pairs.length; TBT.done = 0;
  const cand = [];
  for (const sym of syms) for (const pair of pairs) {
    const P = TOOL_P[pair];
    try {
      TBT.msg = `${sym} ${P.name}`;
      const L = await toolKlRange(sym, P.ltf, P.lms, start - warm, Date.now()), H = await toolKlRange(sym, P.htf, P.hms, start - warm - 10 * P.hms, Date.now());
      if (L.length < 200 || H.length < 3) continue;
      const sb = toolStruct(L, 50), ib = toolStruct(L, 5), atr = toolAtr(L, 14), found = [];
      if (S.zh) for (const x of toolZh(L, P, ib)) found.push({ ...x, type: 'zh' });
      if (S.crt) for (const x of toolCrt(L, H, P, sb, ib, atr)) found.push({ ...x, type: 'crt' });
      if (S.hunt) for (const x of toolHunt(L, P, sb, ib)) found.push({ ...x, type: 'hunt' });
      for (const x of found) {
        const et = L[x.i].t + P.lms; if (et < start) continue;
        const ex = toolExit(L, x.i, x.dir, L[x.i].c, T, lev, P.lms);
        cand.push({ sym, type: x.type, pair, dir: x.dir, et, entry: L[x.i].c, xt: ex.t, roe: ex.roe, how: ex.how });
      }
    } catch (e) { TBT.msg = `${sym}：${e.message}`; }
    TBT.done++;
  }
  // 資金模擬：照時間先後；同一個幣還開著就跳過；可用資金不夠也跳過
  cand.sort((a, b) => a.et - b.et);
  const open = [], trades = [], eq = [[start, cap0]]; let cash = cap0, used = 0, peakEq = cap0, mdd = 0, maxOpen = 0, skipCoin = 0, skipCash = 0;
  const settle = until => {
    open.sort((a, b) => a.xt - b.xt);
    while (open.length && open[0].xt <= until && open[0].how !== 'open') {
      const t = open.shift(); used -= m; cash += t.pnl; eq.push([t.xt, +(cash).toFixed(4)]);
      peakEq = Math.max(peakEq, cash); mdd = Math.max(mdd, peakEq > 0 ? (peakEq - cash) / peakEq * 100 : 0);
    }
  };
  for (const c of cand) {
    settle(c.et);
    if (open.some(o => o.sym === c.sym)) { skipCoin++; continue; }
    if (cash - used < m) { skipCash++; continue; }
    c.pnl = m * c.roe / 100 - 2 * m * lev * fee; c.net = c.pnl / m * 100;   // 損益（U）＝保證金 × 報酬率 − 開平倉手續費
    open.push(c); used += m; trades.push(c); maxOpen = Math.max(maxOpen, open.length);
  }
  settle(Infinity);
  const unreal = open.reduce((a, t) => a + t.pnl, 0);
  const grp = L => { const done = L.filter(t => t.how !== 'open'), win = done.filter(t => t.pnl > 0).length;
    return { n: L.length, done: done.length, win, rate: done.length ? +(win / done.length * 100).toFixed(1) : null, avg: done.length ? +(done.reduce((a, t) => a + t.net, 0) / done.length).toFixed(1) : null, sum: +L.reduce((a, t) => a + t.pnl, 0).toFixed(3),
      fail: done.filter(t => t.how === 'fail').length, lock: done.filter(t => t.how === 'lock').length, hold: done.filter(t => t.how === 'hold').length }; };
  ST.tool.bt = {
    at: Date.now(), start, end: Date.now(), days, coins: syms.length, pairs,
    rule: { tp: T.tp, step: T.step, sl: T.sl, hold: T.hold, lev, m, cap0, fee: fee * 100 },
    all: grp(trades), by: { zh: grp(trades.filter(t => t.type === 'zh')), crt: grp(trades.filter(t => t.type === 'crt')), hunt: grp(trades.filter(t => t.type === 'hunt')) },
    byPair: { h4: grp(trades.filter(t => t.pair === 'h4')), h1: grp(trades.filter(t => t.pair === 'h1')) },
    endCap: +(cash + unreal).toFixed(3), realCap: +cash.toFixed(3), mdd: +mdd.toFixed(1), maxOpen, skipCoin, skipCash, found: cand.length,
    eq: eq.length > 400 ? eq.filter((_, i) => i % Math.ceil(eq.length / 400) === 0 || i === eq.length - 1) : eq,
    trades: trades.slice(-300).reverse().map(t => ({ sym: t.sym, type: t.type, pair: t.pair, dir: t.dir, et: t.et, entry: t.entry, xt: t.xt, how: t.how, net: +t.net.toFixed(1), pnl: +t.pnl.toFixed(4) }))
  };
  dirty = true; TOOLV++;
}

const TOOLR = { h4: 0, h1: 0, busy: false };
async function toolScan(pair) {
  const T = ST.tool, S = T.set, P = TOOL_P[pair]; let n = 0, newN = 0;
  const syms = await toolUniverse(Math.max(5, Math.min(100, +S.n || 30)));
  for (const sym of syms) {
    try {
      const L = await toolKl(sym, P.ltf, 500, P.lms), H = await toolKl(sym, P.htf, 120, P.hms);
      if (L.length < 120 || H.length < 3) continue;
      n++;
      { const a = L[L.length - 1], k = Math.round(24 * HOUR / P.lms), b0 = L[L.length - 1 - k]; T.px = T.px || {}; T.px[sym] = { c: a.c, chg: b0 ? (a.c / b0.c - 1) * 100 : null, at: Date.now() }; }   // 卡片上的現價、24 小時漲跌
      const sb = toolStruct(L, 50), ib = toolStruct(L, 5), atr = toolAtr(L, 14), last = L.length - 1, found = [];
      if (S.zh) for (const x of toolZh(L, P, ib)) found.push({ ...x, type: 'zh' });
      if (S.crt) for (const x of toolCrt(L, H, P, sb, ib, atr)) found.push({ ...x, type: 'crt' });
      if (S.hunt) for (const x of toolHunt(L, P, sb, ib)) found.push({ ...x, type: 'hunt' });
      for (const x of found) {
        const b = L[x.i], key = `${sym}|${x.type}|${pair}|${b.t}|${x.dir}`;
        if (T.seen[key]) continue; T.seen[key] = Date.now();
        const sg = { id: key, sym, type: x.type, pair, dir: x.dir, t: b.t + P.lms, px: b.c, sl: x.sl || 0, tp: x.tp || 0, tag: x.tag || '' };
        T.sigs.push(sg); newN++;
        if (x.i >= last - 1 && Date.now() - sg.t < 3 * P.lms) {   // 剛收盤的才通知、才下單；往回補的舊訊號只放進列表
          toolNotify(sg);
          for (const XA of allX()) if (XA.A.lt.sp && toolOkUid(XA.uid)) ltFlipOpen(XA, { id: sg.id, sym, dir: x.dir, abN: 0, src: 'tool', ttype: x.type, tpair: pair, last: b.c }).catch(e => log('特級交易下單失敗', XA.uid, sym, e.message));   // 同一個幣反方向：反手
        }
      }
    } catch (e) { T.scan.err = `${sym}：${e.message}`; }
  }
  T.sigs.sort((a, b) => b.t - a.t); T.sigs = T.sigs.slice(0, 400);
  const cut = Date.now() - 8 * 24 * HOUR; for (const k of Object.keys(T.seen)) if (T.seen[k] < cut) delete T.seen[k];
  T.scan = { ...T.scan, at: Date.now(), coins: n, n: syms.length };
  if (newN) { dirty = true; TOOLV++; }
}
setInterval(async () => {                              // 每根 5 分／15 分 K 收盤後約 20 秒掃一次
  if (TOOLR.busy) return;
  const t = Date.now() - 20000, S = ST.tool.set;
  for (const pair of ['h1', 'h4']) {
    const ms = TOOL_P[pair].lms, slot = Math.floor(t / ms);
    if (!S[pair] || slot <= TOOLR[pair]) continue;
    TOOLR[pair] = slot; TOOLR.busy = true;
    try { await toolScan(pair); } catch (e) { ST.tool.scan.err = e.message; } finally { TOOLR.busy = false; }
  }
}, 15000);

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

/* ---------------- 📈 BTC 急漲急跌統計：抓過去 N 天的 BTC 1 分鐘 K 線，算「W 分鐘內漲跌超過 X%」多久發生一次 ----------------
   一頁一頁抓、只留數字（13 萬根也只佔幾 MB）；同一波行情觸發後 30 分鐘內不重複算 */
const BSTAT = { busy: false, msg: '', at: 0, v: null };
async function btcStat(days = 90) {
  if (BSTAT.busy) return; BSTAT.busy = true; BSTAT.msg = '開始抓 BTC 1 分鐘 K 線…';
  try {
    const M = 60000, end = Math.floor(Date.now() / M) * M, from = end - days * 24 * HOUR, N = Math.ceil((end - from) / M);
    const T = new Float64Array(N), H = new Float64Array(N), L = new Float64Array(N), C = new Float64Array(N); let n = 0;
    for (let f = from, pg = 0; f < end; f += 1000 * M, pg++) {
      const rows = await getJSON(`${BF}/fapi/v1/klines?symbol=BTCUSDT&interval=1m&startTime=${f}&limit=1000`);
      for (const r of rows) { const t = +r[0]; if (t >= end || (n && t <= T[n - 1])) continue; T[n] = t; H[n] = +r[2]; L[n] = +r[3]; C[n] = +r[4]; n++; }
      BSTAT.msg = `抓 K 線中…${Math.min(100, Math.round((pg + 1) * 1000 / N * 100))}%`;
    }
    if (n < 1000) throw new Error('抓到的 K 線太少');
    BSTAT.msg = '計算中…';
    const span = (T[n - 1] - T[0]) / (7 * 24 * HOUR), COOL = 30;   // 幾週、觸發後冷卻幾分鐘
    const scan = (W, thr, dir) => {                     // dir 1＝急漲（現在的高點比 W 分鐘內最低點高 thr%）；-1＝急跌
      const ev = [];
      for (let i = W; i < n; i++) {
        let ext = dir > 0 ? Infinity : 0;
        for (let k = i - W + 1; k <= i; k++) ext = dir > 0 ? Math.min(ext, L[k]) : Math.max(ext, H[k]);
        const mv = dir > 0 ? H[i] / ext - 1 : 1 - L[i] / ext;
        if (mv * 100 >= thr) { ev.push(i); i += COOL; }
      }
      return ev;
    };
    const Ws = [3, 5, 10, 15], Ts = [0.5, 0.75, 1, 1.5, 2], grid = [];
    for (const W of Ws) for (const thr of Ts) {
      const up = scan(W, thr, 1), dn = scan(W, thr, -1);
      grid.push({ W, thr, up: up.length, dn: dn.length, upW: Math.round(up.length / span * 10) / 10, dnW: Math.round(dn.length / span * 10) / 10 });
    }
    // 以「5 分鐘 1%」為例：觸發後 30、60 分鐘是繼續往同方向，還是拉回來（用觸發那根 K 棒的收盤價當作「我們出手的價格」）
    const after = (dir) => scan(5, 1, dir).map(i => {
      const p0 = C[i], at = (m) => (i + m < n ? (C[i + m] / p0 - 1) * 100 * dir : null);
      let more = 0, back = 0; for (let k = i + 1; k <= Math.min(n - 1, i + 60); k++) { more = Math.max(more, ((dir > 0 ? H[k] : L[k]) / p0 - 1) * 100 * dir); back = Math.min(back, ((dir > 0 ? L[k] : H[k]) / p0 - 1) * 100 * dir); }
      return { t: T[i], px: p0, a30: at(30), a60: at(60), more: Math.round(more * 100) / 100, back: Math.round(back * 100) / 100 };
    });
    const sum = list => { const d = list.filter(x => x.a30 !== null); return { n: list.length, cont30: d.filter(x => x.a30 > 0).length, rev30: d.filter(x => x.a30 <= 0).length, avg30: d.length ? Math.round(d.reduce((a, x) => a + x.a30, 0) / d.length * 100) / 100 : null, avgMore: list.length ? Math.round(list.reduce((a, x) => a + x.more, 0) / list.length * 100) / 100 : null }; };
    const up = after(1), dn = after(-1);
    BSTAT.v = { at: Date.now(), from: T[0], to: T[n - 1], bars: n, weeks: Math.round(span * 10) / 10, cool: COOL, grid, up: { ...sum(up), list: up.slice(-15).reverse() }, dn: { ...sum(dn), list: dn.slice(-15).reverse() } };
    BSTAT.at = Date.now(); BSTAT.msg = ''; ST.bstat = BSTAT.v; dirty = true;
    log('BTC 急漲急跌統計完成', n, '根 K 線');
  } catch (e) { BSTAT.msg = '統計失敗：' + e.message; log('BTC 急漲急跌統計失敗', e.message); }
  BSTAT.busy = false;
}

/* ---------------- 🩺 伺服器健康：出問題就傳 Discord，每天早上回報一次 ---------------- */
const BOOT = Date.now(), HL = { scanBad: 0, bx: {} };
function healthTick() {
  const now = Date.now(), OX = ctx(ownerUid());
  // 掃描超過 10 分鐘沒成功（幣安連不到、程式卡住）→ 告訴擁有者；一小時最多一次，恢復時也說一聲
  const age = now - (SCAN.okAt || BOOT);
  if (age > 10 * 60000) { if (now - HL.scanBad > HOUR) { HL.scanBad = now; dcX(OX, `🩺 **掃描已經 ${Math.round(age / 60000)} 分鐘沒成功**${SCAN.err ? `：${mdEsc(SCAN.err)}` : ''}\n新訊號會停住，已開的單照常管理。持續沒恢復請在 SSH 打 \`journalctl -u quant -n 50\` 看原因`); } }
  else if (HL.scanBad) { HL.scanBad = 0; dcX(OX, '🩺 **掃描恢復正常**'); }
  // 每個帳號：Bitunix 連續 5 分鐘讀不到 → 告訴那個帳號（讀不到就沒辦法管理持倉）
  for (const X of allX()) {
    if (!hasKey(X)) continue;
    const bad = X.BX.err && now - (X.BX.at || BOOT) > 5 * 60000, H = HL.bx[X.uid] || (HL.bx[X.uid] = { at: 0 });
    if (bad) { if (now - H.at > HOUR) { H.at = now; dcX(X, `🩺 **讀不到你的 Bitunix 帳戶已經 ${Math.round((now - (X.BX.at || BOOT)) / 60000)} 分鐘**：${mdEsc(X.BX.err)}\n這段時間伺服器沒辦法幫你管理持倉（鎖利、到期）。常見原因：API 金鑰被刪、IP 白名單不對、Bitunix 維護`); } }
    else if (H.at) { H.at = 0; dcX(X, '🩺 **Bitunix 帳戶恢復連線**'); }
  }
  // 每天早上 9 點（台北）跟擁有者回報一次：沒收到這則，就代表伺服器可能掛了
  const tp = new Date(now + TZ), day = tp.toISOString().slice(0, 10);
  if (tp.getUTCHours() >= 9 && ST.hb !== day) {
    ST.hb = day; dirty = true;
    const XS = allX(), on = XS.filter(X => X.A.lt.on).length, open = XS.reduce((a, X) => a + ltOpenTrades(X).length, 0), mem = process.memoryUsage().rss / 1048576;
    dcX(OX, `🩺 **伺服器正常**（每天早上 9 點回報）\n版本 ${VER}・已連續運作 ${durTxt(now - BOOT)}・記憶體 ${mem.toFixed(0)}MB\n帳號 ${ST.users.length} 個（自動交易運作中 ${on} 個）・自動單持倉 ${open} 筆・最後成功掃描 ${tw(SCAN.okAt || BOOT)}\n-# 哪天早上沒收到這則，請檢查伺服器`);
  }
}
setInterval(healthTick, 60000);

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
/* ---------------- 📧 寄信（Gmail SMTP，用「應用程式密碼」）：忘記密碼、擁有者登入驗證碼、轉讓擁有者驗證碼 ----------------
   設定放在 /opt/quant/.env：SMTP_USER=寄件的 Gmail、SMTP_PASS=16 碼應用程式密碼（不用另外裝套件） */
const tlsM = require('tls'), netM = require('net');
const MAIL = { host: process.env.SMTP_HOST || 'smtp.gmail.com', port: +process.env.SMTP_PORT || 465, user: process.env.SMTP_USER || '', pass: String(process.env.SMTP_PASS || '').replace(/\s+/g, ''), secure: process.env.SMTP_SECURE !== '0', name: process.env.MAIL_NAME || '無量空處' };
const mailOn = () => !!(MAIL.user && MAIL.pass);
const SITE = (process.env.SITE_URL || 'https://moocow0216-lab.github.io/trace-back/').replace(/\/?$/, '/');
const b64 = x => Buffer.from(String(x), 'utf8').toString('base64');
const maskMail = e => String(e || '').replace(/^([^@]{1,2})[^@]*(@.*)$/, '$1***$2');   // ab***@gmail.com
function sendMail(to, subject, text) {
  return new Promise((resolve, reject) => {
    if (!mailOn()) return reject(new Error('伺服器還沒設定寄信'));
    if (!/^[^\s<>@]+@[^\s<>@]+$/.test(to)) return reject(new Error('收件信箱格式不對'));
    const body = b64(text).replace(/.{76}/g, '$&\r\n');
    const msg = [`From: =?UTF-8?B?${b64(MAIL.name)}?= <${MAIL.user}>`, `To: <${to}>`, `Subject: =?UTF-8?B?${b64(subject)}?=`, `Date: ${new Date().toUTCString()}`,
      `Message-ID: <${crypto.randomBytes(12).toString('hex')}@quant>`, 'MIME-Version: 1.0', 'Content-Type: text/plain; charset=UTF-8', 'Content-Transfer-Encoding: base64', '', body].join('\r\n');
    // SMTP 對話：等到預期的回應碼才送下一句
    const steps = [[220, () => 'EHLO quant-server'], [250, () => 'AUTH LOGIN'], [334, () => b64(MAIL.user)], [334, () => b64(MAIL.pass)], [235, () => `MAIL FROM:<${MAIL.user}>`],
      [250, () => `RCPT TO:<${to}>`], [250, () => 'DATA'], [354, () => msg + '\r\n.'], [250, () => 'QUIT'], [221, null]];
    const sock = MAIL.secure ? tlsM.connect({ host: MAIL.host, port: MAIL.port, servername: MAIL.host }) : netM.connect({ host: MAIL.host, port: MAIL.port });
    let buf = '', i = 0, done = false;
    const end = (e) => { if (done) return; done = true; try { sock.destroy(); } catch (x) {} e ? reject(e) : resolve(true); };
    sock.setTimeout(20000, () => end(new Error('寄信逾時')));
    sock.on('error', e => end(e));
    sock.on('close', () => end(i >= 9 ? null : new Error('寄信伺服器中斷連線')));
    sock.on('data', d => {
      buf += d.toString('utf8');
      const lines = buf.split(/\r?\n/); buf = lines.pop();
      for (const ln of lines) {
        if (!/^\d{3}( |$)/.test(ln)) continue;        // 多行回應（250-xxx）等最後一行
        const code = +ln.slice(0, 3), [want, next] = steps[i] || [];
        if (code !== want) return end(new Error(code === 535 ? 'Gmail 帳號或應用程式密碼不對（535）' : `寄信失敗：${ln.slice(0, 120)}`));
        i++;
        if (i === 9) return end(null);                   // DATA 送出後回 250 就算寄成功（不用等 QUIT）
        sock.write(next() + '\r\n');
      }
    });
  });
}
// 寄信次數限制：同一個帳號每小時 3 封、同一個 IP 每小時 10 封
const MAILRL = new Map();
function mailAllow(key, max) { const now = Date.now(), a = (MAILRL.get(key) || []).filter(t => now - t < HOUR); if (a.length >= max) return false; a.push(now); MAILRL.set(key, a); return true; }
// 一次性憑證：忘記密碼連結（30 分鐘）、6 位數驗證碼（10 分鐘，最多試 5 次）
const RESETS = new Map(), CODES = new Map();
const newCode = () => String(crypto.randomInt(0, 1e6)).padStart(6, '0');
function codeCheck(pre, code, kind) {
  const c = CODES.get(String(pre || ''));
  if (!c || c.kind !== kind || c.exp < Date.now()) { CODES.delete(String(pre || '')); return { err: '驗證碼已過期，請重新來一次' }; }
  if (++c.tries > 5) { CODES.delete(String(pre)); return { err: '錯太多次了，請重新來一次' }; }
  if (!crypto.timingSafeEqual(Buffer.from(sha(String(code || '').trim())), Buffer.from(c.h))) return { err: `驗證碼不對（還可以試 ${5 - c.tries} 次）` };
  CODES.delete(String(pre)); return { c };
}
async function mailCode(usr, kind, extra = {}) {      // 寄 6 位數驗證碼到綁定的信箱，回傳 pre（用來配對驗證碼）
  const code = newCode(), pre = crypto.randomBytes(16).toString('hex');
  for (const [k, v] of CODES) if (v.exp < Date.now()) CODES.delete(k);
  CODES.set(pre, { uid: usr.uid, kind, h: sha(code), exp: Date.now() + 10 * 60000, tries: 0, ...extra });
  const what = kind === 'login' ? '擁有者登入' : `把擁有者轉讓給 ${extra.to}`;
  await sendMail(usr.bind.email, `無量空處：${what}的驗證碼 ${code}`, `你的驗證碼是：${code}\n\n用途：帳號 ${usr.uid} ${what}\n10 分鐘內有效，只能用一次。\n\n如果不是你本人在操作，代表你的密碼可能外洩了，請盡快改密碼。`);
  return pre;
}

/* ---------------- 帳號綁定：Google 信箱＋手機號碼，綁好才能用網站 ----------------
   有設定 Google 用戶端 ID：用 Google 登入按鈕驗證信箱（伺服器向 Google 確認）；還沒設定：先手動輸入 Gmail。
   手機號碼目前只檢查格式（簡訊驗證碼要接付費簡訊服務）。同一個信箱、同一支手機只能綁一個帳號。 */
const GOOGLE_INFO = process.env.GOOGLE_TOKENINFO || 'https://oauth2.googleapis.com/tokeninfo';
const gClient = () => '';                              // Google 用戶端 ID 已經拿掉：綁定手動輸入 Gmail，擁有者登入、轉讓都改用信箱驗證碼
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
const PRE = new Map();                                 // 擁有者登入：密碼過了、等 Google 驗證的暫時憑證（5 分鐘）
const pick = (o, keys) => Object.fromEntries(keys.filter(k => o[k] !== undefined).map(k => [k, o[k]]));
http.createServer(async (req, res) => {
  try {
    if (req.method === 'OPTIONS') return send(res, 204, {});
    const u = new URL(req.url, 'http://x');
    if (req.method === 'GET' && u.pathname === '/api/ping') return send(res, 200, { ok: true, time: Date.now() });
    if (req.method === 'GET' && u.pathname === '/api/health') {   // 給外部監控用：掃描 10 分鐘沒成功就回 503（不需要登入，也不透露任何帳號資料）
      const age = Date.now() - (SCAN.okAt || BOOT);
      return send(res, age < 10 * 60000 ? 200 : 503, { ok: age < 10 * 60000, scanAgeS: Math.round(age / 1000), up: Math.round((Date.now() - BOOT) / 1000) });
    }
    if (req.method === 'GET' && u.pathname === '/api/auth') return send(res, 200, { needSetup: !ST.users.length });
    if (req.method === 'POST' && ['/api/login', '/api/setup', '/api/logout', '/api/login/google', '/api/login/code', '/api/forgot', '/api/reset'].includes(u.pathname)) {
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
      if (u.pathname === '/api/forgot') {               // 🔑 忘記密碼：UID＋綁定的信箱都對，才寄重設連結（不管對不對都回一樣的話，別人猜不出帳號）
        if (!mailOn()) return send(res, 400, { error: '伺服器還沒設定寄信功能，請聯絡擁有者幫你改密碼' });
        const OK = { ok: true, msg: '如果 UID 和信箱正確，重設密碼的信已經寄出了。請到信箱收信（也看一下垃圾郵件），連結 30 分鐘內有效。' };
        if (!mailAllow('ip:' + ip, 10)) return send(res, 429, { error: '這台裝置寄太多次了，請一小時後再試' });
        const usr = ST.users.find(x => x.uid === String(b.uid || '').trim()), email = String(b.email || '').trim().toLowerCase();
        if (!usr || !usr.bind || usr.bind.email !== email) { failed(ip); return send(res, 200, OK); }
        if (!mailAllow('uid:' + usr.uid, 3)) return send(res, 200, OK);
        const tok = crypto.randomBytes(24).toString('hex');
        for (const [k, v] of RESETS) if (v.exp < Date.now() || v.uid === usr.uid) RESETS.delete(k);   // 同一個帳號只留最新的連結
        RESETS.set(sha(tok), { uid: usr.uid, exp: Date.now() + 30 * 60000 });
        sendMail(email, '無量空處：重設密碼', `你好，\n\n有人（希望是你）要求重設帳號 ${usr.uid} 的密碼。請在 30 分鐘內打開下面的連結設定新密碼：\n\n${SITE}?reset=${tok}\n\n連結只能用一次。重設後，這個帳號在所有裝置的登入都會被登出。\n\n如果不是你本人要求的，忽略這封信就好，你的密碼不會被改。`)
          .then(() => log('寄出重設密碼信', usr.uid, maskMail(email)))
          .catch(e => { log('重設密碼信寄不出去', usr.uid, e.message); dcX(ctx(ownerUid()), `📧 **寄信失敗**（${usr.uid} 的重設密碼信）：${mdEsc(e.message)}\n請檢查 /opt/quant/.env 的 SMTP_USER、SMTP_PASS`); });
        return send(res, 200, OK);
      }
      if (u.pathname === '/api/reset') {                // 🔑 用信裡的連結設定新密碼
        const R = RESETS.get(sha(String(b.token || '')));
        if (!R || R.exp < Date.now()) { failed(ip); return send(res, 400, { error: '連結已經失效（超過 30 分鐘或已經用過），請重新按「忘記密碼」' }); }
        if (!validPw(b.password)) return send(res, 400, { error: '新密碼至少 8 個字' });
        const usr = ST.users.find(x => x.uid === R.uid); if (!usr) return send(res, 400, { error: '找不到這個帳號' });
        RESETS.delete(sha(String(b.token)));
        Object.assign(usr, hashPw(b.password)); ST.sessions = ST.sessions.filter(x => x.uid !== usr.uid); dirty = true;
        log('用信箱重設密碼', usr.uid); dcX(ctx(usr.uid), '🔑 **你的密碼已經用信箱連結重設**，所有裝置都被登出了。如果不是你本人，請馬上聯絡擁有者。');
        return send(res, 200, { ok: true, uid: usr.uid });
      }
      if (u.pathname === '/api/login/code') {           // 擁有者第二步：輸入寄到信箱的 6 位數驗證碼
        const r = codeCheck(b.pre, b.code, 'login');
        if (r.err) { failed(ip); return send(res, 401, { error: r.err }); }
        const usr = ST.users.find(x => x.uid === r.c.uid); if (!usr) return send(res, 401, { error: '找不到帳號' });
        FAILS.delete(ip); log('擁有者登入（信箱驗證碼）', usr.uid);
        return send(res, 200, { token: newSession(usr), uid: usr.uid, role: usr.role });
      }
      if (u.pathname === '/api/login/google') {         // 擁有者第二步：Google 驗證綁定的信箱
        const P = PRE.get(String(b.pre || '')); PRE.delete(String(b.pre || ''));
        const usr = P && P.exp > Date.now() ? ST.users.find(x => x.uid === P.uid) : null;
        if (!usr) return send(res, 401, { error: '驗證逾時，請重新輸入密碼登入' });
        const email = b.credential ? await googleEmail(String(b.credential), gClient()) : '';
        if (!email || !usr.bind || email !== usr.bind.email) { failed(ip); log('擁有者 Google 驗證失敗', usr.uid, email); return send(res, 401, { error: email ? `要用綁定的信箱登入，你選的是 ${email}` : 'Google 驗證失敗' }); }
        FAILS.delete(ip); log('擁有者登入（Google 驗證）', usr.uid);
        return send(res, 200, { token: newSession(usr), uid: usr.uid, role: usr.role });
      }
      const usr = ST.users.find(x => x.uid === String(b.uid || ''));
      if (!usr || !validPw(b.password) || !pwOk(usr, b.password)) { failed(ip); return send(res, 401, { error: 'UID 或密碼不對' }); }
      FAILS.delete(ip);
      if (usr.uid === ownerUid() && gClient() && usr.bind && usr.bind.email) {   // 👑 擁有者：密碼對了還要第二層 Google 驗證
        const pre = crypto.randomBytes(16).toString('hex'); PRE.set(pre, { uid: usr.uid, exp: Date.now() + 5 * 60000 });
        for (const [k, v] of PRE) if (v.exp < Date.now()) PRE.delete(k);
        return send(res, 200, { need2fa: true, pre, google: gClient(), email: maskMail(usr.bind.email) });
      }
      if (usr.uid === ownerUid() && mailOn() && usr.bind && usr.bind.email) {   // 👑 擁有者：密碼對了，再寄驗證碼到綁定的信箱
        try { const pre = await mailCode(usr, 'login'); return send(res, 200, { need2fa: true, via: 'mail', pre, email: maskMail(usr.bind.email) }); }
        catch (e) { log('擁有者驗證碼寄不出去，這次只用密碼登入', e.message); dcX(ctx(usr.uid), `📧 **驗證碼寄不出去**（${mdEsc(e.message)}），這次擁有者登入只用了密碼。請檢查寄信設定。`); }
      }
      return send(res, 200, { token: newSession(usr), uid: usr.uid, role: usr.role });
    }
    const me = who(req), admin = keyOk(req) || (me && me.role === 'admin'), owner = keyOk(req) || (me && me.uid === ownerUid());   // 擁有者 ⊃ 灰色管理員 ⊃ 一般
    if (u.pathname.startsWith('/api/') && !me && !keyOk(req)) return send(res, 401, { error: '請先登入', needLogin: true, needSetup: !ST.users.length });
    if (me && needBind(me) && u.pathname !== '/api/me' && u.pathname !== '/api/bind') return send(res, 403, { error: '請先綁定 Google 信箱和手機號碼', needBind: true });
    const X = ctx(me ? me.uid : ownerUid());          // 這次請求的「自己」：每個帳號只看得到、改得到自己的 Bitunix／自動交易／Discord（用管理金鑰登入＝擁有者）
    if (req.method === 'GET' && u.pathname === '/api/me') return send(res, 200, { uid: me ? me.uid : '管理金鑰', role: admin ? 'admin' : 'viewer', owner: !!owner, needBind: needBind(me), bind: bindOut(me), google: gClient() });
    if (req.method === 'GET' && u.pathname === '/api/users') {
      if (!admin) return send(res, 403, { error: '只有管理員可以看' });
      return send(res, 200, { users: ST.users.map(x => { const A = ST.accts[x.uid]; return { uid: x.uid, role: x.role, created: x.created, last: x.last || 0, sessions: ST.sessions.filter(s => s.uid === x.uid && s.exp > Date.now()).length,
        api: !!(A && A.bx.key), auto: !!(A && A.lt.on), sp: !!(A && A.lt.sp), tool: toolOkUid(x.uid), open: A ? A.ltTrades.filter(t => t.status === 'open').length : 0, owner: x.uid === ownerUid(), bind: bindOut(x), note: x.note || '', noteAt: x.noteAt || 0, noteBy: x.noteBy || '' }; }), google: gClient(), googleEnv: !!process.env.GOOGLE_CLIENT_ID, mail: { on: mailOn(), from: maskMail(MAIL.user) } });   // 只給管理員看「有沒有設」，不會給金鑰
    }
    if (req.method === 'GET' && u.pathname === '/api/users/view') {      // 管理員查看某個帳號的狀況：只能看，沒有任何能動倉位或資金的東西，也不會給金鑰
      if (!admin) return send(res, 403, { error: '只有管理員可以看' });
      const usr = ST.users.find(x => x.uid === String(u.searchParams.get('uid') || ''));
      if (!usr) return send(res, 404, { error: '找不到這個帳號' });
      const out = { uid: usr.uid, role: usr.role, owner: usr.uid === ownerUid(), bind: bindOut(usr), last: usr.last || 0, created: usr.created || 0, note: usr.note || '' };
      if (!ST.accts[usr.uid]) return send(res, 200, { ...out, api: false, empty: true });
      const V = ctx(usr.uid), L = V.A.lt, TR = V.A.ltTrades.filter(t => inStat(t, L.startAt));
      const done = TR.filter(t => t.status === 'closed'), net = done.reduce((a, t) => a + ltNet(t), 0);
      return send(res, 200, {
        ...out, api: hasKey(V), err: V.BX.err, at: V.BX.at, acctEq: bxEquity(V), bot: ltBotEq(V), dayPnl: V.LT.dayPnl || 0, msg: V.LT.msg, hook: !!V.A.notify.webhook,
        lt: { on: L.on, tp: L.tp || ST.trade.tp, budget: L.budget, margin: L.margin, lev: L.lev, dayLoss: L.dayLoss, sl: L.sl, step: L.step, hold: L.hold, startCap: L.startCap, startAt: L.startAt },
        pos: V.BX.pos.map(p => ({ id: p.id, sym: p.sym, dir: p.dir, lev: p.lev, qty: p.qty, entry: p.entry, px: PX.map[p.sym] || null, upnl: p.upnl, margin: p.margin, liq: p.liq, ctime: p.ctime, bot: !!V.A.ltTrades.find(t => t.status === 'open' && t.positionId === p.id) })),
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
        time: Date.now(), ver: VER, cv: CV, bv: BV * 2 + (X.A.lt.btcF ? 1 : 0), set: ST.set, trade: ST.trade, canWrite: !!ADMIN_KEY,
        scan: { ...SCAN, pause: RL.pause }, bt: { at: ST.bt.at, coins: ST.bt.coins, n: btActive().length, cmp: btCompare() }, btp: BTP, bstat: { busy: BSTAT.busy, msg: BSTAT.msg, v: BSTAT.v || ST.bstat || null },
        notify: { enabled: X.A.notify.enabled, entry: X.A.notify.entry, exit: X.A.notify.exit, hasHook: !!X.A.notify.webhook, name: X.A.notify.name, last: dcStat(X.A.notify.webhook) },
        me: { uid: me ? me.uid : '管理金鑰', admin: !!admin, owner: !!owner },
        eq: ST.eq, rep: { ...ST.rep, busy: REP.busy, msg: REP.msg }, rv: RV,
        bx: { set: hasKey(X), notify: X.A.bx.notify, liq: X.A.bx.liq, liqPct: X.A.bx.liqPct, at: X.BX.at, err: X.BX.err, acct: X.BX.acct,
          pos: X.BX.pos.map(p => ({ ...p, px: PX.map[p.sym] || null, tp: ((X.BX.tpsl && X.BX.tpsl.get(p.id)) || {}).tp || 0, sl: ((X.BX.tpsl && X.BX.tpsl.get(p.id)) || {}).sl || 0, sig: !!ST.cards.find(c => c.sym === p.sym && c.dir === p.dir && c.et && isLive(c)), bot: !!X.A.ltTrades.find(t => t.status === 'open' && t.positionId === p.id) })) },
        eco: { list: ECO.list.filter(e => e.t > Date.now() - 7 * 24 * HOUR), at: ECO.at, err: ECO.err, hasNext: !!ECO.hasNext, today: ecoToday().map(e => ({ t: e.t, zh: e.zh || e.title })) },
        lt: { cfg: X.A.lt, bud: ltBudEq(X), low: (() => { const C = X.A.lt, a = bxEquity(X), n = C.budget > 0 ? ltBotEq(X).eq : 0, p = C.spBudget > 0 && toolOkUid(X.uid) ? ltSpEq(X).eq : 0; return a > 0 && (C.budget > 0 || C.spBudget > 0) && n + p > a + 0.01 ? { acct: a, n, sp: p } : null; })(), pause: X.LT.pause || null, toolOk: toolOkUid(X.uid), spBot: ltSpEq(X), spDay: X.LT.spDayPnl || 0, msg: X.LT.msg, dayPnl: X.LT.dayPnl || 0, v: X.v, bot: ltBotEq(X), acctEq: bxEquity(X) },
        aws: !(X.uid === ownerUid()) ? null : { on: ST.aws.on, created: ST.aws.created, auto: ST.aws.auto, price: ST.aws.price, detected: awsDetect(), ...awsNext() }
      };
      if (+u.searchParams.get('cv') !== CV) out.cards = ST.cards;
      if (+u.searchParams.get('bv') !== BV * 2 + (X.A.lt.btcF ? 1 : 0)) out.trades = ST.bt.trades.filter(t => (X.A.lt.btcF ? t.c1 : t.c0) !== false);   // 自己開著 BTC 過濾就看有過濾的那條
      if (+u.searchParams.get('rv') !== RV) out.reports = ST.reports;
      if (+u.searchParams.get('lv') !== X.v) out.ltTrades = X.A.ltTrades.map(({ closing, ...t }) => t);
      return send(res, 200, out);
    }
    if (req.method === 'POST' && u.pathname.startsWith('/api/')) {
      // 個人設定：每個帳號都能改「自己的」；其他（掃描條件、浮盈規則、回測、帳號管理、AWS）只有管理員能改
      // 個人（每個帳號）：自己的 API、Discord、交易設定、平倉；管理員（灰色）：帳號管理；其他全站設定只有擁有者能改
      const PERSONAL = ['/api/bind', '/api/bitunix', '/api/lt/config', '/api/lt/testOpen', '/api/lt/close', '/api/lt/closeAll', '/api/lt/adopt', '/api/notify', '/api/notify/test', '/api/me/password', '/api/tool', '/api/lt/withdraw'];
      const ADMIN = ['/api/users', '/api/users/delete', '/api/users/kick', '/api/check'];
      if (ADMIN.includes(u.pathname) && !admin) return send(res, 403, { error: '這個功能只有管理員可以用' });
      if (!PERSONAL.includes(u.pathname) && !ADMIN.includes(u.pathname) && !owner) return send(res, 403, { error: '這個設定只有擁有者可以改' });
      const b = await readBody(req);
      if (u.pathname === '/api/users') {               // 後台：新增帳號／改密碼／改權限
        if (!validUid(b.uid)) return send(res, 400, { error: 'UID 應該是 4～20 位數字' });
        let usr = ST.users.find(x => x.uid === String(b.uid));
        const isNew = !usr, self = !!(me && usr && usr.uid === me.uid);
        if (usr && usr.uid === ownerUid() && !owner) return send(res, 403, { error: '不能修改擁有者帳號' });
        if (!isNew && b.password && !self && !owner) return send(res, 403, { error: '只有擁有者可以改別人的密碼（灰色管理員只能幫新帳號設定密碼）' });
        if (b.role && usr && usr.uid === ownerUid() && b.role !== 'admin') return send(res, 400, { error: '擁有者帳號一定是管理員；要換擁有者請用「轉讓擁有者」' });
        if (!usr) { if (!validPw(b.password)) return send(res, 400, { error: '新帳號要設定密碼，至少 8 個字' }); usr = { uid: String(b.uid), role: 'viewer', created: Date.now() }; ST.users.push(usr); }
        if (b.password) { if (!validPw(b.password)) return send(res, 400, { error: '密碼至少 8 個字' }); Object.assign(usr, hashPw(b.password)); ST.sessions = ST.sessions.filter(s => s.uid !== usr.uid || (me && s.uid === me.uid)); }
        if (b.unbind) { delete usr.bind; ST.sessions = ST.sessions.filter(s => s.uid !== usr.uid); }   // 重設綁定：對方下次登入要重新綁定
        if (b.role === 'admin' || b.role === 'viewer') {
          if (b.role === 'viewer' && usr.uid === ownerUid()) return send(res, 400, { error: '擁有者帳號一定是管理員' });
          if (b.role === 'viewer' && usr.role === 'admin' && ST.users.filter(x => x.role === 'admin').length <= 1) return send(res, 400, { error: '至少要留一個管理員' });
          usr.role = b.role;
        }
        if (typeof b.note === 'string') {                // 📝 備註：只有管理員看得到；擁有者的備註只有擁有者能改（上面已經擋了）
          usr.note = b.note.normalize('NFC').replace(/[\u0000-\u001f]/g, ' ').trim().slice(0, 200);
          usr.noteAt = Date.now(); usr.noteBy = me ? me.uid : '管理金鑰';
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
          if (!/^[a-z0-9.+_-]{1,64}@(gmail|googlemail)\.com$/.test(email)) return send(res, 400, { error: '請輸入 Google 信箱（@gmail.com）' });
        }
        const dup = ST.users.find(x => x !== me && x.bind && (x.bind.email === email || x.bind.phone === phone));
        if (dup) return send(res, 400, { error: dup.bind.email === email ? '這個 Google 信箱已經綁定別的帳號了' : '這支手機號碼已經綁定別的帳號了' });
        me.bind = { email, phone, google, at: Date.now() }; dirty = true;
        log('帳號綁定', me.uid, email, google ? '（Google 驗證）' : '（手動輸入）');
        return send(res, 200, { ok: true, bind: bindOut(me) });
      }
      if (u.pathname === '/api/btcstat') {             // 📈 擁有者：統計 BTC 急漲急跌（背景跑，大約 1～2 分鐘）
        if (BSTAT.busy) return send(res, 400, { error: '還在統計中' });
        btcStat(Math.min(180, Math.max(7, +b.days || 90)));
        return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/users/lt') {            // 👑 擁有者在帳號管理後台：幫某個帳號開始／暫停自動交易
        const usr = ST.users.find(x => x.uid === String(b.uid || '')); if (!usr) return send(res, 404, { error: '找不到這個帳號' });
        if (typeof b.on !== 'boolean') return send(res, 400, { error: '要指定開始或暫停' });
        const XA = ctx(usr.uid);
        if (b.on && !hasKey(XA)) return send(res, 400, { error: `${usr.uid} 還沒設定 Bitunix API，不能開始交易` });
        XA.A.lt.allOff = false;
        if (XA.A.lt.on !== b.on) { XA.A.lt.on = b.on; if (!b.on) XA.LT.pause = { t: Date.now(), why: '擁有者幫你暫停' }; touchLT(XA); dcX(XA, b.on ? '▶️ **自動交易已開始**（擁有者幫你開啟）' : '⏸ **自動交易已暫停**（擁有者幫你暫停，已開的單照常管理）'); log(b.on ? '擁有者幫帳號開始交易' : '擁有者幫帳號暫停交易', usr.uid); }
        return send(res, 200, { ok: true, on: XA.A.lt.on });
      }
      if (u.pathname === '/api/lt/all') {             // 👑 擁有者：一鍵全部暫停／開始。「全部開始」只恢復被「全部暫停」停掉的帳號，在那之前就暫停的維持暫停
        if (typeof b.on !== 'boolean') return send(res, 400, { error: '要指定開始或暫停' });
        const sp = !!b.sp, ON = sp ? 'sp' : 'on', MARK = sp ? 'spAllOff' : 'allOff', NM = sp ? '🗡 特級交易' : '自動交易';
        let n = 0, skip = 0, keep = 0;
        for (const XA of allX()) {
          const L = XA.A.lt;
          if (!b.on) {                                   // 全部暫停：只停有在跑的，並記下「是被擁有者一鍵暫停的」
            if (!L[ON]) continue;
            L[ON] = false; L[MARK] = true; XA.LT.pause = { t: Date.now(), why: `擁有者一鍵全部暫停${sp ? '特級交易' : ''}` }; touchLT(XA); n++;
            dcX(XA, `⏸ **${NM}已暫停**（擁有者一鍵暫停，已開的單照常管理）`);
            continue;
          }
          if (L[ON]) continue;
          if (!hasKey(XA) || (sp && !toolOkUid(XA.uid))) { if (L[MARK]) { L[MARK] = false; touchLT(XA); } skip++; continue; }   // 沒有 API（或沒有特級權限）：跳過
          if (!L[MARK]) { keep++; continue; }            // 在一鍵暫停之前就已經暫停：維持暫停
          L[ON] = true; L[MARK] = false; touchLT(XA); n++;
          dcX(XA, `▶️ **${NM}已恢復**（擁有者一鍵恢復）`);
        }
        log(b.on ? `一鍵恢復${sp ? '特級交易' : ''}` : `一鍵全部暫停${sp ? '特級交易' : ''}`, n, '個帳號', b.on ? `維持暫停 ${keep}` : '');
        return send(res, 200, { ok: true, n, skip, keep });
      }
      if (u.pathname === '/api/owner/transfer') {      // 👑 轉讓擁有者：一定要用 Google 驗證「擁有者綁定的信箱」才能轉
        const cid = gClient(), O = ST.users.find(x => x.uid === ownerUid());
        if (!me || !O || me.uid !== O.uid) return send(res, 403, { error: '只有擁有者本人登入才能轉讓' });
        const to = ST.users.find(x => x.uid === String(b.uid || ''));
        if (!to) return send(res, 404, { error: '找不到要轉讓的帳號' });
        if (to.uid === O.uid) return send(res, 400, { error: '已經是擁有者了' });
        if (needBind(to)) return send(res, 400, { error: '對方還沒綁定 Google 信箱和手機，請他先登入完成綁定' });
        if (!O.bind || !O.bind.email) return send(res, 400, { error: '你自己還沒綁定信箱' });
        let email = '';
        if (cid && b.credential) {                      // 有 Google 用戶端 ID：用 Google 按鈕驗證
          email = await googleEmail(String(b.credential), cid);
          if (!email) return send(res, 400, { error: 'Google 驗證失敗，請重新按 Google 按鈕' });
          if (email !== O.bind.email) return send(res, 400, { error: `要用擁有者綁定的信箱（${O.bind.email}）驗證，你剛剛選的是 ${email}` });
        } else {                                        // 沒有：寄驗證碼到擁有者綁定的信箱
          if (!mailOn()) return send(res, 400, { error: '要先設定寄信功能（或 Google 用戶端 ID），轉讓一定要驗證你的信箱' });
          if (!b.code) {
            if (!mailAllow('uid:' + O.uid, 3)) return send(res, 429, { error: '寄太多次了，請一小時後再試' });
            try { const pre = await mailCode(O, 'xfer', { to: to.uid }); return send(res, 200, { needCode: true, pre, email: maskMail(O.bind.email) }); }
            catch (e) { return send(res, 500, { error: '驗證碼寄不出去：' + e.message }); }
          }
          const r = codeCheck(b.pre, b.code, 'xfer');
          if (r.err) return send(res, 400, { error: r.err });
          if (r.c.uid !== O.uid || r.c.to !== to.uid) return send(res, 400, { error: '驗證碼跟要轉讓的帳號對不上，請重新來一次' });
          email = O.bind.email;
        }
        ST.owner = to.uid; to.role = 'admin'; dirty = true;      // 原本的擁有者變成灰色管理員
        log('擁有者轉讓', O.uid, '→', to.uid);
        dcX(ctx(O.uid), `👑 **擁有者已轉讓**：${O.uid} → **${to.uid}**（用 ${email} 驗證）。你現在是管理員。`);
        dcX(ctx(to.uid), `👑 **你現在是這台伺服器的擁有者**（由 ${O.uid} 轉讓）。`);
        return send(res, 200, { ok: true, owner: to.uid });
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
      if (u.pathname === '/api/users/kick') {
        if (String(b.uid) === ownerUid() && !owner) return send(res, 403, { error: '不能讓擁有者登出' });
        ST.sessions = ST.sessions.filter(s => s.uid !== String(b.uid)); dirty = true; return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/settings') {
        if (b.set) {
          const was = ST.set.btcF; Object.assign(ST.set, pick(b.set, Object.keys(DEF_SET)));
          ST.set.btcF = ST.set.btcF ? 1 : 0; if (!['24h', 'day', '4h'].includes(ST.set.btcMode)) ST.set.btcMode = '24h';
          ST.set.btcWith = Math.min(5, Math.max(1, Math.round(+ST.set.btcWith) || 2)); ST.set.btcAgainst = Math.min(5, Math.max(1, Math.round(+ST.set.btcAgainst) || 4));
          if (was !== ST.set.btcF) touchBT();
          ST.set.zSum = Math.min(20, Math.max(1, Math.round((+ST.set.zSum || 5) * 10) / 10)); ST.set.zBar = Math.min(20, Math.max(1, Math.round((+ST.set.zBar || 5) * 10) / 10));
        }
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
          Object.assign(C, DEF_BX); X.A.lt.on = false; X.A.lt.sp = false; X.LT.pause = { t: Date.now(), why: '刪除了 Bitunix API' }; BX.pos = []; BX.acct = null; BX.seeded = false; touchLT(X); return send(res, 200, { ok: true });
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
          if (changed) { X.A.lt.on = false; X.A.lt.sp = false; X.LT.pause = { t: Date.now(), why: '換了 Bitunix API 金鑰' }; X.A.lt.startCap = 0; X.A.lt.startAt = Date.now(); X.LT.lev = {}; touchLT(X); }   // 換帳號：先暫停，統計等讀到新帳戶的資金再開始
        }
        for (const k of ['notify', 'liq']) if (typeof b[k] === 'boolean') C[k] = b[k];
        if (+b.liqPct > 0) C.liqPct = +b.liqPct;
        dirty = true; bxPollOne(X).catch(e => log('讀持倉失敗', X.uid, e.message));
        return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/lt/config') {
        const C = X.A.lt;
        if (typeof b.on === 'boolean') {
          if (b.on && !hasKey(X)) return send(res, 400, { error: '請先設定你自己的 Bitunix API 金鑰（要開交易權限）' });
          C.on = b.on; C.allOff = false; if (!b.on) X.LT.pause = { t: Date.now(), why: '你按了暫停' }; dcX(X, b.on ? '▶️ **自動交易已開始**' : '⏸ **自動交易已暫停**（已開的單照常管理）');
        }
        if (typeof b.sp === 'boolean') {                 // 🗡 特級交易：只有特級咒具權限的人能開
          if (b.sp && !toolOkUid(X.uid)) return send(res, 403, { error: '特級交易要先解鎖特級咒具' });
          if (b.sp && !hasKey(X)) return send(res, 400, { error: '請先設定你自己的 Bitunix API 金鑰（要開交易權限）' });
          C.spAllOff = false;
          if (C.sp !== b.sp) { C.sp = b.sp; dcX(X, b.sp ? `🗡 **特級交易已開始**：特級咒具的莊家、CRT、獵殺進場訊號會用你的帳戶真實下單\n每筆 ${C.spMargin}U・${C.spLev}x・浮盈 +${C.spTp}% 開始鎖利、每 ${C.spStep}% 上調・浮虧 −${C.spSl}% 停損・持有 ${Math.round(C.spHold / 24 * 10) / 10} 天${C.spBudget > 0 ? `・投入 ${C.spBudget}U` : ''}${C.spDayLoss > 0 ? `・單日虧損上限 ${C.spDayLoss}U` : ''}` : '⏸ **特級交易已暫停**（已開的單照常管理）'); }
        }
        if (+b.margin > 0) C.margin = +b.margin;
        if (+b.lev >= 1 && +b.lev <= 125) C.lev = Math.round(+b.lev);
        if (+b.maxOpen >= 0) C.maxOpen = Math.round(+b.maxOpen);
        if (+b.dayLoss >= 0) C.dayLoss = +b.dayLoss;
        if (b.budget !== undefined && +b.budget >= 0) {
          const e = bxEquity(X);
          if (+b.budget > 0 && !hasKey(X)) return send(res, 400, { error: '請先設定 Bitunix API，才知道合約帳戶有多少資金' });
          if (+b.budget > 0 && !(e > 0)) return send(res, 400, { error: '還沒讀到合約帳戶的資金，請等 10 秒再試' });
          if (+b.budget > e + 1e-9) return send(res, 400, { error: `資金不足：合約帳戶目前只有 ${e.toFixed(2)}U，投入資金不能設 ${+b.budget}U` });
          if (+b.budget > 0 && +b.budget !== C.budget) { const M = ltBudMax(X, false); if (M && +b.budget > M.max + 0.009) return send(res, 400, { error: `資金不足：合約帳戶 ${M.acct.toFixed(2)}U，🗡 特級交易目前用了 ${M.other.toFixed(2)}U，一般交易的投入資金最多只能設 ${Math.max(0, M.max).toFixed(2)}U` }); }
          C.budget = +b.budget;
          if (C.budget > 0) { C.startCap = C.budget; C.startAt = C.startAt || Date.now(); C.wd = 0; }   // 重新投入：收回的紀錄清掉   // 投入資金＝起始本金；過去的盈虧照算（100U 虧到 98U，改成 50U 就是 48U）
        }
        if (b.sp_set) {                                 // 🗡 特級交易自己的設定（只有有權限的人能改）
          if (!toolOkUid(X.uid)) return send(res, 403, { error: '特級交易要先解鎖特級咒具' });
          const v = b.sp_set, num0 = k => (v[k] === undefined || v[k] === '' ? undefined : +v[k]);
          const lev = num0('lev'), m = num0('margin'), bud = num0('budget'), dl = num0('dayLoss'), tp = num0('tp'), st = num0('step'), sl = num0('sl'), hd = num0('hold');
          if (lev !== undefined && !(lev >= 1 && lev <= 125)) return send(res, 400, { error: '特級交易的槓桿要在 1～125 倍之間' });
          if (m !== undefined && !(m > 0)) return send(res, 400, { error: '特級交易的每筆保證金要大於 0' });
          if (dl !== undefined && !(dl >= 0)) return send(res, 400, { error: '特級交易的單日虧損上限不能是負的' });
          if (tp !== undefined && !(tp >= 10 && tp <= 1000)) return send(res, 400, { error: '特級交易的開始鎖利要在 10～1000 % 之間' });
          if (st !== undefined && !(st >= 0 && st <= 1000)) return send(res, 400, { error: '特級交易的鎖利線上調要在 0～1000 % 之間' });
          if (sl !== undefined && !(sl >= 10 && sl <= 1000)) return send(res, 400, { error: '特級交易的停損要在 10～1000 % 之間' });
          if (hd !== undefined && !(hd >= 1 && hd <= 720)) return send(res, 400, { error: '特級交易的持有時間要在 1 小時～30 天之間' });
          if (bud !== undefined) {
            const e = bxEquity(X);
            if (!(bud >= 0)) return send(res, 400, { error: '特級交易的投入資金不能是負的' });
            if (bud > 0 && !(e > 0)) return send(res, 400, { error: '還沒讀到合約帳戶的資金，請等 10 秒再試' });
            if (bud > e + 1e-9) return send(res, 400, { error: `資金不足：合約帳戶目前只有 ${e.toFixed(2)}U，特級交易的投入資金不能設 ${bud}U` });
            if (bud > 0 && bud !== C.spBudget) { const M = ltBudMax(X, true); if (M && bud > M.max + 0.009) return send(res, 400, { error: `資金不足：合約帳戶 ${M.acct.toFixed(2)}U，一般交易目前用了 ${M.other.toFixed(2)}U，特級交易的投入資金最多只能設 ${Math.max(0, M.max).toFixed(2)}U` }); }
            if (bud !== C.spBudget) { C.spBudget = bud; C.spWd = 0; }   // 🗡 投入資金＝特級的起始本金，過去的盈虧照算；重新投入時收回的紀錄清掉
          }
          const slChanged = sl !== undefined && sl !== C.spSl;
          if (lev !== undefined) C.spLev = Math.round(lev); if (m !== undefined) C.spMargin = m; if (dl !== undefined) C.spDayLoss = dl;
          if (tp !== undefined) C.spTp = tp; if (st !== undefined) C.spStep = st; if (sl !== undefined) C.spSl = sl; if (hd !== undefined) C.spHold = hd;
          if (slChanged) setTimeout(() => ltSyncSL(X, 'sp').catch(e => log('改特級止損失敗', X.uid, e.message)), 500);
        }
        if (typeof b.btcF === 'boolean') {               // 🧭 自己要不要用 BTC 方向過濾
          C.btcF = b.btcF ? 1 : 0;
          if (X.uid === ownerUid() && ST.set.btcF !== C.btcF) { ST.set.btcF = C.btcF; touchBT(); }   // 擁有者的選擇也用在共用的結算報告
          dcX(X, b.btcF ? '🧭 **BTC 方向過濾已開啟**：順勢、逆勢的異常項數不夠就不下單' : '🧭 **BTC 方向過濾已關閉**：所有訊號都會下單');
        }
        let rule = false;                                // 個人的出場規則
        if (b.sl !== undefined) { const v = +b.sl; if (!(v >= 10 && v <= 1000)) return send(res, 400, { error: '浮虧 % 要在 10～1000 之間' }); if (C.sl !== v) setTimeout(() => ltSyncSL(X, 'n').catch(e => log('改止損失敗', X.uid, e.message)), 500); C.sl = v; rule = true; }
        if (b.tp !== undefined) { const v = +b.tp; if (!(v >= 10 && v <= 1000)) return send(res, 400, { error: '開始鎖利要在 10～1000 % 之間' }); C.tp = v; rule = true; }   // 浮盈達到幾 % 開始鎖利
        if (b.step !== undefined) { const v = +b.step; if (!(v >= 0 && v <= 1000)) return send(res, 400, { error: '鎖利線上調要在 0～1000 之間' }); C.step = v; rule = true; }
        if (b.hold !== undefined) { const v = +b.hold; if (!(v >= 1 && v <= 720)) return send(res, 400, { error: '持有時間要在 1 小時～30 天之間' }); C.hold = v; rule = true; }
        if (+b.lev >= 1 && +b.lev <= 125) rule = true;
        if (rule && X.uid === ownerUid()) {             // 擁有者的設定也拿來當「訊號模擬、回測、Discord 訊號通知」的共用規則
          Object.assign(ST.trade, { tp: C.tp || ST.trade.tp, sl: C.sl, step: C.step, hold: C.hold, lev: C.lev });
          CACHE.clear(); markSettledNotified(); touchCards();
        }
        if (b.reset) { const e = bxEquity(X); C.startAt = Date.now(); C.startCap = C.budget > 0 ? C.budget : e > 0 ? Math.round(e * 100) / 100 : 0; }   // 有設投入資金就用它，沒有就用目前帳戶權益
        touchLT(X); return send(res, 200, { ok: true, cfg: C });
      }
      if (u.pathname === '/api/lt/testOpen' && process.env.LT_TEST === '1') { await ltFlipOpen(X, { id: 'test', sym: b.sym, dir: b.dir || 1, abN: b.abN || 2, last: 1, btcPass: b.btcPass, btcNeed: 4, src: b.src, ttype: b.ttype, tpair: b.tpair }); return send(res, 200, { ok: true, msg: X.LT.msg }); }
      if (u.pathname === '/api/lt/close') {
        const pct = Math.min(1, Math.max(0.01, +b.pct || 1));
        try { const r = await ltClosePos(X, String(b.positionId), pct, 'manual'); setTimeout(() => bxPollOne(X), 1500); return send(res, 200, { ok: true, r }); }
        catch (e) { return send(res, 400, { error: e.message }); }
      }
      if (u.pathname === '/api/tool') {                // 🗡 特級咒具：擁有者直接能用；其他人要輸入擁有者設的密碼
        const T = ST.tool, op = String(b.op || 'get');
        if (op === 'unlock') {
          if (toolOk(me, owner)) return send(res, 200, { ok: true });
          if (!T.pw) return send(res, 400, { error: '擁有者還沒設定密碼' });
          const ip = (req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
          if (!pwOk(T.pw, String(b.pw || ''))) { failed(ip); return send(res, 400, { error: '密碼不對' }); }
          if (me && !T.grants.includes(me.uid)) T.grants.push(me.uid);
          dirty = true; log('特級咒具解鎖', me ? me.uid : ''); return send(res, 200, { ok: true });
        }
        if (!toolOk(me, owner)) return send(res, 403, { error: '特級咒具還沒解鎖', locked: true, hasPw: !!T.pw });
        if (op === 'get') return send(res, 200, { owner, v: TOOLV, px: T.px || {}, bt: T.bt || null, btRun: { run: TBT.run, done: TBT.done, total: TBT.total, msg: TBT.msg }, sigs: T.sigs.slice(0, 400), set: T.set, scan: T.scan, hook: me && T.hooks[me.uid] ? '已設定' : '', hookLast: (() => { try { return me && T.hooks[me.uid] ? dcStat(dec(T.hooks[me.uid])) : null; } catch (e) { return null; } })(), hasPw: !!T.pw, grants: owner ? T.grants : undefined });
        if (op === 'hook') {
          if (!me) return send(res, 400, { error: '用管理金鑰登入不能設定' });
          const w = String(b.webhook || '').replace(/\s+/g, '');
          if (w && !/^https:\/\/(?:(?:canary|ptb)\.)?(?:discord|discordapp)\.com\/api\/webhooks\/\d+\/[\w-]+$/.test(w)) return send(res, 400, { error: '網址格式不對，應該是 https://discord.com/api/webhooks/ 開頭' });
          T.hooks[me.uid] = w ? enc(w) : ''; dirty = true; return send(res, 200, { ok: true });
        }
        if (op === 'test') {
          let h = ''; try { h = me ? dec(T.hooks[me.uid] || '') : ''; } catch (e) {}
          if (!h) return send(res, 400, { error: '還沒設定 Webhook' });
          const ok = await dcSend('🗡 **特級咒具**：通知設定成功，之後有進場訊號會傳到這裡。', { webhook: h }, true), st = dcStat(h);
          return ok ? send(res, 200, { ok: true }) : send(res, 400, { error: `傳送失敗：${(st && st.err) || '原因不明'}` });
        }
        if (!owner) return send(res, 403, { error: '只有擁有者可以改' });
        if (op === 'bt') {                               // 🗡 特級咒具回測（在背景跑，幾分鐘）
          if (TBT.run) return send(res, 400, { error: '回測進行中，請稍等' });
          TBT.run = true; TBT.msg = '準備中…';
          toolBacktest(X, b).catch(e => { TBT.msg = '回測失敗：' + e.message; log('特級咒具回測失敗', e.message); }).finally(() => { TBT.run = false; });
          return send(res, 200, { ok: true });
        }
        if (op === 'pw') {
          if (!validPw(b.pw)) return send(res, 400, { error: '密碼至少 8 個字' });
          T.pw = hashPw(String(b.pw)); const n0 = T.grants.length, old = T.grants; T.grants = []; dirty = true; log('特級咒具改密碼');
          for (const uid of old) { const XA = ctx(uid); if (XA.A.lt.sp) { XA.A.lt.sp = false; touchLT(XA); dcX(XA, '⏸ **特級交易已暫停**：特級咒具的密碼改了，要重新輸入新密碼才能再開（已開的單照常管理）'); } }
          return send(res, 200, { ok: true, revoked: n0 });
        }
        if (op === 'set') {
          const x = b.set || {}; T.set = { n: Math.max(5, Math.min(100, Math.round(+x.n || T.set.n))), h4: x.h4 !== false, h1: x.h1 !== false, zh: x.zh !== false, crt: x.crt !== false, hunt: x.hunt !== false };
          dirty = true; return send(res, 200, { ok: true, set: T.set });
        }
        return send(res, 400, { error: '不認得的操作' });
      }
      if (u.pathname === '/api/lt/withdraw') {         // 💸 收回資金：一般、特級分開；只改「目前」的金額，盈虧率、資金曲線不變
        const sp = b.kind === 'sp', C = X.A.lt;
        if (sp && !toolOkUid(X.uid)) return send(res, 403, { error: '特級交易要先解鎖特級咒具' });
        if (!(sp ? C.spBudget > 0 : C.budget > 0)) return send(res, 400, { error: `${sp ? '特級交易' : '一般交易'}沒有設定投入資金，沒有可以收回的` });
        const B = sp ? ltSpEq(X) : ltBotEq(X), cur = Math.floor(B.eq * 100) / 100;
        if (!(cur > 0)) return send(res, 400, { error: '目前沒有可以收回的資金' });
        const amt = b.amount === undefined || b.amount === '' || b.amount === null ? B.eq : Math.min(+b.amount, B.eq);   // 留空＝全部收回（連零頭一起）
        if (!(amt > 0)) return send(res, 400, { error: '收回的金額要大於 0' });
        if (sp) C.spWd = (C.spWd || 0) + amt; else C.wd = (C.wd || 0) + amt;
        const left = cur - amt, all = left < 0.01;
        if (all) { if (sp) C.sp = false; else C.on = false; X.LT.pause = { t: Date.now(), why: `${sp ? '特級交易' : '一般交易'}收回資金` }; }
        touchLT(X); log('收回資金', X.uid, sp ? '特級' : '一般', amt);
        dcX(X, `💸 **${sp ? '🗡 特級交易' : '一般交易'}收回資金 ${amt.toFixed(2)}U**：目前剩 ${Math.max(0, left).toFixed(2)}U${all ? `，${sp ? '特級交易' : '自動交易'}已暫停` : ''}${B.used > 0 ? `\n-# 還有持倉（保證金 ${B.used.toFixed(2)}U），之後的盈虧會繼續算進「目前」` : ''}`);
        return send(res, 200, { ok: true, amt, left: Math.max(0, left) });
      }
      if (u.pathname === '/api/me/password') {         // 🔑 改自己的密碼：要先輸入目前的密碼；改完其他裝置登出，這台保持登入
        if (!me) return send(res, 400, { error: '用管理金鑰登入不能改密碼' });
        const ip = (req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
        if (!pwOk(me, String(b.old || ''))) { failed(ip); return send(res, 400, { error: '目前的密碼不對' }); }
        if (!validPw(b.password)) return send(res, 400, { error: '新密碼至少 8 個字' });
        if (String(b.password) === String(b.old)) return send(res, 400, { error: '新密碼跟目前的一樣' });
        Object.assign(me, hashPw(b.password));
        const m0 = String(req.headers.authorization || '').match(/^Bearer\s+([0-9a-f]{64})$/i), keep = m0 ? tokHash(m0[1]) : '';
        const n0 = ST.sessions.length; ST.sessions = ST.sessions.filter(x => x.uid !== me.uid || x.h === keep); dirty = true;
        log('改自己的密碼', me.uid); dcX(ctx(me.uid), `🔑 **你的密碼已經更改**${n0 - ST.sessions.length ? `，其他 ${n0 - ST.sessions.length} 個裝置已登出` : ''}。如果不是你本人，請馬上聯絡擁有者。`);
        return send(res, 200, { ok: true, out: n0 - ST.sessions.length });
      }
      if (u.pathname === '/api/lt/adopt') {            // 🤖 把一筆手動單改成自動單：之後照「那個帳號自己」的規則管理（鎖利、停損、到期、一鍵平倉），交易所也補掛止損
        let XA = X;                                      // 👑 擁有者可以在帳號管理後台幫別人改（對方的 Discord 會收到通知）
        if (b.uid && String(b.uid) !== X.uid) {
          if (!owner) return send(res, 403, { error: '只有擁有者可以幫別人改成自動單' });
          const usr = ST.users.find(x => x.uid === String(b.uid)); if (!usr) return send(res, 404, { error: '找不到這個帳號' });
          XA = ctx(usr.uid);
        }
        if (!hasKey(XA)) return send(res, 400, { error: '還沒設定 Bitunix API' });
        await bxPollOne(XA);
        const p = XA.BX.pos.find(x => x.id === String(b.positionId || ''));
        if (!p) return send(res, 404, { error: '交易所上找不到這筆倉位，可能已經平倉了' });
        if (ltOpenTrades(XA).some(t => t.positionId === p.id)) return send(res, 400, { error: '這筆已經是自動單了' });
        if (ltOpenTrades(XA).some(t => t.sym === p.sym)) return send(res, 400, { error: `${p.sym} 已經有一筆自動單，同一個幣只能有一筆` });
        const C = XA.A.lt, px = PX.map[p.sym] || p.entry, roe = p.dir * (px / p.entry - 1) * C.lev * 100;   // 規則一樣用「設定的槓桿」換算
        const t = {
          id: 'lt-adopt-' + Date.now(), sym: p.sym, dir: p.dir, card: '', abN: 0, et: p.ctime > 0 ? p.ctime : Date.now(), lev: p.lev,
          entry: p.entry, qty: p.qty, qty0: p.qty, margin: p.margin, m0: p.margin || C.margin, positionId: p.id, orderId: '', status: 'open', ruleLev: C.lev,
          realized: p.rpnl || 0, fee: p.fee || 0, funding: p.funding || 0, closes: [], locked: false, fav: Math.max(0, roe), adv: Math.min(0, roe), exSL: false, adopted: Date.now(), prec: 0, minQty: 0
        };
        const pr = await ltPair(p.sym).catch(() => null); if (pr) { t.prec = +pr.basePrecision || 0; t.minQty = +pr.minTradeVolume || 0; }
        XA.A.ltTrades.unshift(t); touchLT(XA);
        log('手動單改成自動單', XA.uid, p.sym, XA !== X ? '（擁有者 ' + X.uid + ' 幫他改）' : '');
        const T = TT(XA), k = rk(t, C.lev);
        dcX(XA, `🤖 **手動單改成自動單** ${p.dir > 0 ? '🟢 做多' : '🔴 做空'} **${mdEsc(p.sym)}**（${p.lev}x）\n開倉價 ${fpx(p.entry)}・數量 ${p.qty}\n之後照你的規則管理${XA !== X ? `（擁有者 ${X.uid} 幫你改的）` : ''}：浮盈 **+${pctK(T.tp, k)}%** 開始鎖利、浮虧 **−${pctK(T.sl, k)}%** 停損、持有 ${T.hold} 小時到期`);
        setTimeout(() => ltSyncSL(XA).catch(e => log('補掛止損失敗', XA.uid, e.message)), 500);   // 交易所補掛止損
        return send(res, 200, { ok: true });
      }
      if (u.pathname === '/api/lt/closeAll') {
        // 只平自動下單的倉位：手動開的單（含「符合訊號」）一律不動
        if (!hasKey(X)) return send(res, 400, { error: '還沒設定 Bitunix API 金鑰' });
        if (b.pause) { X.A.lt.on = false; X.A.lt.sp = false; X.LT.pause = { t: Date.now(), why: '一鍵平倉時選擇暫停' }; }
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
        if (!X.A.notify.webhook) return send(res, 400, { error: '還沒儲存 Webhook 網址' });
        const ok = await dcSend('🔔 **合約量化進場**：通知測試成功！之後每次有新訊號進場、結單，都會傳到這個頻道。', X.A.notify, true);
        const st = dcStat(X.A.notify.webhook);
        return ok ? send(res, 200, { ok: true }) : send(res, 400, { error: `傳送失敗：${(st && st.err) || '原因不明'}` });
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

/* =====================================================================
   Homework 1 — PRIVATE KEY -> PUBLIC KEY on a toy elliptic curve
   Curve: y^2 = x^3 + 7 (mod p)   (same family as Ethereum's secp256k1)
   Public key: Q = k*G   (scalar multiplication)
   ===================================================================== */
'use strict';

/* =====================================================================
   1. Modular arithmetic and elliptic-curve group law
   A point is {x, y}; the point at infinity O is represented by null.
   ===================================================================== */

function mod(a, p) {
  const r = a % p;
  return r < 0 ? r + p : r;
}

// Modular inverse with the extended Euclidean algorithm.
function modInv(a, p) {
  let r0 = mod(a, p), r1 = p, s0 = 1, s1 = 0;
  while (r1 !== 0) {
    const q = Math.floor(r0 / r1);
    [r0, r1] = [r1, r0 - q * r1];
    [s0, s1] = [s1, s0 - q * s1];
  }
  if (r0 !== 1) throw new Error('not invertible');
  return mod(s0, p);
}

function makeCurve(p) {
  return { p, a: 0, b: 7 }; // y^2 = x^3 + 7
}

function isOnCurve(P, c) {
  if (!P) return true;
  const lhs = (P.y * P.y) % c.p;
  const rhs = mod(((P.x * P.x) % c.p) * P.x + c.a * P.x + c.b, c.p);
  return lhs === rhs;
}

// Point addition / doubling, returning every intermediate quantity
// (needed for the step-by-step tables and for the animation).
function addDetailed(P, Q, c) {
  const p = c.p;
  if (!P) return { R: Q, kind: 'identity' };
  if (!Q) return { R: P, kind: 'identity' };
  if (P.x === Q.x && mod(P.y + Q.y, p) === 0) {
    return { R: null, kind: 'inverse', A: P, B: Q };           // P + (-P) = O
  }
  let kind, num, den;
  if (P.x === Q.x) {                                           // P == Q : tangent
    kind = 'double';
    num = mod(3 * P.x * P.x + c.a, p);
    den = mod(2 * P.y, p);
  } else {                                                     // chord
    kind = 'add';
    num = mod(Q.y - P.y, p);
    den = mod(Q.x - P.x, p);
  }
  const lambda = mod(num * modInv(den, p), p);
  const x3 = mod(lambda * lambda - P.x - Q.x, p);
  const y3 = mod(lambda * (P.x - x3) - P.y, p);
  return { R: { x: x3, y: y3 }, kind, A: P, B: Q, num, den, lambda };
}

function add(P, Q, c) { return addDetailed(P, Q, c).R; }

// Slow method: G, 2G, 3G, ..., kG by repeated addition of G.
function naiveOps(k, G, c) {
  const ops = [];
  let R = G;
  for (let j = 2; j <= k; j++) {
    const d = addDetailed(R, G, c);
    ops.push({ ...d, mA: j - 1, mB: 1, mR: j });
    R = d.R;
  }
  return { R, ops };
}

// Fast method: left-to-right double-and-add over the bits of k.
function doubleAddOps(k, G, c) {
  const bits = k.toString(2);
  const ops = [];
  let R = G, m = 1;
  for (let i = 1; i < bits.length; i++) {
    let d = addDetailed(R, R, c);
    ops.push({ ...d, mA: m, mB: m, mR: 2 * m, bit: bits[i], tag: 'double' });
    R = d.R; m *= 2;
    if (bits[i] === '1') {
      d = addDetailed(R, G, c);
      ops.push({ ...d, mA: m, mB: 1, mR: m + 1, bit: bits[i], tag: 'add' });
      R = d.R; m += 1;
    }
  }
  return { R, ops, bits };
}

function scalarMul(k, G, c) { return doubleAddOps(k, G, c).R; }

// Order n of G: the smallest n with nG = O.
function pointOrder(G, c) {
  let R = G, n = 1;
  while (R) {
    R = add(R, G, c);
    n++;
    if (n > 2 * c.p + 10) throw new Error('order search failed');
  }
  return n;
}

// All affine points of the curve, sorted by x then y.
function allPoints(c) {
  const p = c.p;
  const root = new Int32Array(p).fill(-1);
  for (let y = 0; y < p; y++) {
    const s = (y * y) % p;
    if (root[s] === -1) root[s] = y;      // smallest y with y^2 = s
  }
  const pts = [];
  for (let x = 0; x < p; x++) {
    const rhs = mod(((x * x) % p) * x + c.a * x + c.b, p);
    const y = root[rhs];
    if (y >= 0) {
      pts.push({ x, y });
      if (y !== 0) pts.push({ x, y: p - y });
    }
  }
  pts.sort((u, v) => u.x - v.x || u.y - v.y);
  return pts;
}

// Multiples G, 2G, ..., (n-1)G as two coordinate arrays (index = k-1).
function multiplesSequence(G, c, n) {
  const m = n - 1;
  const X = new Array(m), Y = new Array(m);
  let P = G;
  X[0] = P.x; Y[0] = P.y;
  for (let k = 2; k <= m; k++) {
    P = add(P, G, c);
    X[k - 1] = P.x; Y[k - 1] = P.y;
  }
  return { X, Y };
}

/* =====================================================================
   2. Small statistics toolbox
   ===================================================================== */

const bitLength = v => (v <= 0 ? 1 : v.toString(2).length);

function popcount(v) {
  v >>>= 0;
  let c = 0;
  while (v) { c += v & 1; v >>>= 1; }
  return c;
}

function pearson(a, b) {
  const n = a.length;
  if (n < 3) return NaN;
  let ma = 0, mb = 0;
  for (let i = 0; i < n; i++) { ma += a[i]; mb += b[i]; }
  ma /= n; mb /= n;
  let sab = 0, saa = 0, sbb = 0;
  for (let i = 0; i < n; i++) {
    const da = a[i] - ma, db = b[i] - mb;
    sab += da * db; saa += da * da; sbb += db * db;
  }
  return saa === 0 || sbb === 0 ? NaN : sab / Math.sqrt(saa * sbb);
}

// Histogram of values in [0,p) over `bins` equal-ish bins + number of
// field elements falling in each bin (needed for the expected counts).
function histogram(vals, p, bins) {
  const counts = new Array(bins).fill(0);
  const width = new Array(bins).fill(0);
  for (const v of vals) counts[Math.floor((v * bins) / p)]++;
  for (let v = 0; v < p; v++) width[Math.floor((v * bins) / p)]++;
  return { counts, width };
}

function chiSquare(h, total, p) {
  let chi = 0;
  for (let i = 0; i < h.counts.length; i++) {
    const e = (total * h.width[i]) / p;
    chi += ((h.counts[i] - e) ** 2) / e;
  }
  const df = h.counts.length - 1;
  // Wilson–Hilferty approximation of the 5% critical value
  const crit = df * Math.pow(1 - 2 / (9 * df) + 1.645 * Math.sqrt(2 / (9 * df)), 3);
  return { chi, df, crit, reject: chi > crit };
}

// Fraction of ones for each bit, from MSB (index 0) to LSB.
function bitFrequencies(vals, b) {
  const f = new Array(b).fill(0);
  for (const v of vals) for (let j = 0; j < b; j++) f[b - 1 - j] += (v >>> j) & 1;
  return f.map(x => x / vals.length);
}

function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/* ---- SHA-256 (single block, 4-byte messages) used as a reference "real hash" ---- */
const SHA = (function () {
  const primes = [];
  for (let n = 2; primes.length < 64; n++) {
    let ok = true;
    for (let d = 2; d * d <= n; d++) if (n % d === 0) { ok = false; break; }
    if (ok) primes.push(n);
  }
  const frac = x => Math.floor((x - Math.floor(x)) * 4294967296);
  return {
    K: primes.map(q => frac(Math.cbrt(q))),
    H0: primes.slice(0, 8).map(q => frac(Math.sqrt(q)))
  };
})();

const rotr = (x, n) => (x >>> n) | (x << (32 - n));

// First 32 bits of SHA-256(k as 4 big-endian bytes).
function sha256First32(k) {
  const w = new Array(64).fill(0);
  w[0] = k | 0;
  w[1] = 0x80000000 | 0;
  w[15] = 32;
  for (let i = 16; i < 64; i++) {
    const s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >>> 3);
    const s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >>> 10);
    w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
  }
  let [a, b, c, d, e, f, g, h] = SHA.H0;
  for (let i = 0; i < 64; i++) {
    const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
    const ch = (e & f) ^ (~e & g);
    const t1 = (h + S1 + ch + SHA.K[i] + w[i]) | 0;
    const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
    const maj = (a & b) ^ (a & c) ^ (b & c);
    const t2 = (S0 + maj) | 0;
    h = g; g = f; f = e; e = (d + t1) | 0;
    d = c; c = b; b = a; a = (t1 + t2) | 0;
  }
  return (SHA.H0[0] + a) >>> 0;
}

function sampleKs(m, cap) {
  if (m <= cap) return Array.from({ length: m }, (_, i) => i + 1);
  const rnd = mulberry32(2026);
  return Array.from({ length: cap }, () => 1 + Math.floor(rnd() * m));
}

// Avalanche test: flip one bit of k, count how many output bits change.
// Output of the EC function = bits of (x, y); output of the reference hash =
// the first 2b bits of SHA-256(k).
function avalanche(X, Y, n, b, cap) {
  const m = n - 1, nb = bitLength(m), outBits = 2 * b;
  const ks = sampleKs(m, cap);
  const perEC = new Array(nb).fill(0), perH = new Array(nb).fill(0), cnt = new Array(nb).fill(0);
  const H = k => sha256First32(k) >>> (32 - outBits);
  for (const k of ks) {
    const h1 = H(k);
    for (let i = 0; i < nb; i++) {
      const k2 = k ^ (1 << i);
      if (k2 < 1 || k2 > m) continue;
      perEC[i] += (popcount(X[k - 1] ^ X[k2 - 1]) + popcount(Y[k - 1] ^ Y[k2 - 1])) / outBits;
      perH[i] += popcount((h1 ^ H(k2)) >>> 0) / outBits;
      cnt[i]++;
    }
  }
  const tot = cnt.reduce((s, v) => s + v, 0);
  return {
    nb, pairs: tot,
    ec: perEC.reduce((s, v) => s + v, 0) / tot,
    hash: perH.reduce((s, v) => s + v, 0) / tot,
    perEC: perEC.map((v, i) => (cnt[i] ? v / cnt[i] : 0)),
    perH: perH.map((v, i) => (cnt[i] ? v / cnt[i] : 0))
  };
}

// Full statistical analysis of the map k -> kG over all k in [1, n-1].
function analyse(c, G, n, cap) {
  const p = c.p, b = bitLength(p - 1), m = n - 1;
  const { X, Y } = multiplesSequence(G, c, n);
  const K = Array.from({ length: m }, (_, i) => i + 1);

  const cx = new Int32Array(p), cy = new Int32Array(p);
  for (let i = 0; i < m; i++) { cx[X[i]]++; cy[Y[i]]++; }
  const mult = (cnt) => {
    const t = {};
    for (let v = 0; v < p; v++) t[cnt[v]] = (t[cnt[v]] || 0) + 1;
    return t;
  };
  const pairs = new Set();
  for (let i = 0; i < m; i++) pairs.add(X[i] * p + Y[i]);

  const bitsX = bitFrequencies(X, b), bitsY = bitFrequencies(Y, b);
  let baseline = 0;
  for (const f of bitsX.concat(bitsY)) baseline += 2 * f * (1 - f);
  baseline /= 2 * b;

  const coarse = Math.min(16, p);
  const fineX = histogram(X, p, p), fineY = histogram(Y, p, p);
  const coarseX = histogram(X, p, coarse), coarseY = histogram(Y, p, coarse);

  // Consecutive outputs: Q_{k+1} = Q_k + G
  const X1 = X.slice(0, m - 1), X2 = X.slice(1), Y1 = Y.slice(0, m - 1), Y2 = Y.slice(1);

  // Reflection symmetry: (n-k)G = -kG
  let sym = 0;
  for (let k = 1; k <= m; k++) {
    if (X[n - k - 1] === X[k - 1] && Y[n - k - 1] === mod(p - Y[k - 1], p)) sym++;
  }

  return {
    p, b, n, m, X, Y, K, cx, cy,
    distinctX: [...cx].filter(v => v > 0).length,
    distinctY: [...cy].filter(v => v > 0).length,
    distinctPairs: pairs.size,
    multX: mult(cx), multY: mult(cy),
    fineX, fineY, coarseX, coarseY,
    chi: {
      xFine: chiSquare(fineX, m, p), xCoarse: chiSquare(coarseX, m, p),
      yFine: chiSquare(fineY, m, p), yCoarse: chiSquare(coarseY, m, p)
    },
    bitsX, bitsY, baseline,
    corr: {
      kx: pearson(K, X), ky: pearson(K, Y), xy: pearson(X, Y),
      xx: pearson(X1, X2), yy: pearson(Y1, Y2)
    },
    symmetry: sym / m,
    aval: avalanche(X, Y, n, b, cap)
  };
}

// Check (k1+k2)G = k1G + k2G on random pairs.
function homomorphismCheck(G, c, n, trials) {
  const rnd = mulberry32(7);
  let ok = 0;
  for (let t = 0; t < trials; t++) {
    const k1 = 1 + Math.floor(rnd() * (n - 1)), k2 = 1 + Math.floor(rnd() * (n - 1));
    const s = (k1 + k2) % n;
    const left = s === 0 ? null : scalarMul(s, G, c);
    const right = add(scalarMul(k1, G, c), scalarMul(k2, G, c), c);
    const same = (!left && !right) || (left && right && left.x === right.x && left.y === right.y);
    if (same) ok++;
  }
  return { ok, trials };
}

// Pick a "good" default base point: first point whose order is >= half the group size.
function chooseBasePoint(c, pts, groupSize) {
  let best = null, bestOrder = 0;
  for (const P of pts.slice(0, 24)) {
    const o = pointOrder(P, c);
    if (o > bestOrder) { best = P; bestOrder = o; }
    if (o * 2 >= groupSize) return { G: P, n: o };
  }
  return { G: best, n: bestOrder };
}

/* =====================================================================
   3. Page code (DOM) — skipped when the file is loaded from Node
   ===================================================================== */

const PRIMES = [17, 61, 103, 1009, 10009, 65521];
const S = { curve: null, G: null, k: 6, n: 0, pts: [], A: null };
const viz = { ops: [], t: -1, playing: false, timer: null, method: 'doubleadd' };
const pointCache = new Map();

const $ = id => document.getElementById(id);
const fmtPt = P => (P ? `(${P.x}, ${P.y})` : 'O');
const nm = m => (m === 1 ? 'G' : m + 'G');
const f3 = v => (Number.isFinite(v) ? v.toFixed(3) : '—');
const f4 = v => (Number.isFinite(v) ? v.toFixed(4) : '—');
const hex = (v, digits) => v.toString(16).padStart(digits, '0');

function getPoints(p) {
  if (!pointCache.has(p)) pointCache.set(p, allPoints(makeCurve(p)));
  return pointCache.get(p);
}

function table(headers, rows) {
  return '<table><thead><tr>' + headers.map(h => `<th>${h}</th>`).join('') + '</tr></thead><tbody>' +
    rows.map(r => '<tr>' + r.map(c => `<td>${c}</td>`).join('') + '</tr>').join('') + '</tbody></table>';
}

/* ---------- canvas helpers ---------- */

function cssVar(name, fallback) {
  const v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  return v || fallback;
}
const COL = () => ({
  ink: cssVar('--ink', '#202b33'), muted: cssVar('--muted', '#7b8a95'),
  line: cssVar('--line', '#dce6ed'), accent: cssVar('--accent', '#547f98'),
  paper: cssVar('--paper', '#ffffff'), warm: '#c9743a', green: '#3f8f5a'
});

function prep(cv, w, h) {
  const dpr = window.devicePixelRatio || 1;
  cv.width = Math.round(w * dpr);
  cv.height = Math.round(h * dpr);
  cv.style.width = '100%';
  cv.style.height = 'auto';
  cv.style.aspectRatio = `${w} / ${h}`;
  const ctx = cv.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.font = '12px "Courier New", monospace';
  return ctx;
}

// Grouped bar chart. cfg: {w,h,title,cats,series:[{name,values,color}],ref,yMax,labelEvery,yFmt}
function barChart(cv, cfg) {
  const w = cfg.w || 760, h = cfg.h || 240, C = COL();
  const ctx = prep(cv, w, h);
  const L = 48, R = 12, T = 30, B = 32;
  ctx.fillStyle = C.paper; ctx.fillRect(0, 0, w, h);
  const all = cfg.series.flatMap(s => s.values);
  const yMax = cfg.yMax || Math.max(1e-9, Math.max(...all) * 1.15);
  const yFmt = cfg.yFmt || (v => (Math.abs(v) >= 10 || Number.isInteger(v) ? String(Math.round(v)) : v.toFixed(2)));
  const px = w - L - R, py = h - T - B;
  const Y = v => T + py - (v / yMax) * py;

  ctx.fillStyle = C.muted; ctx.textAlign = 'left';
  ctx.fillText(cfg.title || '', L, 16);
  ctx.textAlign = 'right';
  for (let i = 0; i <= 4; i++) {
    const v = (yMax * i) / 4;
    ctx.strokeStyle = C.line; ctx.beginPath(); ctx.moveTo(L, Y(v)); ctx.lineTo(w - R, Y(v)); ctx.stroke();
    ctx.fillStyle = C.muted; ctx.fillText(yFmt(v), L - 6, Y(v) + 4);
  }
  const nC = cfg.cats.length, cw = px / nC, ns = cfg.series.length;
  const bw = Math.max(1, (cw * 0.8) / ns);
  cfg.series.forEach((s, si) => {
    ctx.fillStyle = s.color || C.accent;
    s.values.forEach((v, i) => {
      const x = L + i * cw + cw * 0.1 + si * bw;
      ctx.fillRect(x, Y(v), bw, Math.max(0, Y(0) - Y(v)));
    });
  });
  ctx.fillStyle = C.muted; ctx.textAlign = 'center';
  const every = cfg.labelEvery || 1;
  cfg.cats.forEach((c, i) => {
    if (i % every === 0) ctx.fillText(String(c), L + i * cw + cw / 2, h - B + 16);
  });
  if (cfg.ref !== undefined && cfg.ref !== null) {
    ctx.strokeStyle = C.warm; ctx.setLineDash([5, 4]);
    ctx.beginPath(); ctx.moveTo(L, Y(cfg.ref)); ctx.lineTo(w - R, Y(cfg.ref)); ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle = C.warm; ctx.textAlign = 'right';
    ctx.fillText(cfg.refLabel || '', w - R - 2, Y(cfg.ref) - 4);
  }
  if (ns > 1) {
    ctx.textAlign = 'right';
    let lx = w - R;
    for (const s of cfg.series.slice().reverse()) {
      ctx.fillStyle = C.muted; ctx.fillText(s.name, lx, 16);
      const tw = ctx.measureText ? ctx.measureText(s.name).width : 80;
      ctx.fillStyle = s.color; ctx.fillRect(lx - tw - 14, 7, 9, 9);
      lx -= tw + 30;
    }
  }
  ctx.strokeStyle = C.ink; ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, T + py); ctx.lineTo(w - R, T + py); ctx.stroke();
}

// Scatter plot. cfg: {w,h,title,xs,ys,xMax,yMax,xLabel,yLabel}
function scatter(cv, cfg) {
  const w = cfg.w || 370, h = cfg.h || 260, C = COL();
  const ctx = prep(cv, w, h);
  const L = 40, R = 10, T = 28, B = 30;
  ctx.fillStyle = C.paper; ctx.fillRect(0, 0, w, h);
  const px = w - L - R, py = h - T - B;
  ctx.fillStyle = C.muted; ctx.textAlign = 'left'; ctx.fillText(cfg.title, L, 16);
  ctx.strokeStyle = C.ink; ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, T + py); ctx.lineTo(w - R, T + py); ctx.stroke();
  const r = cfg.xs.length > 5000 ? 1 : cfg.xs.length > 300 ? 1.4 : 2.4;
  ctx.fillStyle = C.accent; ctx.globalAlpha = cfg.xs.length > 5000 ? 0.45 : 0.9;
  for (let i = 0; i < cfg.xs.length; i++) {
    const x = L + (cfg.xs[i] / cfg.xMax) * px, y = T + py - (cfg.ys[i] / cfg.yMax) * py;
    ctx.fillRect(x - r / 2, y - r / 2, r, r);
  }
  ctx.globalAlpha = 1;
  ctx.fillStyle = C.muted; ctx.textAlign = 'center';
  ctx.fillText(cfg.xLabel + ` (0…${cfg.xMax})`, L + px / 2, h - 8);
  ctx.textAlign = 'right'; ctx.fillText(String(cfg.yMax), L - 5, T + 10); ctx.fillText('0', L - 5, T + py);
}

/* ---------- parameters, tables, public key ---------- */

function readParams() {
  const p = +$('sel-p').value;
  S.curve = makeCurve(p);
  const [gx, gy] = $('sel-g').value.split(',').map(Number);
  S.G = { x: gx, y: gy };
  S.k = Math.floor(+$('inp-k').value);
  S.n = pointOrder(S.G, S.curve);
  S.pts = getPoints(p);
}

function fillBasePoints(selectG) {
  const sel = $('sel-g');
  const pts = S.pts.slice(0, 24);
  sel.innerHTML = pts.map(P => `<option value="${P.x},${P.y}">G = (${P.x}, ${P.y})</option>`).join('');
  if (selectG) sel.value = `${selectG.x},${selectG.y}`;
  $('g-note').textContent = S.pts.length > 24
    ? `(first 24 of ${S.pts.length} affine points)` : `(all ${S.pts.length} affine points)`;
}

function renderParams() {
  const c = S.curve, p = c.p, G = S.G, k = S.k;
  const rhs = mod(((G.x * G.x) % p) * G.x + c.b, p);
  $('params-out').innerHTML =
    `Field: F<sub>p</sub> with p = ${p}<br>` +
    `Curve: <code>y² = x³ + 7 (mod ${p})</code> &nbsp;(a = 0, b = 7)<br>` +
    `Base point: G = ${fmtPt(G)} &nbsp;check: y² = ${(G.y * G.y) % p}, x³ + 7 = ${rhs} ${isOnCurve(G, c) ? '✔ on the curve' : '✘ NOT on the curve'}<br>` +
    `Order of G: n = ${S.n} &nbsp;(smallest n with nG = O) &nbsp;|&nbsp; points on the curve: ${S.pts.length + 1} (including O)<br>` +
    `Private key: <strong>k = ${k}</strong> &nbsp;(binary ${k.toString(2)}, valid range 1 … ${S.n - 1})<br>` +
    `Public key: <strong>Q = kG</strong>`;
}

function opText(op) {
  if (op.kind === 'inverse') return `${nm(op.mA)} + ${nm(op.mB)} = O`;
  const what = op.kind === 'double' ? 'doubling' : 'addition';
  return `${nm(op.mA)} ${op.kind === 'double' ? '+' : '+'} ${nm(op.mB)} (${what})`;
}

function renderMultiples() {
  const { ops } = naiveOps(S.k, S.G, S.curve);
  const rows = [['1', `<strong>G = ${fmtPt(S.G)}</strong>`, 'base point', '—']];
  ops.forEach(op => rows.push([String(op.mR), `<strong>${nm(op.mR)} = ${fmtPt(op.R)}</strong>`, opText(op), String(op.lambda)]));
  let shown = rows;
  let note = '';
  if (rows.length > 40) {
    shown = rows.slice(0, 10).concat([['…', '…', '…', '…']], rows.slice(-3));
    note = `<p class="meta">Table shortened (${rows.length} rows). The fast method below needs only ~${doubleAddOps(S.k, S.G, S.curve).ops.length} operations.</p>`;
  }
  $('naive-out').innerHTML = table(['j', 'jG', 'operation', 'λ mod p'], shown) + note;
}

function renderTrace() {
  const c = S.curve, da = doubleAddOps(S.k, S.G, c);
  const rows = [['init', da.bits[0], 'R = G', '—', `<strong>${fmtPt(S.G)}</strong>`]];
  da.ops.forEach((op, i) => rows.push([
    String(i + 1), op.bit, op.tag === 'double' ? `double: ${nm(op.mA)} + ${nm(op.mA)}` : `add: ${nm(op.mA)} + G`,
    String(op.lambda), `${nm(op.mR)} = <strong>${fmtPt(op.R)}</strong>`
  ]));
  const slow = naiveOps(S.k, S.G, c).R;
  const same = slow && da.R && slow.x === da.R.x && slow.y === da.R.y;
  $('trace-out').innerHTML =
    `<p>k = ${S.k} = <code>${da.bits}</code> in binary. Start with R = G; for every following bit: double R, and if the bit is 1 also add G. ` +
    `That is ${da.ops.length} group operations instead of ${Math.max(0, S.k - 1)}.</p>` +
    table(['step', 'bit', 'operation', 'λ mod p', 'result'], rows) +
    `<p class="meta">Check: repeated addition and double-and-add give ${same ? 'the same point ✔' : 'DIFFERENT points ✘'}.</p>`;

  const Q = da.R, b = bitLength(S.curve.p - 1), d = 2 * Math.ceil(b / 8);
  $('pubkey-out').innerHTML =
    `TOY PRIVATE KEY &nbsp;k = <strong>${S.k}</strong><br>` +
    `TOY PUBLIC KEY &nbsp;&nbsp;Q = kG = <strong>${fmtPt(Q)}</strong><br>` +
    `<span class="meta">uncompressed encoding (Ethereum style 0x04 ‖ x ‖ y, ${d / 2} byte(s) per coordinate): ` +
    `04 ${hex(Q.x, d)} ${hex(Q.y, d)}</span>`;
}

/* ---------- slow-motion visualisation ---------- */

const VIZ_MAX_P = 103;
const PHASES = 4;

function vizOps() {
  return viz.method === 'naive' ? naiveOps(S.k, S.G, S.curve).ops : doubleAddOps(S.k, S.G, S.curve).ops;
}

function initViz() {
  stopViz();
  const p = S.curve.p, ok = p <= VIZ_MAX_P;
  $('viz-wrap').style.display = ok ? '' : 'none';
  $('viz-msg').style.display = ok ? 'none' : '';
  if (!ok) return;
  viz.ops = vizOps();
  viz.t = -1;
  drawViz();
}

function stopViz() {
  viz.playing = false;
  clearTimeout(viz.timer);
  if ($('viz-play')) $('viz-play').textContent = '▶ Play';
}

function vizAdvance() {
  const total = viz.ops.length * PHASES;
  if (viz.t < total - 1) viz.t++;
  drawViz();
}

function vizTick() {
  if (!viz.playing) return;
  if (viz.t >= viz.ops.length * PHASES - 1) { stopViz(); return; }
  vizAdvance();
  viz.timer = setTimeout(vizTick, 1700 / +$('viz-speed').value);
}

function drawViz() {
  const cv = $('viz-canvas'), C = COL(), p = S.curve.p;
  const W = 640, H = 640, M = 40;
  const ctx = prep(cv, W, H);
  ctx.fillStyle = C.paper; ctx.fillRect(0, 0, W, H);
  const cell = (W - 2 * M) / (p - 1);
  const X = x => M + x * cell, Y = y => H - M - y * cell;
  const big = Math.max(3.5, Math.min(9, cell * 0.28)), small = Math.max(1.6, Math.min(4.5, cell * 0.14));
  const tick = p <= 17 ? 1 : p <= 61 ? 5 : 10;

  // grid and axes
  ctx.strokeStyle = C.line; ctx.fillStyle = C.muted; ctx.textAlign = 'center';
  for (let v = 0; v < p; v += tick) {
    ctx.beginPath(); ctx.moveTo(X(v), Y(0)); ctx.lineTo(X(v), Y(p - 1)); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(X(0), Y(v)); ctx.lineTo(X(p - 1), Y(v)); ctx.stroke();
    ctx.fillText(String(v), X(v), Y(0) + 18);
    ctx.textAlign = 'right'; ctx.fillText(String(v), X(0) - 8, Y(v) + 4); ctx.textAlign = 'center';
  }
  const dot = (x, y, r, fill, stroke) => {
    ctx.beginPath(); ctx.arc(X(x), Y(y), r, 0, 2 * Math.PI);
    if (fill) { ctx.fillStyle = fill; ctx.fill(); }
    if (stroke) { ctx.strokeStyle = stroke; ctx.lineWidth = 2; ctx.stroke(); ctx.lineWidth = 1; }
  };
  const label = (x, y, txt, color) => {
    ctx.fillStyle = color; ctx.textAlign = 'left'; ctx.fillText(txt, X(x) + big + 3, Y(y) - big - 2);
  };

  // all curve points
  ctx.globalAlpha = 0.55;
  for (const P of S.pts) dot(P.x, P.y, small + 0.8, C.accent);
  ctx.globalAlpha = 1;

  const total = viz.ops.length;
  const t = viz.t;
  const opIdx = t < 0 ? -1 : Math.floor(t / PHASES), phase = t < 0 ? -1 : t % PHASES;
  const labelsOn = p <= 17;

  // base point + earlier results
  dot(S.G.x, S.G.y, big, C.green);
  if (labelsOn) label(S.G.x, S.G.y, 'G', C.green);
  for (let i = 0; i < total; i++) {
    const op = viz.ops[i];
    const done = i < opIdx || (i === opIdx && phase >= 3);
    if (done && op.R) {
      dot(op.R.x, op.R.y, big * 0.85, C.green);
      if (labelsOn) label(op.R.x, op.R.y, nm(op.mR), C.green);
    }
  }

  if (opIdx >= 0) {
    const op = viz.ops[opIdx];
    if (phase >= 1) {                                    // the (modular) line
      ctx.fillStyle = C.warm; ctx.globalAlpha = 0.85;
      if (op.kind === 'inverse') {
        for (let y = 0; y < p; y++) { ctx.beginPath(); ctx.arc(X(op.A.x), Y(y), small, 0, 7); ctx.fill(); }
      } else {
        for (let x = 0; x < p; x++) {
          const y = mod(op.lambda * (x - op.A.x) + op.A.y, p);
          ctx.beginPath(); ctx.arc(X(x), Y(y), small, 0, 7); ctx.fill();
        }
      }
      ctx.globalAlpha = 1;
    }
    if (op.R && phase >= 2) {                            // third intersection -R
      const ny = mod(-op.R.y, p);
      dot(op.R.x, ny, big + 1, null, C.warm);
      if (labelsOn) label(op.R.x, ny, '−' + nm(op.mR), C.warm);
    }
    if (op.R && phase >= 3) {                            // reflection
      ctx.strokeStyle = C.warm; ctx.setLineDash([5, 4]); ctx.beginPath();
      ctx.moveTo(X(op.R.x), Y(mod(-op.R.y, p))); ctx.lineTo(X(op.R.x), Y(op.R.y)); ctx.stroke(); ctx.setLineDash([]);
      dot(op.R.x, op.R.y, big + 2, C.green, C.ink);
      label(op.R.x, op.R.y, nm(op.mR), C.ink);
    }
    // operands
    dot(op.A.x, op.A.y, big + 1, C.ink);
    if (op.kind !== 'double') dot(op.B.x, op.B.y, big + 1, C.ink);
    ctx.fillStyle = C.ink; ctx.textAlign = 'left';
    ctx.fillText(nm(op.mA), X(op.A.x) + big + 3, Y(op.A.y) + 14);
    if (op.kind !== 'double') ctx.fillText(nm(op.mB), X(op.B.x) + big + 3, Y(op.B.y) + 14);
  }

  ctx.fillStyle = C.muted; ctx.textAlign = 'left';
  ctx.fillText('x →', X(p - 1) - 24, Y(0) + 32); ctx.fillText('y ↑', 4, 16);

  $('viz-progress').textContent = t < 0
    ? `ready — ${total} operation(s), ${total * PHASES} phases`
    : `operation ${opIdx + 1}/${total}, phase ${phase + 1}/${PHASES}`;
  $('viz-caption').innerHTML = captionHTML(opIdx, phase);
}

function captionHTML(opIdx, phase) {
  const p = S.curve.p, total = viz.ops.length;
  if (opIdx < 0) {
    return `Blue dots: all points of <code>y² = x³ + 7</code> over F<sub>${p}</sub>. ` +
      `Green dot: the base point G = ${fmtPt(S.G)}. Press <strong>▶ Play</strong> (or <strong>Step</strong>) to compute ` +
      `Q = ${S.k}·G with ${viz.method === 'naive' ? 'repeated addition' : 'double-and-add'}.` +
      (total === 0 ? ' (k = 1: nothing to compute, Q = G.)' : '');
  }
  const op = viz.ops[opIdx];
  if (op.kind === 'inverse') return `${nm(op.mA)} + ${nm(op.mB)} = O (point at infinity).`;
  const A = op.A, B = op.B, R = op.R, ny = mod(-R.y, p);
  const head = `<strong>Operation ${opIdx + 1}/${total}</strong> — `;
  let html;
  if (phase === 0) {
    html = head + (op.kind === 'double'
      ? `doubling: P + P with P = ${nm(op.mA)} = ${fmtPt(A)}. Target: ${nm(op.mR)}.`
      : `addition: P + Q with P = ${nm(op.mA)} = ${fmtPt(A)} and Q = ${nm(op.mB)} = ${fmtPt(B)}. Target: ${nm(op.mR)}.`);
  } else if (phase === 1) {
    html = head + (op.kind === 'double'
      ? `tangent at P: λ = 3x₁²·(2y₁)⁻¹ = ${op.num}·${op.den}⁻¹ ≡ <strong>${op.lambda}</strong> (mod ${p}).`
      : `chord through P and Q: λ = (y₂−y₁)·(x₂−x₁)⁻¹ = ${op.num}·${op.den}⁻¹ ≡ <strong>${op.lambda}</strong> (mod ${p}).`) +
      ` Orange dots = the points of the line y = λ(x − x₁) + y₁ reduced mod ${p}.`;
  } else if (phase === 2) {
    html = head + `third intersection of the line with the curve: x₃ = λ² − x₁ − x₂ = ${op.lambda}² − ${A.x} − ${B.x} ≡ <strong>${R.x}</strong> ` +
      `(mod ${p}); the line passes through (${R.x}, ${ny}) = −${nm(op.mR)} (orange ring).`;
  } else {
    html = head + `reflect across the x-axis (y → −y mod ${p}): y₃ = λ(x₁ − x₃) − y₁ ≡ <strong>${R.y}</strong>. ` +
      `Result: ${nm(op.mR)} = <strong>${fmtPt(R)}</strong>.`;
    if (opIdx === total - 1) html += `<br><strong>Done: TOY PUBLIC KEY Q = ${S.k}G = ${fmtPt(R)}</strong>`;
  }
  return html;
}

/* ---------- statistical exploration ---------- */

function renderStats() {
  const c = S.curve, p = c.p;
  const ids = ['freq-out', 'chi-out', 'corr-out', 'sym-out', 'aval-out'];
  if (S.n < 6) {
    $('stat-summary').innerHTML = `The base point has order ${S.n}: too few public keys for statistics. Choose another base point.`;
    ids.forEach(i => { $(i).innerHTML = ''; });
    $('keys-details').style.display = 'none';
    return;
  }
  const A = analyse(c, S.G, S.n, 4096);
  S.A = A;
  const C = COL();

  $('stat-summary').innerHTML =
    `All keys k = 1 … ${A.m} (n = ${A.n}) were computed for G = ${fmtPt(S.G)} on p = ${p}.<br>` +
    `Public keys: ${A.m} &nbsp;|&nbsp; distinct (x, y) pairs: ${A.distinctPairs} ` +
    `(${A.distinctPairs === A.m ? 'no collisions: k ↦ kG is injective' : 'collisions found'})<br>` +
    `Distinct x values reached: ${A.distinctX} of ${p} (${(100 * A.distinctX / p).toFixed(1)} %) &nbsp;|&nbsp; ` +
    `distinct y values reached: ${A.distinctY} of ${p} (${(100 * A.distinctY / p).toFixed(1)} %)`;

  // all keys (small groups only)
  const det = $('keys-details');
  if (A.m <= 120) {
    det.style.display = '';
    $('keys-out').innerHTML = table(['k', 'x', 'y', 'x (bin)', 'y (bin)'],
      A.K.map((k, i) => [String(k), String(A.X[i]), String(A.Y[i]),
        A.X[i].toString(2).padStart(A.b, '0'), A.Y[i].toString(2).padStart(A.b, '0')]));
  } else det.style.display = 'none';

  // histograms
  const bins = p <= 64 ? p : 64;
  const hx = histogram(A.X, p, bins), hy = histogram(A.Y, p, bins);
  const cats = hx.counts.map((_, i) => (p <= 64 ? i : Math.floor((i * p) / bins)));
  const every = bins <= 17 ? 1 : Math.ceil(bins / 8);
  const ref = A.m / bins;
  barChart($('ch-xhist'), { title: `x coordinate (${bins} bins)`, cats, series: [{ name: 'x', values: hx.counts, color: C.accent }], ref, refLabel: 'uniform over F_p', labelEvery: every, h: 230, w: 370 });
  barChart($('ch-yhist'), { title: `y coordinate (${bins} bins)`, cats, series: [{ name: 'y', values: hy.counts, color: C.accent }], ref, refLabel: 'uniform over F_p', labelEvery: every, h: 230, w: 370 });

  // frequency of individual values
  let html = '';
  if (p <= 17) {
    html += table(['value v', '#k with x = v', '#k with y = v'],
      Array.from({ length: p }, (_, v) => [String(v), String(A.cx[v]), String(A.cy[v])]));
  }
  const ms = [...new Set([...Object.keys(A.multX), ...Object.keys(A.multY)].map(Number))].sort((a, b) => a - b);
  html += table(['multiplicity m', '# x-values hit by exactly m keys', '# y-values hit by exactly m keys'],
    ms.map(m => [String(m), String(A.multX[m] || 0), String(A.multY[m] || 0)]));
  $('freq-out').innerHTML = html;

  // chi-square
  const row = (name, r, res) => [name, String(res), r.chi.toFixed(1), String(r.df), r.crit.toFixed(1), r.reject ? 'rejected' : 'not rejected'];
  $('chi-out').innerHTML = table(['test (H₀: uniform over F_p)', 'resolution', 'χ²', 'df', '5 % critical', 'H₀'], [
    row('x coordinate', A.chi.xFine, 'every value'), row('x coordinate', A.chi.xCoarse, `${A.coarseX.counts.length} bins`),
    row('y coordinate', A.chi.yFine, 'every value'), row('y coordinate', A.chi.yCoarse, `${A.coarseY.counts.length} bins`)
  ]);

  // bits
  const bcats = Array.from({ length: A.b }, (_, i) => `b${A.b - 1 - i}`);
  barChart($('ch-xbits'), { title: 'P(bit = 1) in x', cats: bcats, series: [{ name: 'x', values: A.bitsX, color: C.accent }], ref: 0.5, refLabel: '0.5', yMax: 1, h: 220, w: 370, yFmt: v => v.toFixed(2) });
  barChart($('ch-ybits'), { title: 'P(bit = 1) in y', cats: bcats, series: [{ name: 'y', values: A.bitsY, color: C.accent }], ref: 0.5, refLabel: '0.5', yMax: 1, h: 220, w: 370, yFmt: v => v.toFixed(2) });

  // correlation
  scatter($('ch-kx'), { title: 'private key k vs x of kG', xs: A.K, ys: A.X, xMax: A.m, yMax: p - 1, xLabel: 'k', yLabel: 'x' });
  scatter($('ch-ky'), { title: 'private key k vs y of kG', xs: A.K, ys: A.Y, xMax: A.m, yMax: p - 1, xLabel: 'k', yLabel: 'y' });
  const hm = homomorphismCheck(S.G, c, S.n, 300);
  $('corr-out').innerHTML = table(['pair', 'Pearson r'], [
    ['k vs x(kG)', f4(A.corr.kx)], ['k vs y(kG)', f4(A.corr.ky)],
    ['x(kG) vs y(kG)', f4(A.corr.xy)],
    ['x(kG) vs x((k+1)G)  (consecutive keys)', f4(A.corr.xx)], ['y(kG) vs y((k+1)G)', f4(A.corr.yy)]
  ]) + `<p class="meta">For ${A.m} samples, |r| below about ${(2 / Math.sqrt(A.m)).toFixed(3)} is compatible with “no linear correlation” (≈ 2/√N).</p>`;

  $('sym-out').innerHTML =
    `<strong>Hidden structure that r does not see.</strong><br>` +
    `Reflection symmetry (n−k)G = −kG, i.e. same x and y ↦ p − y: holds for ${(100 * A.symmetry).toFixed(1)} % of all k.<br>` +
    `Homomorphism (k₁+k₂)G = k₁G + k₂G: holds for ${hm.ok} of ${hm.trials} random pairs (k₁, k₂).`;

  // avalanche
  const nbCats = A.aval.perEC.map((_, i) => `k bit ${i}`);
  barChart($('ch-aval'), {
    title: 'fraction of output bits that flip when ONE input bit of k flips', cats: nbCats, h: 250, w: 760,
    series: [{ name: 'EC: k ↦ kG', values: A.aval.perEC, color: C.accent }, { name: 'SHA-256 (truncated)', values: A.aval.perH, color: C.warm }],
    ref: 0.5, refLabel: 'ideal 0.5', yMax: 1, yFmt: v => v.toFixed(2)
  });
  $('aval-out').innerHTML = table(['function', 'mean fraction of flipped output bits'], [
    [`EC scalar multiplication, output = ${2 * A.b} bits of (x, y)`, f4(A.aval.ec)],
    [`SHA-256 of k, first ${2 * A.b} bits`, f4(A.aval.hash)],
    ['EC baseline: two <em>independent</em> points with the same bit frequencies', f4(A.baseline)]
  ]) + `<p class="meta">${A.aval.pairs} (k, flipped-k) pairs tested.</p>`;

  renderBasePoints();
}

function renderBasePoints() {
  const c = S.curve, p = c.p;
  if (p > 1009) {
    $('bp-out').innerHTML = '<p class="meta">Table only computed for p ≤ 1009 (orders are found by brute force).</p>';
    return;
  }
  const rows = S.pts.slice(0, 24).map(G => {
    const o = pointOrder(G, c), kk = S.k % o;
    const Q = kk === 0 ? null : scalarMul(kk, G, c);
    return [fmtPt(G), String(o), kk === 0 ? `k ≡ 0 (mod ${o}) → O` : fmtPt(Q), String(Q ? Q.x : '—')];
  });
  $('bp-out').innerHTML = table(['base point G', 'order of G', `Q = ${S.k}·G`, 'x(Q)'], rows);
}

function runScaling() {
  $('btn-scale').disabled = true;
  $('scale-out').innerHTML = '<p class="meta">Running…</p>';
  setTimeout(() => {
    const rows = PRIMES.map(p => {
      const c = makeCurve(p), pts = getPoints(p);
      const { G, n } = chooseBasePoint(c, pts, pts.length + 1);
      const A = analyse(c, G, n, 4096);
      const lowBias = A.bitsX.slice(1).concat(A.bitsY.slice(1)).reduce((s, f) => s + Math.abs(f - 0.5), 0) / (2 * (A.b - 1));
      return [String(p), p % 3 === 1 ? '1' : '2', fmtPt(G), String(n), `${(100 * A.distinctX / p).toFixed(1)} %`,
        f4(A.corr.kx), f4(lowBias), f3(A.aval.ec), f3(A.baseline), f3(A.aval.hash)];
    });
    $('scale-out').innerHTML = table(['p', 'p mod 3', 'G', 'order n', 'x-values reached', 'r(k, x)', 'mean |P(bit)−½| (non-top bits)', 'avalanche EC', 'EC baseline', 'avalanche SHA-256'], rows);
    $('btn-scale').disabled = false;
  }, 30);
}

/* ---------- wiring ---------- */

function recompute() {
  stopViz();
  try {
    readParams();
  } catch (e) {
    $('params-out').textContent = 'Invalid parameters.';
    return;
  }
  if (!(S.k >= 1 && S.k <= S.n - 1)) {
    $('params-out').innerHTML = `<strong>k must be an integer in 1 … ${S.n - 1}</strong> (the order of G is n = ${S.n}; ` +
      `kG repeats with period n). Choose another k or base point.`;
    return;
  }
  renderParams();
  renderMultiples();
  renderTrace();
  initViz();
  renderStats();
}

function onPrimeChange() {
  const p = +$('sel-p').value;
  S.curve = makeCurve(p);
  S.pts = getPoints(p);
  let G, n;
  if (p === 17) { G = { x: 1, y: 5 }; n = pointOrder(G, S.curve); }
  else ({ G, n } = chooseBasePoint(S.curve, S.pts, S.pts.length + 1));
  fillBasePoints(G);
  $('inp-k').value = p === 17 ? 6 : Math.max(2, Math.floor(n * 0.4142));
  recompute();
}

function init() {
  $('sel-p').innerHTML = PRIMES.map(p => `<option value="${p}">${p}${p === 17 ? ' (assignment)' : ''}</option>`).join('');
  $('sel-p').value = '17';
  $('sel-p').addEventListener('change', onPrimeChange);
  $('sel-g').addEventListener('change', recompute);
  $('inp-k').addEventListener('change', recompute);
  $('btn-rand').addEventListener('click', () => {
    $('inp-k').value = 1 + Math.floor(Math.random() * Math.max(1, S.n - 1));
    recompute();
  });
  $('btn-reset').addEventListener('click', () => { $('sel-p').value = '17'; onPrimeChange(); });
  $('btn-scale').addEventListener('click', runScaling);

  $('viz-method').addEventListener('change', () => { viz.method = $('viz-method').value; initViz(); });
  $('viz-reset').addEventListener('click', () => { stopViz(); viz.t = -1; drawViz(); });
  $('viz-step').addEventListener('click', () => { stopViz(); vizAdvance(); });
  $('viz-play').addEventListener('click', () => {
    if (viz.playing) { stopViz(); return; }
    if (viz.t >= viz.ops.length * PHASES - 1) viz.t = -1;
    viz.playing = true;
    $('viz-play').textContent = '⏸ Pause';
    vizTick();
  });
  onPrimeChange();
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
}

if (typeof module !== 'undefined') {
  module.exports = {
    mod, modInv, makeCurve, isOnCurve, addDetailed, add, naiveOps, doubleAddOps, scalarMul, pointOrder,
    allPoints, multiplesSequence, analyse, avalanche, sha256First32, homomorphismCheck, chooseBasePoint,
    bitFrequencies, pearson, histogram, chiSquare
  };
}
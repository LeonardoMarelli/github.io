'use strict';

/* ==========================================================================
   HMWK 1 - Public-key cryptography: private key k -> public key Q = kG
   Toy elliptic curve:  y^2 = x^3 + a*x + b   (mod p)
   Everything below uses plain integers (Number); the curves are tiny on purpose.
   ========================================================================== */

const CURVES = [
  { label: 'Curve A - main example', p: 17, a: 0, b: 7, G: [1, 5], k: 6 },
  { label: 'Curve B - larger prime, same equation form', p: 1019, a: 0, b: 7, G: null, k: 1234 },
];

const INF = null;        // point at infinity O (identity element of the group)
const SAMPLES = 300;     // random scalars used in the avalanche test
const INPUT_BITS = 12;   // scalars for the avalanche test are in 1 .. 2^12 - 1

/* ---------- modular arithmetic ---------- */

const mod = (n, p) => ((n % p) + p) % p;

// Modular inverse with the extended Euclidean algorithm.
function modInv(a, p) {
  let r0 = mod(a, p), r1 = p;
  let s0 = 1, s1 = 0;
  while (r1 !== 0) {
    const q = Math.floor(r0 / r1);
    [r0, r1] = [r1, r0 - q * r1];
    [s0, s1] = [s1, s0 - q * s1];
  }
  if (r0 !== 1) throw new Error(`${a} has no inverse mod ${p}`);
  return mod(s0, p);
}

/* ---------- elliptic-curve group law ---------- */

function isOnCurve(P, c) {
  if (P === INF) return true;
  return mod(P.y * P.y, c.p) === mod(P.x ** 3 + c.a * P.x + c.b, c.p);
}

// Point addition (chord-and-tangent rule).
function pointAdd(P, Q, c) {
  if (P === INF) return Q;
  if (Q === INF) return P;
  if (P.x === Q.x && mod(P.y + Q.y, c.p) === 0) return INF;   // P + (-P) = O

  let lambda;
  if (P.x === Q.x) {
    // P = Q: slope of the tangent
    lambda = mod((3 * P.x * P.x + c.a) * modInv(2 * P.y, c.p), c.p);
  } else {
    // P != Q: slope of the chord
    lambda = mod((Q.y - P.y) * modInv(Q.x - P.x, c.p), c.p);
  }
  const x = mod(lambda * lambda - P.x - Q.x, c.p);
  const y = mod(lambda * (P.x - x) - P.y, c.p);
  return { x, y };
}

// Scalar multiplication kP by double-and-add (O(log k) group operations).
function scalarMult(k, P, c) {
  let result = INF;
  let addend = P;
  let n = k;
  while (n > 0) {
    if (n % 2 === 1) result = pointAdd(result, addend, c);
    addend = pointAdd(addend, addend, c);
    n = Math.floor(n / 2);
  }
  return result;
}

// Order n of a point: the smallest n >= 1 with nP = O.
function orderOf(P, c) {
  let Q = P;
  let n = 1;
  while (Q !== INF) {
    Q = pointAdd(Q, P, c);
    n++;
  }
  return n;
}

// All affine points (x, y) with 0 <= x, y < p satisfying the curve equation.
function allPoints(c) {
  const pts = [];
  for (let x = 0; x < c.p; x++) {
    const rhs = mod(x ** 3 + c.a * x + c.b, c.p);
    for (let y = 0; y < c.p; y++) {
      if (mod(y * y, c.p) === rhs) pts.push({ x, y });
    }
  }
  return pts;
}

/* ---------- helpers ---------- */

const bitLength = n => n.toString(2).length;

// Bits of v, most significant first, padded to L bits.
function toBits(v, L) {
  const out = [];
  for (let j = L - 1; j >= 0; j--) out.push((v >> j) & 1);
  return out;
}

const mean = arr => arr.reduce((s, v) => s + v, 0) / arr.length;

function pearson(a, b) {
  const ma = mean(a), mb = mean(b);
  let num = 0, da = 0, db = 0;
  for (let i = 0; i < a.length; i++) {
    const u = a[i] - ma, v = b[i] - mb;
    num += u * v;
    da += u * u;
    db += v * v;
  }
  return da && db ? num / Math.sqrt(da * db) : NaN;
}

const pct = v => (100 * v).toFixed(1) + '%';
const fmt = P => (P === INF ? 'O (point at infinity)' : `(${P.x}, ${P.y})`);
const same = (P, Q) => (P === INF || Q === INF ? P === Q : P.x === Q.x && P.y === Q.y);

function bitFreq(values, L) {
  const f = Array(L).fill(0);
  values.forEach(v => toBits(v, L).forEach((bit, j) => { f[j] += bit; }));
  return f.map(s => s / values.length);
}

function histogram(values, p, label) {
  const counts = Array(p).fill(0);
  values.forEach(v => { counts[v]++; });
  const lines = [`Frequency of ${label} values:`];
  counts.forEach((cnt, v) => lines.push(`  ${String(v).padStart(3)} | ${'#'.repeat(cnt)} ${cnt}`));
  return lines;
}

// Avalanche test: flip each input bit of k and measure how many output bits change.
function avalanche(G, c, L) {
  let rng = 2024;
  const next = () => (rng = (Math.imul(rng, 1664525) + 1013904223) >>> 0);
  const enc = P => [...toBits(P.x, L), ...toBits(P.y, L)];
  const perBit = Array(INPUT_BITS).fill(0);
  const trials = Array(INPUT_BITS).fill(0);

  for (let s = 0; s < SAMPLES; s++) {
    const k = 1 + (next() % ((1 << INPUT_BITS) - 1));
    const P = scalarMult(k, G, c);
    if (P === INF) continue;
    const e1 = enc(P);

    for (let i = 0; i < INPUT_BITS; i++) {
      const k2 = k ^ (1 << i);
      if (k2 === 0) continue;
      const Q = scalarMult(k2, G, c);
      if (Q === INF) continue;
      const e2 = enc(Q);
      const diff = e1.reduce((d, bit, j) => d + (bit !== e2[j] ? 1 : 0), 0);
      perBit[i] += diff / e1.length;
      trials[i]++;
    }
  }
  return perBit.map((v, i) => (trials[i] ? v / trials[i] : NaN));
}

/* ---------- DOM helpers ---------- */

function el(tag, text, cls) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (cls) node.className = cls;
  return node;
}

function makeTable(headers, rows) {
  const table = el('table');
  const head = el('tr');
  headers.forEach(h => head.appendChild(el('th', h)));
  table.appendChild(head);
  rows.forEach(r => {
    const tr = el('tr');
    r.forEach(cell => tr.appendChild(el('td', String(cell))));
    table.appendChild(tr);
  });
  return table;
}

/* ---------- report for one curve ---------- */

function buildCurveReport(spec) {
  const c = { p: spec.p, a: spec.a, b: spec.b };
  const L = bitLength(c.p);
  const section = el('section');
  section.appendChild(el('h2', spec.label));

  const pts = allPoints(c);

  // Base point: given explicitly, or the one with the largest order among the first candidates.
  let G;
  if (spec.G) {
    G = { x: spec.G[0], y: spec.G[1] };
  } else {
    const candidates = pts.slice(0, 40);
    G = candidates.reduce((best, P) => (orderOf(P, c) > orderOf(best, c) ? P : best), candidates[0]);
  }
  if (!isOnCurve(G, c)) throw new Error('Base point is not on the curve');
  const n = orderOf(G, c);

  const out = [];

  // ---- curve and base point ----
  out.push(`Curve:            y^2 = x^3 + ${c.a}*x + ${c.b}  (mod ${c.p})`);
  out.push(`Points on curve:  ${pts.length} affine points, plus the point at infinity O`);
  out.push(`Base point G:     ${fmt(G)}   (on curve: ${isOnCurve(G, c)})`);
  out.push(`Order of G:       n = ${n}   (nG = O)`);

  // ---- multiples G, 2G, ..., kG ----
  out.push('');
  out.push('--- Multiples of G by repeated addition ---');
  let R = INF;
  const shown = Math.min(spec.k, 12);
  for (let i = 1; i <= shown; i++) {
    R = pointAdd(R, G, c);
    out.push(`${String(i).padStart(4)}G = ${fmt(R)}`);
  }
  if (spec.k > shown) out.push(`  ... (first ${shown} shown)`);

  // ---- private key -> public key ----
  const Q = scalarMult(spec.k, G, c);
  let slow = INF;
  for (let i = 0; i < spec.k; i++) slow = pointAdd(slow, G, c);

  out.push('');
  out.push(`Private key:      k = ${spec.k}   (k mod n = ${spec.k % n})`);
  out.push(`TOY PUBLIC KEY:   Q = kG = ${fmt(Q)}`);
  out.push(`Check: double-and-add and repeated addition agree: ${same(Q, slow)}`);

  // ---- statistics over one full period ----
  out.push('');
  out.push(`--- Statistics over one full period (k = 1 .. n-1) ---`);
  const xs = [], ys = [];
  let P = INF;
  for (let k = 1; k < n; k++) {
    P = pointAdd(P, G, c);
    xs.push(P.x);
    ys.push(P.y);
  }
  const ks = xs.map((_, i) => i + 1);

  out.push(`Samples: ${xs.length} points; every point of <G> appears exactly once.`);
  out.push(`Mean x = ${mean(xs).toFixed(2)}, mean y = ${mean(ys).toFixed(2)}` +
           `   (a uniform value on 0..${c.p - 1} would average ${((c.p - 1) / 2).toFixed(2)})`);
  out.push(`Distinct x values: ${new Set(xs).size} / ${c.p}   ` +
           `distinct y values: ${new Set(ys).size} / ${c.p}`);

  if (c.p <= 40) {
    out.push('');
    out.push(...histogram(xs, c.p, 'x'));
    out.push('');
    out.push(...histogram(ys, c.p, 'y'));
  }

  const fx = bitFreq(xs, L), fy = bitFreq(ys, L);
  out.push('');
  out.push('Bit balance (fraction of 1s; bit 1 = most significant):');
  for (let j = 0; j < L; j++) {
    out.push(`  bit ${j + 1}:  x ${pct(fx[j])}   y ${pct(fy[j])}`);
  }

  out.push('');
  out.push('--- Correlations ---');
  out.push(`Pearson r(k, x)       = ${pearson(ks, xs).toFixed(3)}`);
  out.push(`Pearson r(k, y)       = ${pearson(ks, ys).toFixed(3)}`);
  out.push(`Serial r(x_k, x_k+1)  = ${pearson(xs.slice(0, -1), xs.slice(1)).toFixed(3)}`);
  out.push(`Serial r(y_k, y_k+1)  = ${pearson(ys.slice(0, -1), ys.slice(1)).toFixed(3)}`);

  // ---- avalanche ----
  out.push('');
  out.push(`--- Avalanche test (${SAMPLES} random k in 1..${(1 << INPUT_BITS) - 1}; ideal for a hash ~ 50%) ---`);
  const aval = avalanche(G, c, L);
  aval.forEach((v, i) => out.push(`  flip bit ${i} of k: ${pct(v)} of the ${2 * L} output bits change`));
  out.push(`  average: ${pct(mean(aval.filter(v => !Number.isNaN(v))))}`);

  section.appendChild(el('pre', out.join('\n'), 'output'));

  // ---- orders of all points: other valid base points ----
  if (pts.length <= 60) {
    section.appendChild(el('h3', 'Order of every point on this curve (other possible base points)'));
    const rows = [['O', 1], ...pts.map(Pt => [fmt(Pt), orderOf(Pt, c)])];
    section.appendChild(makeTable(['Point', 'Order'], rows));
  }

  return section;
}

/* ---------- main ---------- */

function main() {
  const root = document.getElementById('results');
  if (!root) return;
  try {
    CURVES.forEach(spec => root.appendChild(buildCurveReport(spec)));
  } catch (err) {
    root.appendChild(el('p', `Error: ${err.message}`));
  }
}

/* ---------- interactive tool (curve A only, as in the assignment) ---------- */

// Text explaining how P + Q is computed, with the slope lambda.
function slopeText(P, Q, c) {
  if (P === INF) return 'O + Q = Q';
  if (Q === INF) return 'P + O = P';
  if (P.x === Q.x && mod(P.y + Q.y, c.p) === 0) return 'P + (-P) = O';
  if (P.x === Q.x) {
    const num = mod(3 * P.x * P.x + c.a, c.p);
    const den = mod(2 * P.y, c.p);
    const lam = mod(num * modInv(den, c.p), c.p);
    return `doubling: λ = (3·${P.x}² + ${c.a}) / (2·${P.y}) ≡ ${num}/${den} ≡ ${lam} (mod ${c.p})`;
  }
  const num = mod(Q.y - P.y, c.p);
  const den = mod(Q.x - P.x, c.p);
  const lam = mod(num * modInv(den, c.p), c.p);
  return `λ = (${Q.y} - ${P.y}) / (${Q.x} - ${P.x}) ≡ ${num}/${den} ≡ ${lam} (mod ${c.p})`;
}

// Grid of the whole curve: G, Q, the multiples of G (subgroup) and the other points.
function gridTable(c, onCurve, subgroup, G, Q) {
  const t = el('table');

  for (let y = c.p - 1; y >= 0; y--) {
    const tr = el('tr');
    tr.appendChild(el('th', String(y)));
    for (let x = 0; x < c.p; x++) {
      const key = `${x},${y}`;
      let mark = '';
      if (G && x === G.x && y === G.y) mark = 'G';
      else if (Q && x === Q.x && y === Q.y) mark = 'Q';
      else if (subgroup.has(key)) mark = '•';
      else if (onCurve.has(key)) mark = '·';
      const td = el('td', mark);
      td.style.padding = '2px 4px';
      td.style.textAlign = 'center';
      tr.appendChild(td);
    }
    t.appendChild(tr);
  }

  // x labels go at the bottom, so the origin (0, 0) is the bottom-left corner
  const foot = el('tr');
  foot.appendChild(el('th', 'y \\ x'));
  for (let x = 0; x < c.p; x++) foot.appendChild(el('th', String(x)));
  t.appendChild(foot);

  return t;
}

// The real-number curve y^2 = x^3 + 7, drawn with the origin at the bottom-left.
// This is only for intuition: the homework computes on the same equation mod 17.

function buildInteractive() {
  const root = document.getElementById('interactive');
  if (!root) return;

  const spec = CURVES[0];
  const c = { p: spec.p, a: spec.a, b: spec.b };
  const pts = allPoints(c);
  const onCurve = new Set(pts.map(P => `${P.x},${P.y}`));

  // Controls
  const controls = el('div', undefined, 'card');

  const kLabel = el('label', 'Private key k (1 to 50): ');
  const kInput = el('input');
  kInput.type = 'number';
  kInput.min = '1';
  kInput.max = '50';
  kInput.value = String(spec.k);
  kLabel.appendChild(kInput);

  const gLabel = el('label', 'Base point G: ');
  const gSelect = el('select');
  pts.forEach(P => {
    const opt = el('option', fmt(P));
    opt.value = `${P.x},${P.y}`;
    gSelect.appendChild(opt);
  });
  gSelect.value = `${spec.G[0]},${spec.G[1]}`;
  gLabel.appendChild(gSelect);

  controls.append(kLabel, ' ', gLabel);

  const output = el('div');
  root.append(controls, output);

  const render = () => {
    output.textContent = '';
    const k = Number(kInput.value);
    if (!Number.isInteger(k) || k < 1 || k > 50) {
      output.appendChild(el('p', 'Please enter an integer k between 1 and 50.'));
      return;
    }

    const [gx, gy] = gSelect.value.split(',').map(Number);
    const G = { x: gx, y: gy };
    const n = orderOf(G, c);
    const Q = scalarMult(k, G, c);

    // Step-by-step table: each row adds G to the previous multiple
    const rows = [];
    let R = INF;
    for (let i = 1; i <= k; i++) {
      const prev = R;
      R = pointAdd(R, G, c);
      rows.push([
        `${i}G`,
        prev === INF ? 'O' : fmt(prev),
        prev === INF ? 'O + G = G' : slopeText(prev, G, c),
        fmt(R),
      ]);
    }

    output.appendChild(el('p', `Toy public key: Q = ${k}G = ${fmt(Q)}   ` +
      `(order of G: n = ${n}; k mod n = ${k % n})`));
    output.appendChild(makeTable(['Step', 'Previous point', 'How it is computed', 'Result'], rows));

    // Subgroup generated by G
    const subgroup = new Set();
    let P = INF;
    for (let i = 1; i <= n; i++) {
      P = pointAdd(P, G, c);
      if (P !== INF) subgroup.add(`${P.x},${P.y}`);
    }

    output.appendChild(el('h3', 'Where the points sit on the curve'));
    const wrap = el('div', undefined, 'output');
    wrap.appendChild(gridTable(c, onCurve, subgroup, G, Q));
    output.appendChild(wrap);
  };

  kInput.addEventListener('input', render);
  gSelect.addEventListener('change', render);
  render();
}

document.addEventListener('DOMContentLoaded', () => {
  main();
  buildInteractive();
});
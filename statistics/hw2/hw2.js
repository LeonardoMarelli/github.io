// HMWK 2 - From a mnemonic to an Ethereum address
// Pipeline: mnemonic -> BIP-39 seed -> BIP-32 master key -> BIP-44 path -> private key
//           -> secp256k1 public key -> Keccak-256 -> address -> EIP-55 checksum
// Libraries are loaded as ES modules from jsDelivr. Nothing is sent to any server.

import {
  generateMnemonic,
  mnemonicToSeedSync,
  validateMnemonic,
} from 'https://cdn.jsdelivr.net/npm/@scure/bip39@1.3.0/+esm';
import { wordlist } from 'https://cdn.jsdelivr.net/npm/@scure/bip39@1.3.0/wordlists/english/+esm';
import { HDKey } from 'https://cdn.jsdelivr.net/npm/@scure/bip32@1.4.0/+esm';
import { secp256k1 } from 'https://cdn.jsdelivr.net/npm/@noble/curves@1.4.0/secp256k1/+esm';
import { keccak_256, sha3_256 } from 'https://cdn.jsdelivr.net/npm/@noble/hashes@1.4.0/sha3/+esm';
import { bytesToHex, utf8ToBytes } from 'https://cdn.jsdelivr.net/npm/@noble/hashes@1.4.0/utils/+esm';

/* =====================================================================
   1. Pure logic (no DOM, so it can be tested in Node)
   ===================================================================== */

// Test vector: public, widely used, and NEVER to be used with real funds.
export const TEST_MNEMONIC =
  'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about';
export const DEFAULT_PATH = "m/44'/60'/0'/0/0";   // BIP-44 path used by Ethereum wallets
const SECP_N = secp256k1.CURVE.n;

/* ---------- EIP-55 checksum ---------- */

// Mixed-case checksum: hash the lowercase hex address with Keccak-256,
// then uppercase a letter when the matching hash nibble is 8 or higher.
export function toEip55(addrLower) {
  const lower = addrLower.toLowerCase();
  const h = bytesToHex(keccak_256(utf8ToBytes(lower)));
  let body = '';
  for (let i = 0; i < 40; i++) {
    body += parseInt(h[i], 16) >= 8 ? lower[i].toUpperCase() : lower[i];
  }
  return '0x' + body;
}

// Returns whether a string is a valid address and why.
export function checkAddress(address) {
  if (!/^0x[0-9a-fA-F]{40}$/.test(address)) {
    return { ok: false, reason: 'Not an address: it must be 0x followed by 40 hex characters.' };
  }
  const body = address.slice(2);
  if (body === body.toLowerCase() || body === body.toUpperCase()) {
    return { ok: true, reason: 'All lowercase or all uppercase: valid hex, but no checksum is applied.' };
  }
  const ok = toEip55(body) === address;
  return {
    ok,
    reason: ok
      ? 'Mixed case and matches the EIP-55 checksum.'
      : 'Mixed case but the case pattern does not match the checksum: the address was mistyped or altered.',
  };
}

/* ---------- full pipeline ---------- */

// Runs every step and keeps the intermediate values so the page can show them.
export function deriveAccount(mnemonic, path = DEFAULT_PATH, passphrase = '') {
  const valid = validateMnemonic(mnemonic.trim(), wordlist);
  if (!valid) throw new Error('Mnemonic is not valid: check the words and the checksum word.');

  const words = mnemonic.trim().split(/\s+/);
  const seed = mnemonicToSeedSync(mnemonic.trim(), passphrase);   // PBKDF2-HMAC-SHA512, 2048 rounds
  const master = HDKey.fromMasterSeed(seed);                      // HMAC-SHA512 with key "Bitcoin seed"
  const node = master.derive(path);                               // BIP-32 child derivation along the path
  const priv = node.privateKey;

  const pubUncompressed = secp256k1.getPublicKey(priv, false);    // 65 bytes: 0x04 || x || y
  const pubCompressed = secp256k1.getPublicKey(priv, true);       // 33 bytes: prefix || x
  const hash = keccak_256(pubUncompressed.slice(1));              // Keccak-256 of the 64-byte body
  const addrLower = bytesToHex(hash.slice(-20));                  // last 20 bytes
  const address = toEip55(addrLower);

  return {
    words,
    valid,
    seed,
    masterPriv: master.privateKey,
    masterChain: master.chainCode,
    path,
    pathParts: path.split('/').slice(1).map(p => ({ text: p, hardened: p.endsWith("'") })),
    priv,
    pubUncompressed,
    pubCompressed,
    hash,
    addrLower,
    address,
  };
}

/* ---------- hashing comparisons ---------- */

export const keccakEmpty = () => bytesToHex(keccak_256(utf8ToBytes('')));
export const sha3Empty = () => bytesToHex(sha3_256(utf8ToBytes('')));

/* ---------- statistics ---------- */

function popcountXor(a, b) {
  let d = 0;
  for (let i = 0; i < a.length; i++) {
    let v = a[i] ^ b[i];
    while (v) { d += v & 1; v >>= 1; }
  }
  return d;
}

// Avalanche for Keccak-256: flip one input bit, count changed output bits.
export function keccakAvalanche(samples = 16) {
  const totals = Array(256).fill(0);
  for (let s = 0; s < samples; s++) {
    const base = keccak_256(utf8ToBytes('hw2-msg-' + s));   // 32-byte input
    const h1 = keccak_256(base);
    for (let i = 0; i < 256; i++) {
      const msg = base.slice();
      msg[i >> 3] ^= 1 << (7 - (i & 7));
      totals[i] += popcountXor(h1, keccak_256(msg)) / 256;
    }
  }
  return totals.map(t => t / samples);
}

// Avalanche for secp256k1: flip one bit of the private key, count changed bits of the x-coordinate.
export function secpAvalanche(keys = 2, bits = 64) {
  const totals = Array(bits).fill(0);
  for (let s = 0; s < keys; s++) {
    const k = keccak_256(utf8ToBytes('hw2-key-' + s));
    const kBig = BigInt('0x' + bytesToHex(k)) % (SECP_N - 1n) + 1n;
    const base = hexToBytes32(kBig);
    const x1 = secp256k1.getPublicKey(base, true).slice(1);
    for (let i = 0; i < bits; i++) {
      const flipped = base.slice();
      flipped[31 - (i >> 3)] ^= 1 << (i & 7);     // flip bit i of the low-order bytes
      const v = BigInt('0x' + bytesToHex(flipped));
      if (v === 0n || v >= SECP_N) continue;
      const x2 = secp256k1.getPublicKey(flipped, true).slice(1);
      totals[i] += popcountXor(x1, x2) / 256;
    }
  }
  return totals.map(t => t / keys);
}

function hexToBytes32(big) {
  const hex = big.toString(16).padStart(64, '0');
  const out = new Uint8Array(32);
  for (let i = 0; i < 32; i++) out[i] = parseInt(hex.slice(2 * i, 2 * i + 2), 16);
  return out;
}

// Address statistics over many keys: hex digit frequencies and EIP-55 uppercase share.
export function addressStats(count = 256) {
  const digitCounts = Array(16).fill(0);
  let letters = 0, upper = 0, made = 0;
  for (let i = 0; i < count; i++) {
    const k = keccak_256(utf8ToBytes('hw2-addr-' + i));
    const kBig = BigInt('0x' + bytesToHex(k));
    if (kBig === 0n || kBig >= SECP_N) continue;
    const pub = secp256k1.getPublicKey(hexToBytes32(kBig), false);
    const addrLower = bytesToHex(keccak_256(pub.slice(1)).slice(-20));
    const checksummed = toEip55(addrLower).slice(2);
    made++;
    for (const ch of addrLower) digitCounts[parseInt(ch, 16)]++;
    for (const ch of checksummed) {
      if (/[a-fA-F]/.test(ch)) { letters++; if (ch === ch.toUpperCase()) upper++; }
    }
  }
  const total = digitCounts.reduce((a, b) => a + b, 0);
  const e = total / 16;
  const chi2 = digitCounts.reduce((s, c) => s + (c - e) ** 2 / e, 0);
  return { made, digitCounts, chi2, upperShare: upper / letters, letters };
}

// Error detection: change the case of every letter in an address and count how many changes are caught.
export function caseFlipDetection(address) {
  const body = address.slice(2);
  let flips = 0, caught = 0;
  for (let i = 0; i < body.length; i++) {
    const ch = body[i];
    if (!/[a-fA-F]/.test(ch)) continue;
    const flipped = body.slice(0, i) + (ch === ch.toLowerCase() ? ch.toUpperCase() : ch.toLowerCase()) + body.slice(i + 1);
    flips++;
    if (!checkAddress('0x' + flipped).ok) caught++;
  }
  return { flips, caught };
}

// Chi-square statistic against a uniform distribution.
export function chiSquareUniform(counts) {
  const total = counts.reduce((a, b) => a + b, 0);
  const e = total / counts.length;
  return counts.reduce((s, c) => s + (c - e) ** 2 / e, 0);
}

/* =====================================================================
   2. Page (only runs in the browser)
   ===================================================================== */

function el(tag, text, cls) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (cls) node.className = cls;
  return node;
}

function card(title, lines, cls = 'output') {
  const wrap = el('div', undefined, 'card');
  wrap.style.marginBottom = '12px';
  wrap.appendChild(el('h3', title));
  wrap.appendChild(el('pre', lines.join('\n'), cls));
  return wrap;
}

function renderPipeline(acc) {
  const root = document.getElementById('pipeline');
  root.textContent = '';

  root.appendChild(card('Step 1. Mnemonic (BIP-39)', [
    `Words: ${acc.words.length}`,
    `Checksum valid: ${acc.valid}`,
    'The last word carries a checksum: SHA-256 of the entropy, its first bits appended.',
  ]));

  root.appendChild(card('Step 2. Seed (BIP-39)', [
    'PBKDF2-HMAC-SHA512, 2048 rounds, salt = "mnemonic" + passphrase.',
    `Seed (64 bytes): ${bytesToHex(acc.seed)}`,
  ]));

  root.appendChild(card('Step 3. Master key (BIP-32)', [
    'HMAC-SHA512 with key "Bitcoin seed" applied to the seed.',
    `Master private key: ${bytesToHex(acc.masterPriv)}`,
    `Master chain code:  ${bytesToHex(acc.masterChain)}`,
  ]));

  const pathLines = [`Path: ${acc.path}`];
  acc.pathParts.forEach((p, i) => {
    pathLines.push(`  level ${i + 1}: ${p.text}  ${p.hardened ? '(hardened)' : '(normal)'}`);
  });
  root.appendChild(card('Step 4. Derivation path (BIP-32 / BIP-44)', pathLines));

  root.appendChild(card('Step 5. Private key (32 bytes)', [
    bytesToHex(acc.priv),
  ]));

  root.appendChild(card('Step 6. Public key (secp256k1)', [
    `Uncompressed (65 bytes): ${bytesToHex(acc.pubUncompressed)}`,
    `Compressed (33 bytes):   ${bytesToHex(acc.pubCompressed)}`,
  ]));

  root.appendChild(card('Step 7. Hash and address (Keccak-256)', [
    'Keccak-256 of the 64-byte public key (without the 0x04 prefix).',
    `Hash: ${bytesToHex(acc.hash)}`,
    `Address = last 20 bytes, lowercase: 0x${acc.addrLower}`,
  ]));

  // EIP-55 display with uppercase letters in bold
  const eipWrap = el('div', undefined, 'card');
  eipWrap.style.marginBottom = '12px';
  eipWrap.appendChild(el('h3', 'Step 8. Checksum (EIP-55)'));
  eipWrap.appendChild(el('p', 'Letters that appear uppercase are the checksum; the rest is the address itself.'));
  const addrEl = el('pre', undefined, 'output');
  addrEl.appendChild(document.createTextNode('0x'));
  for (const ch of acc.address.slice(2)) {
    if (/[A-F]/.test(ch)) {
      const s = el('strong', ch);
      addrEl.appendChild(s);
    } else {
      addrEl.appendChild(document.createTextNode(ch));
    }
  }
  eipWrap.appendChild(addrEl);
  root.appendChild(eipWrap);
}

function renderStats(out) {
  const root = document.getElementById('stats');
  root.textContent = '';
  out.forEach(block => root.appendChild(block));
}

function runStatistics() {
  const blocks = [];
  const t0 = performance.now();

  const kav = keccakAvalanche(16);
  const kMean = kav.reduce((a, b) => a + b, 0) / kav.length;
  blocks.push(card('Keccak-256 avalanche (1 flipped input bit, 16 messages)', [
    `Mean fraction of output bits changed: ${(100 * kMean).toFixed(1)}%  (ideal for a hash: 50%)`,
    `Range over the 256 input bit positions: ${(100 * Math.min(...kav)).toFixed(1)}% .. ${(100 * Math.max(...kav)).toFixed(1)}%`,
  ]));

  const sav = secpAvalanche(2, 64);
  const sMean = sav.reduce((a, b) => a + b, 0) / sav.length;
  blocks.push(card('secp256k1 avalanche (flip one low bit of the private key)', [
    `Mean fraction of x-coordinate bits changed: ${(100 * sMean).toFixed(1)}%`,
    'Scalar multiplication also looks random bit by bit, but the algebraic structure is still there: (k+1)G = kG + G.',
  ]));

  const st = addressStats(256);
  const chi = st.chi2;
  blocks.push(card('Address hex digits and EIP-55 case (256 keys)', [
    `Addresses generated: ${st.made}`,
    `Hex digit counts (0..f): ${st.digitCounts.join(' ')}`,
    `Chi-square vs uniform (15 degrees of freedom): ${chi.toFixed(2)}  (critical value at 5%: 25.00)`,
    `Share of letters uppercased by the checksum: ${(100 * st.upperShare).toFixed(1)}%  (ideal: 50%)`,
  ]));

  blocks.push(card('Timing', [`Statistics computed in ${((performance.now() - t0) / 1000).toFixed(2)} s`]));
  renderStats(blocks);
}

function init() {
  const mnemonicEl = document.getElementById('mnemonic');
  const passEl = document.getElementById('passphrase');
  const pathEl = document.getElementById('path');
  const errEl = document.getElementById('error');

  mnemonicEl.value = TEST_MNEMONIC;
  pathEl.value = DEFAULT_PATH;

  const derive = () => {
    errEl.textContent = '';
    try {
      renderPipeline(deriveAccount(mnemonicEl.value, pathEl.value.trim(), passEl.value));
    } catch (err) {
      errEl.textContent = err.message;
      document.getElementById('pipeline').textContent = '';
    }
  };

  document.getElementById('derive').addEventListener('click', derive);
  document.getElementById('new-mnemonic').addEventListener('click', () => {
    mnemonicEl.value = generateMnemonic(wordlist, 128);
    derive();
  });
  document.getElementById('run-stats').addEventListener('click', runStatistics);

  const checkInput = document.getElementById('check-input');
  const checkOut = document.getElementById('check-output');
  const runCheck = () => {
    const r = checkAddress(checkInput.value.trim());
    checkOut.textContent = (r.ok ? 'VALID  - ' : 'INVALID - ') + r.reason;
  };
  document.getElementById('check-btn').addEventListener('click', runCheck);
  document.getElementById('flip-btn').addEventListener('click', () => {
    const addr = checkInput.value.trim();
    const d = caseFlipDetection(addr);
    checkOut.textContent = `Changing the case of one letter at a time: ${d.caught} of ${d.flips} changes are detected.`;
  });
  checkInput.value = '0x9858EfFD232B4033E47d90003D41EC34EcaEda94';

  derive();
  document.getElementById('hashes').textContent =
    `keccak256("") = ${keccakEmpty()}\nsha3_256("")  = ${sha3Empty()}`;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', init);
}
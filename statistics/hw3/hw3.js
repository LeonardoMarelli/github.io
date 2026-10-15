// HMWK 3 - Caesar cipher vs modern elliptic-curve encryption
// Letter statistics use plain JavaScript. The ECC part uses WebCrypto, which is built into
// the browser (P-256 ECDH, HKDF-SHA-256, AES-256-GCM). No external library is loaded.
// WebCrypto needs a secure context: an https:// page or localhost.

export const SAMPLE_EN =
  'Cryptography has a long history. For centuries, military commanders and diplomats relied on secret ' +
  'writing to protect their plans, and most early methods were simple substitutions. The Caesar cipher is ' +
  'one of the oldest and best known of them. Each letter is moved a fixed number of places along the alphabet, ' +
  'so a message that reads attack at dawn becomes something else entirely. Anyone who knows the shift can read ' +
  'it at once, yet anyone who only sees the output can try the few possible shifts and check which one gives ' +
  'text that looks like the language. Letter frequencies make this check easy, because in ordinary English the ' +
  'letter E appears far more often than Z, and that pattern survives the shift unchanged.';

export const SAMPLE_IT =
  'La crittografia ha una storia lunga. Per secoli i comandanti militari e i diplomatici si sono affidati ' +
  'alla scrittura segreta per proteggere i propri piani, e i metodi più antichi erano semplici sostituzioni. ' +
  'Il cifrario di Cesare è uno dei più antichi e noti. Ogni lettera viene spostata di un numero fisso di ' +
  'posizioni nell\'alfabeto, quindi un messaggio qualsiasi diventa qualcosa di completamente diverso. Chi conosce ' +
  'lo spostamento può leggerlo subito, ma chi vede solo il risultato può provare i pochi spostamenti possibili ' +
  'e verificare quale produce un testo simile alla lingua. Le frequenze delle lettere rendono questo controllo ' +
  'facile, perché nell\'italiano comune la E compare molto più spesso della Z, e questa regolarità resta ' +
  'invariata dopo lo spostamento.';

// Reference letter frequencies in percent, A to Z.
// English: Oxford University Mathematical Institute table (relative frequencies x 100).
export const ENGLISH_FREQ = [
  8.167, 1.492, 2.782, 4.253, 12.702, 2.228, 2.015, 6.094, 6.966, 0.153, 0.772, 4.025, 2.406,
  6.749, 7.507, 1.929, 0.095, 5.987, 6.327, 9.056, 2.758, 0.978, 2.360, 0.150, 1.974, 0.074,
];
// Italian: sttmedia.com character-frequency table. J, K, W, X, Y are not in the Italian
// alphabet, so they get 0.05 instead of 0 to keep the chi-square statistic defined.
export const ITALIAN_FREQ = [
  10.85, 1.05, 4.30, 3.39, 11.49, 1.01, 1.65, 1.43, 10.18, 0.05, 0.05, 5.70, 2.87,
  7.02, 9.97, 2.96, 0.45, 6.19, 5.48, 6.97, 3.16, 1.75, 0.05, 0.05, 0.05, 0.85,
];

// Critical values at the 5% level (chi-square distribution).
export const CRIT_LETTERS_DF25 = 37.65;   // 26 letters, 25 degrees of freedom
export const CRIT_BYTES_DF255 = 293.3;    // 256 byte values, 255 df (Wilson-Hilferty approximation)

/* ---------- Caesar cipher ---------- */

// Shift every letter by k places (k may be negative). Non-letters are left unchanged.
export function shiftText(text, k) {
  const s = ((k % 26) + 26) % 26;
  return text.replace(/[A-Za-z]/g, ch => {
    const base = ch <= 'Z' ? 65 : 97;
    return String.fromCharCode(((ch.charCodeAt(0) - base + s) % 26) + base);
  });
}

// Count letters A-Z, ignoring case, digits, spaces and punctuation.
export function letterCounts(text) {
  const counts = Array(26).fill(0);
  for (const ch of text.toUpperCase()) {
    const i = ch.charCodeAt(0) - 65;
    if (i >= 0 && i < 26) counts[i]++;
  }
  return counts;
}

// Chi-square statistic: sum over letters of (observed - expected)^2 / expected.
// The expected count of letter i is total * freq[i] / sum(freq).
export function chiSquareLetters(counts, freq) {
  const total = counts.reduce((a, b) => a + b, 0);
  if (total === 0) return Infinity;
  const sumFreq = freq.reduce((a, b) => a + b, 0);
  let chi = 0;
  for (let i = 0; i < 26; i++) {
    const expected = (total * freq[i]) / sumFreq;
    chi += (counts[i] - expected) ** 2 / expected;
  }
  return chi;
}

// Try all 26 keys. Candidate key k means: decrypt by shifting back k places.
// Returns the candidates sorted from most to least plausible (lowest chi-square first).
export function rankShifts(cipher, freq) {
  const rows = [];
  for (let k = 0; k < 26; k++) {
    const plain = shiftText(cipher, -k);
    rows.push({ key: k, chi: chiSquareLetters(letterCounts(plain), freq), plain });
  }
  return rows.sort((a, b) => a.chi - b.chi);
}

/* ---------- Modern ECC encryption (ECIES-style) ---------- */

const enc = new TextEncoder();
const dec = new TextDecoder();
const ECDH_PARAMS = { name: 'ECDH', namedCurve: 'P-256' };
const KDF_INFO = enc.encode('hw3-ecies-aes-256-gcm');

// Turn the ECDH shared secret into an AES-256-GCM key with HKDF-SHA-256.
async function deriveAesKey(sharedBits) {
  const base = await crypto.subtle.importKey('raw', sharedBits, 'HKDF', false, ['deriveKey']);
  return crypto.subtle.deriveKey(
    { name: 'HKDF', hash: 'SHA-256', salt: new Uint8Array(0), info: KDF_INFO },
    base,
    { name: 'AES-GCM', length: 256 },
    false,
    ['encrypt', 'decrypt'],
  );
}

export function generateRecipientKeys() {
  return crypto.subtle.generateKey(ECDH_PARAMS, true, ['deriveBits']);
}

// Sender: fresh ephemeral key pair, ECDH with the recipient's public key, AES-GCM encryption.
export async function eccEncrypt(message, recipientPublic) {
  const ephemeral = await crypto.subtle.generateKey(ECDH_PARAMS, false, ['deriveBits']);
  const shared = await crypto.subtle.deriveBits(
    { name: 'ECDH', public: recipientPublic }, ephemeral.privateKey, 256);
  const aesKey = await deriveAesKey(shared);
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const ct = new Uint8Array(await crypto.subtle.encrypt({ name: 'AES-GCM', iv }, aesKey, enc.encode(message)));
  const ephPub = new Uint8Array(await crypto.subtle.exportKey('raw', ephemeral.publicKey));
  return { ephPub, iv, ct };
}

// Recipient: the same ECDH secret is recomputed from the ephemeral public key, then AES-GCM decryption.
export async function eccDecrypt(packet, recipientPrivate) {
  const ephPublic = await crypto.subtle.importKey('raw', packet.ephPub, ECDH_PARAMS, false, []);
  const shared = await crypto.subtle.deriveBits({ name: 'ECDH', public: ephPublic }, recipientPrivate, 256);
  const aesKey = await deriveAesKey(shared);
  const pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: packet.iv }, aesKey, packet.ct);
  return dec.decode(pt);
}

/* ---------- byte statistics ---------- */

export function byteCounts(bytes) {
  const counts = Array(256).fill(0);
  for (const b of bytes) counts[b]++;
  return counts;
}

// Chi-square against a uniform distribution over the 256 byte values.
export function chiSquareUniform(counts) {
  const total = counts.reduce((a, b) => a + b, 0);
  const expected = total / counts.length;
  return counts.reduce((s, c) => s + (c - expected) ** 2 / expected, 0);
}

/* =====================================================================
   Page (runs only in the browser)
   ===================================================================== */

const $ = id => document.getElementById(id);

function el(tag, text, cls) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (cls) node.className = cls;
  return node;
}

function table(headers, rows, highlight = -1) {
  const t = el('table');
  const head = el('tr');
  headers.forEach(h => head.appendChild(el('th', h)));
  t.appendChild(head);
  rows.forEach((r, i) => {
    const tr = el('tr');
    if (i === highlight) tr.style.fontWeight = 'bold';
    r.forEach(cell => tr.appendChild(el('td', String(cell))));
    t.appendChild(tr);
  });
  return t;
}

const pctOf = (count, total) => (total ? ((100 * count) / total).toFixed(1) : '0.0');
const toBase64 = bytes => btoa(Array.from(bytes, b => String.fromCharCode(b)).join(''));
const toHex = (bytes, n) => Array.from(bytes.slice(0, n), b => b.toString(16).padStart(2, '0')).join('');

// ---- Caesar section ----

function reference() {
  const wrap = $('reference');
  if (!wrap) return;
  wrap.textContent = '';
  const rows = LETTERS_LIST().map((L, i) => [L, ENGLISH_FREQ[i].toFixed(2), ITALIAN_FREQ[i].toFixed(2)]);
  wrap.appendChild(table(['Letter', 'English %', 'Italian %'], rows));
}

function LETTERS_LIST() {
  return 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.split('');
}

function analyse() {
  const cipher = $('caesar-cipher-in').value;
  const italian = $('caesar-lang').value === 'italian';
  const freq = italian ? ITALIAN_FREQ : ENGLISH_FREQ;
  const ranked = rankShifts(cipher, freq);
  const best = ranked[0];

  const out = $('caesar-result');
  out.textContent = '';
  out.appendChild(el('p',
    `Most likely key: ${best.key} (chi-square ${best.chi.toFixed(1)}; the critical value at 5% is ${CRIT_LETTERS_DF25}).`));
  out.appendChild(el('pre', best.plain, 'output'));

  const cCounts = letterCounts(cipher);
  const cTotal = cCounts.reduce((a, b) => a + b, 0);
  const dCounts = letterCounts(best.plain);
  const dTotal = dCounts.reduce((a, b) => a + b, 0);
  const sumRef = freq.reduce((a, b) => a + b, 0);
  const rows = LETTERS_LIST().map((L, i) => [
    L,
    ((100 * freq[i]) / sumRef).toFixed(2),
    pctOf(cCounts[i], cTotal),
    pctOf(dCounts[i], dTotal),
  ]);
  out.appendChild(el('h3', 'Letter frequencies: reference, ciphertext and decoded text (%)'));
  out.appendChild(table(['Letter', 'Reference', 'Ciphertext', 'Decoded with best key'], rows));

  out.appendChild(el('h3', 'All 26 keys, ranked by chi-square'));
  const rankRows = ranked.map(r => [r.key, r.chi.toFixed(1), r.plain.slice(0, 50) + '...']);
  out.appendChild(table(['Key', 'Chi-square', 'Decoded start'], rankRows, 0));
  return best;
}

// ---- ECC section ----

let recipient = null;
let lastPacket = null;

async function eccSetup() {
  recipient = await generateRecipientKeys();
  $('ecc-plain').value = SAMPLE_EN;
  await eccEncryptShow(SAMPLE_EN);
  await eccStats();
}

async function eccEncryptShow(text) {
  lastPacket = await eccEncrypt(text, recipient.publicKey);
  const out = $('ecc-out');
  out.textContent = '';
  out.appendChild(table(['Field', 'Value (truncated)', 'Length (bytes)'], [
    ['Ephemeral public key', toHex(lastPacket.ephPub, 16) + '...', lastPacket.ephPub.length],
    ['IV (nonce)', toHex(lastPacket.iv, 12), lastPacket.iv.length],
    ['Ciphertext + GCM tag', toBase64(lastPacket.ct).slice(0, 48) + '...', lastPacket.ct.length],
  ]));
  $('ecc-decrypt-out').textContent = '';
}

async function eccDecryptShow() {
  if (!lastPacket) return;
  const text = await eccDecrypt(lastPacket, recipient.privateKey);
  const original = $('ecc-plain').value;
  $('ecc-decrypt-out').textContent =
    `Decrypted text: ${text}\nMatches the original message: ${text === original}`;
}

// Statistics on a longer ciphertext (the sample repeated 4 times), so each byte value has
// enough expected counts for the chi-square test to be meaningful.
async function eccStats() {
  const long = SAMPLE_EN.repeat(4);
  const p = await eccEncrypt(long, recipient.publicKey);
  const byteChi = chiSquareUniform(byteCounts(p.ct));
  const b64 = toBase64(p.ct).replace(/[^A-Za-z]/g, '');
  const letterCountsB64 = letterCounts(b64);
  const ranked = rankShifts(b64, ENGLISH_FREQ);
  const rows = [
    ['ECC ciphertext bytes vs uniform random (256 values)', byteChi.toFixed(1),
      CRIT_BYTES_DF255, byteChi < CRIT_BYTES_DF255 ? 'consistent with random bytes' : 'not random'],
    ['ECC ciphertext letters (base64) vs English, best shift', ranked[0].chi.toFixed(1),
      CRIT_LETTERS_DF25, ranked[0].chi < CRIT_LETTERS_DF25 ? 'looks like English' : 'not English'],
  ];
  $('ecc-stats').textContent = '';
  $('ecc-stats').appendChild(table(['Test', 'Chi-square', 'Critical (5%)', 'Verdict'], rows));
  $('ecc-stats').appendChild(el('p',
    `Ciphertext length: ${p.ct.length} bytes, so each of the 256 byte values is expected about ` +
    `${(p.ct.length / 256).toFixed(1)} times. Non-letter base64 characters were removed before the letter test.`));
  return { byteChi, letterChi: ranked[0].chi, letterCountsB64 };
}

// ---- comparison section ----

function compare(best) {
  const cipher = $('caesar-cipher-in').value;
  const italian = $('caesar-lang').value === 'italian';
  const freq = italian ? ITALIAN_FREQ : ENGLISH_FREQ;
  const unshifted = chiSquareLetters(letterCounts(cipher), freq);
  const rows = [
    ['Caesar ciphertext vs reference, no decryption', unshifted.toFixed(1),
      unshifted < CRIT_LETTERS_DF25 ? 'looks like the language' : 'does not look like the language'],
    ['Caesar text after best key', best.chi.toFixed(1),
      best.chi < CRIT_LETTERS_DF25 ? 'looks like the language' : 'does not look like the language'],
  ];
  const wrap = $('compare');
  if (!wrap) return;
  wrap.textContent = '';
  wrap.appendChild(table(['Text', 'Chi-square vs language', 'Verdict (5%)'], rows));
  wrap.appendChild(el('p', 'The ECC rows are in the ECC section above.'));
}

function init() {
  if (!$('caesar-plain')) return;

  // Caesar: encryption
  $('caesar-plain').value = SAMPLE_EN;
  $('caesar-key').value = '7';
  $('caesar-cipher-in').value = shiftText(SAMPLE_EN, 7);
  const encryptNow = () => {
    const k = Number($('caesar-key').value);
    if (!Number.isInteger(k) || k < 1 || k > 25) {
      $('caesar-cipher-out').textContent = 'Please enter an integer key from 1 to 25.';
      return;
    }
    $('caesar-cipher-out').textContent = shiftText($('caesar-plain').value, k);
  };
  $('caesar-encrypt').addEventListener('click', encryptNow);
  $('caesar-analyse').addEventListener('click', () => compare(analyse()));
  $('caesar-lang').addEventListener('change', () => compare(analyse()));
  encryptNow();
  reference();
  compare(analyse());

  // ECC
  $('ecc-encrypt').addEventListener('click', () => eccEncryptShow($('ecc-plain').value).catch(showEccError));
  $('ecc-decrypt').addEventListener('click', () => eccDecryptShow().catch(showEccError));
  eccSetup().catch(showEccError);
}

function showEccError(err) {
  const out = $('ecc-out');
  if (out) out.textContent = `WebCrypto error: ${err.message}. The page must run over https:// or localhost.`;
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', init);
}
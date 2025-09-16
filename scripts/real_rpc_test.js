#!/usr/bin/env node
/**
 * Headless real Lean RPC test runner (no Electron/VSCode).
 * - launches `lake env lean --server`
 * - initializes LSP
 * - didOpen a Lean file (provided or a generated scratch)
 * - calls $/lean/rpc/connect and MathEye RPCs (getByBlockRange/insertHaveByAction)
 * - writes resulting text to a .post.out.lean and compiles it via `lake env lean`
 *
 * Usage:
 *   node scripts/real_rpc_test.js --mode current|by_start|by_end [--file <path>]
 */
const cp = require('child_process');
const fs = require('fs');
const path = require('path');

const args = process.argv.slice(2);
function parseArgs() {
  const out = { mode: 'current', file: null };
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--mode' && args[i+1]) { out.mode = args[++i]; continue; }
    if (args[i] === '--file' && args[i+1]) { out.file = args[++i]; continue; }
  }
  if (!['current','by_start','by_end'].includes(out.mode)) throw new Error('mode must be current|by_start|by_end');
  return out;
}

function defaultSample() {
  return [
    'import Mathlib',
    'import MathEye',
    'macro "human_oracle" : tactic => `(tactic| sorry)',
    '',
    '/-- A prime is a number larger than 1 with no trivial divisors -/',
    'def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n',
    '',
    '/-- Every number larger than 1 has a prime factor -/',
    'theorem exists_prime_factor :',
    '    ∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by',
    '  intro n h1[cursor]',
    '  -- Either `n` is prime...',
    '  by_cases hprime : IsPrime n',
    '  · grind [Nat.dvd_refl]',
    '  -- ... or it has a non-trivial divisor with a prime factor',
    '  · obtain ⟨k, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by',
    '      simp_all [IsPrime]',
    '    obtain ⟨p, _, _⟩ := exists_prime_factor k (by grind)',
    '    grind [Nat.dvd_trans]',
    ''
  ].join('\n');
}

// Find a [cursor ...] placeholder and return { text, pos } with the marker removed
function extractCursor(content) {
  const re = /\[cursor[^\]]*\]/i;
  const m = re.exec(content);
  if (!m) return null;
  const idx = m.index;
  const before = content.slice(0, idx);
  const after = content.slice(idx + m[0].length);
  const text = before + after;
  const lines = before.split(/\r?\n/);
  const line = lines.length - 1;
  const character = lines[lines.length - 1].length;
  return { text, pos: { line, character } };
}

function lspMessage(method, params, id) {
  const msg = JSON.stringify({ jsonrpc: '2.0', id, method, params });
  return `Content-Length: ${Buffer.byteLength(msg, 'utf8')}\r\n\r\n${msg}`;
}

function lspNotification(method, params) {
  const msg = JSON.stringify({ jsonrpc: '2.0', method, params });
  return `Content-Length: ${Buffer.byteLength(msg, 'utf8')}\r\n\r\n${msg}`;
}

async function run() {
  const { mode, file } = parseArgs();
  const repoRoot = path.resolve(__dirname, '..');
  const scratchDir = path.join(repoRoot, '.it_scratch');
  try { fs.mkdirSync(scratchDir, { recursive: true }); } catch {}
  const srcPath = file ? path.resolve(file) : path.join(scratchDir, `real_case_${Date.now()}.lean`);
  let content0 = file ? fs.readFileSync(srcPath, 'utf8') : defaultSample();
  // Prefer explicit [cursor] marker if present
  const cur = extractCursor(content0);
  let initialPos = { line: 0, character: 0 };
  if (cur) { content0 = cur.text; initialPos = cur.pos; }
  // Persist cleaned content
  if (!file) fs.writeFileSync(srcPath, content0, 'utf8');
  else fs.writeFileSync(srcPath, content0, 'utf8');
  const uri = 'file://' + srcPath;
  const content = fs.readFileSync(srcPath, 'utf8');

  // launch lean server
  const proc = cp.spawn('lake', ['env', 'lean', '--server'], { cwd: repoRoot });
  proc.stdin.setDefaultEncoding('utf8');
  let buf = Buffer.alloc(0);
  const pending = new Map();
  proc.stdout.on('data', (chunk) => {
    buf = Buffer.concat([buf, chunk]);
    while (true) {
      const headerEnd = buf.indexOf('\r\n\r\n');
      if (headerEnd < 0) break;
      const header = buf.slice(0, headerEnd).toString('utf8');
      const m = header.match(/Content-Length: (\d+)/i);
      if (!m) { buf = buf.slice(headerEnd+4); continue; }
      const len = parseInt(m[1], 10);
      const start = headerEnd + 4;
      if (buf.length < start + len) break;
      const body = buf.slice(start, start + len).toString('utf8');
      buf = buf.slice(start + len);
      let obj = null;
      try { obj = JSON.parse(body); } catch {}
      const id = obj && obj.id;
      if (id != null && pending.has(id)) {
        const { resolve } = pending.get(id);
        pending.delete(id);
        resolve(obj);
      }
      // ignore notifications
    }
  });
  function sendReq(method, params, id) {
    return new Promise((resolve, reject) => {
      pending.set(id, { resolve, reject });
      proc.stdin.write(lspMessage(method, params, id));
    });
  }
  function sendNotif(method, params) { proc.stdin.write(lspNotification(method, params)); }

  // initialize
  await sendReq('initialize', { rootUri: 'file://' + repoRoot, capabilities: {} }, 1);
  sendNotif('initialized', {});

  // didOpen
  sendNotif('textDocument/didOpen', {
    textDocument: { uri, languageId: 'lean4', version: 1, text: content }
  });

  // request RPC session
  const c = await sendReq('$/lean/rpc/connect', { uri }, 2);
  const sessionId = c && c.result && c.result.sessionId;
  if (!sessionId) throw new Error('no sessionId');

  // where is the pos?
  // Find the line with 'intro n h1' and put cursor right after 'h1' (CURRENT), or
  // at by start/end depending on mode.
  const lines = content.split(/\r?\n/);
  let pos = initialPos;
  if (!cur && mode === 'current') {
    const idx = lines.findIndex(l => /\bintro\s+n\s+h1\b/.test(l));
    if (idx >= 0) {
      const col = lines[idx].indexOf('h1') + 2;
      pos = { line: idx, character: col };
    }
  }

  // ask server getByBlockRange to locate by container
  const r1 = await sendReq('$/lean/rpc/call', {
    sessionId,
    method: 'MathEye.getByBlockRange',
    textDocument: { uri },
    position: pos,
    params: { pos }
  }, 3);
  if (!r1 || !r1.result || !r1.result.success) throw new Error('getByBlockRange failed: ' + JSON.stringify(r1));
  const range = r1.result.range;
  let usePos = pos;
  if (mode === 'by_start') usePos = { line: range.start.line, character: range.start.character };
  if (mode === 'by_end') usePos = { line: range.stop.line, character: Math.max(0, range.stop.character - 1) };

  // insertHaveByAction (current/deny admit configurable; here admit)
  const r2 = await sendReq('$/lean/rpc/call', {
    sessionId,
    method: 'MathEye.insertHaveByAction',
    textDocument: { uri },
    position: usePos,
    params: {
      pos: usePos,
      action: 'admit',
      'returnWholeFile?': true
    }
  }, 4);
  if (!r2 || !r2.result || !r2.result.success) throw new Error('insertHaveByAction failed: ' + JSON.stringify(r2));
  const newText = r2.result.newText;
  const outPath = srcPath.replace(/\.lean$/, `.post.${mode}.out.lean`);
  fs.writeFileSync(outPath, newText, 'utf8');

  // compile the result
  console.log('Saved:', outPath);
  cp.execSync(`lake env lean "${outPath}"`, { cwd: repoRoot, stdio: 'inherit' });
  console.log('[OK] compiled');
  try { proc.kill(); } catch {}
}

run().catch(e => { console.error('[ERROR]', e && e.stack || e); process.exit(1); });

import * as path from 'path';
import { runTests, downloadAndUnzipVSCode, resolveCliPathFromVSCodeExecutablePath } from '@vscode/test-electron';
import * as fs from 'fs';
import { execSync } from 'child_process';

async function main() {
  try {
    process.env.MATHEYE_TEST_MODE = '1';
    // point to the extension root (package.json)
    const extensionDevelopmentPath = path.resolve(__dirname, '../../..');
    // point to compiled test runner index.js
    const extensionTestsPath = path.resolve(__dirname, './index');

    // Ensure Lean RPC server side (MathEye) is freshly built for the test host.
    // Build at the repository root so the VSCode test instance sees up-to-date .olean files.
    try {
      const repoRoot = path.resolve(extensionDevelopmentPath, '..');
      execSync('lake build MathEye', { stdio: 'inherit', cwd: repoRoot });
    } catch (e) {
      // Allow tests to proceed; failures will surface in cases that require the RPC.
      console.warn('Warning: lake build MathEye failed before integration tests:', e);
    }

    // Download VS Code for tests; install Lean4 only when using real RPC
    const vscodeExecutablePath = await downloadAndUnzipVSCode('stable');
    const cliPath = resolveCliPathFromVSCodeExecutablePath(vscodeExecutablePath);
    // Use short paths to avoid UNIX socket path length limits (<= 103 chars)
    const os = require('os') as typeof import('os');
    const shortBase = path.resolve(os.tmpdir(), `me-vsc-${process.pid}`);
    const extDir = path.join(shortBase, 'ext');
    const userDataDir = path.join(shortBase, 'ud');
    try { fs.mkdirSync(extDir, { recursive: true }); } catch {}
    try { fs.mkdirSync(userDataDir, { recursive: true }); } catch {}

    // Migrate any pre-populated assets from the legacy extensions dir into the short extDir
    try {
      const legacyExtDir = path.resolve(__dirname, '../../.vscode-test/extensions');
      if (fs.existsSync(legacyExtDir)) {
        const hasLean4 = fs.readdirSync(extDir).some(n => /^leanprover\.lean4/i.test(n))
          || fs.readdirSync(legacyExtDir).some(n => /^leanprover\.lean4/i.test(n));
        // Copy everything from legacy into short extDir to make local VSIX packaging possible
        const entries = fs.readdirSync(legacyExtDir);
        for (const name of entries) {
          const src = path.join(legacyExtDir, name);
          const dst = path.join(extDir, name);
          try {
            // Use cpSync recursive if available (Node >=16)
            (fs as any).cpSync ? (fs as any).cpSync(src, dst, { recursive: true, force: false, errorOnExist: false })
                               : fs.mkdirSync(dst, { recursive: true });
          } catch {}
        }
      }
    } catch {}
    const useReal = process.env.MATHEYE_USE_REAL_RPC === '1';
    if (useReal) {
      try {
        const fsx = require('fs') as typeof import('fs');
        const p = require('path') as typeof import('path');
        const { execFileSync } = require('child_process') as typeof import('child_process');
        const vsixEnv = process.env.MATHEYE_LEAN4_VSIX;
        const skipInstall = process.env.MATHEYE_SKIP_INSTALL === '1';

        // Step 1: Try to synthesize a VSIX from any pre-populated lean4 directory in extensions dir
        // e.g., a symlink like leanprover.lean4-0.0.209-universal
        const entries = (() => { try { return fsx.readdirSync(extDir); } catch { return [] as string[]; } })();
        const leanDir = entries.find((n: string) => /^leanprover\.lean4(\b|[-.])/i.test(n) && fsx.statSync(p.join(extDir, n)).isDirectory());
        const vsixPath = p.resolve(extDir, 'lean4.vsix');
        if (!fsx.existsSync(vsixPath) && leanDir) {
          try {
            const src = p.join(extDir, leanDir);
            // zip the directory contents into lean4.vsix
            const cmd = `cd ${JSON.stringify(src)} && zip -r -q ${JSON.stringify(vsixPath)} .`;
            execFileSync('bash', ['-lc', cmd], { stdio: 'inherit' });
          } catch (e) {
            console.warn('Warning: failed to create local lean4.vsix from directory:', e);
          }
        }

        // Step 2: Ensure lean4 is installed into the test host (with verification + retries)
        const ensureInstalled = () => {
          const list = String(execFileSync(cliPath, ['--extensions-dir', extDir, '--user-data-dir', userDataDir, '--list-extensions']));
          return /leanprover\.lean4/i.test(list);
        };
        const installFrom = (src: string) => {
          execFileSync(cliPath, ['--extensions-dir', extDir, '--user-data-dir', userDataDir, '--install-extension', src], { stdio: 'inherit' });
        };
        if (!skipInstall) {
          let ok = false;
          try { ok = ensureInstalled(); } catch {}
          if (!ok) {
            if (vsixEnv && fsx.existsSync(vsixEnv)) installFrom(vsixEnv);
            else if (fsx.existsSync(vsixPath)) installFrom(vsixPath);
            else installFrom('leanprover.lean4');
            try { ok = ensureInstalled(); } catch {}
          }
          // One more retry: rebuild vsix then install
          if (!ok && leanDir) {
            try {
              const src = p.join(extDir, leanDir);
              const cmd = `cd ${JSON.stringify(src)} && rm -f ${JSON.stringify(vsixPath)} && zip -r -q ${JSON.stringify(vsixPath)} .`;
              execFileSync('bash', ['-lc', cmd], { stdio: 'inherit' });
              installFrom(vsixPath);
              ok = ensureInstalled();
            } catch {}
          }
          if (!ok) {
            console.warn('Warning: lean4 extension not registered after install attempts; real RPC may fail.');
          }
        }
      } catch (e) {
        console.warn('Warning: failed to ensure leanprover.lean4 extension:', e);
      }
    }

    // Build launch args; avoid forcing online install when extension already present or install skipped
    const p = require('path') as typeof import('path');
    const fsx2 = require('fs') as typeof import('fs');
    const localVsix = (() => {
      const candidate = p.resolve(extDir, 'lean4.vsix');
      try { return fsx2.existsSync(candidate) ? candidate : null; } catch { return null; }
    })();
    // Build launch args with straightforward control flow to avoid TS parsing quirks
    let launchArgs: string[];
    if (useReal) {
      if (localVsix) {
        launchArgs = [
          '--extensions-dir', extDir,
          '--user-data-dir', userDataDir,
          '--install-extension', localVsix,
          path.resolve(__dirname, '../../..'),
        ];
      } else {
        launchArgs = [
          '--extensions-dir', extDir,
          '--user-data-dir', userDataDir,
          '--install-extension', 'leanprover.lean4',
          path.resolve(__dirname, '../../..'),
        ];
      }
    } else {
      launchArgs = [
        '--extensions-dir', extDir,
        '--user-data-dir', userDataDir,
        path.resolve(__dirname, '../../..'),
      ];
    }

    await runTests({ 
      vscodeExecutablePath,
      extensionDevelopmentPath, 
      extensionTestsPath, 
      extensionTestsEnv: { MATHEYE_TEST_MODE: '1', MATHEYE_USE_REAL_RPC: process.env.MATHEYE_USE_REAL_RPC || '' } as any,
      launchArgs
    });
  } catch (err) {
    console.error('Failed to run tests', err);
    process.exit(1);
  }
}

main();

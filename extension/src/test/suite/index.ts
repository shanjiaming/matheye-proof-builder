import * as path from 'path';

// Use commonjs require to be compatible with VSCode test host
const MochaCtor: any = require('mocha');

export function run(): Promise<void> {
  const Mocha = MochaCtor.default ? MochaCtor.default : MochaCtor;
  const mocha = new Mocha({ ui: 'tdd', timeout: 180000, color: true });
  const testsRoot = __dirname;
  const onlyComplex = process.env.MATHEYE_ONLY_COMPLEX === '1';
  const singleCase = process.env.MATHEYE_SINGLE_CASE === '1';
  const candidates = singleCase ? ['single_case.js'] : (onlyComplex ? ['cases.js'] : ['cases.js', 'suite.js']);
  for (const f of candidates) {
    const full = path.resolve(testsRoot, f);
    try { require('fs').accessSync(full); mocha.addFile(full); } catch {}
  }
  return new Promise((resolve, reject) => {
    try {
      const runner = mocha.run((failures: number) => failures ? reject(new Error(`${failures} tests failed.`)) : resolve());
      const fs = require('fs');
      const logPath = path.resolve(testsRoot, 'mocha_results.log');
      try { fs.writeFileSync(logPath, `START\n`, 'utf8'); } catch {}
      runner.on('pass', (test: any) => {
        try { fs.appendFileSync(logPath, `PASS: ${test.fullTitle()}\n`, 'utf8'); } catch {}
      });
      runner.on('fail', (test: any, err: any) => {
        try { fs.appendFileSync(logPath, `FAIL: ${test.fullTitle()} :: ${err?.message || err}\n`, 'utf8'); } catch {}
      });
    } catch (err) { reject(err); }
  });
}

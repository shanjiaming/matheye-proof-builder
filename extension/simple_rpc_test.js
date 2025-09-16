// Simple RPC test to debug insertHaveByAction failure
const fs = require('fs');
const path = require('path');

// Set test environment
process.env.MATHEYE_TEST_MODE = '1';
process.env.MATHEYE_USE_REAL_RPC = '1';

// Test file content
const testContent = `import Mathlib.Data.Nat.Basic
import MathEye
macro "human_oracle" : tactic => \`(tactic| sorry)

theorem have_exact_simple (n : Nat) : n = n := by rfl`;

const testFile = path.join(__dirname, 'out', 'simple_rpc_test.lean');
fs.writeFileSync(testFile, testContent);

console.log('Test file created:', testFile);
console.log('File content:');
console.log(testContent);
console.log('\nNow run the VS Code extension and call insertHaveAdmit at position 4:49 (rfl)');
console.log('Check debug logs in out/ directory');

import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';

const repoRoot = path.resolve(__dirname, '..', '..');
const testFile = path.join(repoRoot, 'test_cases', 'test_01_basic_theorem.lean');

async function simpleTest() {
  console.log('=== Simple Integration Test ===');
  console.log('Test file:', testFile);
  
  if (!fs.existsSync(testFile)) {
    console.log('Test file does not exist!');
    return;
  }
  
  const content = fs.readFileSync(testFile, 'utf8');
  console.log('File content:');
  console.log(content);
  console.log('---');
  
  console.log('Test completed - file exists and readable');
}

simpleTest().catch(console.error);

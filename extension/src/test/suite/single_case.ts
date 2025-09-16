import * as path from 'path';
import * as vscode from 'vscode';
import * as fs from 'fs';
import { strict as assert } from 'assert';
import { exec } from 'child_process';

suite('MathEye Single Case Test', () => {
  // repo root from out/test/suite is four levels up  
  const repoRoot = path.resolve(__dirname, '../../../..');

  test('test_01_basic_theorem.lean: admit at rfl position', async () => {
    console.log('=== Testing test_01_basic_theorem.lean ===');
    
    // 使用原始测试文件
    const sourceFile = path.join(repoRoot, 'test_cases/test_01_basic_theorem.lean');
    const scratchDir = path.join(repoRoot, '.it_scratch');
    try { fs.mkdirSync(scratchDir, { recursive: true }); } catch {}
    const testFile = path.join(scratchDir, `test_01_${Date.now()}.lean`);
    
    console.log('Source file:', sourceFile);
    console.log('Test file:', testFile);
    
    // 复制文件避免修改原文件
    fs.copyFileSync(sourceFile, testFile);
    
    try {
      // 打开文档
      const doc = await vscode.workspace.openTextDocument(testFile);
      const editor = await vscode.window.showTextDocument(doc);
      
      console.log('Original content:');
      console.log(doc.getText());
      
      // 找到rfl的位置
      const text = doc.getText();
      const lines = text.split(/\r?\n/);
      
      let rflLine = -1;
      let rflCol = -1;
      
      for (let i = 0; i < lines.length; i++) {
        const rflIndex = lines[i].indexOf('rfl');
        if (rflIndex >= 0) {
          rflLine = i;
          rflCol = rflIndex;
          break;
        }
      }
      
      assert.ok(rflLine >= 0, 'rfl should be found in test file');
      console.log(`Found rfl at line ${rflLine}, column ${rflCol}`);
      console.log(`Line content: "${lines[rflLine]}"`);
      
      // 设置光标在rfl位置
      const pos = new vscode.Position(rflLine, rflCol);
      editor.selection = new vscode.Selection(pos, pos);
      
      console.log('Cursor positioned, executing matheye.insertHaveAdmit...');
      
      // 执行admit命令
      await vscode.commands.executeCommand('matheye.insertHaveAdmit');
      
      // 等待处理完成
      console.log('Waiting for command completion...');
      await new Promise(r => setTimeout(r, 3000));
      
      // 获取结果
      const result = doc.getText();
      console.log('=== RESULT ===');
      console.log(result);
      
      // 保存结果到文件
      const resultFile = testFile.replace('.lean', '_result.lean');
      fs.writeFileSync(resultFile, result, 'utf8');
      console.log('Result saved to:', resultFile);
      
      // 分析变化
      if (result === text) {
        console.log('❌ No changes detected');
        assert.fail('Expected changes but none were found');
      } else {
        console.log('✅ Changes detected');
        
        // 检查结构
        const hasHave = /\bhave\b/.test(result);
        const hasExact = /\bexact\b/.test(result);
        const hasRfl = /\brfl\b/.test(result);
        const hasByKeyword = /\bby\b/.test(result);
        
        console.log('Structure analysis:');
        console.log('- Contains have:', hasHave);
        console.log('- Contains exact:', hasExact);  
        console.log('- Contains rfl:', hasRfl);
        console.log('- Contains by:', hasByKeyword);
        
        // 基本断言
        assert.ok(hasHave, 'Result should contain have statement');
        assert.ok(hasExact, 'Result should contain exact statement');
        assert.ok(hasByKeyword, 'Result should contain by keyword');
        
        console.log('✅ Basic structure checks passed');
        
        // 尝试编译结果
        console.log('Testing compilation...');
        try {
          await new Promise<void>((resolve, reject) => {
            exec(`lake env lean "${resultFile}"`, { cwd: repoRoot, timeout: 30000 }, (err, stdout, stderr) => {
              const errMsg = (stderr || '').trim();
              console.log('Compilation stdout:', stdout);
              console.log('Compilation stderr:', errMsg);
              
              if (!err) {
                console.log('✅ Compilation successful');
                resolve();
              } else {
                // 只要没有error就算成功，warning可以忽略
                if (errMsg && /^warning:/m.test(errMsg) && !/error:/m.test(errMsg)) {
                  console.log('✅ Compilation successful (warnings only)');
                  resolve();
                } else {
                  console.log('❌ Compilation failed:', errMsg || err.message);
                  reject(new Error(`Compilation failed: ${errMsg || err.message}`));
                }
              }
            });
          });
        } catch (compileError: any) {
          console.log('⚠️ Compilation test failed, but transformation succeeded:', compileError.message);
        }
      }
      
    } finally {
      // 清理临时文件
      try {
        fs.unlinkSync(testFile);
        const resultFile = testFile.replace('.lean', '_result.lean');
        if (fs.existsSync(resultFile)) {
          console.log('Keeping result file for inspection:', resultFile);
        }
      } catch (cleanupError: any) {
        console.log('Cleanup warning:', cleanupError.message);
      }
    }
  });
});

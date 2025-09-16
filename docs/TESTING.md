# 测试与运行（mock 与 real）

本文说明如何在本地运行 mock 与 real 模式的端到端测试，并给出离线环境下的安装方式。

## 前置
- Lean 构建：在仓库根执行 `lake build`
- 扩展构建：`cd extension && npm ci && npm run compile`

## mock 集成测试（默认）
- 命令：`cd extension && npm run test:integration`
- 要点：
  - 使用 Mock 的 Lean 客户端（不启动 Lean 服务器）；
  - 但每个用例的 `*.post.out.lean` 会通过 `lake env lean` 编译验证；
  - 能有效发现：范围替换、缩进对齐、rfl 裁剪、重复 have/exact 等问题。

## real 集成测试（真实 Lean 服务器）

### 在线安装（要求可联网）
```bash
cd extension
MATHEYE_USE_REAL_RPC=1 npm run test:integration
```

### 离线安装（两种方式二选一）
1) 使用 VSIX 包
```bash
cd extension
MATHEYE_USE_REAL_RPC=1 MATHEYE_LEAN4_VSIX=/abs/path/leanprover.lean4-<ver>.vsix npm run test:integration
```

2) 预置扩展目录（推荐）
```bash
# 将本机已安装的 lean4 扩展目录软链到测试宿主目录
mkdir -p extension/out/.vscode-test/extensions
ln -s ~/.cursor/extensions/leanprover.lean4-0.0.209-universal \
      extension/out/.vscode-test/extensions/leanprover.lean4-0.0.209-universal

cd extension && MATHEYE_USE_REAL_RPC=1 npm run test:integration
```

### 选择性加载测试套件（无需修改 .only）

- 仅运行复杂容器用例：
  ```bash
  cd extension
  MATHEYE_USE_REAL_RPC=1 MATHEYE_ONLY_COMPLEX=1 npm run test:integration
  ```
- 仅运行单文件自检套件：
  ```bash
  cd extension
  MATHEYE_USE_REAL_RPC=1 MATHEYE_SINGLE_CASE=1 npm run test:integration
  ```

### 关于 Preflight（扩展激活时的 lake 构建）

- 默认开启：扩展激活后会执行一次 `lake build MathEye` 并尝试重启 Lean 服务器，以保证 RPC 与 .olean 同步。
- 如需禁用（例如本地已提前构建好）：设置 `MATHEYE_PREFLIGHT=0` 再启动测试或扩展。

### 实际覆盖点
- 光标在 `|` 前、在 `=>` 后（含/不含空格）；
- 分支已有 `rfl` 或已有 `have/exact`，再次 admit/deny；
- 断言：
  - 头部合法（`=>` 后换行或 `=> by`）；
  - rfl 被裁剪；
  - 不重复 have/exact；
  - `*.post.out.lean` 通过 `lake env lean` 编译；
  - 无 Meta/pp 异常（无法读取类型则明确失败，不做 `_` 回退）。

## 调试小贴士
- VSCode CLI 路径含空格已在测试 runner 适配；
- 如 VSCode 会话报 “closed file”，runner 会尝试确保文档可见并重试；
- 输出日志：`extension/out/test/suite/mocha_results.log`、`extension/out/test/suite/rpc_debug.log`。

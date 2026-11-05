# riscv-mini：Chisel 到 Lean 的验证项目

## 已证明的结论

原始复位与环境契约下，对任意执行步，全部 45 条原始断言成立；没有新增排除条件。

最终定理：`RiscvMiniProofs.correct_after_reset`，入口为
`verification/lean/Proofs/Correctness.lean`。原始电路有 45 条 assert、1 条 assume。
状态轨迹由生成的状态转移函数递归定义；从任意初始状态出发，输入须满足证明中定义的
`ResetPrefix` 和 `Environment`。最终定理仅依赖 Lean 标准公理
`propext`、`Classical.choice`、`Quot.sound`，无 sorry 或额外公理。

## 源码版本与配置

`source/riscv-mini-coq/` 是 https://github.com/chenjie35335/riscv-mini-coq.git 的 Git 子模块：
分支 `JSA25`，固定提交 `dac51f0b4c2d02ac0ec235ddcd10bd5738b15f6e`。
嵌套子模块提交列于 `manifest.json`，以提交哈希而非分支最新状态复现。

生成入口：`new mini.CoreSoc(new mini.Core(mini.MiniConfig().core))`，连接 DUT、CheckerWithResult 和 RiscvCore。指令/数据内存各 16 个 32 位 word；不是带 cache 的 Tile。

Scala 2.13.7、Chisel 3.6.0、Scala FIRRTL 1.6.0；
使用源码自己的依赖。外部驱动在 `scripts/Export.scala` 和 `scripts/ExportHigh.scala`，
不修改被验证仓库。BoringUtils 在 Scala FIRRTL 阶段解析。

## 只检查证明

安装 elan，并使 `lean`、`lake` 在 PATH 中；项目固定 Lean 4.24.0，无第三方 Lean 包依赖。
在本目录执行：

```sh
python3 scripts/check.py --build
# 等价的 Lean 编译入口：
(cd verification/lean && lake build)
```

`check.py` 还核对文件哈希、拆分前后定义一致性、断言/假设数量及最终定理公理依赖。
加 `--sources` 可检查源码子模块版本与工作区。仅检查证明不需要 Java 或 CIRCT。

## 从 Chisel 重新生成到原位置

需要 Python 3、Java 17、Mill 0.11.12 启动器、firtool 1.158.0、elan，以及
`../tool/lean-export-20261105/` 中的固定导出工具包。
Mill 启动器应支持 `MILL_VERSION`（脚本会设置为 0.11.12），或者直接提供该版本可执行文件。
Mill 与 firtool 可分别从官方 `com-lihaoyi/mill`、`llvm/circt` 发布页获取对应版本；
首次执行 Mill 需要网络下载源码 build.sc 指定的依赖。
导出工具要求 Linux x86-64、glibc ≥ 2.38、支持 GLIBCXX_3.4.32 的 libstdc++，
以及 libz、libgcc_s、libatomic、tar、xz。

工具压缩包由 Git LFS 管理；安装 Git LFS 后先执行 `git lfs install` 和 `git lfs pull`。

在本目录执行（替换三个外部工具路径）：

```sh
git submodule update --init --recursive source/riscv-mini-coq
python3 scripts/regenerate.py \
  --mill /path/to/mill --java /path/to/java17/bin/java \
  --firtool /path/to/firtool
python3 scripts/check.py --sources --build
git diff -- artifacts verification/lean/Generated manifest.json
```

脚本验证源码 commit 与工作区、使用包内插件、检查内存适配及所有验证语句，
同时生成分层 High FIRRTL，并验证其降到 Low 后与主转换链逐字节一致。
生成结果**直接覆盖下面已纳入 Git 的位置**，旧分片会清除；`Proofs/` 不会被改写。
`manifest.json` 的文件哈希也随生成结果更新，所以应审阅 Git diff，再编译既有证明。
生成成功本身不代表新模型上的证明已通过。验证新的源码版本时，应显式更新
子模块提交与 manifest 中的源码版本，再运行生成命令。

| 位置 | 内容 |
|---|---|
| `artifacts/firrtl/CoreSoc.chirrtl.fir` | 原始 Chisel elaboration（CHIRRTL，尚未降到 High） |
| `artifacts/firrtl/CoreSoc.hi.fir` | 解析 wiring 后的分层 High FIRRTL |
| `artifacts/firrtl/CoreSoc.nomem.hi.fir` | 保留层次的无 mem High FIRRTL，imem/dmem 各展开为 16 个 32 位 reg |
| `artifacts/firrtl/CoreSoc.lo.fir` | 分层 Low FIRRTL |
| `artifacts/firrtl/CoreSoc.flat.lo.fir` | 展平后的 Low FIRRTL |
| `artifacts/firrtl/CoreSoc.prepared.lo.fir`、`.fir2.lo.fir` | 任意值显式输入、小内存适配、版本头适配 |
| `artifacts/mlir/CoreSoc.hw.mlir`、`.final.mlir` | firtool 输出、移除 OM 后交给 exporter 的 IR |
| `artifacts/export/CoreSoc.lean` | 单文件 Lean 导出 |
| `verification/lean/Generated/` | 按定义边界拆分的相同模型，供证明 import |
| `verification/lean/Proofs/` | 证明源码 |

`CoreSoc.nomem.hi.fir` 由 `scripts/MemToRegsHigh.scala` 从 High 电路转换，
保留模块、端口、验证语句与任意初始内存内容；异步读用 mux，禁用读用 validif 保留未定义语义，
同步写按 enable/mask 更新。`export-high.py` 会检查无 memory 声明并实际降到 Low；
`regenerate.py` 会同步更新此产物。现有 Lean 证明仍使用原先的 Low 适配链。

文件名中 `.hi.fir` 表示 High，`.lo.fir` 表示 Low；`.chirrtl.fir` 是原始 CHIRRTL。
`.hi.anno.json` 和 `.lo.anno.json` 分别是对应阶段的元数据。

FIRRTL annotations 的输出目录统一写为 `${TASK_ROOT}`，避免机器路径造成差异。
编译缓存、过程日志只在忽略的 `build/`、`.lake/`；没有证明搜索或生成证明的脚本。

独立拷贝时带上本目录（含已初始化的 `source/riscv-mini-coq/`），并携带上述工具版本目录；
可用 `--tool /path/to/lean-export-20261105` 指定工具位置。
不依赖另一个验证任务或根目录检查脚本。未来可增加 `verification/coq/`。
Scala/FIRRTL/CIRCT/exporter 的转换正确性仍是可信边界，文件哈希不是其正确性证明。

# arithmetic：算术电路与证明

从私有 chisel-examples 仓库整理的 12 个具体算术电路实例，以及新增的 8 位香山乘法器实例。`source/` 是直接纳入 Git 的
Chisel 7 工程及电路源码，不是子模块，不需要访问原仓库。来源与文件哈希固定在 `manifest.json`。

## 目录

| 路径 | 内容 |
|---|---|
| `source-legacy/` | Chisel 3.6.0 工程，共用 source/ 的电路源码 |
| `artifacts/chisel3/firrtl/` | 旧版直接生成的 High/Low FIRRTL |
| `source/` | Chisel 7.15.0 工程、共享电路源码、测试和 HW/模型导出入口 |
| `artifacts/chisel7/mlir/<backend>/` | 按需生成的 HW MLIR，不提交 Git |
| `verification/lean/` | 展平 Lean 模型和证明 |
| `verification/lean-hierarchical/` | 分层 Lean 模型和证明 |
| `verification/rocq/` | 基于整数模运算的 Coq 模型和证明 |
| `verification/rocq-bits/` | bits 模型、Rocq 证明及与整数模型的 refinement |
| `scripts/` | 快照检查、重生成和证明构建入口 |

每个证明工程区分 `Generated/` 和 `Proofs/`。路径固定；可重建产物仅保留哈希，首次拉取后按下文生成。

## 证明范围

下表为展平 Lean 的主要入口；Rocq 两种表示的详细契约另见各自 README。

| 电路实例 | 断言数 | 主要 Lean 证明入口及结论 |
|---|---:|---|
| Adder(8) | 1 | `Proofs/Adder.lean`：加法结果、全部断言 |
| CSA2_2/CSA3_2(8)、C22/C32 | 各 1 | `Proofs/CarrySave.lean`：进位保存的和守恒 |
| CSA5_3(8)、C53 | 各 3 | 同上：含内部压缩器的全部断言 |
| MultiCycleMac(8) | 8 | `Proofs/MultiCycleMac.lean`：`(a+b)*c`、接收后再经过两条边完成、复位及背压 |
| ArrayMulDataModule(65) | 3481 | `Proofs/ArrayProduct.lean`、`ArrayAssertions.lean`：有符号乘积、独立使能的两级流水及全部断言 |
| Radix2Divider(64) | 11 | `Proofs/RadixOutput.lean`、`RadixTrace.lean`：除法结果、完成界限、复位后全部断言 |
| MulDiv(64，默认配置) | 0 | `Proofs/MulDiv*.lean`：乘除法各合法模式、延迟及背压 |
| MulDivChecked | 11 | `Proofs/MulDivCheckedAssertions.lean`：原 MulDiv 数据通路与监视器的全部断言 |

证明针对这些固定实例，不声称任意 Scala 参数都成立。顺序电路的契约包含各定理声明的
复位、使能、kill 和握手前提；不能把完成定理解读为允许随时复位或取消时仍必定完成。
Scala/Chisel/firtool/exporter 转换仍属于可信边界，文件哈希只用于固定快照。
保留原证明所用的自动化及其公理依赖；部分 Lean 位向量证明的审计输出含
`Lean.ofReduceBool` / `Lean.trustCompiler`，不能套用 CPU 项目“仅三个标准公理”的说明。

## 小规模香山乘法器

`ArrayMulDataModule8` 复用 `ArrayMulDataModule(8)`，输入各 8 位，乘积 16 位。
新旧 Chisel 工程均导出此独立实例，原 65 位实例及其证明保持不变。
8 位参数生成的压缩树较浅，只有第一级流水寄存器；不能用它替代原实例的两级流水验证。
其 48 条展开断言随模型保留，**尚未为此参数添加性质证明**。

| 实例 | Low FIRRTL | 展平 HW MLIR（含断言） |
|---|---:|---:|
| ArrayMulDataModule(65) | 3,109,550 字节 | 4,204,174 字节 |
| ArrayMulDataModule8 | 96,424 字节 | 58,189 字节 |
| Radix2Divider(64) | 73,408 字节 | 36,172 字节 |

展平 HW 使用固定工具包的 `strip-om,hw-flatten-modules,hw.module(hw-aggregate-to-comb),canonicalize`
流水线测量。8 位实例约为除法器的 1.6 倍、原乘法器的 1/72。
High/Low 文件保存在 `artifacts/chisel3/firrtl/ArrayMulDataModule8.{hi,lo}.fir`；
四个后端的 HW 和模型仍不提交，使用下文 `regenerate.py --backend all` 一并恢复。

## 首次拉取：恢复省略的文件

High/Low FIRRTL 全部保留在 Git：`artifacts/chisel3/firrtl/`。以下文件被 `.gitignore` 排除：

| 省略内容 | 恢复方法 |
|---|---|
| 四个后端的 `artifacts/chisel7/mlir/<backend>/` | 对应 Chisel 导出入口 |
| 四个后端的 `verification/<backend>/Generated/` | 固定导出工具包及模型拆分脚本 |
| 1,572 个可重建的 Lean `Proofs/*.lean` 文件 | 随仓库提供的 `scripts/lean-proof-generators/`，不调用 Lean 求解器 |

省略的准确文件列表与 SHA-256 在 `manifest.json` 的 `generated_files` 中；其他文件在 `files` 中。
手写证明以及没有验证重建结果的 Coq/Rocq 证明继续提交。工具包仍由 Git LFS 保存。
无需访问私有原仓库；生成脚本已经收录，代码变更仅适配本仓库的目录。

```sh
# 仓库根目录
git lfs pull
cd arithmetic
# 无任何生成文件时也可运行；生成全部 HW、模型和可重建 Lean 证明
python3 scripts/regenerate.py --backend all
# 核对源码、所有产物及 import 完整性（不编译证明）
python3 scripts/check.py --sources --backend all
```

只使用某个后端时可执行 `python3 scripts/regenerate.py --backend lean`（或
`lean-hierarchical`、`rocq`、`rocq-bits`），然后 `python3 scripts/check.py --backend lean --sources`。
`regenerate.py --backend all --check` 在临时目录重建并对比 manifest 哈希，**不恢复**本地缺失文件。
`check.py --sources --allow-missing-generated` 可检查尚未生成的源码检出，不能与 `--build` 一起使用。

生成入口会先验证全部选定产物的哈希，再写回 `.gitignore` 中列出的文件；不会覆盖手写证明，
也不会自动更新预期哈希。首次恢复成功后，再按下一节的 `--build` 命令运行证明检查。
原 12 个实例曾从缺少全部 1,713 个省略文件的状态恢复并逐字比较；这验证重建过程，不代表重新检查证明正确性。

## 检查已有证明

```sh
# 模型已恢复后，从 arithmetic/ 执行；证明构建不需要原仓库
python3 scripts/check.py --sources
python3 scripts/check.py --backend lean --build --jobs 4
python3 scripts/check.py --backend lean-hierarchical --build --jobs 4
python3 scripts/check.py --backend rocq --build --coq-switch rocq-export --jobs 4
python3 scripts/check.py --backend rocq-bits --build --rocq-bits-switch rocq-bits --jobs 4
# 一次检查四个后端
python3 scripts/check.py --backend all --build \
  --coq-switch rocq-export --rocq-bits-switch rocq-bits --jobs 4
```

默认 `--build` 编译展平 Lean；Lean 固定 4.24.0，无第三方 Lean 包。
脚本默认使用 4 个构建工作线程，`--jobs` 可调整；高并发可能导致 SAT 求解超时。
Coq/Rocq 通过 `make check` 完整编译并调用 `coqchk` / `rocq check` 检查证明项。
不提供 switch 参数时使用 PATH 中的工具；两种 Rocq 工程需要不同版本。
首次安装可使用：

```sh
opam switch create rocq-export ocaml-base-compiler.4.14.2 --no-switch
opam install --switch=rocq-export coq.8.16.0 coq-mathcomp-ssreflect.2.2.0
opam switch create rocq-bits ocaml-base-compiler.4.14.2 --no-switch
opam install --switch=rocq-bits rocq-core.9.3.0 rocq-stdlib.9.2.0
```

`check.py` 还检查已登记文件哈希、13 个模型入口、Lean 本地 import 和证明占位符；
这些静态检查不代替编译。`--sources` 同时核对直接收录的源码。
根目录的 `scripts/verify.py arithmetic --sources --build` 调用默认 Lean 入口。

## 新版 Chisel：HW MLIR 和证明模型

固定 Mill 1.1.2、Scala 2.13.18、Chisel 7.15.0，使用 Java 21。
固定工具包 [arithmetic-export-20261112](../tool/arithmetic-export-20261112/README.md)
包含 firtool 1.158.0、circt-opt、四后端导出插件、Spot 库和源码快照，通过 Git LFS 保存。
无需原来的 chisel-examples 或 circt-spot 工作区；工具来源、构建方法和系统要求见工具包 README。

```sh
# 仓库根目录首次下载工具包
git lfs pull
# 以下从 arithmetic/ 执行
python3 scripts/regenerate.py --backend all --check
python3 scripts/regenerate.py --backend lean --check
# 恢复固定生成产物，包括已登记的自动生成 Lean 证明
python3 scripts/regenerate.py --backend lean
```

后端为 `lean`、`lean-hierarchical`、`rocq`、`rocq-bits`；`all` 选择全部后端。
`--tool /path/to/arithmetic-export-20261112` 可指定同一固定工具包的独立拷贝。
脚本校验工具 manifest、解包脚本和归档哈希，在临时目录从 Chisel 重生成 HW MLIR、模型和已登记的 Lean 证明片段，
`--check` 对比 manifest 中的固定哈希，不要求本地已存在生成文件。HW 始终放在 `artifacts/chisel7/mlir/`，模型保留在对应证明工程中。

重新导出不等于性质已证明；修改电路或模型后应编译证明。编译链仍在可信边界内。
修改源码或工具版本时必须审阅并显式更新固定哈希，脚本不会静默接受版本漂移。

## 旧版 Chisel：原生 High / Low FIRRTL

`source-legacy/` 是独立的 Mill 工程，使用 Chisel 3.6.0、Scala 2.13.10、Scala FIRRTL 1.6.0、
Temurin 17.0.15、Mill 1.1.2。它引用 `source/` 中同一套电路源码，生成全部 13 个实例，参数与新版一致。
电路及 assert 没有另写一份，两个项目使用各自的编译缓存。

```sh
# 从 arithmetic/ 执行
python3 scripts/legacy_firrtl.py --check
# 恢复固定快照
python3 scripts/legacy_firrtl.py
# 或直接调用旧版 Scala 入口
cd source-legacy
./mill --no-server Examples.runMain LegacyEmit
```

旧版 `chisel3.stage.ChiselStage` 的 `-X high`、`-X low` 直接生成传统 FIRRTL 1.2.0 文本：
`artifacts/chisel3/firrtl/<模块>.hi.fir` 和 `<模块>.lo.fir`，共 26 个文件。
中间 CHIRRTL 与注解留在 `build/`。不需要 CIRCT 文本导出器或自定义 FIRRTL 文本转换工具。

`legacy-manifest.json` 固定版本、源码和产物哈希；`check.py --sources` 同时核对两个项目，
`regenerate.py --backend all --check` 同时重生成旧版 FIRRTL 和新版四后端 HW/模型。
Scala FIRRTL 的位置注解含源码检出路径；跨绝对路径生成时可能出现位置注解差异，检查会报告而非静默改写哈希。

当前已经完成的证明针对 Chisel 7 导出的模型，不声称新旧编译链已建立形式等价证明。

## 验证记录

- 新增 8 位实例后，旧版 26 个 High/Low FIRRTL 重生成与快照逐字一致。
- 已完成的四后端 HW/模型重生成与固定快照逐字一致，证明源码保持不变。
- 2026-11-12 四个后端的证明构建/检查通过。2026-11-13 两个 Lean 后端和 Coq 复查通过；
  Rocq bits 复查按用户要求在 refinement 编译阶段停止，未完成该轮内核检查。
- 当前整理采用语法、Scala 编译、快照及产物复现检查，不重新运行证明正确性检查，
  也不将未完成的复查记作通过。

日志和编译缓存保存在忽略的 `build/`，不纳入 Git。

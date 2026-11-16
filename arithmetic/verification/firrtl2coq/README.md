# 当前 csj 修复与证明

方法、语义边界、性能问题及代码规模见 [证明经验总结](../../docs/firrtl2coq-proof-experience.md)。

当前工具基于上游 `csj` 的 `ced58a8125da4b044ca6c4b75b528040af88cf80`，当前工具引用包含本次修复。仍执行原始分层 FIRRTL AST 和原始位向量、周期解释器。

除法器的 [Divider/Proof.v](Divider/Proof.v) 提供 11 个外部证明，小乘法器的
[SmallMultiplier/Proof.v](SmallMultiplier/Proof.v) 提供 5 个外部证明及总定理。
最终生成的 `Divider.Radix2Divider` 和 `SmallMultiplier.ArrayMulDataModule8` 模块
保留原始 `generated_assert_i` Lemma 声明，每个仅通过一行 `exact` 调用外部证明。
`obligation_i` 现在只是外部证明文件内部的命题别名。
证明覆盖任意初始寄存器、真实 reset 高电平的一拍及复位后任意步，使用生成器给出的合法执行前提；
除法器通过已证明的逐拍对应关系复用数学不变量，小乘法器证明分层组合收敛、周期提交和流水线不变量。

历史版本的两个完整证明均通过独立 `coqchk`，按电路名整理后除法器也再次通过独立检查。
本轮拆分模型与 Lemma 后，两个最终生成模块的共 16 个 Lemma 及其依赖均通过 `coqc`；
两个目标均使用 `--compile-only`，没有重复独立 `coqchk`。

证明依赖上游 `ftype_eqn_eq`、`ffield_eqn_eq` 两个类型相等性公理；未使用上游未证明的表达式类型正确性定理，也未新增公理或 `Admitted`。工具修复与电路证明分别保存在工具仓库和本仓库中。

## 模型与证明的目录边界

`firrtl2coq` 生成的 Coq 按 FIRRTL 的真实 circuit/top 名称放在 `Generated/`：

| 路径 | 内容 |
|---|---|
| `Generated/Radix2Divider/Model.v` | 除法器原始输出的完整模型和性质定义，逐字保留首个 Lemma 之前的全部内容 |
| `Generated/Radix2Divider/Radix2Divider.v` | 11 个原始 `generated_assert_i` Lemma；每个只用一行 `exact` 引用外部证明 |
| `Generated/ArrayMulDataModule8/Model.v` | 8 位乘法器原始输出的完整模型和性质定义，逐字保留首个 Lemma 之前的全部内容 |
| `Generated/ArrayMulDataModule8/ArrayMulDataModule8.v` | 5 个原始 `generated_assert_i` Lemma；每个只用一行 `exact` 引用外部证明 |
| `Common/`、`Divider/`、`SmallMultiplier/` | 证明库、桥接、证书和最终定理；包括手写与 Python 生成的证明 |

每个电路的两份 Coq 文件都保留为可审核源码；仅 `manifest.json` 保持忽略。
`generate_firrtl2coq_models.py` 不修改 firrtl2coq 本身：它调用真实工具，将第一个
`Lemma generated_assert_0` 之前的全部内容逐字写入 `Model.v`，将原始 Lemma
声明逐字放入电路同名文件。后者只补充导入和 notation scope，并将每个 `Admitted.`
替换为 `Proof. exact Divider.Proof.divider_obligation_0. Qed.` 这样的外部证明调用。
实际复杂证明仍位于 `Divider/Proof.v` 和 `SmallMultiplier/Proof.v`；它们只依赖
`Model.v`，不导入最终 Lemma 文件，避免循环和引用未经证明的生成目标。
外部证明内部的 `obligation_i` 是便于复用的命题别名，不是生成器的证明占位。
最终检查目标是包含所有原始 Lemma 的电路同名文件，而非这些别名的定义。

`--check` 重新调用工具并逐字比较模型、Lemma 和 manifest；命题改变或缺少证明调用
都会产生差异。生成本身不代表证明通过，必须编译最终 Lemma 文件。
相同内容不会重写文件。`prepare.py` 等证书脚本也保留完整模型前缀。

Coq 逻辑模块为 `Divider.Model` / `Divider.Radix2Divider` 和
`SmallMultiplier.Model` / `SmallMultiplier.ArrayMulDataModule8`。
检查脚本将各电路生成目录和对应证明目录映射到同一命名空间，并拒绝重复的同名源文件。
生成模型目录优先于证明目录中的旧编译缓存。`Archive/` 保存历史原文，不参与当前构建。

复现（仓库根目录，已安装 `firrtl2coq` opam switch）：

```sh
# 工具语义有修改时，必须重编 Coq、重新提取，再编 OCaml。
(cd tool/firrtl2coq && opam exec --switch=firrtl2coq -- coq_makefile -f _CoqProject -o Makefile && opam exec --switch=firrtl2coq -- make -j1)
(cd tool/firrtl2coq/src/ocaml && opam exec --switch=firrtl2coq -- dune build && opam exec --switch=firrtl2coq -- dune runtest)
python3 arithmetic/scripts/generate_firrtl2coq_models.py
python3 arithmetic/scripts/generate_firrtl2coq_models.py --check
# 旧数学模型若被忽略/删除，先恢复它：
python3 arithmetic/scripts/regenerate.py --backend rocq
python3 arithmetic/scripts/check_firrtl2coq_divider.py --compile-only
python3 arithmetic/scripts/check_firrtl2coq_multiplier.py --jobs 2 --compile-only
```

`generate_firrtl2coq_models.py --firrtl-root /path/to/arithmetic/artifacts/chisel3/firrtl` 可指定输入目录。
两个检查脚本审计所有依赖中的 `Admitted`、`Axiom` 等并编译最终生成 Lemma；
`--compile-only` 跳过额外的独立 `coqchk`，结果分别记录 `coqc: passed` 和 `coqchk: skipped`。
省略该选项则继续检查最终 `Divider.Radix2Divider` / `SmallMultiplier.ArrayMulDataModule8`。
结果写入各自的 `arithmetic/build/firrtl2coq-*-proof/result.json`。编译产物和结果无需提交。


未进入最终证明依赖的探索文件及相关脚本保存在 [Archive/](Archive/README.md)，保留原文与原路径记录，不参与当前构建。

---

# 旧版 Low FIRRTL 与 firrtl2coq：当前状态

**以下旧诊断保留作历史记录；当前状态见本节。** 这里保存旧版生成入口和上游执行语义的反例，不能替代已有 `rocq` 后端的硬件证明，也不声称两种模型已经建立对应关系。

## 固定输入与生成

- Chisel 3.6.0、Scala 2.13.10、Scala FIRRTL 1.6.0、Temurin 17.0.15、Mill 1.1.2。
- 直接编译 `arithmetic/source/src/main/scala/singlefile/xiangshan/` 中的原有源码，不改写 assert，不复制另一套电路实现。
- `ArrayMulDataModule(65)`、`Radix2Divider(64)`；传统 FIRRTL 文件头为 1.2.0。
- `ChiselStage.execute(-X low)` 直接输出，未经过 CIRCT MLIR 或自定义文本生成器。
- 文件在 `arithmetic/artifacts/chisel3/firrtl/`；构建、源码和产物哈希在 `arithmetic/legacy-manifest.json`。

从仓库根目录运行：

```sh
python3 arithmetic/scripts/legacy_firrtl.py --check
```

省略 `--check` 可恢复固定哈希的产物。中间 CHIRRTL 和注解保存在临时构建目录。旧版编译器的 source-info 含源码路径，因此跨不同绝对检出路径时原始文本可能不同；比较失败不会静默更新哈希。

## 转换测试

`firrtl2coq` 固定在 `58759b554890e0fc877c0a07c5093fec6d69b104`。未修改子模块源码。
原版 dune 构建因缺少 `storage_id` 失败。诊断副本仅用该提交根目录已有的
`transhiast_without_inline.ml` 和 `coqgen.ml` 覆盖其 `lib/` 中未同步的文件，不修改执行语义。

```sh
python3 arithmetic/scripts/probe_firrtl2coq.py
```

脚本使用已安装的 `firrtl2coq` opam switch，先构建上游 Coq 库及提取代码，再生成和编译测试文件。结果及日志位于 `arithmetic/build/firrtl2coq-legacy-probe/`。
这是诊断脚本，成功退出仅表示诊断执行完成，**不表示目标电路的性质已经证明**。

旧版 Low FIRRTL 中 assert 的错误消息为空，printf 单独保存；转换器忽略 printf，不删除 assert。
两个电路都能被诊断副本解析并生成 Coq：乘法器生成 5 个模块级断言目标（包括压缩器），除法器生成 11 个。
乘法器的跨模块同名断言仍导致 Coq 定义重名；除法器生成文件可编译，但 11 个目标全部是 `Admitted`。

## 生成的目标与语义阻碍

上游生成的目标确实形如：

```coq
forall inputs (k : nat) states,
  generated_run inputs k = Some states ->
  generated_all_assumptions states ->
  generated_assert_NAME_all states.
```

其中 `generated_run` 调用 `circuit_run_from_reset`：`k=0` 返回初始化的复位状态，后续步调用 `circuit_value_with_memory`。它是对任意 k 的条件性质，而不是已经证明的定理。对合法输入的执行成功性也要另行保证，不能依赖 `None` 使前提不成立来获得空洞结论。复位实现将没有复位的寄存器也置零，这比硬件任意初值更强，不能忽略这一建模差异。

`Diagnostics/RegisterIteration.v` 用 Coq 检查了以下反例：

1. `value_iter_with_memory ... false ...` 在应当只做组合求值时，仍将寄存器从 0 改为 1。
2. 两级寄存器 `r0 <= 1; r1 <= r0` 在上游复位状态中为 `(r0,r1)=(0,0)`；执行 `circuit_run_from_reset ... 1` 后 r1 已是 1，正确的一步同步更新应保留 r1=0。原因是组合稳定迭代提前推进了寄存器。

反例以 `vm_compute; reflexivity` 结束，无新增 `Admitted` 或公理。`Print Assumptions` 报告仍依赖上游的 `ftype_eqn_eq`、`ffield_eqn_eq` 两个类型相等性公理，不能称作整个依赖链无公理。

因此目前不能把此 `generated_run` 上的证明解释成原 Chisel 的时钟步不变量。尚需修复并验证寄存器更新、模块实例连线和状态采样语义，处理断言命名，以及建立针对这两个电路的可达状态不变量并完成全部证明。未将已有其他后端证明冒充为 firrtl2coq 证明。

## 另一个分支的复测

未经覆盖的 `csj` 分支结果另见 [CSJ-RESULTS.md](CSJ-RESULTS.md)。以上保留旧提交的历史诊断。

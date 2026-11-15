# 当前 csj 修复与证明

当前工具基于上游 `csj` 的 `ced58a8125da4b044ca6c4b75b528040af88cf80`，当前工具引用包含本次修复。仍执行原始分层 FIRRTL AST 和原始位向量、周期解释器。

除法器的 [Divider/Proof.v](Divider/Proof.v) 已构造生成文件 `ArithmeticFIRRTL.Radix2Divider.obligation_0` 至 `obligation_10` 的证明。覆盖任意初始寄存器、真实 reset 高电平的一拍，以及复位后任意步；结论和前提均使用生成器给出的合法执行定义。通过已证明的逐拍对应关系复用已有数学不变量，没有假设模型等价。8 位乘法器的分层组合收敛、完整周期寄存器提交、任意初始寄存器与真实复位、复位后任意步流水线不变量，以及全部局部 assert 已经由 Coq 检查；`SmallMultiplier/Proof.v` 的五个原始生成目标及总定理已通过 `coqc`，依赖审计仅显示上游两个类型相等性公理。140 个证明依赖文件已全部强制重编译成功，独立 `coqchk` 已通过。检查结果记录在 `arithmetic/build/firrtl2coq-multiplier-proof/result.json`，其中证明源文件、工具源文件及输入和生成模型的哈希已核对一致。

证明依赖上游 `ftype_eqn_eq`、`ffield_eqn_eq` 两个类型相等性公理；未使用上游未证明的表达式类型正确性定理，也未新增公理或 `Admitted`。工具修复与电路证明分别保存在工具仓库和本仓库中。

复现（仓库根目录，已安装 `firrtl2coq` opam switch）：

```sh
# 工具语义有修改时，必须重编 Coq、重新提取，再编 OCaml。
(cd tool/firrtl2coq && opam exec --switch=firrtl2coq -- coq_makefile -f _CoqProject -o Makefile && opam exec --switch=firrtl2coq -- make -j1)
(cd tool/firrtl2coq/src/ocaml && opam exec --switch=firrtl2coq -- dune build && opam exec --switch=firrtl2coq -- dune runtest)
python3 arithmetic/scripts/generate_firrtl2coq_models.py
# 旧数学模型若被忽略/删除，先恢复它：
python3 arithmetic/scripts/regenerate.py --backend rocq
python3 arithmetic/scripts/check_firrtl2coq_divider.py
python3 arithmetic/scripts/check_firrtl2coq_multiplier.py --jobs 2 --force
```

`generate_firrtl2coq_models.py --firrtl-root /path/to/arithmetic/artifacts/chisel3/firrtl` 可指定输入目录。它将生成器留下的待证定理变成精确的 `Prop` 定义，生成操作本身不声称证明完成。两个检查脚本分别审计证明依赖、按依赖构建并执行 `coqchk`；通过后分别写入 `arithmetic/build/firrtl2coq-divider-proof/result.json` 和 `arithmetic/build/firrtl2coq-multiplier-proof/result.json`。`.vo`、生成模型、构建日志和该结果文件均不需要提交，hi/lo FIRRTL 输入保留。

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

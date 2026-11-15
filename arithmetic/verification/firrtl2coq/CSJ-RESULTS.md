# `csj` 分支复测（修复前历史记录）

当前修复及已完成的除法器、乘法器证明见 [README.md](README.md)。以下结论仅针对修复前的上游提交。

本文件与 `README.md` 中旧 `58759b5` 诊断分开保存；旧反例针对旧语义，不能在新版上期待同样结论。
复测使用未经覆盖或修改的上游 `csj` 提交 `ced58a8125da4b044ca6c4b75b528040af88cf80`，
Coq 8.16.0 / MathComp 1.15 / opam switch `firrtl2coq`。

从本工作树根目录运行：

```sh
python3 arithmetic/scripts/probe_firrtl2coq_csj.py
```

脚本校验工具提交及源码未修改，构建 Coq 库、提取代码及原版 dune 项目，运行 dune 测试，
分别转换和编译香山 65 位乘法器、64 位除法器的 high / low FIRRTL，最后编译寄存器回归。
产物、日志和 `results.json` 在被忽略的 `arithmetic/build/firrtl2coq-csj/`。
脚本退出成功仅表示诊断执行完成，四个转换的具体编译结果须看 `results.json`。

`Diagnostics/CSJRegisterIteration.v` 使用与历史反例相同的两级寄存器模型，补充声明了 reset 输入端口，
检查组合求值保留寄存器，并分别检查 `circuit_run_from_reset` 与新 `circuit_formal_run_from_reset`
在第 0、1、2 步得到 `(0,0)`、`(1,0)`、`(1,1)`。这里没有证明香山电路的 assert。

## 新生成接口的含义

`generated_run` 现调用 `circuit_formal_run_from_reset`，量化初始 memory 内容及逐周期 `formal_inputs`。
`formal_inputs` 同时包含外部输入和按实例、语句、叶节点、位宽区分的符号值；DontCare 不必固定为零。
`generated_legal_trace` 要求每个已消耗周期（1 到 k）执行成功并满足 assume。
第 0 步是组合求值之前的初始化状态，不在该 trace 前提内，但生成的 assert 目标仍允许任意 k（包括 0）。

生成的 assert 目标仍以 `Admitted` 结束，编译生成文件并不是证明这些目标。
此外 `reset_registers` 对无复位寄存器仍使用零值初始化；该建模与任意上电初值的关系需要另行处理。
新 `finish_registers` 修复组合迭代提前更新寄存器的路径，但以下小型回归不构成对全部转换及同步语义的等价性证明。

## 本次实际结果

| 输入或检查 | 结果 |
| --- | --- |
| 原版 Coq 库、提取、dune build | 全部成功；缺 `storage_id` 的构建问题已修复 |
| dune runtest | 成功；覆盖 literal 位序、截断、有符号值和 NBits 解码 |
| 乘法器 high FIRRTL | 解析失败，报第 21 行（嵌套 when 中 node）；未改写输入规避 |
| 乘法器 low FIRRTL | 转换成功，生成 5 个目标；Coq 第 162 行报 `generated_assert_assert_local already exists` |
| 除法器 high FIRRTL | 解析失败，报第 18 行（when 中连接）；未改写输入规避 |
| 除法器 low FIRRTL | 转换、Coq 编译成功，11 个目标仍全部 `Admitted` |
| 组合迭代保持寄存器 | `vm_compute; reflexivity` 通过 |
| 旧 concrete API 两级流水线 | 0/1/2 步为 00/10/11，Coq 检查通过 |
| 新 formal API 两级流水线 | 0/1/2 步为 00/10/11，Coq 检查通过 |

三个回归证明无新增公理或 `Admitted`；`Print Assumptions` 仍报告上游
`ftype_eqn_eq`、`ffield_eqn_eq` 两个公理。旧寄存器问题在该回归中得到修复，
但跨模块断言重名仍阻止乘法器生成文件通过 Coq 编译。没有开展或完成这两个真实电路的 assert 证明。

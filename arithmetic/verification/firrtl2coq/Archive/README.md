# 证明探索归档

这里保留未进入两个最终 `Proof.v` 依赖链的中间证明和相关生成脚本，供回顾证明经历。文件原文未修改，原路径及 SHA-256 记录在 `manifest.json`。归档不参与当前完整证明的构建。

## 保留的经历

- `SmallMultiplier/Capture.v`、`CaptureWiring8.v`、`Invariant8.v`：早期捕获线路及流水线不变量的探索。
- `Child*Local.v`、`Child*Pass.v`、`Child*Widths.v`、`ChildConnections.v`、`ChildGeneric.v`：局部子模块求值、位宽及连接的中间证明。
- `LocalEnvironment.v`、`PassCertificates.v`、`StableFront.v`、`StableProduct.v`、`Widths.v`、`WeightedCompressors.v`：局部组合求值、稳定值及乘积关系的早期组织方式。
- `IterationCount.v`、`UninitializedProbe.v`：迭代次数及初始化的探索。
- `Common/InterpreterFacts.v`：最终证明未引用的解释器辅助引理。
- 相关 Python 脚本（含旧 `check.py`）与证明一同归档，保留原来的生成和局部检查方式。

这些文件不在最终依赖中，不表示结论错误，也不意味着它们单独构成完整电路证明。当前完整证明使用全电路求值、端口同步、寄存器提交与逐拍不变量的对应关系。

## 查看及重新实验

归档保留原逻辑模块名和脚本中的相对路径，没有为新目录改写证明。不要直接在归档目录运行生成器或把整个归档递归加入当前 Coq 工程。

如需重新实验，在独立的临时工作树中，按 `manifest.json` 将归档文件复制回 `original` 指定的位置（路径相对于本目录的父目录），再使用该时期的依赖和检查方式。这恢复文件布局，不保证所有历史检查都适配当前工具；`SmallMultiplier/check.py` 仅检查旧局部组件，并非最终定理的完整验证入口。

最终验证继续使用 `arithmetic/scripts/check_firrtl2coq_divider.py` 和 `arithmetic/scripts/check_firrtl2coq_multiplier.py`。

`SmallMultiplier/CaptureAST.v` 虽不在最终 Coq 证明依赖中，仍被三个当前生成脚本读取，因此留在活动目录。除法器的全部 44 个专属证明文件都在最终依赖中，没有归档。

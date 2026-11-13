# 硬件验证项目

- [riscv-mini/](riscv-mini/README.md)：45 条原始断言，在原始复位和环境契约下全部证明。
- [nutshell/](nutshell/README.md)：48 条原始断言，在额外有效 IDU PC[38:32] = 0 限制下全部证明；反例记录见其 counterexamples/。
- [arithmetic/](arithmetic/README.md)：12 个算术电路实例，源码直接收录，包含 Lean、分层 Lean、Coq/Rocq 证明。
- [tool/](tool/README.md)：按版本独立存放导出工具。

每个任务的 README 独立说明固定源码、配置、生成流程和证明范围。
各自运行 scripts/regenerate.py 会更新 Git 中的模型和中间产物，
供 git diff 审阅；不会改写 Proofs。算术任务使用直接收录的源码，包含多种证明后端；
其重新导出所需工具和 CPU 任务不同，详见各任务 README。

```sh
git lfs install
git lfs pull
git submodule update --init --recursive
python3 scripts/verify.py riscv-mini nutshell arithmetic --sources --build
```

只验证现有证明无需初始化硬件源码或使用导出工具，去掉 --sources 即可。

# 工具版本

- [lean-export-20261105](lean-export-20261105/README.md)：Linux x86-64，约 21 MB；两个 CPU 任务使用的固定版本。

- [arithmetic-export-20261112](arithmetic-export-20261112/README.md)：算术任务四个后端的固定工具，包含 firtool 和导出插件源码快照。

- [firrtl2coq](firrtl2coq/README.md)：FIRRTL 到 Coq 的转换器和语义库，作为 Git 子模块固定版本；本项目的编译方法见下文。

每个版本保存在独立子目录；新增版本不覆盖旧包。任务 manifest 的 tool_bundle 指定所用版本。
工具压缩包使用 Git LFS 存储。安装 Git LFS 后，在仓库根目录执行：

```sh
git lfs install
git lfs pull
```

Git 中保存指针；本地下载完成后仍是原始压缩包，校验哈希不变。

## firrtl2coq 的 Coq 环境

上游：https://github.com/wky17/firrtl2coq 。子模块位于 `tool/firrtl2coq/`，
固定提交 `58759b554890e0fc877c0a07c5093fec6d69b104`（master，多时钟支持）。

已安装独立的 `firrtl2coq` opam switch：OCaml 4.14.2、Coq 8.16.0、
MathComp ssreflect/algebra 1.15.0。默认 switch 未改变。

按上游 README 编译 Coq：

```sh
cd tool/firrtl2coq
opam exec --switch=firrtl2coq -- coq_makefile -f _CoqProject -o Makefile
opam exec --switch=firrtl2coq -- make
```

不修改上游源码，不应用补丁，不补证明。此前的自定义构建脚本、两处冗余匹配
删除补丁及带补丁的构建副本已撤销；此前“编译通过”仅适用于带补丁的副本，
不能作为原版编译通过的结论。

原版 `05ec8e1` 清理后按上述命令重新编译失败，`make` 退出码为 2：

```text
File "./src/Semantics_with_implicit_widths.v", line 5825, characters 6-15:
Error: Pattern "_" is redundant in this clause.
```

错误位于 `value_iter` 的末尾兜底分支，前面的模式已穷尽所有情况。
本次在首个错误处停止，没有继续修改源码验证后续问题。
日志位于 `build/firrtl2coq/upstream-original.log`（从项目根目录计算）。

新版 `482f062` 已由上游删除两处冗余匹配、补充 `_CoqProject` 的语义文件，
并修正文档路径。按新版 README 执行的 Coq 库编译、`src/TestAdder.v` 编译、
`dune build`、`CoreSoc.hi.fir` 转换及生成文件 `CoreSoc_memory.v` 编译均已通过，
没有应用本地补丁。日志位于 `build/firrtl2coq/482f062-*.log`。

转换器重新生成的 `CoreSoc_memory.v` 相比上游提交只多导入了
`Semantics_for_circuit`。45 个断言目标仍为 `Admitted`，未开展性质证明。
README 的依赖安装命令仍未列出源码实际导入的 MathComp algebra，当前环境已安装该包。

新版 `58759b5` 增加多时钟执行及复位初始化支持，生成的断言目标改用 `generated_run inputs k`。
上游同时将 `HiFirrtl_with_implicit_widths.v` 中的 `hfmem_eq_dec` 改为 `Admitted`；
因此即使编译成功，也不能将此版本视为无证明缺口。此次只更新上游固定提交，不应用本地补丁。

2026-11-13 对 `58759b5` 使用上述独立 switch 检查：Coq 库 `make -j4` 和
`src/TestAdder.v` 编译通过；`dune build` 失败，未继续执行 CoreSoc 转换及生成文件编译：

```text
File "lib/transhiast_without_inline.ml", lines 152-158:
Error: Some record fields are undefined: storage_id
```

上游更新了 `src/ocaml/transhiast_without_inline.ml`，但 dune 实际使用的
`src/ocaml/lib/transhiast_without_inline.ml` 仍缺少新增字段。因此前述 `482f062`
的转换成功结论不适用于当前版本。日志为 `build/firrtl2coq/58759b5-coq.log`
和 `build/firrtl2coq/58759b5-validation.log`；未修改子模块源码。

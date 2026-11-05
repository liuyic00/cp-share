# Lean 导出工具

`lean-export-linux-x86_64.tar.xz` 约 21 MiB，解压约 100 MiB，包含
`circt-opt`、`CIRCTSpotPlugin.so`、`libspot.so.0`、`libbddx.so.0`。
仅对副本执行 `strip --strip-unneeded`；原始与精简后的 SHA-256 均记录在
`manifest.json`。两个任务的 manifest 固定本工具包及插件哈希；均已用它从 Chisel 重新生成并核对模型。

从仓库根目录运行：

```sh
python3 tool/lean-export-20261105/export-lean.py riscv-mini/artifacts/mlir/CoreSoc.hw.mlir riscv-mini/build/reexport/CoreSoc.lean
python3 tool/lean-export-20261105/export-lean.py nutshell/artifacts/mlir/NutCore.hw.mlir nutshell/build/reexport/NutCore.lean
cmp riscv-mini/build/reexport/CoreSoc.lean riscv-mini/artifacts/export/CoreSoc.lean
cmp nutshell/build/reexport/NutCore.lean nutshell/artifacts/export/NutCore.lean
```

脚本校验压缩包与解压文件的哈希，缓存至忽略的 `tool/lean-export-20261105/build/`，设置动态库搜索路径，
执行 `strip-om,export-lean`，输出单文件 Lean 和 `.final.mlir`。
不改动已有 Generated 或 Proofs；拆分和完整 FIRRTL 转换见各任务 scripts。

## 运行环境

Linux x86-64；Python 3、tar、xz。系统需提供 glibc 2.38 或更新版本、
提供 GLIBCXX_3.4.32 的 libstdc++，以及 libgcc_s、libz、libatomic。
包内没有系统运行库，不承诺兼容较旧发行版、macOS 或 ARM。
不包含 firtool；此工具包负责 HW MLIR → Lean，完整生成流程仍使用任务清单指定的 firtool。
仅检查已有 Lean 证明无需此工具包。

## 来源

- CIRCT：<https://github.com/llvm/circt>，修订 `9de24b873409b154c977a015dff1a40f02ef020b`，LLVM 24 开发版，启用 assertions。
- 导出插件：以工具 manifest 中的原始 SHA-256 固定身份；该二进制未独立嵌入可核验的插件源码 commit，不将当前源码 HEAD 当作构建版本。
- Spot 2.16 与其 BuDDy：<https://spot.lrde.epita.fr/>；对应源码发布包 <https://www.lrde.epita.fr/dload/spot/spot-2.16.tar.gz>。

这是现有生成工具的精简二进制归档，不是可重现构建证明。

# 算术电路导出工具（2026-11-12）

独立的 Linux x86-64 二进制包，用于 `arithmetic/` 的四个后端：
`export-lean`、`export-lean-hierarchical`、`export-rocq`、`export-rocq-bits`。
不替换 `lean-export-20261105`；CPU 任务仍使用原包。

包内包含 `firtool` 1.158.0、兼容的 `circt-opt`、新编译的 `CIRCTSpotPlugin.so`、
Spot 2.16 的 `libspot.so.0` 和 `libbddx.so.0`，以及许可证文本。
二进制副本经 `strip --strip-unneeded`；原始及精简后的哈希记录在 manifest。

```sh
# 仓库根目录；压缩包由 Git LFS 管理
git lfs pull
python3 arithmetic/scripts/regenerate.py --backend all --check
```

`prepare.py` 校验归档及每个解压文件的 SHA-256，将工具解压到忽略的 `build/`，
并配置动态库搜索路径。重生成脚本同时固定工具 manifest 和解压脚本本身的哈希。
不需要本机存在 circt-spot 源码工作区。仅检查已有证明也不需要这个包。

## 工具来源及重新编译

- circt-spot 源码固定为 `96e4c04c3027f94a07705632c1d7b8708112c4fc`，
  完整 Git 源码快照在 `circt-spot-source.tar.xz`。
- CIRCT 固定为 `9de24b873409b154c977a015dff1a40f02ef020b`，
  来源 <https://github.com/llvm/circt>；LLVM 24 开发版，启用 assertions。
- Spot 2.16，源码 <https://www.lrde.epita.fr/dload/spot/spot-2.16.tar.gz>。
- firtool 1.158.0，采用原工程使用的发行二进制。

构建插件需要上述兼容的 CIRCT/MLIR 开发树、Spot 安装、CMake、Ninja 和 C++20 编译器：

```sh
# 在本工具目录下执行，替换两个依赖安装路径
mkdir -p build/rebuild-source
tar -xJf circt-spot-source.tar.xz -C build/rebuild-source
cmake -G Ninja -S build/rebuild-source/circt-spot -B build/rebuild-plugin \
  -DCMAKE_BUILD_TYPE=Release \
  -DCIRCT_DIR=/path/to/circt/lib/cmake/circt \
  -DMLIR_DIR=/path/to/circt/lib/cmake/mlir \
  -DSPOT_ROOT=/path/to/spot
cmake --build build/rebuild-plugin --target CIRCTSpotPlugin -j4
```

当前分发插件就是从上述固定提交新编译得到，随后与其他工具一起打包。
这里固定的是可运行转换链，不承诺不同编译器、系统下重编译的二进制逐字节相同。
替换工具需要发布新版本、更新任务中的工具哈希，并重新执行全部模型比较和证明检查。

## 运行环境

Python 3.12+（安全 tar 解压）、Java 21、Linux x86-64、glibc ≥ 2.43（circt-opt 的 libm 符号要求），
以及提供 GLIBCXX_3.4.32 的 libstdc++、libz、libgcc_s、libatomic。
Mill 启动器和依赖配置在任务 `source/` 中；首次运行需网络下载 Mill、JDK 和 Maven 依赖。
系统运行库不打包，不承诺兼容旧发行版、macOS 或 ARM。

# 工具版本

- [lean-export-20261105](lean-export-20261105/README.md)：Linux x86-64，约 21 MB；两个 CPU 任务使用的固定版本。

- [arithmetic-export-20261112](arithmetic-export-20261112/README.md)：算术任务四个后端的固定工具，包含 firtool 和导出插件源码快照。

每个版本保存在独立子目录；新增版本不覆盖旧包。任务 manifest 的 tool_bundle 指定所用版本。
工具压缩包使用 Git LFS 存储。安装 Git LFS 后，在仓库根目录执行：

```sh
git lfs install
git lfs pull
```

Git 中保存指针；本地下载完成后仍是原始压缩包，校验哈希不变。

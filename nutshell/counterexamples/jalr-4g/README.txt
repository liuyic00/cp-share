NutShell JALR 4GiB 反例候选资料包

本目录可直接整体拷贝；查看波形和记录不需要原项目。
打开波形：在本目录运行
  gtkwave jalr-4g.vcd jalr-4g.gtkw

文件说明：
  jalr-4g.vcd                完整波形（寄存器、输入输出、中间节点及检查信号）
  jalr-4g.gtkw               GTKWave 关键观测信号配置
  jalr-4g.summary.json       关键事件摘要
  jalr-4g.json               原反例记录，包含程序、逐周期输入及复现说明
  jalr-4g-trace.json         完整执行记录，包含初始状态、输入、输出及检查结果
  jalr-4g-trace.log          逐周期发现日志
  check-jalr-4g-runtime.log  原 Lean runtime 交叉检查日志
  SHA256SUMS                本目录文件校验和

关键事件（周期从 0 开始）：
  第 24 周期 / 240 ns：有效 IDU PC = 0x100000000，违反额外 PC32 限制。
  第 27 周期 / 270 ns：原始断言 43、45、46、47 失败。
  全部已记录 28 个周期内，四条原始 assume 均通过。
  时间采用每周期 10 ns 的展示尺度，状态在 10*t ns 展示，时钟上升沿在 10*t+5 ns。

证据边界：
  波形来自生成 Lean 电路模型的具体重放，不是独立 RTL 仿真。
  最终周期的全部生成表达式曾与 Lean runtime 交叉检查。
  这是有限执行反例候选，不是内核检查过的可达性反例，
  也尚未证明可无限延续且始终满足原始 Environment。

JSON 内的 build/、scripts/、lean/ 等路径是发现时的历史记录，非当前复现命令。
本目录保存反例结果，不包含当时的搜索脚本。当前模型与证明位于 ../../verification/lean/；
从 Chisel 重新生成模型的命令见 ../../README.md。
原 jalr-4g.json 中 restricted_goal_proved=false 是发现时的历史状态；
目前额外 PC32 限制下的全部断言已经证明，但无限制版本没有证明。

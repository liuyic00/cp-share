package singlefile.basic.fsm

import chisel3._
import chisel3.util._

class MacOperands(width: Int) extends Bundle {
  val a = UInt(width.W)
  val b = UInt(width.W)
  val c = UInt(width.W)
}

/** 多周期计算 y = (a + b) * c，输入为无符号数，结果不截断。
  *
  * 时序约定：在上升沿 t 发生 in.fire，记当时的输入为 A、B、C；
  * t 之后进入 add，t+1 之后进入 multiply，t+2 之后进入 output 并拉高 out.valid。
  * out.ready 不影响计算延迟；若下游反压，结果一直保持到 out.fire。
  * 同时最多处理一个事务，输出握手的同一拍不接收新输入。
  *
  * 性质的前提：先复位；事务期间若再次复位，则丢弃该事务。
  * 输入只在 in.fire 时采样，其余时间可以任意变化。
  * “最终产生 out.valid”不依赖下游；“最终发生 out.fire”需要下游最终给出 ready。
  * 以下断言用于仿真及后续形式化检查，本文件本身不代表已经完成形式化证明。
  */
class MultiCycleMac(width: Int = 8) extends Module {
  require(width > 0)

  val io = IO(new Bundle {
    val in  = Flipped(Decoupled(new MacOperands(width)))
    val out = Decoupled(UInt((2 * width + 1).W))
  })

  object State extends ChiselEnum {
    val idle, add, multiply, output = Value
  }
  val state = RegInit(State.idle)
  val operands = Reg(new MacOperands(width))
  val sum = Reg(UInt((width + 1).W))
  val result = Reg(UInt((2 * width + 1).W))

  io.in.ready := state === State.idle && !reset.asBool
  io.out.valid := state === State.output && !reset.asBool
  io.out.bits := Mux(io.out.valid, result, 0.U)

  switch(state) {
    is(State.idle) {
      // 空闲阶段：out.valid = 0；仅 in.fire 可创建事务并记录 A、B、C。
      // 不要求尚未初始化的 sum/result 满足任何性质。
      when(io.in.fire) {
        operands := io.in.bits
        state := State.add
      }
    }
    is(State.add) {
      // 加法阶段：operands = (A,B,C)，in.ready = out.valid = 0。
      // 本阶段结束后 sum = A+B；width+1 位容纳进位，不发生模截断。
      sum := operands.a +& operands.b
      state := State.multiply
    }
    is(State.multiply) {
      // 乘法阶段：sum = A+B，operands 仍为接收时的值。
      // 本阶段结束后 result = (A+B)*C；2*width+1 位可容纳最大结果。
      result := sum * operands.c
      state := State.output
    }
    is(State.output) {
      // 输出阶段：out.valid => out.bits = (A+B)*C，A/B/C 来自最近一次 in.fire，
      // 而非当前输入引脚。反压时 valid 和 bits 必须保持；仅 out.fire 返回 idle。
      when(io.out.fire) { state := State.idle }
    }
  }

  // 阶段不变量：这些条件只在相应寄存器已计算完成时检查。
  when(state === State.multiply || state === State.output) {
    assert(sum === (operands.a +& operands.b))
  }
  when(io.out.valid) {
    assert(io.out.bits === ((operands.a +& operands.b) * operands.c))
  }
  assert(!(io.in.ready && io.out.valid))

  // 跨周期性质：握手之后固定依次经过 add、multiply、output。
  // RegNext 的初值避免首次复位后引用无效历史；Chisel assert 在复位时不检查。
  val accepted = RegNext(io.in.fire, false.B)
  val wasAdding = RegNext(state === State.add, false.B)
  val wasMultiplying = RegNext(state === State.multiply, false.B)
  when(accepted) { assert(state === State.add) }
  when(wasAdding) { assert(state === State.multiply) }
  when(wasMultiplying) { assert(io.out.valid) }

  val stalled = RegNext(io.out.valid && !io.out.ready, false.B)
  val previousOutput = RegNext(io.out.bits)
  when(stalled) {
    assert(io.out.valid)
    assert(io.out.bits === previousOutput)
  }
}

object MultiCycleMacEmit extends App {
  val target = java.nio.file.Paths.get("build/verilog/basic/fsm")
  java.nio.file.Files.createDirectories(target)
  java.nio.file.Files.writeString(
    target.resolve("MultiCycleMac.fir"),
    _root_.circt.stage.ChiselStage.emitCHIRRTL(new MultiCycleMac())
  )
  java.nio.file.Files.writeString(
    target.resolve("MultiCycleMac.sv"),
    _root_.circt.stage.ChiselStage.emitSystemVerilog(new MultiCycleMac())
  )
}

package singlefile.basic.fsm

import chisel3._
import chisel3.simulator.scalatest.ChiselSim
import org.scalatest.flatspec.AnyFlatSpec

class MultiCycleMacSpec extends AnyFlatSpec with ChiselSim {
  behavior of "MultiCycleMac"

  for (width <- Seq(1, 8)) {
    it should s"preserve full precision, latency and backpressure at width $width" in {
      simulate(new MultiCycleMac(width)) { dut =>
        val max = (BigInt(1) << width) - 1
        val random = new scala.util.Random(0)
        val cases = if (width == 1) {
          for (a <- 0 to 1; b <- 0 to 1; c <- 0 to 1) yield (BigInt(a), BigInt(b), BigInt(c))
        } else {
          Seq((max, max, max), (max, max, BigInt(0)), (BigInt(0), BigInt(0), max)) ++
            Seq.fill(24)((BigInt(width, random), BigInt(width, random), BigInt(width, random)))
        }
        dut.io.in.valid.poke(false.B)
        dut.io.out.ready.poke(false.B)
        dut.clock.step()
        dut.io.in.ready.expect(true.B)
        dut.io.out.valid.expect(false.B)

        for (((a, b, c), index) <- cases.zipWithIndex) {
          dut.io.in.bits.a.poke(a)
          dut.io.in.bits.b.poke(b)
          dut.io.in.bits.c.poke(c)
          dut.io.in.valid.poke(true.B)
          dut.io.in.ready.expect(true.B)
          dut.io.out.ready.poke((index % 2 == 0).B)
          dut.clock.step() // 接收输入，进入 add。

          // 忙时保持 valid 并改变引脚，验证不会误接收或使用当前引脚计算。
          dut.io.in.bits.a.poke(max - a)
          dut.io.in.bits.b.poke(max - b)
          dut.io.in.bits.c.poke(max - c)
          for (_ <- 0 until 2) {
            dut.io.in.ready.expect(false.B)
            dut.io.out.valid.expect(false.B)
            dut.clock.step()
          }
          val expected = (a + b) * c
          dut.io.out.valid.expect(true.B)
          dut.io.out.bits.expect(expected)
          dut.io.in.ready.expect(false.B)

          if (index % 2 != 0) {
            for (_ <- 0 until 3) {
              dut.clock.step()
              dut.io.out.valid.expect(true.B)
              dut.io.out.bits.expect(expected)
              dut.io.in.ready.expect(false.B)
            }
          }
          dut.io.out.ready.poke(true.B)
          dut.clock.step() // 输出握手；本上升沿不能同时接收仍拉高的输入 valid。
          dut.io.in.valid.poke(false.B)
          dut.io.out.valid.expect(false.B)
          dut.io.in.ready.expect(true.B)
          dut.clock.step(2)
          dut.io.out.valid.expect(false.B) // 不得凭空生成重复事务。
        }
      }
    }
  }

  it should "discard an in-flight transaction on reset in every active stage" in {
    simulate(new MultiCycleMac(8)) { dut =>
      dut.io.out.ready.poke(false.B)
      dut.io.in.valid.poke(false.B)
      for (cyclesAfterAccept <- 0 to 2) {
        dut.io.in.bits.a.poke(200)
        dut.io.in.bits.b.poke(100)
        dut.io.in.bits.c.poke(3)
        dut.io.in.valid.poke(true.B)
        dut.io.in.ready.expect(true.B)
        dut.clock.step()
        dut.io.in.valid.poke(false.B)
        dut.clock.step(cyclesAfterAccept)
        dut.reset.poke(true.B)
        dut.io.in.ready.expect(false.B)
        dut.io.out.valid.expect(false.B)
        dut.clock.step()
        dut.reset.poke(false.B)
        dut.io.in.ready.expect(true.B)
        dut.clock.step(3)
        dut.io.out.valid.expect(false.B)
      }
      // 复位后仍能接收并完成新事务。
      dut.io.in.bits.a.poke(2)
      dut.io.in.bits.b.poke(3)
      dut.io.in.bits.c.poke(4)
      dut.io.in.valid.poke(true.B)
      dut.clock.step()
      dut.io.in.valid.poke(false.B)
      dut.clock.step(2)
      dut.io.out.valid.expect(true.B)
      dut.io.out.bits.expect(20)
      dut.io.out.ready.poke(true.B)
      dut.clock.step()
      dut.io.out.valid.expect(false.B)
      dut.io.in.ready.expect(true.B)
    }
  }
}

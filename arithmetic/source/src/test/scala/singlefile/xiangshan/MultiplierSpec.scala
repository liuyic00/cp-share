package singlefile.xiangshan.multiplier

import chisel3._
import chisel3.simulator.scalatest.ChiselSim
import org.scalatest.flatspec.AnyFlatSpec

import testutil.MulTestCase

class ArrayMulDataModuleSpec extends AnyFlatSpec with ChiselSim {
  behavior of "ArrayMulDataModule"

  val lens     = Seq(64)
  val testSize = 1

  lens.foreach { len =>
    it should s"pass in ${len} bits" in {
      simulate(new ArrayMulDataModule(len + 1)) { dut =>
        (1 to testSize).foreach { i =>
          val tc = MulTestCase.random(len)

          dut.io.a.poke(tc.xaBits)
          dut.io.b.poke(tc.xbBits)
          dut.io.regEnables(0).poke(true.B)
          dut.io.regEnables(1).poke(true.B)
          dut.clock.step(1)
          if (len >= 64) { dut.clock.step(1) }
          dut.io.result.expect(tc.xcBits)
        }
      }
    }
  }
}

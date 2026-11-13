package singlefile

import chisel3._
import _root_.circt.stage.ChiselStage
import java.nio.file.{Files, Paths}
import scala.sys.process._

/** Independent hierarchical models; never regenerates the legacy Lean tree. */
object HierarchicalLeanEmit extends App {
  val spot = Paths.get(sys.env.getOrElse("CIRCT_SPOT", "../circt-spot")).toAbsolutePath.normalize
  val circtOpt = sys.env.getOrElse("CIRCT_OPT", spot.resolve("deps/circt/bin/circt-opt").toString)
  val plugin = sys.env.getOrElse("SPOT_PLUGIN", spot.resolve("build/circt-spot/lib/CIRCTSpotPlugin.so").toString)
  val stageArgs = sys.env.get("FIRTOOL").map(path => Array("--firtool-binary-path", path))
    .getOrElse(Array.empty[String])
  val root = Paths.get(sys.env.getOrElse("ARITHMETIC_ROOT", "..")).toAbsolutePath.normalize
  val target = root.resolve("artifacts/chisel7/mlir/lean-hierarchical")
  Files.createDirectories(target)
  Files.createDirectories(root.resolve("verification/lean-hierarchical/Generated"))

  def emit(name: String, module: => RawModule): Unit = {
    val hwFile = target.resolve(s"$name.hw.mlir")
    val modelFile = root.resolve(s"verification/lean-hierarchical/Generated/$name.lean").toString
    Files.writeString(hwFile, ChiselStage.emitHWDialect(module,
      args = stageArgs,
      firtoolOpts = Array("--lower-to-core", "--verification-flavor=immediate",
        "--default-layer-specialization=enable")))
    val command = Seq(circtOpt, hwFile.toString,
      s"--load-pass-plugin=$plugin", "--mlir-print-op-on-diagnostic=false",
      s"--pass-pipeline=builtin.module(strip-om,hw.module(hw-aggregate-to-comb),canonicalize,export-lean-hierarchical{output-file=$modelFile})",
      "-o", "/dev/null")
    require(Process(command).! == 0, s"Hierarchical Lean export failed for $name")
    require(Process(Seq("python3", "../scripts/split-hierarchical-lean.py", modelFile)).! == 0,
      s"Hierarchical Lean partition failed for $name")
  }
    emit("Adder", new basic.alu.Adder(8))
    emit("MultiCycleMac", new basic.fsm.MultiCycleMac(8))
    emit("CSA2_2", new xiangshan.multiplier.CSA2_2(8))
    emit("CSA3_2", new xiangshan.multiplier.CSA3_2(8))
    emit("CSA5_3", new xiangshan.multiplier.CSA5_3(8))
    emit("C22", new xiangshan.multiplier.C22)
    emit("C32", new xiangshan.multiplier.C32)
    emit("C53", new xiangshan.multiplier.C53)
    emit("ArrayMulDataModule", new xiangshan.multiplier.ArrayMulDataModule(65))
    emit("Radix2Divider", new xiangshan.radix2divider.Radix2Divider(64))
    emit("MulDiv", new rocket.MulDiv.MulDiv(rocket.MulDiv.MulDivParams(), 64))
    emit("MulDivChecked", new rocket.MulDiv.MulDivChecked)
    emit("ArrayMulDataModule8", new xiangshan.multiplier.ArrayMulDataModule8)
}

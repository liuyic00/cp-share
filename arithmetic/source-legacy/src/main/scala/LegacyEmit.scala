import chisel3._
import chisel3.stage.ChiselStage
import java.nio.file.{Files, Paths, StandardCopyOption}

/** Use the Scala FIRRTL compiler directly; no CIRCT text conversion. */
object LegacyEmit extends App {
  val root = Paths.get(sys.env.getOrElse("ARITHMETIC_ROOT", "..")).toAbsolutePath.normalize
  val target = root.resolve("artifacts/chisel3/firrtl")
  val staging = root.resolve("build/legacy-stage")
  Files.createDirectories(target)
  Files.createDirectories(staging)
  def emit(name: String, gen: => RawModule): Unit = {
    for (stage <- Seq("high", "low")) {
      val suffix = if (stage == "high") "hi" else "lo"
      val filename = s"$name.$suffix.fir"
      (new ChiselStage).execute(Array("-X", stage, "--target-dir", staging.toString,
        "--output-file", filename), Seq(chisel3.stage.ChiselGeneratorAnnotation(() => gen)))
      Files.copy(staging.resolve(filename), target.resolve(filename), StandardCopyOption.REPLACE_EXISTING)
    }
  }
  emit("Adder", new singlefile.basic.alu.Adder(8))
  emit("MultiCycleMac", new singlefile.basic.fsm.MultiCycleMac(8))
  emit("CSA2_2", new singlefile.xiangshan.multiplier.CSA2_2(8))
  emit("CSA3_2", new singlefile.xiangshan.multiplier.CSA3_2(8))
  emit("CSA5_3", new singlefile.xiangshan.multiplier.CSA5_3(8))
  emit("C22", new singlefile.xiangshan.multiplier.C22)
  emit("C32", new singlefile.xiangshan.multiplier.C32)
  emit("C53", new singlefile.xiangshan.multiplier.C53)
  emit("ArrayMulDataModule", new singlefile.xiangshan.multiplier.ArrayMulDataModule(65))
  emit("Radix2Divider", new singlefile.xiangshan.radix2divider.Radix2Divider(64))
  emit("MulDiv", new singlefile.rocket.MulDiv.MulDiv(singlefile.rocket.MulDiv.MulDivParams(), 64))
  emit("MulDivChecked", new singlefile.rocket.MulDiv.MulDivChecked)
}

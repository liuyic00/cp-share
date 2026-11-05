// Compile against the unchanged upstream Chisel 3.6 / FIRRTL 1.6 classpath.
import chisel3.stage.{ChiselGeneratorAnnotation, ChiselStage}
import firrtl.stage.FirrtlCircuitAnnotation
import firrtl.transforms.formal.DontAssertSubmoduleAssumptionsAnnotation

object ExportRiscvMiniHigh extends App {
  require(args.length == 1, "usage: ExportRiscvMiniHigh OUTPUT_DIRECTORY")
  val annotations = (new ChiselStage).execute(
    Array("--target-dir", args(0), "-X", "high"),
    Seq(DontAssertSubmoduleAssumptionsAnnotation,
      ChiselGeneratorAnnotation(() =>
        new mini.CoreSoc(new mini.Core(mini.MiniConfig().core)))))
  require(!annotations.exists(_.getClass.getName.startsWith("firrtl.passes.wiring.")),
    "Unresolved BoringUtils wiring")
  val circuit = annotations.collectFirst { case FirrtlCircuitAnnotation(c) => c }.get
  require(Set("CoreSoc", "CheckerWithResult", "RiscvCore").subsetOf(
    circuit.modules.map(_.name).toSet), "Missing checker/reference hierarchy")
}

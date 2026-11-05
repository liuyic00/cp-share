// External driver; upstream source and dependency versions remain unchanged.
import chisel3.stage.{ChiselGeneratorAnnotation, ChiselStage}
import firrtl.stage.FirrtlCircuitAnnotation
import firrtl.transforms.formal.DontAssertSubmoduleAssumptionsAnnotation
import firrtl.passes.wiring.{SourceAnnotation, SinkAnnotation}
object ExportNutShellHigh extends App {
  require(args.length == 1, "usage: ExportNutShellHigh OUTPUT_DIRECTORY")
  _root_.top.Settings.settings ++= _root_.top.FormalSettings() ++ _root_.top.InOrderSettings() ++ Map("Formal" -> true, "RVFI" -> true)
  val elaborated = (new ChiselStage).execute(
    Array("--target-dir", args(0), "--no-run-firrtl"),
    Seq(DontAssertSubmoduleAssumptionsAnnotation,
      ChiselGeneratorAnnotation(() => new nutcore.NutCore()(nutcore.NutCoreConfig()))))
  val sinks = elaborated.collect { case a: SinkAnnotation => a.pin }.toSet
  val orphans = elaborated.collect { case a: SourceAnnotation if !sinks(a.pin) => a }
  require(orphans.map(_.pin).toSet == Set("RandReg"), "Unexpected orphan BoringUtils source")
  val annotations = (new firrtl.stage.FirrtlStage).execute(
    Array("-X", "high"), elaborated.filterNot(orphans.contains(_)))
  require(!annotations.exists(_.getClass.getName.startsWith("firrtl.passes.wiring.")),
    "Unresolved BoringUtils wiring")
  val circuit = annotations.collectFirst { case FirrtlCircuitAnnotation(c) => c }.get
  require(circuit.main == "NutCore")
}

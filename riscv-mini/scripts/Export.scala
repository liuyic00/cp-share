// External driver: compiled against the target project's unchanged classpath.
import chisel3.stage.{ChiselGeneratorAnnotation, ChiselStage}
import firrtl._
import firrtl.ir._
import firrtl.backends.experimental.smt.random.{InvalidToRandomPass, DefRandom}
import firrtl.passes.MemPortUtils
import scala.collection.mutable.ArrayBuffer
import firrtl.annotations.{CircuitName, ModuleName}
import firrtl.stage.FirrtlCircuitAnnotation
import firrtl.transforms.{Flatten, FlattenAnnotation}
import firrtl.transforms.formal.DontAssertSubmoduleAssumptionsAnnotation
import java.nio.file.{Files, Paths}

object ExportRiscvMini extends App {
  require(args.length == 1 || args.length == 2,
    "usage: ExportRiscvMini OUTPUT_DIRECTORY [ADAPTER_TEST_FIRRTL]")
  val dir = Paths.get(args(0)).toAbsolutePath
  Files.createDirectories(dir)
  val annotations = if (args.length == 2) {
    (new firrtl.stage.FirrtlStage).execute(
      Array("--target-dir", dir.toString, "-i", args(1), "-X", "low"),
      Seq(DontAssertSubmoduleAssumptionsAnnotation))
  } else (new ChiselStage).execute(
    Array("--target-dir", dir.toString, "-X", "low"),
    Seq(DontAssertSubmoduleAssumptionsAnnotation,
      ChiselGeneratorAnnotation(() => new mini.CoreSoc(new mini.Core(mini.MiniConfig().core)))))
  require(!annotations.exists(a => a.getClass.getName.startsWith("firrtl.passes.wiring.")),
    "Unresolved BoringUtils annotations")
  require(!annotations.exists(a => a.getClass.getSimpleName.matches(".*(Memory.*Init|LoadMemory).*")),
    "Memory initialization annotations need an explicit adapter")
  val circuit = annotations.collectFirst { case FirrtlCircuitAnnotation(c) => c }.get
  val flat = (new Flatten).runTransform(CircuitState(circuit, LowForm,
    Seq(FlattenAnnotation(ModuleName(circuit.main, CircuitName(circuit.main)))))).circuit
  val top = flat.modules.collectFirst { case m: Module if m.name == flat.main => m }.get
  def noInstances(s: Statement): Unit = {
    require(!s.isInstanceOf[DefInstance], "Flatten left an instance")
    s.foreachStmt(noInstances)
  }
  noInstances(top.body)
  val onlyTop = flat.copy(modules = Seq(top))
  Files.writeString(dir.resolve("CoreSoc.flat.fir"), onlyTop.serialize)
  val randomized = InvalidToRandomPass.runTransform(CircuitState(onlyTop, LowForm)).circuit
  val m = randomized.modules.head.asInstanceOf[Module]
  val ns = Namespace(m)
  val ports = ArrayBuffer.empty[Port]
  var prints = 0
  var memories = 0
  def arbitrary(hint: String, tpe: Type): Expression = {
    val name = ns.newName(hint)
    ports += Port(NoInfo, name, Input, tpe)
    WRef(name, tpe, PortKind, SourceFlow)
  }
  def passive(t: Type): Type = t match {
    case b: BundleType => b.copy(fields = b.fields.map(f => f.copy(flip = Default, tpe = passive(f.tpe))))
    case other => other
  }
  def and(a: Expression, b: Expression): Expression = Utils.and(a, b)
  def lower(s: Statement): Statement = s match {
    case r: DefRandom =>
      require(r.clock.isEmpty, "Clocked random source is unsupported")
      ports += Port(r.info, r.name, Input, r.tpe)
      EmptyStmt
    case _: Print => prints += 1; EmptyStmt // observational diagnostics only
    case _: Stop => sys.error("Cannot discard a stop operation")
    case mem: DefMemory =>
      require(mem.readLatency == 0 && mem.writeLatency == 1 && mem.readwriters.isEmpty,
        "Only asynchronous-read, synchronous-write memories are supported")
      require(mem.writers.size <= 1 && mem.depth >= 2 && mem.depth <= 1024 &&
        (mem.depth & (mem.depth - 1)) == 0, "Unsupported memory depth or write ports")
      require(mem.dataType.isInstanceOf[UIntType], "Only UInt memories are supported")
      memories += 1
      val stmts = ArrayBuffer.empty[Statement]
      val portType = MemPortUtils.memType(mem)
      stmts += DefWire(mem.info, mem.name, passive(portType))
      def field(p: String, f: String): Expression = MemPortUtils.memPortField(mem, p, f)
      val clockPort = mem.writers.headOption.orElse(mem.readers.headOption).get
      val regs = (0 until mem.depth.toInt).map { j =>
        val name = ns.newName(s"${mem.name}_word_$j")
        val ref = WRef(name, mem.dataType, RegKind, SourceFlow)
        stmts += DefRegister(mem.info, name, mem.dataType, field(clockPort, "clk"), Utils.zero, ref)
        val next = mem.writers.headOption.map { w =>
          val selected = Utils.eq(field(w, "addr"), UIntLiteral(j))
          Utils.mux(and(and(field(w, "en"), field(w, "mask")), selected), field(w, "data"), ref)
        }.getOrElse(ref)
        stmts += Connect(mem.info, ref, next)
        ref
      }
      mem.readers.foreach { r =>
        val selected = regs.zipWithIndex.foldRight[Expression](regs.last) {
          case ((reg, j), tail) => Utils.mux(Utils.eq(field(r, "addr"), UIntLiteral(j)), reg, tail)
        }
        val disabled = arbitrary(s"${mem.name}_${r}_disabled", mem.dataType)
        stmts += Connect(mem.info, field(r, "data"), Utils.mux(field(r, "en"), selected, disabled))
      }
      Block(stmts.toSeq)
    case other => other.mapStmt(lower)
  }
  def verifications(s: Statement): Seq[String] = {
    val found = ArrayBuffer.empty[String]
    def visit(stmt: Statement): Unit = {
      stmt match { case v: Verification => found += v.serialize; case _ => () }
      stmt.foreachStmt(visit)
    }
    visit(s)
    found.toSeq
  }
  val body = lower(m.body)
  require(verifications(m.body) == verifications(body), "Adapter changed verification statements")
  val prepared = randomized.copy(modules = Seq(m.copy(ports = m.ports ++ ports, body = body)))
  Files.writeString(dir.resolve("CoreSoc.prepared.fir"), prepared.serialize)
  println(s"Explicit arbitrary inputs: ${ports.size}; lowered memories: $memories; removed diagnostic prints: $prints")
  println(s"Wired and flattened FIRRTL: ${dir.resolve("CoreSoc.flat.fir")}")
}

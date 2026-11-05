// Hierarchy-preserving adapter for the supported small UInt memories.
import firrtl._
import firrtl.ir._
import firrtl.passes.MemPortUtils
import scala.collection.mutable.ArrayBuffer
import java.nio.file.{Files, Paths}

object MemToRegsHigh {
  def convert(circuit: Circuit): Circuit = {
    var memories = 0
    val result = circuit.copy(modules = circuit.modules.map {
      case m: Module =>
        val ns = Namespace(m)
        def passive(t: Type): Type = t match {
          case b: BundleType => b.copy(fields = b.fields.map(f => f.copy(flip = Default, tpe = passive(f.tpe))))
          case other => other
        }
        def and(a: Expression, b: Expression): Expression = Utils.and(a, b)
        def lower(s: Statement): Statement = s match {
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
              // Disabled asynchronous reads remain undefined in High FIRRTL.
              stmts += Connect(mem.info, field(r, "data"), ValidIf(field(r, "en"), selected, mem.dataType))
            }
            Block(stmts.toSeq)
          case other => other.mapStmt(lower)
        }
        m.copy(body = lower(m.body))
      case other => other
    })
    require(memories == 2, s"Expected CoreSoc imem/dmem; found $memories memories")
    result
  }
  def main(args: Array[String]): Unit = {
    require(args.length == 2, "usage: MemToRegsHigh INPUT.hi.fir OUTPUT.nomem.hi.fir")
    val circuit = Parser.parse(Files.readString(Paths.get(args(0))))
    Files.writeString(Paths.get(args(1)), convert(circuit).serialize)
  }
}

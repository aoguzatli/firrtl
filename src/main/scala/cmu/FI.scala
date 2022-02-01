package cmu

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.annotations._
import firrtl.options.Dependency
import firrtl.stage.Forms
import firrtl.stage.TransformManager.TransformDependency
import firrtl.transforms.DeadCodeElimination
import java.io.{File, PrintWriter}
import scala.collection.mutable.ListBuffer
import scala.collection.mutable
import scala.math.log
import scala.io.Source


object CustomOps {
  def and(a: Expression, b: Expression) = DoPrim(PrimOps.And, Seq(a, b), Nil, a.tpe)
  def or(a: Expression, b: Expression) = DoPrim(PrimOps.Or, Seq(a, b), Nil, a.tpe)
  def xor(a: Expression, b: Expression) = DoPrim(PrimOps.Xor, Seq(a, b), Nil, a.tpe)
  def not(a: Expression) = DoPrim(PrimOps.Not, Seq(a), Nil, a.tpe)
  def mux(s: Expression, a1: Expression, a0: Expression) = or(and(s, a1), and(not(s), a0))
  def asSInt(a: Expression) = DoPrim(PrimOps.AsSInt, Seq(a), Nil, SIntType(UnknownWidth))
  def asUInt(a: Expression) = DoPrim(PrimOps.AsUInt, Seq(a), Nil, UIntType(UnknownWidth))
}

object InjInterfaceFF {
  import CustomOps._

  def apply(d: Expression, q: Expression, inj: Expression, halt: Expression): Expression = {
    // Mux(inj, not(q), Mux(halt, q, d))
    // == (inj & not(q)) | (not(inj) & Mux...))
//    val logic = or(and(inj, not(asUInt(q))), and(not(inj), Mux(halt, asUInt(q), asUInt(d))))
    val logic = mux(inj, not(asUInt(q)), Mux(halt, asUInt(q), asUInt(d)))
    if (d.tpe.isInstanceOf[SIntType]) {
      asSInt(logic)
    } else {
      logic
    }
  }
}

object InjInterfaceMacro {
  import CustomOps._

  def apply(d: Expression, radr: Expression, wadr: Expression, we: Expression, q: Expression, mask: Expression,
            injEn: Expression, injBitsRow: Expression, injBitsCol: Expression, halt: Expression):
            (Expression, Expression, Expression, Expression, Expression) = {
    val maskWidth =  IntWidth.unapply(mask.tpe.asInstanceOf[GroundType].width.asInstanceOf[IntWidth]).get.toInt
    val dOut = Mux(injEn, xor(q, injBitsCol), d)
    val weOut = or(injEn, and(not(halt), we))
    val radrOut = Mux(injEn, injBitsRow, radr)
    val wadrOut = Mux(injEn, injBitsRow, wadr)
    val maskOut = Mux(injEn, UIntLiteral((1<<maskWidth)-1), mask)
    (dOut, weOut, radrOut, wadrOut, maskOut)
  }

    def gatedWE(halt: Expression, we: Expression) = {
      and(not(halt), we)
    }
}


class ModuleData() {
  val insts = mutable.Map[String, ModuleData]()
  val macros = mutable.Map[String, MacroData]()
  val clkNetwork = mutable.Map[String, String]()
  var ffs = 0

  var _allffs = Option.empty[Int]
  var _allMacros = Option.empty[mutable.Map[String, MacroData]]
  var _ffOffset = 0
  var _macroOffset = 0

  def getMacroOffset(width: Int): Int = {
    _macroOffset += width
    assert(_macroOffset <= allMacros.size)
    _macroOffset - width
  }

  def getFFOffset(width: Int): Int = {
    _ffOffset += width
    assert(_ffOffset <= allffs)
    _ffOffset - width
  }

  def allffs: Int = {
    if (_allffs.isEmpty) {
      _allffs = Some(ffs + insts.map(_._2.allffs).sum)
    }
    _allffs.get
  }

  def allMacros: mutable.Map[String, MacroData] = {
    if (_allMacros.isEmpty) {
      _allMacros = Some(macros)
      for ((instName, instData) <- insts) {
        for ((macroName, instMacro) <- instData.allMacros)
        _allMacros.get(s"${instName}/${macroName}") = instMacro
      }
//      println(s"Total ${m.name}: ${_allMacros.get}")
    }
    _allMacros.get
  }

  def maxMacroWidth: Int = {
    assert(allMacros.nonEmpty)
    allMacros.map(_._2.width).max
  }

  def getHaltPortOf(name: String): Expression = {
    val matches = clkNetwork.filter(_._1 == name)
    if (matches.isEmpty) {
      val portName = name.split("/")
      if (portName.size == 2) {
        return SubField(WRef(portName(0)), s"halt_${portName(1)}", ClockType)
      } else {
        return WRef(s"halt_${name}")
      }

    } else {
      assert(matches.size == 1)
      return getHaltPortOf(matches(name))
    }
  }

  def setFFParams(n: Int): Unit = {
    _allffs = Some(n)
  }

  def setMacroParams(n: Int, width: Int) : Unit = {
    val macroMap = for (i <- 0 until n) yield ("Dummy", new MacroData("Dummy", width, mutable.Map[String, Expression]()))
    _allMacros = Some(mutable.Map() ++ macroMap.toMap)
  }
}

class ExtModuleData(numFFs: Int, injSelWidth: Int, injBitsWidth: Int) extends ModuleData {
  _allffs = Some(numFFs)
  _allMacros = Some(_dummyMacros(injSelWidth))

  def _dummyMacros(i: Int) : mutable.Map[String, MacroData] = {
    val macroMap = for (i <- 0 until injSelWidth) yield ("Dummy", new MacroData("Dummy", injBitsWidth, mutable.Map[String, Expression]()))
    mutable.Map() ++ macroMap.toMap
  }
}

case class MacroData(tpe: String, width: Int, signals: mutable.Map[String, Expression]);

class FI extends Transform {
  val inputForm = LowForm
  val outputForm = HighForm

  val annotationClasses = Seq(classOf[TMRAnnotation])
  val bannedModules = Seq()

  def log2Up(x: Int) : Int = {
    math.max(1, (log(x.toFloat)/log(2.0)).toInt)
  }

  var stmtDelta = 0

  def connectInjStmt(moduleData: ModuleData, fp: PrintWriter)(s: Statement): Statement = {
    s match {
      case Connect(info, WRef(name, tpe, RegKind, SinkFlow), rhs_orig) if moduleData.allffs != 0  => // Need the if check because of TLMonitors
        val width = IntWidth.unapply(tpe.asInstanceOf[GroundType].width.asInstanceOf[IntWidth]).get.toInt
        val offset = moduleData.getFFOffset(width)
        val clk = moduleData.clkNetwork(name)
        val halt = moduleData.getHaltPortOf(clk)
        val inj = DoPrim(PrimOps.Bits, Seq(WRef("inj_ff")), Seq(offset + width - 1, offset), UnknownType)
        val lhs = WRef(name)
        val rhs = InjInterfaceFF(rhs_orig, lhs, inj, halt)
        val conn = Connect(info, lhs, rhs)
        fp.write(s"reg ${name} ${offset + width - 1}:${offset}\n")
        conn

      case s: DefMemory =>
        val memData = moduleData.macros(s.name)
        if (memData.tpe == "SyncMem") {
          s
        } else {
          // Works for single ported FF-based async memories for now
//          assert(s.readers.size == 1 && s.writers.size == 1)
          val rdPort = s.readers(0)
          val wrPort = s.writers(0)
          val width = IntWidth.unapply(s.dataType.asInstanceOf[GroundType].width.asInstanceOf[IntWidth]).get.toInt
          val depth = s.depth.intValue

          val d = memData.signals(s"${wrPort}/data")
          val q = SubField(SubField(Reference(s.name), rdPort), "data")
          val radr = memData.signals(s"${rdPort}/addr")
          val wadr = memData.signals(s"${wrPort}/addr")
          val we = memData.signals(s"${wrPort}/en")
          val re = memData.signals(s"${rdPort}/en")
          val wclk = memData.signals(s"${wrPort}/clk")
          val rclk = memData.signals(s"${rdPort}/clk")
          val mask = memData.signals(s"${wrPort}/mask")
          val halt = moduleData.getHaltPortOf(wclk.asInstanceOf[HasName].name)
          val injEnIdx = moduleData.getMacroOffset(1)
          val injEn = DoPrim(PrimOps.Bits, Seq(WRef("inj_macro_sel")), Seq(injEnIdx, injEnIdx), UnknownType)

          val injBits = WRef("inj_macro_bits")
          val injBitsCol = DoPrim(PrimOps.Bits, Seq(injBits), Seq(log2Up(width)-1, 0), UnknownType)
          val injBitsRow = DoPrim(PrimOps.Bits, Seq(injBits), Seq(log2Up(width)+log2Up(depth)-1, log2Up(width)), UnknownType)

          val (dNew, weNew, radrNew, wadrNew, maskNew) = InjInterfaceMacro(d, radr, wadr, we, q, mask, injEn, injBitsRow, injBitsCol, halt)

          val info = NoInfo
          val wadrConn = Connect(info, SubField(SubField(Reference(s.name), wrPort), "addr"), wadrNew)
          val weConn = Connect(info, SubField(SubField(Reference(s.name), wrPort), "en"), weNew)
          val wclkConn = Connect(info, SubField(SubField(Reference(s.name), wrPort), "clk"), wclk)
          val dConn = Connect(info, SubField(SubField(Reference(s.name), wrPort), "data"), dNew)
          val maskConn = Connect(info, SubField(SubField(Reference(s.name), wrPort), "mask"), maskNew)

          val radrConn = Connect(info, SubField(SubField(Reference(s.name), rdPort), "addr"), radrNew)
          val reConn = Connect(info, SubField(SubField(Reference(s.name), wrPort), "en"), re)
          val rclkConn = Connect(info, SubField(SubField(Reference(s.name), wrPort), "clk"), rclk)

          var newStmts = Seq(wadrConn, weConn, wclkConn, dConn, radrConn, reConn, rclkConn, maskConn)

          // TODO: Gating the WE of the other write ports. Assumes they operate on the same clk domain
          // separate power domains.
          for (i <- 1 until s.writers.size) {
            val auxWrPort = s.writers(i)
            val newAuxWE = InjInterfaceMacro.gatedWE(halt, memData.signals(s"${auxWrPort}/en"))
            newStmts = newStmts ++ Seq(
              Connect(info, SubField(SubField(Reference(s.name), auxWrPort), "addr"), memData.signals(s"${auxWrPort}/addr")),
              Connect(info, SubField(SubField(Reference(s.name), auxWrPort), "en"), newAuxWE),
              Connect(info, SubField(SubField(Reference(s.name), auxWrPort), "clk"), memData.signals(s"${auxWrPort}/clk")),
              Connect(info, SubField(SubField(Reference(s.name), auxWrPort), "data"), memData.signals(s"${auxWrPort}/data")),
              Connect(info, SubField(SubField(Reference(s.name), auxWrPort), "mask"), memData.signals(s"${auxWrPort}/mask")))
          }

          for (i <- 1 until s.readers.size) {
            val auxRdPort = s.readers(i)
            newStmts = newStmts ++ Seq(
              Connect(info, SubField(SubField(Reference(s.name), auxRdPort), "addr"), memData.signals(s"${auxRdPort}/addr")),
              Connect(info, SubField(SubField(Reference(s.name), auxRdPort), "en"), memData.signals(s"${auxRdPort}/en")),
              Connect(info, SubField(SubField(Reference(s.name), auxRdPort), "clk"), memData.signals(s"${auxRdPort}/clk")))
          }

          stmtDelta += newStmts.size
          s
        }

      case s: DefInstance =>
        if (s.module == "cc_dir_0_ext") {
          println(s"Debug: 1")
        }
        if (!moduleData.insts.contains(s.name)) {
          s
        } else {
          if (s.module == "cc_dir_0_ext") {
            println(s"Debug: 2")
          }

          val newStmts = mutable.ArrayBuffer[Statement]()

          val ffWidth = moduleData.insts(s.name).allffs
          if (ffWidth == 0) {
            s
          } else {
            val ffOffset = moduleData.getFFOffset(ffWidth)
            val lhs = SubField(WRef(s.name), "inj_ff", UnknownType, UnknownFlow)
            val rhs = DoPrim(PrimOps.Bits, Seq(WRef("inj_ff")), Seq(ffOffset + ffWidth - 1, ffOffset), lhs.tpe)
            val inj_connect = PartialConnect(s.info, lhs, rhs)
            fp.write(s"inst_ff:${s.module} ${s.name} ${ffOffset + ffWidth - 1}:${ffOffset}\n")
            newStmts += inj_connect
          }

          val macroInjWidth = moduleData.insts(s.name).allMacros.size
          if (macroInjWidth == 0) {
            s
          } else {
            if (s.module == "cc_dir_0_ext") {
              println(s"Debug: 3")
            }
            val macroOffset = moduleData.getMacroOffset(macroInjWidth)
            val sel_lhs = SubField(WRef(s.name), "inj_macro_sel", UnknownType, UnknownFlow)
            val sel_rhs = DoPrim(PrimOps.Bits, Seq(WRef("inj_macro_sel")), Seq(macroOffset + macroInjWidth - 1, macroOffset), sel_lhs.tpe)

            val bits_lhs = SubField(WRef(s.name), "inj_macro_bits", UnknownType, UnknownFlow)
            val bits_rhs = Reference("inj_macro_bits")

            fp.write(s"inst_macro:${s.module} ${s.name} ${macroOffset + macroInjWidth - 1}:${macroOffset}\n")
            newStmts += PartialConnect(s.info, sel_lhs, sel_rhs)
            newStmts += PartialConnect(s.info, bits_lhs, bits_rhs)
          }
          Block(Seq(s) ++ newStmts)
        }

      case _ =>
        s map connectInjStmt(moduleData, fp)
    }
  }

  def connectHaltStmt(moduleData: ModuleData)(s: Statement): Statement = {
    s match {
      // instance.clock <= clockPort
      case s: DefInstance =>
        val clks = moduleData.clkNetwork.filter(_._1.split("/")(0) == s.name)
        val halt_connects = clks.map(clk => Connect(s.info, SubField(WRef(s.name), s"halt_${clk._1.split("/")(1)}", UnknownType, UnknownFlow), moduleData.getHaltPortOf(clk._2)))
        Block(Seq(s) ++ halt_connects)

      // clockPort <= net
      case Connect(info, Reference(lhs_name, ClockType, PortKind, lhs_flow), Reference(rhs_name, rhs_type, rhs_kind, rhs_flow)) =>
        val halt_conn = Connect(info,
          WRef(s"halt_${lhs_name}"),
          moduleData.getHaltPortOf(rhs_name))
        Block(Seq(s, halt_conn))

      // clockPort <= instance.clock
      case Connect(info, Reference(lhs_name, ClockType, PortKind, lhs_flow), SubField(rhs_ref, rhs_name, rhs_kind, rhs_flow)) =>
        val halt_conn = Connect(info,
          WRef(s"halt_${lhs_name}"),
          moduleData.getHaltPortOf(s"${rhs_ref.serialize}/$rhs_name"))
        Block(Seq(s, halt_conn))

      // instance.clock <= otherInstance.clock
      case Connect(info, SubField(lhs_ref, lhs_name, ClockType, lhs_flow), SubField(rhs_ref, rhs_name, rhs_kind, rhs_flow)) =>
        val halt_conn = Connect(info,
          moduleData.getHaltPortOf(s"${lhs_ref.serialize}/$lhs_name"),
          moduleData.getHaltPortOf(s"${rhs_ref.serialize}/$rhs_name"))
        Block(Seq(s, halt_conn))

      case _ =>
        s map connectHaltStmt(moduleData)
    }
  }


  def addInjPortsMod(moduleDataMap: Map[String, ModuleData])(m: DefModule) : DefModule = {
    val moduleData = moduleDataMap(m.name)
    val inj_ff_width = moduleData.allffs
    val inj_macro_sel_width = moduleData.allMacros.size

    val newPorts = mutable.ListBuffer[Port]()
    if (inj_ff_width != 0) {
      newPorts += Port(NoInfo, "inj_ff", Input, UIntType(new IntWidth(inj_ff_width)))
    }
    if (inj_macro_sel_width != 0) {
      newPorts += Port(NoInfo, "inj_macro_sel", Input, UIntType(new IntWidth(inj_macro_sel_width)))
      val inj_macro_bits_width = moduleData.maxMacroWidth
      newPorts += Port(NoInfo, "inj_macro_bits", Input, UIntType(new IntWidth(inj_macro_bits_width)))
    }

    m match {
      case Module(info, name, _, body) =>
        Module(info, name, m.ports ++ newPorts, body)
      case ExtModule(info, name, ports, defname, params) =>
        ExtModule(info, name, ports ++ newPorts, defname, params)
    }
  }

  def addHaltPortsMod(m: DefModule) : DefModule = {
    val clkPorts = m.ports.filter(_.tpe == ClockType)
    val haltPorts = clkPorts.map(p => Port(NoInfo, s"halt_${p.name}", p.direction, UIntType(new IntWidth(1))))

    val newPorts = haltPorts ++ m.ports

    m match {
      case Module(info, name, _, body) =>
        if (clkPorts.isEmpty || bannedModules.contains(name) ) {
          m
        } else {
          Module(info, name, newPorts, body)
        }
      case ExtModule(info, name, ports, defname, params) =>
        if (clkPorts.isEmpty || bannedModules.contains(name) ) {
          m
        } else {
          ExtModule(info, name, newPorts, defname, params)
        }
    }
  }

  def connectInjMod(moduleDataMap: Map[String, ModuleData], fp: PrintWriter)(m: DefModule): DefModule = {
    if (bannedModules.contains(m.name)) {
      fp.write(s"--- Module skipped: ${m.name} - Numffs: ${moduleDataMap(m.name).allffs}\n")
      m
    } else {
      fp.write(s"--- Module: ${m.name}\n")
      m match {
        case i: Module =>
          println(s"Class: ${i.body.getClass}")
        case _ =>
      }

      m map connectInjStmt(moduleDataMap(m.name), fp)


    }
  }

  def connectHaltMod(moduleDataMap: Map[String, ModuleData])(m: DefModule) : DefModule = {
    val moduleData = moduleDataMap(m.name)
    val clkPorts = m.ports.filter(_.tpe == ClockType)

    if (bannedModules.contains(m.name) || clkPorts.isEmpty) {
      m
    } else {
      m map connectHaltStmt(moduleData)
    }
  }

  def populateModulePorts(moduleData: ModuleData)(s: Statement) : Statement = {
    /*
     * Find the AsyncMem port connections and populate ModuleData to contain the nets that
     * connect to them. It also removes those statements to be replaced by the connectInj method.
     */
//    if (containsReference(s, "io_deq_bits_data")) {
//      println("This stmt contains the net:")
//      println(s)
//    }

    val asyncMems = moduleData.macros.filter(m => m._2.tpe == "AsyncMem").keys.toSeq
    s match {
      // Sinkflow
      case Connect(info, SubField(SubField(Reference(memName, _, _, _), portName, _, _), pinName, _, _), net)
        if asyncMems.contains(memName) =>
//          println(s"Memory connection: ${memName}/${portName}/${pinName}")
          moduleData.macros(memName).signals(s"${portName}/${pinName}") = net
          stmtDelta -= 1
          EmptyStmt

//      // Sourceflow
//      case Connect(info, net, SubField(SubField(Reference(memName, _, _, _), portName, _, _), pinName, _, _))
//        if asyncMems.contains(memName) =>
//          if (net.asInstanceOf[HasName].name == "io_deq_bits_data") {
//            println("MATCHED")
//            println(s)
//          }
//          println(s"Memory connection: ${memName}/${portName}/${pinName}")
//          moduleData.macros(memName).signals(s"${portName}/${pinName}") = net
//          EmptyStmt

      case _ =>
        s map populateModulePorts(moduleData)
    }
  }

  def containsReference(s: Statement, str: String) : Boolean = {
//    s.foreachStmt(i => if (containsReference(i, str)) return true)
    s.foreachExpr(i => if (containsReference(i, str)) return true)
    return false
  }

  def containsReference(e: Expression, str: String): Boolean = {
    e match {
      case i: HasName if i.name == str =>
        return true
      case _ =>
        e.foreachExpr(i => if (containsReference(i, str)) return true)
    }
    return false
  }

  def printModule(m: DefModule): Unit = {
    m.foreachStmt(printStatement)
  }

  def printStatement(s: Statement): Unit = {
    if (isComplexStmt(s)) {
      s.foreachStmt(printStatement)
    } else {
      println(s)
    }
  }

  def isComplexStmt(s: Statement): Boolean = {
    var out = false
    s.foreachStmt{case i =>
      out = true
    }
    out
  }

  def populateClkNetwork(moduleData: ModuleData)(s: Statement) : Statement = {
    val clkNetwork = moduleData.clkNetwork
    s match {
      // inst.clock <= clockPort
      case Connect(info, SubField(Reference(inst_name, _, _, _), lhs_name, ClockType, _), Reference(rhs_name, ClockType, _, _)) =>
        clkNetwork(s"${inst_name}/${lhs_name}") = rhs_name

      // reg name : Clock
      case d: DefRegister =>
        clkNetwork(d.name) = d.clock match {
          case SubField(Reference(rhs_inst_name, _, _, _), rhs_name, ClockType, _) =>
            s"${rhs_inst_name}/${rhs_name}"
          case _ =>
            d.clock.serialize
        }

      case m: DefMemory =>
        (m.readers ++ m.writers ++ m.readwriters).foreach(port => s"${m.name}/${port}/clock")

      case Connect(info, WRef(lhs_name, ClockType, _, _), WRef(rhs_name, ClockType, _, _)) =>
        clkNetwork(lhs_name) = rhs_name

      case DefNode(info, lhs_name, SubField(Reference(rhs_inst_name, _, _, _), rhs_name, ClockType, _)) =>
        clkNetwork(lhs_name) = s"${rhs_inst_name}/${rhs_name}"

      case DefNode(info, lhs_name, rhs) =>
        val signals = new ListBuffer[String]
        val clocks = new ListBuffer[String]
        s map findRef(signals, clocks)
        val all = signals ++ clocks
        all.size match {
          case 0 =>
          case 1 =>
            var rhs_name = all.head
            clkNetwork(lhs_name) = rhs_name
          case _ =>
            clocks.size match {
              case 0 =>
              case 1 =>
                clkNetwork(lhs_name) = clocks.head
              case _ =>
                throw new Exception(s"Single clock node fan-in to every clock node assumption broken at ${lhs_name}${info}")
            }

        }
      case _ =>
    }

    s map populateClkNetwork(moduleData)
  }

  def findRef(signals: ListBuffer[String], clocks: ListBuffer[String])(e: Expression) : Expression = {
    e match {
      case Reference(name, ClockType, _, _) =>
        clocks += name
      case Reference(name, _, _, _) =>
        signals += name
      case _ =>
    }
    e map findRef(signals, clocks)
  }

  def populateModuleData(moduleDataMap: Map[String, ModuleData])(m: DefModule) : DefModule = {
    if (!m.ports.forall(_.direction == Input))
      m map populateInsts(m, moduleDataMap)

//    println(s"MODULE: ${m.name}")
    m map populateClkNetwork(moduleDataMap(m.name))
    m map populateModulePorts(moduleDataMap(m.name))
    m
  }

  def populateInsts(m: DefModule, moduleDataMap: Map[String, ModuleData])(s: Statement) : Statement = {
    val moduleData = moduleDataMap(m.name)
    s match {
      case i: DefInstance =>
        moduleData.insts(i.name) = moduleDataMap(i.module)
        s

      case i: DefRegister =>
        val width = i.tpe.asInstanceOf[GroundType].width.asInstanceOf[IntWidth]
        moduleData.ffs += IntWidth.unapply(width).get.toInt
        s

      case i: DefMemory =>
        val width = IntWidth.unapply(i.dataType.asInstanceOf[GroundType].width.asInstanceOf[IntWidth]).get.toInt
        val depth = i.depth
        val id = i.name
        val tpe = if (i.readLatency == 1 && i.writeLatency == 1) "SyncMem"
          else if (i.readLatency == 0 && i.writeLatency == 1) "AsyncMem"
          else "ERROR"

        assert(tpe != "ERROR")
        moduleData.macros(id) = MacroData(tpe, log2Up(depth.intValue) + log2Up(width), mutable.Map[String, Expression]())

//        if (tpe == "AsyncMem") {
//          println(s"Module ${m.name} AsyncMem ${i.name}: ${i.readers.size}R${i.writers.size}W")
//        }

        s

      case _ =>
        s map populateInsts(m, moduleDataMap)
    }
  }

  def populateExtModuleData(moduleDataMap: Map[String, ModuleData], path: String) : Unit = {
    val source = Source.fromFile(path)

    println(moduleDataMap.keys)

    for (line <- source.getLines) {
      val splitLine = line.split(" ")
      val paramItems = for (i <- 0 until splitLine.length by 2) yield {
        splitLine(i) -> splitLine(i+1)
      }
      val params = paramItems.toMap
      val injBitsWidth = log2Up(params("depth").toInt) + log2Up(params("width").toInt)
      moduleDataMap(params("name")).setFFParams(0)
      moduleDataMap(params("name")).setMacroParams(n=1, width=injBitsWidth)
    }
    source.close
  }

  def execute(state: CircuitState): CircuitState = {
    // TODO: Need to check if inj port already exists
    val extModuleFile = "regress/DigitalTop.mems.conf"
    var circuit = state.circuit

//    for (m <- circuit.modules) {
//      if (m.name == "Queue_7") {
//        printModule(m)
//      }
//    }
    println(s"Characterizing the circuit -- ${circuit.modules.size}")
    val moduleDataMap = circuit.modules.map(m => m.name -> new ModuleData).toMap
    circuit = circuit map populateModuleData(moduleDataMap)
    populateExtModuleData(moduleDataMap, extModuleFile)

    println(s"Creating extra ports -- ${circuit.modules.size}")
    circuit = circuit map addInjPortsMod(moduleDataMap)
    circuit = circuit map addHaltPortsMod

    val fp = new PrintWriter(new File("fiff.log"))
    println(s"Connecting inj -- ${circuit.modules.size}")
    circuit = circuit map connectInjMod(moduleDataMap, fp)
    println(s"Connecting halt -- ${circuit.modules.size}")
    circuit = circuit map connectHaltMod(moduleDataMap)
    fp.close()
//
    val outState = state.copy(circuit = circuit)
    println(s"Done! -- ${circuit.modules.size}")
    println(s"stmtDelta: ${stmtDelta}")

    println(moduleDataMap("cc_dir_0").allMacros)

    outState
  }
}

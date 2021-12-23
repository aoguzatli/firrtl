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

import jdk.nashorn.internal.runtime.regexp.joni.exception.ValueException

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Map
import scala.collection.mutable

class IntPtr {
  var value = 0
}



object InjInterface {
  private def and(a: Expression, b: Expression) = DoPrim(PrimOps.And, Seq(a, b), Nil, a.tpe)
  private def or(a: Expression, b: Expression) = DoPrim(PrimOps.Or, Seq(a, b), Nil, a.tpe)
  private def not(a: Expression) = DoPrim(PrimOps.Not, Seq(a), Nil, a.tpe)
//  private def asSInt(a: Expression) = a match {
//    case DoPrim(_, _, _, t: UIntType) =>
//      DoPrim(PrimOps.AsSInt, Seq(a), Nil, SIntType(t.width))
//    case _ =>
//      throw new RuntimeException
//  }

  private def asSInt(a: Expression) = DoPrim(PrimOps.AsSInt, Seq(a), Nil, SIntType(UnknownWidth))
  private def asUInt(a: Expression) = DoPrim(PrimOps.AsUInt, Seq(a), Nil, UIntType(UnknownWidth))

  def apply(d: Expression, q: Expression, inj: Expression, halt: Expression): Expression = {
    // Mux(inj, not(q), Mux(halt, q, d))
    // == (inj & not(q)) | (not(inj) & Mux...))
    val logic = or(and(inj, not(asUInt(q))), and(not(inj), Mux(halt, asUInt(q), asUInt(d))))
    if (d.tpe.isInstanceOf[SIntType]) {
      asSInt(logic)
    } else {
      logic
    }
  }
}

class FI extends Transform {
//  override def prerequisites: List[TransformDependency] = Forms.LowForm.toList
//  override def invalidates(xform: Transform): Boolean = xform match {
//    case _          => false
//  }
//  override def optionalPrerequisites: Seq[TransformDependency] = Seq.empty
//  override def optionalPrerequisiteOf: Seq[TransformDependency] = Seq.empty

  val inputForm = LowForm
  val outputForm = HighForm

  val annotationClasses = Seq(classOf[TMRAnnotation])
  type Inst2Inj = mutable.Map[String, Option[Int]]
  type Mod2Inj = mutable.Map[String, (Option[Int], Inst2Inj)]

  type Inst2Clk = mutable.Map[(String, String), String]
  type Mod2Clk = mutable.Map[String, Inst2Clk]

//  val bannedModules = Seq("ChipTop", "TestHarness", "DividerOnlyClockGenerator", "ClockDividerN", "ClockDividerN_1", "ClockGroupAggregator_6", "ClockGroupAggregator_1", "ClockGroupParameterModifier", "ClockGroupParameterModifier_1", "ClockGroupResetSynchronizer")
  val bannedModules = Seq()

  def getHaltPortOf(name: String, inst2clk: Inst2Clk): Expression = {
    val matches = inst2clk.filter(_._1._1 == name)
    if (matches.isEmpty) {
      val portName = name.split("/")
      if (portName.size == 2) {
        return SubField(WRef(portName(0)), s"halt_${portName(1)}", ClockType)
      } else {
        return WRef(s"halt_${name}")
      }

    } else {
      assert(matches.size == 1)
      if (matches.contains((name, "inst"))) {
        return getHaltPortOf(matches((name, "inst")), inst2clk)
      } else {
        return getHaltPortOf(matches((name, "wire")), inst2clk)
      }
    }
  }

  def total(elem: Tuple2[Option[Int], Inst2Inj]) : Option[Int] = {
    if (elem._1.isEmpty)
      Option.empty[Int]
    else {
      var total = elem._1.get
      for ((k, v) <- elem._2) {
        if (v.isEmpty) {
          return Option.empty[Int]
        } else {
          total += v.get
        }
      }
      Some(total)
    }
  }

  def populateInst2Inj(mod2inj: Mod2Inj, inst2inj: Inst2Inj)(s: Statement): Statement = {
    s match {
      case s: DefInstance =>
        inst2inj(s.name) = total(mod2inj(s.module))
      case _ =>
    }

    s map populateInst2Inj(mod2inj, inst2inj)
  }

  def countRegs(counts: ListBuffer[Int])(s: Statement): Statement = {
    s match {
      case s: DefRegister =>
        val width = s.tpe.asInstanceOf[GroundType].width.asInstanceOf[IntWidth]
        counts += IntWidth.unapply(width).get.toInt
      case _ =>
    }
    s map countRegs(counts)
  }

  def connectInjStmt(offset: IntPtr, inst2inj: Inst2Inj, inst2clk: Inst2Clk, fp: PrintWriter)(s: Statement): Statement = {
    s match {
      case Connect(info, WRef(name, tpe, RegKind, SinkFlow), rhs_orig)  =>
        val width = IntWidth.unapply(tpe.asInstanceOf[GroundType].width.asInstanceOf[IntWidth]).get.toInt
        val halt = getHaltPortOf(inst2clk((name, "reg")), inst2clk)
        val lhs = WRef(name)
        val rhs = InjInterface(rhs_orig, lhs, DoPrim(PrimOps.Bits, Seq(WRef("inj")), Seq(offset.value + width - 1, offset.value), lhs.tpe), halt)
        val conn = Connect(info, lhs, rhs)
        fp.write(s"reg ${name} ${offset.value + width - 1}:${offset.value}\n")
        offset.value += width

        conn

      case s: DefInstance =>
        val width = inst2inj(s.name).get
        if (width == 0) {
          s
        } else {
          val lhs = SubField(WRef(s.name), "inj", UnknownType, UnknownFlow)
          val rhs: Expression = DoPrim(PrimOps.Bits, Seq(WRef("inj")), Seq(offset.value + width - 1, offset.value), lhs.tpe)
          val inj_connect = PartialConnect(s.info, lhs, rhs)
          fp.write(s"inst:${s.module} ${s.name} ${offset.value + width - 1}:${offset.value}\n")
          offset.value += width
          Block(Seq(s, inj_connect))
        }

      case _ =>
        s map connectInjStmt(offset, inst2inj, inst2clk, fp)
    }
  }

  def connectHaltStmt(inst2clk: Inst2Clk)(s: Statement): Statement = {
    s match {
      // instance.clock <= clockPort
      case s: DefInstance =>
        val clks = inst2clk.filter(_._1._1 == s.name)
        val halt_connects = clks.map(clk => Connect(s.info, SubField(WRef(s.name), s"halt_${clk._1._2}", UnknownType, UnknownFlow), getHaltPortOf(clk._2, inst2clk)))
        Block(Seq(s) ++ halt_connects)

      // clockPort <= net
      case Connect(info, Reference(lhs_name, ClockType, PortKind, lhs_flow), Reference(rhs_name, rhs_type, rhs_kind, rhs_flow)) =>
        val halt_conn = Connect(info,
          WRef(s"halt_${lhs_name}"),
          getHaltPortOf(rhs_name, inst2clk))
        Block(Seq(s, halt_conn))

      // clockPort <= instance.clock
      case Connect(info, Reference(lhs_name, ClockType, PortKind, lhs_flow), SubField(rhs_ref, rhs_name, rhs_kind, rhs_flow)) =>
        val halt_conn = Connect(info,
          WRef(s"halt_${lhs_name}"),
          getHaltPortOf(s"${rhs_ref.serialize}/$rhs_name", inst2clk))
        Block(Seq(s, halt_conn))

      // instance.clock <= otherInstance.clock
      case Connect(info, SubField(lhs_ref, lhs_name, ClockType, lhs_flow), SubField(rhs_ref, rhs_name, rhs_kind, rhs_flow)) =>
        val halt_conn = Connect(info,
          getHaltPortOf(s"${lhs_ref.serialize}/$lhs_name", inst2clk),
          getHaltPortOf(s"${rhs_ref.serialize}/$rhs_name", inst2clk))
        Block(Seq(s, halt_conn))

      case _ =>
        s map connectHaltStmt(inst2clk)
    }
  }

  def populateMod2Inj(mod2inj: Mod2Inj)(m: DefModule) : DefModule = {
    val inst2inj = mod2inj(m.name)._2
    val regWidths = new ListBuffer[Int]()
    m map populateInst2Inj(mod2inj, inst2inj) // Populates inst2inj
    m map countRegs(regWidths)

    if (total(mod2inj(m.name)).isEmpty) {
      if (m.ports.forall(_.direction == Input) && !bannedModules.contains(m.name) ) { // Prevent TLMonitors from creating too many inj ports
        mod2inj(m.name) = (Some(0), inst2inj)
      } else if (inst2inj.isEmpty || inst2inj.forall(_._2.nonEmpty)) { // Leaf instance condition
        mod2inj(m.name) = (Some(regWidths.sum), inst2inj)
      }
    }

    m
  }

  def addInjPortsMod(mod2inj: Mod2Inj)(m: DefModule) : DefModule = {
    val injWidth = total(mod2inj(m.name)).get
    val newPorts = Seq(Port(NoInfo, "inj", Input, UIntType(new IntWidth(injWidth)))) ++ m.ports

    m match {
      case Module(info, name, _, body) =>
        if (injWidth == 0 || bannedModules.contains(name) ) {
          m
        } else {
          Module(info, name, newPorts, body)
        }
      case ExtModule(info, name, ports, defname, params) =>
        m
    }
  }

  def addHaltPortsMod(mod2inj: Mod2Inj)(m: DefModule) : DefModule = {
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

  def connectInjMod(mod2inj: Mod2Inj, mod2clk: Mod2Clk, fp: PrintWriter)(m: DefModule) : DefModule = {
    val inst2inj = mod2inj(m.name)._2
    val inst2clk = mod2clk(m.name)

    if (bannedModules.contains(m.name) || total(mod2inj(m.name)).get == 0) {
      m
    } else {
      fp.write(s"--- Module ${m.name}\n")
      m map connectInjStmt(new IntPtr, inst2inj, inst2clk, fp)
    }
  }

  def connectHaltMod(mod2clk: Mod2Clk)(m: DefModule) : DefModule = {
    val inst2clk = mod2clk(m.name)
    val clkPorts = m.ports.filter(_.tpe == ClockType)

    if (bannedModules.contains(m.name) || clkPorts.isEmpty) {
      m
    } else {
      m map connectHaltStmt(inst2clk)
    }
  }

  def populateMod2Clk(mod2clk: Mod2Clk)(m: DefModule) : DefModule = {
    val inst2clk = mutable.Map[(String, String), String]()
    mod2clk(m.name) = inst2clk
    m map populateInst2Clk(inst2clk)
  }


  def populateInst2Clk(inst2clk: Inst2Clk)(s: Statement) : Statement = {
    s match {
      // inst.clock <= clockPort
      case Connect(info, SubField(Reference(inst_name, _, _, _), lhs_name, ClockType, _), Reference(rhs_name, ClockType, _, _)) =>
        inst2clk(Tuple2(inst_name, lhs_name)) = rhs_name

      // reg name : Clock
      case d: DefRegister =>
        inst2clk(Tuple2(d.name, "reg")) = d.clock match {
          case SubField(Reference(rhs_inst_name, _, _, _), rhs_name, ClockType, _) =>
            s"${rhs_inst_name}/${rhs_name}"
          case _ =>
            d.clock.serialize
        }

      case m: DefMemory =>
        (m.readers ++ m.writers ++ m.readwriters).map(port => s"$port/clock")

      case Connect(info, WRef(lhs_name, ClockType, _, _), WRef(rhs_name, ClockType, _, _)) =>
        inst2clk(Tuple2(lhs_name, "wire")) = rhs_name

      case DefNode(info, lhs_name, SubField(Reference(rhs_inst_name, _, _, _), rhs_name, ClockType, _)) =>
        inst2clk(Tuple2(lhs_name, "inst")) = s"${rhs_inst_name}/${rhs_name}"

      case DefNode(info, lhs_name, rhs) =>
        val signals = new ListBuffer[String]
        val clocks = new ListBuffer[String]
        s map findRef(signals, clocks)
        val all = signals ++ clocks
        all.size match {
          case 0 =>
          case 1 =>
            var rhs_name = all.head
            inst2clk(Tuple2(lhs_name, "wire")) = rhs_name
          case _ =>
            clocks.size match {
              case 0 =>
              case 1 =>
                inst2clk(Tuple2(lhs_name, "wire")) = clocks.head
              case _ =>
                throw new Exception(s"Single clock node fan-in to every clock node assumption broken at ${lhs_name}${info}")
            }

        }
      case _ =>
    }

    s map populateInst2Clk(inst2clk)
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

  def execute(state: CircuitState): CircuitState = {
    // TODO: Need to check if inj port already exists
    var circuit = state.circuit
    val mod2inj: Mod2Inj = scala.collection.mutable.Map() ++
      circuit.modules.map(m => m.name -> (Option.empty[Int], scala.collection.mutable.Map[String, Option[Int]]())).toMap

    val mod2clk = mutable.Map[String, mutable.Map[(String, String), String]]()
    circuit map populateMod2Clk(mod2clk)

    var i = 0
    while (! mod2inj.forall(_._2._1.nonEmpty)) {
      circuit = circuit map populateMod2Inj(mod2inj)
      i += 1
    }
//    println(s"Final Mod2Inj: ${mod2inj}")
//    println(s"Final Mod2Clk: ${mod2clk}")

    val fp = new PrintWriter(new File("fiff.log"))
    circuit = circuit map addInjPortsMod(mod2inj)
    circuit = circuit map addHaltPortsMod(mod2inj)

//    circuit.foreachModule(m => println(m.ports))

    println(s"Connecting INJ")
    circuit = circuit map connectInjMod(mod2inj, mod2clk, fp)
    println(s"Connecting HALT")
    circuit = circuit map connectHaltMod(mod2clk)

    fp.close()
    state.copy(circuit = circuit)
  }
}

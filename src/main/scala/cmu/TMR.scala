package cmu

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.annotations._

case class TMRAnnotation(target: Target) extends SingleTargetAnnotation[Target] {
//  println(target.path)
//  println(target.ofModule?
  RenameMap().keys foreach println
  println(target.prettyPrint())
  def duplicate(newTarget: Target): TMRAnnotation = {
    println(target.prettyPrint())
    this.copy(target = newTarget)
  }
}

class TMR extends Transform with ResolvedAnnotationPaths {
  val inputForm = LowForm
  val outputForm = LowForm

  val annotationClasses = Seq(classOf[TMRAnnotation])
  type TripleCopyNameMap = Map[String, Tuple3[String, String, String]]

  private def renameInst(inst: DefInstance, newName: String): DefInstance = {
    val renamed = inst.copy(name = newName)

    // Why did they check for this? should I be careful of a similar situation
    // while duplicating instances??
//    if (renamed.reset == UIntLiteral(0)) {
//      renamed.copy(init = WRef(renamed))
//    }  else {
//      renamed
//    }

    renamed
  }

  private def makeInstTriples(copyNameMap: TripleCopyNameMap, ns: Namespace, renames: RenameMap)(stmt: Statement): Statement = {
    stmt match {
      case inst: DefInstance if (copyNameMap.contains(inst.name)) =>
        // Make three copies of the register with new names
        val (name0, name1, name2) = copyNameMap(inst.name)
        val newTargets = Seq(name0, name1, name2).map(name => inst.copy(name = name))
//        renames.record(inst, newTargets.map(i => TargetToken.Instance(i.name)))

        val c0 = renameInst(inst, name0)
        val c1 = renameInst(inst, name1)
        val c2 = renameInst(inst, name2)
        // Make a majority-valued node that shares the register's original name
//        val majExpr = MajorityGate(WRef(c0), WRef(c1), WRef(c2))
//        val majNode = DefNode(inst.info, inst.name, majExpr)
        Block(Seq(c0, c1, c2))

      case Connect(info, SubField(ref: Reference, field_name, tpe, flow), rhs) if (copyNameMap.contains(ref.name)) =>
//        val (inst_name_0, inst_name_1, inst_name_2) = renames(ref)
        val conn0 = Connect(info, SubField(new WRef(copyNameMap(ref.name)._1), field_name, tpe, SinkFlow), rhs)
        val conn1 = Connect(info, SubField(new WRef(copyNameMap(ref.name)._2), field_name, tpe, SinkFlow), rhs)
        val conn2 = Connect(info, SubField(new WRef(copyNameMap(ref.name)._3), field_name, tpe, SinkFlow), rhs)
        Block(Seq(conn0, conn1, conn2))

      case Connect(info, lhs, SubField(ref: Reference, field_name, tpe, flow)) if (copyNameMap.contains(ref.name)) =>
        val cp0 = SubField(WRef(copyNameMap(ref.name)._1), field_name, tpe, flow)
        val cp1 = SubField(WRef(copyNameMap(ref.name)._2), field_name, tpe, flow)
        val cp2 = SubField(WRef(copyNameMap(ref.name)._3), field_name, tpe, flow)
        val majExpr = MajorityGate(cp0, cp1, cp2)
        val majNodeName = ns.newName(s"${ref.name}_${field_name}_maj")

        val majNode = DefNode(info, majNodeName, majExpr) // I think this is a Connect, but lhs is assumed to be a Reference?
        val connectStmt = Connect(info, lhs, WRef(majNode))

        Block(Seq(majNode, connectStmt))

      case s => s.map(makeInstTriples(copyNameMap, ns, renames))
    }
  }

  private def newTMRInstNames(ns: Namespace, instName: String): (String, String, String) = {
    (ns.newName(s"${instName}_copy_0"), ns.newName(s"${instName}_copy_1"), ns.newName(s"${instName}_copy_2"))
  }

  def execute(state: CircuitState): CircuitState = {
//    println("LALALAA1")
    val TMRTargets = state.annotations.collect { // Filters out everything except RRAnnotation
      case TMRAnnotation(target) =>
        require(target.isLocal)
        print(target)
        target.asInstanceOf[InstanceTarget]
    }
//    println("LALALAA2")

    val TMRTargetsByModule = TMRTargets.groupBy(_.module) // creates a map from list
//    println("LALALAA3")
//    // We need to record that we've split each register into three new ones
      val renames = RenameMap()
//    println("LALALAA4")
    val transformedModules = state.circuit.modules.map {
      case m: DefModule if (TMRTargetsByModule.contains(m.name)) =>
        val ns = Namespace(m)
        val TMRInsts = TMRTargetsByModule(m.name)
        val TMRCopyNameMap = TMRInsts.map(inst => inst.name -> newTMRInstNames(ns, inst.name)).toMap

        m.map(makeInstTriples(TMRCopyNameMap, ns, renames))
      case m => m
    }
//    val transformedModules = state.circuit.modules.map {
//      case m: DefModule if (m.name == "Top") =>
//        val ns = Namespace(m)
//        m.map(makeInstTriples(Map("sub" -> Tuple3("sub_copy_0", "sub_copy_1", "sub_copy_2")), ns, renames))
//      case m => m
//    }

//    val inputTarget = InstanceTarget("RocketCore", "RocketCore", Nil, "ibuf", "IBuf")
//    val outTarget0 = InstanceTarget("RocketCore", "RocketCore", Nil, "ibuf_copy_0", "IBuf")
//    val outTarget1 = InstanceTarget("RocketCore", "RocketCore", Nil, "ibuf_copy_1", "IBuf")
//    val outTarget2 = InstanceTarget("RocketCore", "RocketCore", Nil, "ibuf_copy_2", "IBuf")

    val inputTarget = InstanceTarget("Top", "Sub", Nil, "sub", "Sub")
    val outTarget0 = InstanceTarget("Top", "Sub", Nil, "sub_copy_0", "Sub")
    val outTarget1 = InstanceTarget("Top", "Sub", Nil, "sub_copy_1", "Sub")
    val outTarget2 = InstanceTarget("Top", "Sub", Nil, "sub_copy_2", "Sub")
    renames.record(inputTarget, Seq(outTarget0, outTarget1, outTarget2))

    val transformedCircuit = state.circuit.copy(modules = transformedModules)
    val filteredAnnos = state.annotations.filterNot(_.isInstanceOf[TMRAnnotation])
    println("Finito")
    state.copy(transformedCircuit, outputForm, annotations = filteredAnnos, Some(renames))
//    state.copy(circuit=transformedCircuit)

  }
}
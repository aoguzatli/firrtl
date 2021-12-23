package cmu

import firrtl.Mappers._
import firrtl._
import firrtl.ir._

//// Template - don't modify ////
class PrintStuff extends Transform {
  val inputForm = LowForm
  val outputForm = LowForm

  def transformExpr(e: Expression) : Expression = {
    e map transformExpr
  }

  def transformStmt(s: Statement): Statement = {
    s map transformStmt map transformExpr
  }

  def transformMod(m: DefModule) : DefModule = {
    m map transformStmt
  }

  def execute(state: CircuitState): CircuitState = {
    val circuit = state.circuit map transformMod
    state.copy(circuit = circuit)
  }
}


class PrintQueueStatements extends Transform {
  val inputForm = LowForm
  val outputForm = LowForm

  def transformExpr(e: Expression) : Expression = {
    e map transformExpr
  }

  def transformStmt(s: Statement): Statement = {
//    println(s)
    s match {
      case Connect(info, lhs, rhs) =>
        lhs match {
          case SubField(SubField(Reference(memName, _, MemKind, _), field, _, _), "en", _, _) =>

        }

      case _ =>
    }


    s map transformStmt map transformExpr
  }

  def transformMod(m: DefModule) : DefModule = {
    m match {
      case mod: Module if mod.name == "Queue" =>
        m map transformStmt
      case _ =>
        m
    }

  }

  def execute(state: CircuitState): CircuitState = {
    val circuit = state.circuit map transformMod
    state.copy(circuit = circuit)
  }
}

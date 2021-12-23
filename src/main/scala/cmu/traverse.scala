package cmu

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.annotations._
import firrtl.options.Dependency
import firrtl.stage.Forms
import firrtl.stage.TransformManager.TransformDependency
import firrtl.transforms.DeadCodeElimination

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Map

// Intended to be used only as a template for a custom transform. Copy, don't override.
class Traverse extends Transform {
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
package LIAStarSolver.Linear

import ap.parser._
import ap.terfor.ConstantTerm
import ap.basetypes.IdealInt

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SMT.SMT

class SemilinearSet(val linearSets: Set[LinearSet]) { 

  override def toString(): String = s"SLS(${linearSets.mkString(",")}"
  override def equals(other: Any): Boolean = other match {
    case sls: SemilinearSet => this.linearSets == sls.linearSets
    case _             => false
  }
  override def hashCode(): Int = linearSets.##

  // return the semilinear set received by adding ls
  def addLS(ls: LinearSet): SemilinearSet = {
    SemilinearSet(linearSets + ls)
  }

  // apply merge, offsetDown and shiftDown rules, until the resulting SemilinearSet no longer changes
  def saturate(solverState: SolverState): SemilinearSet = {
    var current = this
    var changed = true
    while (changed) {
      changed = false

      var shiftDownChange = true
      while (shiftDownChange) {
        shiftDownChange = false
        val shiftDownSLSOption: Option[SemilinearSet] =
          current.shiftDown(solverState)
        if (shiftDownSLSOption.isDefined) {
          shiftDownChange = true
          changed = true
          current = shiftDownSLSOption.get
        }
      }

      var offsetDownChange = true
      while (offsetDownChange) {
        offsetDownChange = false
        val offsetDownSLSOption: Option[SemilinearSet] =
          current.offsetDown(solverState)
        if (offsetDownSLSOption.isDefined) {
          changed = true
          offsetDownChange = true
          current = offsetDownSLSOption.get
        }
      }
      var mergeChange = true
      while (mergeChange) {
        mergeChange = false
        val mergeSLSOption: Option[SemilinearSet] =
          current.merge(solverState)
        if (mergeSLSOption.isDefined) {
          changed = true
          mergeChange = true
          current = mergeSLSOption.get
        }
      }
    }
    
    current
  }

  // Try to apply merge rule either return Some(resulting SemilinearSet) or None, if merge rule not applicable
  def merge(
      solverState: SolverState
  ): Option[SemilinearSet] = {
    
    linearSets
      .subsets(2)
      .collectFirst(Function.unlift { subset =>
        val Seq(a, b) = subset.toSeq
        a.merge(b, solverState).map(merged => SemilinearSet(linearSets - a - b + merged))
      })
  }

  // Try to apply the shiftDown rule. Either return Some(resulting SemilinearSet) or None, if shiftDown rule not applicable
  def shiftDown(
      solverState: SolverState
  ): Option[SemilinearSet] = {
    linearSets.collectFirst(Function.unlift { ls =>
      ls.shiftDown(solverState).map { shifted =>
        SemilinearSet(linearSets - ls + shifted)
      }
    })
  } 


  // Try to apply the offsetDown rule. Either return Some(resulting SemilinearSet) or None, if offsetDown rule not applicable
  def offsetDown(
      solverState: SolverState
  ): Option[SemilinearSet] = {
    linearSets.collectFirst(Function.unlift { ls =>
      ls.offsetDown(solverState).map { offset =>
        SemilinearSet(linearSets - ls + offset)
      }
    })
  }
}

package LIAStarSolver.Linear

import ap.parser._
import ap.terfor.ConstantTerm
import ap.basetypes.IdealInt

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SMT.SMT

class SemilinearSet(val linearSets: Set[LinearSet]) { // evtl deterministich TODO

  override def toString(): String = s"SLS(${linearSets.mkString(",")}"
  override def equals(other: Any): Boolean = other match {
    case sls: SemilinearSet => this.linearSets == sls.linearSets
    case _             => false
  }
  override def hashCode(): Int = linearSets.##

  // return the semilinear set recieved by adding ls
  def addLS(ls: LinearSet): SemilinearSet = {
    // TODO: require same length?
    SemilinearSet(linearSets + ls)
  }

  // Try to apply merge rule either return Some(resulting SemilinearSet) or None, if merge rule not applicable
  def merge(
      solverState: SolverState
  ): Option[SemilinearSet] = {

    // if two linear sets are found that can be merged, then Some(ls1, ls2, mergeResult)
    // if no two linear sets can be merged this is None
    val mergedSetsAndMergeResult: Option[(LinearSet, LinearSet, LinearSet)] =
      linearSets
        .subsets(2)
        .collectFirst(Function.unlift { subset =>
          val Seq(a, b) = subset.toSeq
          a.merge(b, solverState).map(merged => (a, b, merged))
        })

    if (mergedSetsAndMergeResult.isDefined) {
      val (ls1, ls2, mergeRes) = mergedSetsAndMergeResult.get
      Some(SemilinearSet(linearSets - ls1 - ls2 + mergeRes))
    } else {
      None
    }

  }

  // Try to apply the shiftDown rule. Either return Some(resulting SemilinearSet) or None, if shiftDown rule not applicable
  def shiftDown(
      solverState: SolverState
  ): Option[SemilinearSet] = {
    val shiftableSetAndShiftedResult: Option[(LinearSet, LinearSet)] =
      linearSets.collectFirst(Function.unlift { ls =>
          ls.shiftDown(solverState).map(shifted => (ls, shifted))
        })

    if (shiftableSetAndShiftedResult.isDefined) {
      val (oldLS, shiftedLS) = shiftableSetAndShiftedResult.get
      Some(SemilinearSet(linearSets - oldLS + shiftedLS))
    } else {
      None
    }
  } 


  // Try to apply the offsetDown rule. Either return Some(resulting SemilinearSet) or None, if offsetDown rule not applicable
  def offsetDown(
      solverState: SolverState
  ): Option[SemilinearSet] = {
    val offsetableSetAndOffsetResult: Option[(LinearSet, LinearSet)] =
      linearSets.collectFirst(Function.unlift { ls =>
          ls.offsetDown(solverState).map(shifted => (ls, shifted))
        })

    if (offsetableSetAndOffsetResult.isDefined) {
      val (oldLS, offsetLS) = offsetableSetAndOffsetResult.get
      Some(SemilinearSet(linearSets - oldLS + offsetLS))
    } else {
      None
    }
  }
}

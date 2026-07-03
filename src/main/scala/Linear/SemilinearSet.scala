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

  def saturate() = {
    val changed = true
    while (changed) {}
  }

  // Try to apply merge rule
  def merge(
      solverState: SolverState
  ): Option[SemilinearSet] = {
    // if two linear sets are found that can be merged, then Some(ls1, ls2, mergeResult)
    // if no two linear sets can be merged this is None
    val lsCombinationsResult: Option[(LinearSet, LinearSet, LinearSet)] =
      linearSets
        .subsets(2)
        .collectFirst(Function.unlift { s =>
          val Seq(a, b) = s.toSeq
          a.merge(b, solverState).map(merged => (a, b, merged))
        })

    if (lsCombinationsResult.isDefined) {
      val (ls1, ls2, mergeRes) = lsCombinationsResult.get
      Some(SemilinearSet(linearSets - ls1 - ls2 + mergeRes))
    } else {
      None
    }

  }
}

package LIAStarSolver.SatProcedure

import ap.SimpleAPI.pp
import ap.parser._
import ap.terfor.ConstantTerm

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.Linear.{LinearSet, SemilinearSet}
import LIAStarSolver.SatResult.Model
import LIAStarSolver.SMT.SMT

class UnderapproximationRefiner(val solverState: SolverState, val formulaFactory: FormulaFactory) {
  def weakenUnderApproximation(solutionToAdd: Model): Unit = {
    val v = solverState.X.map(solutionToAdd).toVector
    println(s"DEBUG: WEAKEN UNDER, adding solution ${v} to U") 
    solverState.underApproxF_SLS = solverState.underApproxF_SLS.addLS(
      LinearSet(v, Vector())
    )

    println(
      s"DEBUG: before Augment application ${solverState.underApproxF_SLS}"
    )

    solverState.underApproxF_SLS = solverState.underApproxF_SLS.augment(solverState)
    println(
      s"DEBUGs: after Augment application ${solverState.underApproxF_SLS}. Transforming this to underapprox via starLIA"
    )
    // convert SLS underapproximating f to a formula underapproximating f*
    solverState.underApproxFStar =
      formulaFactory.starLIA(solverState.underApproxF_SLS)
  }
  }

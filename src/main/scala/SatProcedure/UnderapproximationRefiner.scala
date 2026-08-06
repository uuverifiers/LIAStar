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
    solverState.underApproxF_SLS = solverState.underApproxF_SLS.addLS(
      LinearSet(v, Vector())
    )


    solverState.underApproxF_SLS = solverState.underApproxF_SLS.saturate(solverState)
    
    // convert SLS underapproximating f to a formula underapproximating f*
    solverState.underApproxFStar =
      formulaFactory.starLIA(solverState.underApproxF_SLS)
  }
  }

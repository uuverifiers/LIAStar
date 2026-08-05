package LIAStarSolver.SatProcedure

import ap.SimpleAPI
import ap.SimpleAPI.{ProverStatus, pp}
import ap.parser._
import ap.terfor.ConstantTerm

import ap.util.Timer

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.SMT.SMT
import LIAStarSolver.SatResult.{SatResult, Sat, Unsat, Inconclusive, Model}
import LIAStarSolver.Linear.{LinearSet, SemilinearSet}

class SatProcedure(
    solverInstance: SimpleAPI,
    g: IFormula,
    f: IFormula,
    X: Seq[IConstant]
) {

  val solverState = SolverState(solverInstance, g, f, X)
  val formulaFactory = FormulaFactory(solverState)

  private var measureTime = true
  val defaultNUnfoldings = 2


  // same as checkFormula, but time statistics can be seen with ap.util.Timer
  def checkFormulaWithTimingMeasurement(
      nUnfoldings: Int = defaultNUnfoldings
  ): SatResult = {
    measureTime = true
    Timer.measure("checkFormula") {
      checkFormula(nUnfoldings)
    }
  }

  // calculate if formula g(X) & f*(X) is sat or unsat
  // the parameter nUnfoldings gives the number of unfoldings to use for calculuating
  // interpolants for strengthenOverApproximation
  def checkFormula(nUnfoldings: Int = defaultNUnfoldings): SatResult = {
    val overapproximationRefiner =
      OverapproximationRefiner(solverState, formulaFactory, nUnfoldings)
    val underapproximationRefiner =
      UnderapproximationRefiner(solverState, formulaFactory)

    // check if an exit criteria can be applied right from the start
    if (isEarlyUnsat) {
      //println(
        //s"INFO: EXIT: initial early unsat with overapprox ${pp(solverState.overApproxFStar)}"
      //)
      return Unsat
    }

    val (earlySat, modelOptionRes): (Boolean, Option[Model]) = isEarlySat
    if (earlySat) {
      //println(
        //s"INFO: EXIT:  (initial) early sat with underapprox ${pp(solverState.underApproxFStar)}"
      //)
      return Sat(modelOptionRes.get) ////////////
    }

    var _loopCount = 0 // TODO: only for debuggin purposes?!
    // this loop must converge at some point (could take infeasibly long)
    while (true) {
      //println(s"\n\n INFO: top of while loop (iteration ${_loopCount})\n")
      _loopCount += 1

      //////////////////////////////
      // check convergence of underapproximation to f*
      val convergenceRes = checkUnderApproxConvergence
      if (convergenceRes.isDefined) {
        //println(
          //s"INFO: EXIT: u (${pp(solverState.underApproxFStar)} converged to f*"
        //)
        return convergenceRes.get
      }

      //////////////////////////////
      // strengthen the Overapproximation
      if (measureTime) {
        Timer.measure("overapproximation refinement") {
          overapproximationRefiner.strengthenOverApproximation()
        }
      } else {
        overapproximationRefiner.strengthenOverApproximation()
      }

      //println(s"INFO: new overapproximation ${solverState.overApproxFStar}")

      //////////////////////////////
      // check if exit criteria can be applied with the updated overapproximation
      if (isEarlyUnsat) {
        //println(
          //s"INFO: early unsat with overapprox ${pp(solverState.overApproxFStar)}"
        //)
        return Unsat
      }

      //////////////////////////////
      // weaken the underapproximation

      // TODO: rename? not testing convergence here, but it is the same formula constructed for convergence
      val convergenceCondition = solverState.f & !solverState.underApproxFStar
      // get model to add to solverState.underApproxF_SLS
      // !underApproxFStar can introduce all quantifier => use checkValidityAndModel instead of checkSatAndModel

      val (proverStatus, modelOption) = SMT.checkValidityAndModel(
        convergenceCondition,
        solverState.X,
        solverState
      )
      // since convergence criteria was invalid, a solution exists for f&!underapprox
      assert(proverStatus == ProverStatus.Valid && modelOption.isDefined)

      val solution_fAndNotUnderapprox: Model = modelOption.get

      if (measureTime) {
        Timer.measure("underapproximation refinement") {
          underapproximationRefiner.weakenUnderApproximation(
            solution_fAndNotUnderapprox
          )
        }
      } else {
        underapproximationRefiner.weakenUnderApproximation(
          solution_fAndNotUnderapprox
        )
      }
      //println(
        //s"INFO: WEAKENED underapproximation:${pp(solverState.underApproxFStar)} with U ${solverState.underApproxF_SLS}"
      //)

      //////////////////////////////
      // check if exit criteria can be applied with the updated underapproximation
      val (earlySat, modelOptionRes): (Boolean, Option[Model]) = isEarlySat
      if (earlySat) {
        //println(
          //s"INFO: early sat with underapprox ${pp(solverState.underApproxFStar)}"
        //)
        return Sat(modelOptionRes.get) ////////////
      }

      // println("\nDEBUG: bottom of while loop \n\n")

    }
    assert(true == false) // Can never reach here
    return Inconclusive // TODO: unreachable, maybe refactor
  }

  // return true if g & Overapproximation is unsat. Then g & f* must be unsat
  def isEarlyUnsat: Boolean = {
    SMT.isUnsat(g & solverState.overApproxFStar, solverState)
  }

  // return a if g & Underapproximation is sat. Then g & f* must also be sat.
  // If Sat and a model can be produced, return it as Some(Model)
  def isEarlySat: (Boolean, Option[Model]) = {
    val (
      proverStatus,
      modelOption
    ) = SMT.checkSatAndModel(
      g & solverState.underApproxFStar,
      solverState.X,
      solverState
    )
    proverStatus match {
      case ProverStatus.Sat => (true, modelOption)
      case _                => (false, None)
    }
  }

  // Check if underApproximation has converged to f*. If so, return the SatResult for g&f*
  def checkUnderApproxConvergence: Option[SatResult] = {
    val convergenceCondition = solverState.f & !solverState.underApproxFStar
    if (SMT.isUnsat(convergenceCondition, solverState)) {
      // now g&underapproximation is equivalent to g&f*
      val (
        proverStatus,
        modelOption
      ) =
        SMT.checkValidityAndModel(
          g & solverState.underApproxFStar,
          solverState.X,
          solverState
        )
      val returnValue = proverStatus match {
        case ProverStatus.Valid =>
          Sat(
            modelOption.get ////////////////
          )
        case ProverStatus.Invalid => Unsat

        case _ =>
          // could neither confirm sat nor unsat
          Inconclusive
      }
      Some(returnValue)
    } else {
      // underApproxFStar has not yet converged
      None
    }
  }

}

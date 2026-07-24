package LIAStarSolver.SMT
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SatResult.Model

import ap.parser._
import ap.basetypes.IdealInt
import ap.SimpleAPI
import ap.SimpleAPI.{ProverStatus, NoModelException}

object SMT {

  // check if formula is Unsat.
  // Any other result returns false (including timeout)
  def isUnsat(formula: IFormula, solverState: SolverState): Boolean = {
    import solverState.solverInstance._
    push()
    !!(formula)
    val res = ???

    pop()
    res match {
      case ProverStatus.Unsat => {
        true
      }
      case _ => false
    }
  }

  // check if formula is Sat.
  // Any other result returns false (including timeout)
  // TODO is timeout even possible
  def isSat(formula: IFormula, solverState: SolverState): Boolean = {
    import solverState.solverInstance._
    push()
    !!(formula)
    val res = ???
    pop()
    res match {
      case ProverStatus.Sat => true
      case _                => false
    }
  }
  // check if formula is Valid.
  // Any other result returns false (including timeout)
  // TODO is timeout even possible
  // TODO: remove since only used by one testing function?
  // Rename since still checking Unsat not ProverStatus.Valid?
  def isValid(formula: IFormula, solverState: SolverState): Boolean = {
    import solverState.solverInstance._
    push()
    !!(!(formula))
    val res = ???
    pop()
    res match {
      case ProverStatus.Unsat => true
      case _                  => false
    }
  }

  // check sat of a formula and return model if sat.
  // Use when no all quantifiers are in formula
  def checkSatAndModel(
      formula: IFormula,
      formulaVariables: Seq[IConstant],
      solverState: SolverState
  ): (ProverStatus.Value, Option[Model]) = {

    import solverState.solverInstance._
    push()
    !!(formula)
    val res = ???
    val returnRes = if (res == SimpleAPI.ProverStatus.Sat) {
      // TODO: can this throw NoModelException.type (from SimpleAPI)?
      val model: Model =
        formulaVariables.map { x =>
          x -> eval(x)
        }.toMap
      (res, Some(model))

    } else {
      (res, None)
    }
    pop()
    returnRes

  }

  // check validity of a formula and return model if valid.
  // Use when the formula contains all quantifiers
  def checkValidityAndModel(
      formula: IFormula,
      formulaVariables: Seq[IConstant],
      solverState: SolverState
  ): (ProverStatus.Value, Option[Model]) = {
    import solverState.solverInstance._
    push()
    ??(formula)
    makeExistential(formulaVariables)
    val res = ???
    val returnRes = if (res == SimpleAPI.ProverStatus.Valid) {
      val model: Model =
        formulaVariables.map { x =>
          x -> eval(x)
        }.toMap
      (res, Some(model))

    } else {
      (res, None)
    }
    pop()
    returnRes
  }

  // calculate ITP, s.t a -> ITP and ITP -> !b
  // requires a & b is unsat
  def getInterpolant(
      a: IFormula,
      b: IFormula,
      solverState: SolverState
  ): IFormula = {
    import solverState.solverInstance._
    require(SMT.isUnsat(a & b, solverState)) // TODO: remove for performance?

    push()
    setConstructProofs(true) // needed for getInterpolants
    setPartitionNumber(1)
    !!(a)
    setPartitionNumber(2)
    !!(b)
    ??? // show eldarica a&b is unsat
    val res = getInterpolants(Seq(Set(1), Set(2)))(0)
    pop()

    res
  }
}

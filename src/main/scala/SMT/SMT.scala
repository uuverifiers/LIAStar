package LIAStarSolver.SMT
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SatResult.Model

import ap.parser._
import ap.basetypes.IdealInt
import ap.SimpleAPI
import ap.SimpleAPI.{ProverStatus, NoModelException}

object SMT {

  // check if formula is Unsat.
  // Any other ProverStatus result returns false 
  /////////
  // IMPORTANT: false does not imply formula is sat!!!!!!
  /////////
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

  // check sat of a formula and return model if sat.
  // Use when no all quantifiers are in formula
  def checkSatAndModel(
      formula: IFormula,
      formulaVariables: Seq[IConstant],
      solverState: SolverState
  ): (ProverStatus.Value, Option[Model]) = {

    import solverState.solverInstance._
    push()
    //Handle NoModelException.type
    try {
      !!(formula)
      ??? match {
        case ProverStatus.Sat => {
          val model: Model =
            formulaVariables.map { x =>
              x -> eval(x)
            }.toMap
          (ProverStatus.Sat, Some(model))
        }
        case status => (status, None)
      }
    }
    finally{
      pop()
    }

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
    try {
      ??(formula)
      makeExistential(formulaVariables)
      ??? match {
        case ProverStatus.Valid =>
          val model: Model =
            formulaVariables.map { x =>
              x -> eval(x)
            }.toMap
          (ProverStatus.Valid, Some(model))

        case status =>
          (status, None)
      }
    } finally {
      pop()
    }
  }

  // calculate ITP, s.t a -> ITP and ITP -> !b
  // requires a & b is unsat
  def getInterpolant(
      a: IFormula,
      b: IFormula,
      solverState: SolverState
  ): IFormula = {
    import solverState.solverInstance._

    push()
    try {
      setConstructProofs(true) // needed for getInterpolants
      setPartitionNumber(1)
      !!(a)
      setPartitionNumber(2)
      !!(b)
      ???; // show eldarica a&b is unsat; Semicolon to not treat ??? as infix
      getInterpolants(Seq(Set(1), Set(2)))(0)
    } finally {
      pop()
    }
  }
}

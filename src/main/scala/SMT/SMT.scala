package LIAStarSolver.SMT
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SatResult.Model

import ap.parser._
import ap.basetypes.IdealInt
import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus

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
      case ProverStatus.Unsat => true
      case _                  => false
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

  // return ProverStatus as well as a Model, if ProverStatus.Sat
  def getProverStatusAndModel(
      formula: IFormula,
      formulaVariables: Seq[IConstant],
      solverState: SolverState
  ): (ProverStatus.Value, Option[Model]) = {
    import solverState.solverInstance._
    push()
    !!(formula)
    val res = ???
    val returnRes = if (res == SimpleAPI.ProverStatus.Sat) {
      val evaluator = completeModel
      val model =
        solverState.X.map { x =>
          x -> evaluator(x).asInstanceOf[IIntLit].value
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
    require(SMT.isUnsat(a & b, solverState))

    setConstructProofs(true) // needed for getInterpolants

    push()
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

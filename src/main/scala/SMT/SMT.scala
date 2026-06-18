package LIAStarSolver.SMT
import LIAStarSolver.SolverState.SolverState

import ap.parser._
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
  def isValid(formula: IFormula, solverState: SolverState): Boolean = {
    import solverState.solverInstance._
    push()
    !!(formula)
    val res = ???
    pop()
    res match {
      case ProverStatus.Valid => true
      case _                => false
    }
  }

  // calculate ITP, s.t a -> ITP and ITP -> b
  def getInterpolant(
      a: IFormula,
      b: IFormula,
      solverState: SolverState
  ): IFormula = {
    import solverState.solverInstance._


    setConstructProofs(true) //needed for getInterpolants

    push()
    setPartitionNumber(1)
    !!(a)
    setPartitionNumber(2)
    !!(b)
    println(s"HLEP ${???}") // unsat ????????needed????
    val res = getInterpolants(Seq(Set(1), Set(2)))(0)
    pop()

    // TODO: ? setConstructProofs(false) ???

    res
  }
}

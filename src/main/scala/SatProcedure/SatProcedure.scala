package LIAStarSolver.SatProcedure

import ap.SimpleAPI
import ap.parser._
import ap.terfor._ //ConstantTerm import ap.SimpleAPI
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.SMT.SMT

import ap.SimpleAPI.pp

class SatProcedure(
    solverInstance: SimpleAPI,
    g: IFormula,
    f: IFormula,
    X: Seq[IConstant]
) {

  val solverState = SolverState(solverInstance, g, f, X)
  val formulaFactory = FormulaFactory(solverState)

  var helpVarCounter = 1 // TODO: REFACTOR
  // val interp = Interpolant(g, f)

  // calculate if formula g(X) & f*(X) is sat or unsat
  def checkFormula(): Boolean = {
    // ...
    val nUnfoldings = 2

    /*
     * check underApprox(X) & f_less_2n(Y) & g(X+Y) unsat
     */
    val Y: Seq[IConstant] = solverState.createConstants("y_", X.length)

    val fLess2nUnfoldingsOfY = formulaFactory.fLessN(
      2 * nUnfoldings,
      Y
    )

    val subst: Map[ConstantTerm, ITerm] =
      X.zip(Y)
        .map { case (x, y) =>
          x.asInstanceOf[IConstant].c -> (x + y)
        }
        .toMap

    val g_of_XplusY = ConstantSubstVisitor(g, subst)

    val unsatCondForStrengthenOver: IFormula =
      solverState.underApproxFStar & fLess2nUnfoldingsOfY & g_of_XplusY
    println(
      s"DEBUG: unsatCondForStrengthenOver ${pp(unsatCondForStrengthenOver)}"
    )

    if (SMT.isUnsat(unsatCondForStrengthenOver, solverState)) {
      println("DEBUG: strengthen over")
      getNextOverApproximation(solverState, nUnfoldings)
    } else {
      println("DEBUG: DONT strengthen over")
    }

    // interp.calculateNextOverApproximation(underApprox)

    true
  }

  def getNextOverApproximation(
      solverState: SolverState,
      nUnfoldings: Int
  ): IFormula = {
    import formulaFactory._
    // TODO: QUESTION: is this a problem, if i do it multiple times (already in checkFormula)
    val Y = solverState.createConstants("y_", solverState.X.length)
    val Z = solverState.createConstants("z_", solverState.X.length)

    val f1 =
      substituteX(solverState.underApproxFStar, Y) & fLessN(
        nUnfoldings,
        Z
      ) & xEqualYPlusZ(X, Y, Z)
    val YPrime = solverState.createConstants("yPrime_", solverState.X.length)
    val ZPrime = solverState.createConstants("zPrime_", solverState.X.length)
    val f2 = !(xEqualYPlusZ(X, YPrime, ZPrime) & fLessN(
      nUnfoldings,
      YPrime
    ) & substituteX(solverState.g, ZPrime))

    // TODO: This is theoretically only a sanity check, since it only gets called, when
    // u(x) & flessN(n, y) & g(x+y) is unsat
    // if (SMT.isValid(f1 ==> f2, solverState)) { // TODO: reformulate to unsat question

    println(s"DEBUG f1: ${pp(f1)}")
    println(s"DEBUG f2: ${pp(f2)}")
    if (SMT.isUnsat(f1 & f2.notSimplify, solverState)) { // TODO: reformulate to unsat question
      // get Interpolant between f1 and f2
      println("DEBUG: in f1 implies f2")

      val itp = SMT.getInterpolant(f1, f2.notSimplify, solverState)
      println(s"DEBUG ITP: ${pp(itp)}")
    } else {
      print(
        "DEBUG: NOT f1 implies f2. Don't get Interpolant. (SHOULDNT HAPPEN)\n"
      ) // TODO
    }

    true // PLACEHOLDER
  }

  // return true if g & Overapproximation is unsat. Then g & f* must be unsat
  // def isEarlyUnsat: Boolean = {
  // TODO: uncomment Question: i can check formula unsat/valid without prover instance? but can't create constats without it

  // api.!!(g & interp.getOverApproxFml)
  // api.??? == SimpleAPI.ProverStatus.Unsat
  // }

}

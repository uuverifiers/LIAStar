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
    val nUnfoldings = 1

    /*
     * check underApprox(X) & f_less_2n(Y) & g(X+Y) unsat
     */
    val Y: Seq[IConstant] = solverState.createConstants("y_", X.length)



    // TODO
    val fLess2Unfoldings = formulaFactory.fLessN(2, Y)
    println(pp(fLess2Unfoldings <=> ((Y(0) === 0) | Y(0) === 1 )))
    solverState.solverInstance.!!(
      !(fLess2Unfoldings <=> ((Y(0) === 0) | Y(0) === 1 )))

    println(s"helllo ${solverState.solverInstance.???}")
    println(solverState.solverInstance.partialModel)
    println("\n\n\n\n")





    val subst: Map[ConstantTerm, ITerm] =
      X.zip(Y)
        .map { case (x, y) =>
          x.asInstanceOf[IConstant].c -> (x + y)
        }
        .toMap

    val g_of_XplusY = ConstantSubstVisitor(g, subst)
    val fLess2nUnfoldings = formulaFactory.fLessN(
      2 * nUnfoldings,
      Y
    )

    val unsatCondForStrengthenOver: IFormula =
      solverState.underApproxFStar & fLess2nUnfoldings & g_of_XplusY




    println(pp(unsatCondForStrengthenOver))
    if (SMT.isUnsat(unsatCondForStrengthenOver, solverState)) {
      println("strengthen over")
      getNextOverApproximation(solverState, nUnfoldings)
    } else {
      println("DONT strengthen over")
    }

    // interp.calculateNextOverApproximation(underApprox)

    true
  }

  def getNextOverApproximation(
      solverState: SolverState,
      nUnfoldings: Int
  ): IFormula = {
    import formulaFactory._
    //TODO: QUESTION: is this a problem, if i do it multiple times (already in checkFormula)
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
    ) & substituteX(solverState.underApproxFStar, ZPrime))

    // check
    if (SMT.isValid(f1 ==> f2, solverState)) { // TODO: reformulate to unsat question
      // get Interpolant between f1 and f2
      println("in f1 implies f2")

      val itp = SMT.getInterpolant(f1, f2.notSimplify, solverState)
    } else {
      print("NOT f1 implies f2. Don't get Interpolant.\n")
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

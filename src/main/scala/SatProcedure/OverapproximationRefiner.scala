package LIAStarSolver.SatProcedure

import ap.SimpleAPI.pp
import ap.parser._
import ap.terfor.ConstantTerm

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.SMT.SMT

class OverapproximationRefiner(
    val solverState: SolverState,
    val formulaFactory: FormulaFactory,
    val nUnfoldings: Int
) {

  // construct formulae that are reused wihtout changing
  // for global reachability check:
  val Y: Seq[IConstant] =
    solverState.createConstants("y_", solverState.X.length)
  val fLess2nUnfoldingsOfY = formulaFactory.fLessN(
    2 * nUnfoldings,
    Y
  )
  val subst: Map[ConstantTerm, ITerm] =
    solverState.X
      .zip(Y)
      .map { case (x, y) =>
        x.asInstanceOf[IConstant].c -> (x + y)
      }
      .toMap
  val g_of_XplusY = ConstantSubstVisitor(solverState.g, subst)

  // for local reachability check:
  val Z = solverState.createConstants("z_", solverState.X.length)
  val YPrime = solverState.createConstants("yPrime_", solverState.X.length)
  val ZPrime = solverState.createConstants("zPrime_", solverState.X.length)

  // for f1
  val fLessnUnfoldingsOfZ = formulaFactory.fLessN(
    nUnfoldings,
    Z
  )
  val XEqYPlusZ = solverState.X === (Y +++ Z)

  val f2 = !(solverState.X === (YPrime +++ ZPrime) & formulaFactory.fLessN(
    nUnfoldings,
    YPrime
  ) & formulaFactory.substituteX(solverState.g, ZPrime))
  val notf2Simplified = f2.notSimplify


  def strengthenOverApproximation(): Unit = {
    // global reachability check underApprox(X) & f_less_2n(Y) & g(X+Y) unsat
    val unsatCondForStrengthenOver: IFormula =
      solverState.underApproxFStar & fLess2nUnfoldingsOfY & g_of_XplusY

    if (!(SMT.isUnsat(unsatCondForStrengthenOver, solverState))) {
      // condition to strengthen overapproximation not met
      return
    }

    // check local reachability check: f1->f2 valid (equivalently f1&!f2 unsat)

    val f1 =
      formulaFactory.substituteX(solverState.underApproxFStar, Y) & fLessnUnfoldingsOfZ & XEqYPlusZ
    // construct formulae that change between calls (due to underApproxFStar being updated)
    if (!(SMT.isUnsat(f1 & notf2Simplified, solverState))) {
      // f1 doesn't imply f2: local reachability condition for strengthening not met
      return
    }


    
    // both conditions for strengthening met: 
    // => get Interpolant between f1 and f2

    val itp = SMT.getInterpolant(f1, notf2Simplified, solverState)
    // NOTE: itp has as variables solverState.X

    solverState.overApproxFStar = _getNextOverApprox(itp)
  }

  // update the the conjuncts from all previous interpolations.
  // return the overapproximation resulting from these conjuncts
  def _getNextOverApprox(newItp: IFormula): IFormula = {
    val conjuncts = FormulaFactory.conjuncts(newItp)
    solverState.allInterpolantConjuncts =
      solverState.allInterpolantConjuncts ++ conjuncts

    val inductiveConjuncts = _filterInductivePredicates(
      solverState.allInterpolantConjuncts
    )

    if (inductiveConjuncts.length == 0)
      IExpression.i(true)
    else
      inductiveConjuncts.reduce(_ & _)

  }

  def _filterInductivePredicates(predicates: Seq[IFormula]): Seq[IFormula] = {

    // inductive iff:
    // forall x,y; remainingPredicates(x) & f(y) -> remainingPredicates(x+y)
    def isInductiveClause(
        p: IFormula,
        remainingPredicatesOfX: IFormula,
        fOfY: IFormula,
        substXWithXPlusY: Map[ConstantTerm, ITerm]
    ): Boolean = {
      val pOfXPlusY =
        ConstantSubstVisitor(p, substXWithXPlusY)
      val inductivnessTest =
        remainingPredicatesOfX & fOfY & !pOfXPlusY

      SMT.isUnsat(inductivnessTest, solverState)
    }

    var previousRemainingPredicates: Seq[IFormula] = Seq()
    var remainingPredicates = predicates
    val Y = solverState.createConstants("y_", solverState.X.length)

    // remove non Inductive predicates until convergance
    while (remainingPredicates != previousRemainingPredicates) {
      if (remainingPredicates == Seq())
        // worst case, no clause was inductive
        return Seq()
      previousRemainingPredicates = remainingPredicates

      // compute formulas that remain constant for the inductiveness test upfront
      val remainingPredicatesOfX = remainingPredicates.reduce(_ & _)
      val fOfY = formulaFactory.substituteX(solverState.f, Y)
      val subst = (solverState.X zip Y).map { case (x, y) =>
        x.c -> (x + y)
      }.toMap

      remainingPredicates = for {
        p <- remainingPredicates
        if (isInductiveClause(p, remainingPredicatesOfX, fOfY, subst))
      } yield p
    }
    return remainingPredicates
  }
}

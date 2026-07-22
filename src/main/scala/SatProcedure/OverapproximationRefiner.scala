package LIAStarSolver.SatProcedure

import ap.SimpleAPI.pp
import ap.parser._
import ap.terfor.ConstantTerm

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.SMT.SMT

class OverapproximationRefiner(
    val solverState: SolverState,
    val formulaFactory: FormulaFactory
) {
  def strengthenOverApproximation(
      nUnfoldings: Int
  ): Unit = {
    import formulaFactory._
    val Y = solverState.createConstants("y_", solverState.X.length)
    val Z = solverState.createConstants("z_", solverState.X.length)

    val f1 =
      substituteX(solverState.underApproxFStar, Y) & fLessN(
        nUnfoldings,
        Z
      ) & solverState.X === (Y +++ Z)
    val YPrime = solverState.createConstants("yPrime_", solverState.X.length)
    val ZPrime = solverState.createConstants("zPrime_", solverState.X.length)
    val f2 = !(solverState.X === (YPrime +++ ZPrime) & fLessN(
      nUnfoldings,
      YPrime
    ) & substituteX(solverState.g, ZPrime))

    if (SMT.isUnsat(f1 & f2.notSimplify, solverState)) {
      // f1 ==> f2 is valid
      // get Interpolant between f1 and f2

      val itp = SMT.getInterpolant(f1, f2.notSimplify, solverState)
      // TODO: /NOTE itp has as variables X (in general, where to mention this,
      // how to make clear which variables occur for good readability/code clarity)
      println(s"DEBUG: in strengthenOver: find Interpolant ${pp(itp)}")
      solverState.overApproxFStar = _getNextOverApprox(itp)
    } else {
      println(
        "DEBUG: in strengthenOver: DONT find Interpolant => overapproximation stays the same"
      )
    }

    // TODO: remove this sanity check at the end of implementation
    assert(solverState.___isOverapproximationTest)
    // return new overapproximation
    // TODO: return wether it changed??
  }

  // TODO: Maybe extract into it's own class??
  // update the the conjuncts from all previous interpolations.
  // return the overapproximation resulting from these conjuncts
  def _getNextOverApprox(newItp: IFormula): IFormula = {
    val conjuncts = FormulaFactory.conjuncts(newItp)
    // TODO: make sure allInterpolantsConjuncts don't contain duplicates!?
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

      // compute shared formulas for every p
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

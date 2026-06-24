package LIAStarSolver.SatProcedure

import ap.SimpleAPI
import ap.parser._
import ap.terfor.ConstantTerm
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.SMT.SMT

import ap.SimpleAPI.pp

type Model = Map[IConstant, Int]
sealed trait SatResult
case object Unsat extends SatResult
case class Sat(model: Model) extends SatResult

class SatProcedure(
    solverInstance: SimpleAPI,
    g: IFormula,
    f: IFormula,
    X: Seq[IConstant]
) {

  val solverState = SolverState(solverInstance, g, f, X)
  val formulaFactory = FormulaFactory(solverState)

  // calculate if formula g(X) & f*(X) is sat or unsat
  def checkFormula(): SatResult = {
    if (isEarlyUnsat) {
      return Unsat
    }
    val earlySatRes: Option[Model] = isEarlySat
    if (earlySatRes.isDefined) {
      return Sat(earlySatRes.get)
    }
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

    if (SMT.isUnsat(unsatCondForStrengthenOver, solverState)) {
      println("DEBUG: strengthen over")
      strengthenOverApproximation(solverState, nUnfoldings)
    } else {
      println("DEBUG: DONT strengthen over")
    }

    if (isEarlyUnsat) {
      return Unsat
    }

    // val solution_fAndNotu =
    Unsat // TODO nur platzhalter!!!!!!
  }

  // return true if g & Overapproximation is unsat. Then g & f* must be unsat
  def isEarlyUnsat: Boolean = {
    SMT.isUnsat(g & solverState.overApproxFStar, solverState)
  }

  // return true if g & Underapproximation is sat. Then g & f* must be sat
  def isEarlySat: Option[Model] = {
    import solverState.solverInstance._
    push()
    !!(g & solverState.underApproxFStar)
    val res = ???
    println(res)
    val returnRes = if (res == SimpleAPI.ProverStatus.Sat) {
      val evaluator = completeModel
      Some(
        solverState.X.map { x =>
          x -> evaluator(x).asInstanceOf[IIntLit].value.intValueSafe
        }.toMap
      )
    } else {
      None
    }
    pop()
    returnRes
  }
  def strengthenOverApproximation(
      solverState: SolverState,
      nUnfoldings: Int
  ): Unit = {
    import formulaFactory._
    // TODO: QUESTION: is this a problem, if i do it multiple times (already in checkFormula)
    val Y = solverState.createConstants("y_", solverState.X.length)
    val Z = solverState.createConstants("z_", solverState.X.length)

    val f1 =
      substituteX(solverState.underApproxFStar, Y) & fLessN(
        nUnfoldings,
        Z
      ) & FormulaFactory.xEqualYPlusZ(X, Y, Z)
    val YPrime = solverState.createConstants("yPrime_", solverState.X.length)
    val ZPrime = solverState.createConstants("zPrime_", solverState.X.length)
    val f2 = !(FormulaFactory.xEqualYPlusZ(X, YPrime, ZPrime) & fLessN(
      nUnfoldings,
      YPrime
    ) & substituteX(solverState.g, ZPrime))

    if (SMT.isUnsat(f1 & f2.notSimplify, solverState)) {
      // f1 ==> f2 is valid
      // get Interpolant between f1 and f2
      println("DEBUG: in f1 implies f2")

      val itp = SMT.getInterpolant(f1, f2.notSimplify, solverState)
      // TODO: /NOTE itp has as variables X (in general, where to mention this,
      // how to make clear which variables occur for good readability/code clarity)
      println(s"itp ${itp}")
      solverState.overApproxFStar = getNextOverApprox(itp)
      println(s"updated overapprox ${solverState.overApproxFStar}")
    } else {
      println("DEBUG !(f1==>f2)")
    }

  }

  // TODO: Maybe extract into it's own class??
  // update the the conjuncts from all previous interpolations.
  // return the overapproximation resulting from these conjuncts
  def getNextOverApprox(newItp: IFormula): IFormula = {
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

package LIAStarSolver.FormulaFactory
import ap.parser._
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.parser.IExpression.{ex, all}
import ap.basetypes.IdealInt

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.Linear.SemilinearSet

object FormulaFactory {
  def conjuncts(f: IFormula): Seq[IFormula] = f match {
    case IBinFormula(IBinJunctor.And, left, right) =>
      conjuncts(left) ++ conjuncts(right)

    case _ =>
      Seq(f)
  }

  // Computes λB, where λ is a 1×n row vector and B is an n×m matrix
  // whose rows are the offset vectors.
  // The j-th result component is
  // Σ_i λ_i * B(i)(j)
  // if B is empty return 0-Vector
  def lambdaTimesB(
      lambdas: Seq[IConstant],
      B: Vector[Vector[IdealInt]],
      dim: Int
  ): Seq[ITerm] = {
    assume(B.forall(b => b.length == dim) && lambdas.length == B.length)

    if (B.isEmpty)
      Vector.fill(dim)(IExpression.i(0))
    else
      B.transpose.map { col =>
        (col zip lambdas)
          .map { case (bij: IdealInt, lam: IConstant) => lam * bij }
          .reduceOption(_ + _)
          .getOrElse(IExpression.i(0))
      }
  }

}

class FormulaFactory(val state: SolverState) {

  def fLessN(n: Int, Y: Seq[IConstant]): IFormula = {
    if (n == 0) {
      Y === 0
    } else {
      val h1 = state.createConstants(Y.length)
      val h2 = state.createConstants(Y.length)
      val unquantified = Y === (h1 +++ h2) &&&
        substituteX(state.f, h1) &&&
        fLessN(n - 1, h2)
      // import IExpression.quanConsts(IExpression.Qu)
      val consts = h1.map(_.c) ++ h2.map(_.c)
      val quantifiedFormula =
        IExpression.quanConsts(IExpression.Quantifier.EX, consts, unquantified)

      Y === 0 | quantifiedFormula

    }
  }

  // return formula(Y) (assumes formula has X as IConstants)
  def substituteX(formula: IFormula, Y: Seq[IConstant]): IFormula = {
    require(
      state.X.length == Y.length,
      "X:Seq[IConstant] and Y:Seq[IConstant] must have same length"
    )
    val substMap: Map[ConstantTerm, ITerm] =
      state.X.zip(Y).map { case (x, y) => x.c -> y.asInstanceOf[ITerm] }.toMap
    return ConstantSubstVisitor(formula, substMap)
  }

  // return a formula r, s.t x \in f*(x) <=> r(x),
  // where sls is the semilinear representation of LIA fromula f
  def starLIA(sls: SemilinearSet): IFormula = {
    if (sls.linearSets.isEmpty) {
      state.X === 0
    } else {
      val linSets = sls.linearSets.toSeq
      val dim = linSets(0).a.length
      val nLinSets = linSets.length

      val mu: Seq[IConstant] = state.createConstants(nLinSets)
      val lambdas: Seq[Seq[IConstant]] =
        linSets.map(ls => state.createConstants(ls.B.length))

      // Σ μ_i a_i + λ_i B_i
      val rhs: Seq[ITerm] = (0 until nLinSets)
        .map { i =>
          val mu_i_times_a: Seq[ITerm] =
            (linSets(i).a.map(IExpression.i(_)) *** mu(i))
          val lambda_i_B =
            FormulaFactory.lambdaTimesB(lambdas(i), linSets(i).B, dim)

          mu_i_times_a +++ lambda_i_B
        }
        .reduce(_ +++ _)

      val equality = state.X === rhs

      // mu can't be empty, since nLineSets != 0
      val muNonNegative: IFormula = mu.map(_ >= 0).reduce(_ &&& _)
      // lambdas could be empty
      val lambdasNonNegative: IFormula =
        lambdas.map(b => b.map(_ >= 0).fold(IExpression.i(true))(_ &&& _)).reduce(_ &&& _)

      // only use vectors from B if that linear Set is used in a combination
      // (the corresponding a has to be used aswell)
      val implication: IFormula = (0 until nLinSets)
        .map(i =>
          //(mu(i) === 0) ==> (lambdas(i).map(_.asInstanceOf[ITerm]) === 0)
          (mu(i) =/= 0) ||| (lambdas(i).map(_.asInstanceOf[ITerm]) === 0) // equivalent to mu(i)=0 => lambdas=0
        )
        .reduce(_ &&& _)

      val starLIABody =
        equality &&& implication &&& muNonNegative &&& lambdasNonNegative
      println(s"DEBUG_: equality ${equality}")
      println(s"DEBUG_: implication ${implication}")
      println(s"DEBUG_: muNonNegative ${muNonNegative}")
      println(s"DEBUG_: lambdasNonNegative ${lambdasNonNegative}")
      val consts = (mu +: lambdas).flatten.map(_.c)
      val quantified = IExpression.quanConsts(
        IExpression.Quantifier.EX,
        consts,
        starLIABody
      )
      quantified
    }

  }
}

package LIAStarSolver.FormulaFactory
import ap.parser._
import ap.terfor.ConstantTerm
import LIAStarSolver.SolverState.SolverState

class FormulaFactory(val state: SolverState) {

  def fLessN(n: Int, Y: Seq[IConstant]): IFormula = {
    if (n == 0) {
      FormulaFactory.eqZero(Y)
    } else {
      FormulaFactory.eqZero(Y) |
        state.exVector(Y.length) { h1 =>
          state.exVector(Y.length) { h2 =>
            FormulaFactory.xEqualYPlusZ(Y, h1, h2) &&&
              substituteX(state.f, h1) &&&
              fLessN(n - 1, h2)
          }
        }
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

}

object FormulaFactory {
  def eqZero(Y: Seq[IConstant]): IFormula = {
    Y.map(_ === 0).reduce(_ &&& _)
  }
  def xEqualYPlusZ(
      X: Seq[IConstant],
      Y: Seq[IConstant],
      Z: Seq[IConstant]
  ): IFormula = {
    assume((X.length == Y.length) && (Y.length == Z.length))
    return (0 until X.length)
      .map(i => X(i) === Y(i) + Z(i))
      .reduce(_ & _)
  }

  def conjuncts(f: IFormula): Seq[IFormula] = f match {
    case IBinFormula(IBinJunctor.And, left, right) =>
      conjuncts(left) ++ conjuncts(right)

    case _ =>
      Seq(f)
  }
}

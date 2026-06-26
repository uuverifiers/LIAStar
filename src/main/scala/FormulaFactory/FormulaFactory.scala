package LIAStarSolver.FormulaFactory
import ap.parser._
import ap.terfor.ConstantTerm
import LIAStarSolver.SolverState.SolverState

class FormulaFactory(val state: SolverState) {

  def fLessN(n: Int, Y: Seq[IConstant]): IFormula = {
    if (n == 0) {
      Y === 0
    } else {
      Y === 0 |
        state.exVector(Y.length) { h1 =>
          state.exVector(Y.length) { h2 =>
            Y === (h1 +++ h2) &&&
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
  def conjuncts(f: IFormula): Seq[IFormula] = f match {
    case IBinFormula(IBinJunctor.And, left, right) =>
      conjuncts(left) ++ conjuncts(right)

    case _ =>
      Seq(f)
  }
}

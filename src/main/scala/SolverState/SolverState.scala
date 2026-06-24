package LIAStarSolver.SolverState

import ap.parser._
import ap.SimpleAPI
import ap.parser.IExpression.ex
import LIAStarSolver.FormulaFactory.FormulaFactory

class SolverState(
    val solverInstance: SimpleAPI,
    val g: IFormula,
    val f: IFormula,
    val X: Seq[IConstant]
) {
  require(X.length > 0)

  var underApproxFStar: IFormula = X.map(_ === 0).reduce(_ &&& _)
  var allInterpolantConjuncts: Seq[IFormula] = Seq()

  var overApproxFStar: IFormula = true

  def createConstants(prefix: String, num: Int): Seq[IConstant] = {
    solverInstance
      .createConstants(prefix, 0 until num)
      .map(_.asInstanceOf[IConstant])
  }

  // create n dimensional existentially quantified vector for use in a formula
  // e.g exVector(2) { v=>v(0)===1&v(1)===1}
  // corresponds to: \exists v0,v1; v0=0 & v1=1
  def exVector(n: Int)(body: Seq[IConstant] => IFormula): IFormula = {
    def recursiveHelper(remaining: Int, vars: List[IConstant]): IFormula = {
      if (remaining == 0)
        body(vars)
      else
        ex(v =>
          recursiveHelper(remaining - 1, vars :+ v.asInstanceOf[IConstant])
        )
    }

    recursiveHelper(n, Nil)
  }


}

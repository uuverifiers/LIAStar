package LIAStarSolver.SolverState

import ap.parser._
import ap.SimpleAPI

import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.Linear.SemilinearSet
import LIAStarSolver.SMT.SMT

class SolverState(
    val solverInstance: SimpleAPI,
    val g: IFormula,
    val f: IFormula,
    val X: Seq[IConstant]
) {
  require(X.length > 0)

  var underApproxFStar: IFormula = X === 0
  var underApproxF_SLS = SemilinearSet(Set())
  var allInterpolantConjuncts: Seq[IFormula] = Seq()

  var overApproxFStar: IFormula = true

  def createConstants(prefix: String, num: Int): Seq[IConstant] = {
    solverInstance
      .createConstants(prefix, 0 until num)
      .map(_.asInstanceOf[IConstant])
  }
  def createConstants(num: Int): Seq[IConstant] = {
    solverInstance
      .createConstants(num)
      .map(_.asInstanceOf[IConstant])
  }
}

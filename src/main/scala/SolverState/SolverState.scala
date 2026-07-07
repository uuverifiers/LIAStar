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


  // function for tests/assertions: test if overApproxFStar is truly an overapproximation of f
  // TODO: just have this definition in testing???
  def ___isOverapproximationTest: Boolean = {
    import SimpleAPI.ProverStatus
    val formulaFactory = FormulaFactory(this)
    import formulaFactory._
    val overApproxCondition1 = X === 0 ==> overApproxFStar
    val Y = createConstants("y_", X.length)
    val Z = createConstants("y_", X.length)
    val overApproxCondition2 =
      (substituteX(overApproxFStar, Y) &
        substituteX(f, Z) &
        X === (Y +++ Z))
        ==> overApproxFStar

    SMT.isValid(
      (overApproxCondition1 & overApproxCondition2),
      this
    )
  }

}

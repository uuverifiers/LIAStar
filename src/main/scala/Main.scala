package LIAStarSolver
import ap.SimpleAPI
import ap.parser.{IConstant, IFormula}
import ap.terfor.ConstantTerm
import ap.basetypes.IdealInt
import SatProcedure.SatProcedure
import LIAStarSolver.SatResult.{SatResult, Sat, Unsat}

@main def main(): Unit = {

  // solve g(X) and f*(X)
  // (for LIA formulae g,f and X is a n-dimensional integer Vector)

  val api: SimpleAPI = SimpleAPI.spawnWithAssertions

  // expect: Sat
  // val X: IndexedSeq[IConstant] = api.createConstants("x_", 0 until 2).map(_.asInstanceOf[IConstant])
  // val g: IFormula = (X(1) + 2*X(0) >= 17) &
  // (6*X(0) - X(1) <= 47)
  // val f: IFormula = (5*X(0) + 2*X(1) >= 17) &
  // (3*X(0) - X(1) <= 8) &
  // (2*X(0) + 3*X(1) <= 20)

  // val X = api.createConstants("x_", 0 until 1).map(_.asInstanceOf[IConstant])
//
  // val g: IFormula = X(0) < -2
  //// val g: IFormula = X(0) < 2
  // val f: IFormula = X(0) >= 1
  //// val f: IFormula = X(0) === 1
  

  //import ap.util.Timer

  val X = api.createConstants("x_", 0 until 2).map(_.asInstanceOf[IConstant])

  // expect sat with only solution: X(0)=6, X(1)=3
  val g: IFormula =
    X(1) >= X(0) - 5 & X(1) >= -2 * X(0) + 13 & 4 * X(1) <= X(0) + 7
  val f: IFormula = (X(0) === 1 & X(1) === 1) | (X(0) === 3 & X(1) === 0)

  // expect unsat
  // val X: Seq[IConstant] =
  // api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
  // val g: IFormula = X(0) === 4 & X(1) === 7
  // val f: IFormula = X(0) + X(1) === 3

  val nUnfoldings = 1
  val s = SatProcedure(api, g, f, X)
  val res: SatResult = s.checkFormulaWithTimingMeasurement(nUnfoldings)

  println(res)
  import ap.util.Timer
  println(Timer)

  api.shutDown
}

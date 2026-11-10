package LIAStarSolver
import ap.SimpleAPI
import ap.parser.{IConstant, IFormula}
import ap.terfor.ConstantTerm
import ap.basetypes.IdealInt
import LIAStarSolver.SatProcedure.SatProcedure
import LIAStarSolver.SatResult.{SatResult, Sat, Unsat}

@main def main(): Unit = {
  // usage example:
  
  // expect sat with only solution: X(0)=6, X(1)=3
  val api: SimpleAPI = SimpleAPI.spawnWithAssertions
  val x1 = api.createConstant("x1")
  val x2 = api.createConstant("x2")
  val X = Seq(x1, x2).map(_.asInstanceOf[IConstant])
  val g: IFormula =
    x2 >= x1 - 5 & x2 >= -2 * x1 + 13 & 4 * x2 <= x1 + 7
  val f: IFormula = (x1 === 1 & x2 === 1) | (x1 === 3 & x2 === 0)

  val s = SatProcedure(api, g, f, X)
  val res: SatResult = s.checkFormula(5)
  println(res)
  api.shutDown

  // usage example 2:
  // expect unsat
  /*
  val api2: SimpleAPI = SimpleAPI.spawnWithAssertions
  val X2: Seq[IConstant] =
    api2.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
  val g2: IFormula = X2(0) === 4 & X2(1) === 7
  val f2: IFormula = X2(0) + X2(1) === 3

  val s2 = SatProcedure(api2, g2, f2, X2)
  val res2: SatResult = s2.checkFormula(1)
  println(res2)
  api2.shutDown
  */

}

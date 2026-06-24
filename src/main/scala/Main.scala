package LIAStarSolver
import ap.SimpleAPI
import ap.parser._
import ap.parser.IExpression
import ap.terfor.ConstantTerm
import ap.basetypes.IdealInt
import LIAStarSolver.SatProcedure.SatProcedure

@main def main(): Unit = {

  // solve A(X) and B*(X)
  // (for LIA formulae A,B and X is a n-dimensional integer Vector)

  val api: SimpleAPI = SimpleAPI.spawn

  val nDim = 2
  // val X: Seq[IConstant] =
  // (0 until n).map(i =>
  // new IConstant(new ConstantTerm(s"x$i"))
  // )

  // val u4: IConstant = api.createConstant("u4").asInstanceOf[IConstant]
  // val u5: IConstant = api.createConstant("u5").asInstanceOf[IConstant]
  // val u6: IConstant = api.createConstant("u6").asInstanceOf[IConstant]
  // val n: IConstant = api.createConstant("n").asInstanceOf[IConstant]
  // val t: IConstant = api.createConstant("t").asInstanceOf[IConstant]
  // val f02: IConstant = api.createConstant("f02").asInstanceOf[IConstant]
  // val universalSet: IConstant = api.createConstant("universalSet").asInstanceOf[IConstant]
  // val X: Seq[IConstant] = Seq(u4, u5, u6, n, t, f02, universalSet)
  // val g: IFormula = u4 === 0 & u5 === n & n > 0 & n > 3*t & u6 <= t & n - t <= 0
  // val f: IFormula = (u4 === IExpression.ite(f02 > universalSet, 1, 0))& (u5 === universalSet) & (u6 === f02) &
  // f02 >= 0 & universalSet >= 0

  // val X: IndexedSeq[IConstant] = api.createConstants("x_", 0 until nDim).map(_.asInstanceOf[IConstant])
  // val g: IFormula = (X(1) + 2*X(0) >= 17) &
  // (6*X(0) - X(1) <= 47)
  // val f: IFormula = (5*X(0) + 2*X(1) >= 17) &
  // (3*X(0) - X(1) <= 8) &
  // (2*X(0) + 3*X(1) <= 20)

  val X: IndexedSeq[IConstant] = api.createConstants("x_", 0 until 1).map(_.asInstanceOf[IConstant])
  //val g: IFormula = X(0) < -2
  val g: IFormula = X(0) < 2
  val f: IFormula = X(0) === 1

  println(SimpleAPI.pp(g))

  // api.!!(g)
  // println(api.???)

  val s = SatProcedure(api, g, f, X)
  s.checkFormula()

  api.shutDown
}


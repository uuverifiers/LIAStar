package LIAStarSolver.SemilinearSet

import ap.parser._
import ap.terfor.ConstantTerm
import ap.SimpleAPI.pp //////////
import ap.basetypes.IdealInt

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SMT.SMT
import ap.parser.IExpression.RichITermSeq
def vecLessThan(a: Vector[IdealInt], b: Vector[IdealInt]): Boolean = {
  a.zip(b).forall(_.abs <= _.abs)
}

class LinearSet(var a: Vector[IdealInt], var B: Vector[Vector[IdealInt]]) {
  require(
    B.forall(_.length == a.length),
    s"All vectors in B must have length ${a.length}"
  )
  // if (!B.contains(g))
  // B = B :+ g

  def shiftDown(solverState: SolverState) = {
    println("DEBUG SHIFT DOWN")
    def conditionIsValidFor(b: Vector[IdealInt]): Boolean = {
      println("DEBUG conditionIsValidFor")
      // check if Forall Lamda; f(a - b + Lambda*B) is valid
      // (where Lambda*B is Vector*Matrix multiplication

      val lambdas = solverState.createConstants("lambda_", B.length)

      val lambdaB: Seq[ITerm] =
        B.transpose.map { col =>
          (col zip lambdas)
            .map { case (bij, lam) => lam * bij }
            .reduceOption(_ + _)
            .getOrElse(IExpression.i(0))
        }
      val substMap: Map[ConstantTerm, ITerm] =
        solverState.X.indices.map { i =>
          solverState.X(i).c ->
            (IExpression.i(a(i) - b(i)) + lambdaB(i))
        }.toMap

      // val BTransposed: Seq[Seq[ITerm]] =
      // B.transpose.map(_.map(_.asInstanceOf[ITerm]))
//
      //// TODO: lambda >0 ???
      // val substMap: Map[ConstantTerm, ITerm] =
      // solverState.X.indices.map { i =>
      // val term: ITerm = {
      // IExpression.i(a(i) - b(i)) +
      // (BTransposed
      // .zip(lambdas)
      // .map { case (transposedVec, lam) =>
      // (transposedVec *:* Seq.fill(transposedVec.length)(lam)) //dot product
      // }
      // .reduceOption(_ +++ _)
      // .getOrElse(IExpression.i(0)))
      // }
//
      // solverState.X(i).c -> term
      // }.toMap

      // val substMap: Map[ConstantTerm, ITerm] =
      // solverState.X.indices.map { i =>
      // val term: ITerm = {
      // IExpression.i(a(i) - b(i)) +
      // (B.zip(lambdas)
      // .map { case (bVector, lam) =>
      // lam * IExpression.i(bVector(i))
      // }
      // .reduceOption(_ + _)
      // .getOrElse(IExpression.i(0)))
      // }
//
      // solverState.X(i).c -> term
      // }.toMap
//
      val condition = ConstantSubstVisitor(!(solverState.f), substMap)

      SMT.isUnsat(condition, solverState)

    }

    B.find { b =>
      vecLessThan(b, a) && conditionIsValidFor(b)

    } match {
      case Some(b) =>
        println(s"DEBUG found shiftDown b ${b}")
        println(s"DEBUG {a}-{b} should be: {a.zip(b).map(_ - _).toVector}")
        a = a.zip(b).map(_ - _).toVector
        new LinearSet(a.zip(b).map { case (ai, bi) => ai - bi }, B)

      case None =>
        println("NO b found")
        this
    }
  }

}

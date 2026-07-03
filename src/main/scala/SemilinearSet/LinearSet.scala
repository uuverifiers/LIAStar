package LIAStarSolver.SemilinearSet

import ap.parser._
import ap.terfor.ConstantTerm
import ap.SimpleAPI.pp //////////

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SMT.SMT
def vecLessThan(a: Vector[Int], b: Vector[Int]): Boolean = {
  a.zip(b).forall(_.abs <= _.abs)
}

class LinearSet(var a: Vector[Int], var B: Vector[Vector[Int]]) { //TODO: vals idealint
  require(
    B.forall(_.length == a.length),
    s"All vectors in B must have length ${a.length}"
  )
  // if (!B.contains(g))
  // B = B :+ g

  def shiftDown(solverState: SolverState) = {
    println("DEBUG SHIFT DOWN")
    def conditionIsValidFor(b: Vector[Int]): Boolean = {
      println("DEBUG conditionIsValidFor")
      // check if Forall Lamda; f(a - b + Lambda*B) is valid
      // (where Lambda*B is Vector*Matrix multiplication

      val lambdas = solverState.createConstants("lambda_", B.length)
      val substMap: Map[ConstantTerm, ITerm] =
        solverState.X.indices.map { i =>
          val term: ITerm = {
            IExpression.i(a(i) - b(i)) +
              (B.zip(lambdas)
                .map { case (bVector, lam) =>
                  lam * IExpression.i(bVector(i))
                }
                .reduceOption(_ + _)
                .getOrElse(IExpression.i(0)))
          }

//todo vectoraddition
          solverState.X(i).c -> term
        }.toMap

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

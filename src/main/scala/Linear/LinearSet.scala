package LIAStarSolver.Linear

import ap.parser._
import ap.terfor.ConstantTerm
import ap.basetypes.IdealInt
import ap.parser.IExpression.RichITermSeq

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SMT.SMT
def vecLessThan(a: Vector[IdealInt], b: Vector[IdealInt]): Boolean = {
  a.zip(b).forall((a, b) => (0 <= a && a <= b) || (0 >= a && a >= b))
}
def vecMinus(a: Vector[IdealInt], b: Vector[IdealInt]): Vector[IdealInt] = {
  a.zip(b).map(_ - _)
}

class LinearSet(
    val a: Vector[IdealInt],
    BWithDuplicatesAnd0: Vector[Vector[IdealInt]]
) {
  require(
    BWithDuplicatesAnd0.forall(_.length == a.length),
    s"All vectors in B must have length ${a.length}"
  )

  // BWithDuplicates can contain duplicates and 0 vector.
  // These are removed in B and B is turned into a canonical representation
  val B =
    BWithDuplicatesAnd0.distinct
      .filterNot(b => b.forall(_ == IdealInt.ZERO))
      .sortBy(_.toString.mkString(","))

  override def toString(): String = s"LS(a: ${a}, B: ${B})"
  override def equals(other: Any): Boolean = other match {
    case ls: LinearSet => a == ls.a && B == ls.B
    case _             => false
  }
  override def hashCode(): Int = (a, B).##

  // try to apply shift down rule.
  // if applicapable, return Some(newLinearSet), where newLinearSet is the result of the application.
  // return None, if shiftDown can't be applied
  def shiftDown(solverState: SolverState): Option[LinearSet] = {
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

      val condition =
        lambdas >= 0 & ConstantSubstVisitor(!(solverState.f), substMap)
      SMT.isUnsat(condition, solverState)

    }

    B.find { b =>
      vecLessThan(b, a) && conditionIsValidFor(b)

    } match {
      case Some(b) =>
        Some(LinearSet(vecMinus(a, b), B))

      case None =>
        None
    }
  }

  // try to apply Offset Down rule.
  // if applicapable, return Some(newLinearSet), where newLinearSet is the result of the application.
  // return None, if shiftDown can't be applied
  def offsetDown(solverState: SolverState): Option[LinearSet] = {
    println(s"DEBUG conditionIsValidFor on ${this}")
    def conditionIsValidFor(
        b1: Vector[IdealInt],
        b2: Vector[IdealInt]
    ): Boolean = {
      // check if vecLessThan(b2,b1) and Forall Lamda; f(a + Lambda*B') with
      // B' = B\{b1} union {b1-b2} is valid
      // (where Lambda*B' is Vector*Matrix multiplication

      if (!vecLessThan(b2, b1)) {
        return false
      }
      val lambdas = solverState.createConstants("lambda_", B.length)
      val BPrime = B.filterNot(_ == b1) :+ vecMinus(b1, b2)

      val lambdaBPrime: Seq[ITerm] = BPrime.transpose.map { col =>
        (col zip lambdas)
          .map { case (bij: IdealInt, lam: IConstant) => lam * bij }
          .reduceOption(_ + _)
          .getOrElse(IExpression.i(0))
      }
      val substMap: Map[ConstantTerm, ITerm] = solverState.X.indices.map { i =>
        solverState.X(i).c ->
          (a(i) + lambdaBPrime(i))
      }.toMap
      val condition =
        lambdas >= 0 & ConstantSubstVisitor(!(solverState.f), substMap)
      SMT.isUnsat(condition, solverState)
    }

    // iterate over all combinations of b1,b2 in B and check if rules for applying offset down are satisfied
    B.combinations(2)
      .flatMap { pair =>
        Iterator(
          (pair(0), pair(1)),
          (pair(1), pair(0))
        ) // TODO: check both directions in conditionIsValidFor
      }
      .collectFirst {
        case (b1, b2) if conditionIsValidFor(b1, b2) =>
          val BPrime = B.filterNot(_ == b1) :+ vecMinus(b1, b2)
          LinearSet(a, BPrime)
      }
  }

  // try to merge second linear set to this.
  // If merge rule is applicable, return the result LinearSet, otherwise None
  def merge(that: LinearSet, solverState: SolverState): Option[LinearSet] = {
    def conditionIsValidFor(
        ls1: LinearSet,
        ls2: LinearSet
    ): Boolean = {
      // for ls1 = LinearSet(a1, B1) and ls2 = LinearSet(a2, B2)
      // check if vecLessThan(a2,a1) and Forall Lamda; f(a2 + Lambda1*B1 + Lambda2*B2 + lambda3*(a1-a2))
      // (where Lambda1*B1 and Lambda2*B2 is Vector*Matrix multiplication)

      if (!vecLessThan(ls2.a, ls1.a)) {
        return false
      }
      val Lambdas1 = solverState.createConstants("lambda1_", ls1.B.length)
      val Lambdas2 = solverState.createConstants("lambda2_", ls2.B.length)
      val lambda3 = solverState.solverInstance.createConstant("lambda3")

      val Lambdas1B1: Seq[ITerm] =
        if (ls1.B.isEmpty)
          Vector.fill(ls1.a.length)(IExpression.i(0))
        else
          ls1.B.transpose.map { col =>
            (col zip Lambdas1)
              .map { case (bij: IdealInt, lam: IConstant) => lam * bij }
              .reduceOption(_ + _)
              .getOrElse(IExpression.i(0))
          }
      val Lambdas2B2: Seq[ITerm] =
        if (ls2.B.isEmpty)
          Vector.fill(ls2.a.length)(IExpression.i(0))
        else
          ls2.B.transpose.map { col =>
            (col zip Lambdas2)
              .map { case (bij: IdealInt, lam: IConstant) => lam * bij }
              .reduceOption(_ + _)
              .getOrElse(IExpression.i(0))
          }
      val a1_minus_a2 = vecMinus(ls1.a, ls2.a)
      val substMap: Map[ConstantTerm, ITerm] = solverState.X.indices.map { i =>
        solverState.X(i).c ->
          (ls2.a(i) + Lambdas1B1(i) + Lambdas2B2(i) + a1_minus_a2(i) * lambda3)
      }.toMap
      val condition =
        Lambdas1 >= 0 & Lambdas2 >= 0 & lambda3 >= 0 & ConstantSubstVisitor(
          !(solverState.f),
          substMap
        )
      val res = SMT.isUnsat(condition, solverState) // TODO
      res
    }

    if (conditionIsValidFor(this, that)) {
      Some(LinearSet(that.a, (this.B ++ that.B) :+ vecMinus(this.a, that.a)))
    } else if (conditionIsValidFor(that, this)) {
      Some(LinearSet(this.a, (that.B ++ this.B) :+ vecMinus(that.a, this.a)))
    } else {
      None
    }
  }
}

package LIAStarSolver.TestHelpers


import ap.SimpleAPI
import ap.parser._

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.Linear.LinearSet

trait TestHelpers extends munit.FunSuite {

  def assertEquivalent(
      api: SimpleAPI,
      a: IFormula,
      b: IFormula
  ): Unit = {

    api.push()
    api.!!(!(a <=> b))
    assertEquals(
      api.???,
      SimpleAPI.ProverStatus.Unsat
    )

    api.pop()
  }
  def assertNotEquivalent(
      api: SimpleAPI,
      a: IFormula,
      b: IFormula
  ): Unit = {

    api.push()
    api.!!(!(a <=> b))
    assertEquals(
      api.???,
      SimpleAPI.ProverStatus.Sat
    )

    api.pop()
  }

  def equivalentLSOptions(
      obtained: Option[LinearSet],
      expected: Option[LinearSet]
  ) = {
    (obtained, expected) match {
      case (Some(x), Some(y)) =>
        x.a == y.a && x.B.toSet == y.B.toSet && x.B.length==y.B.length
        //TODO/NOTE duplicates in B ignored. Should i enforce/implement non duplicates later???

      case _ =>
        obtained == expected
    }
  }
}

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

}

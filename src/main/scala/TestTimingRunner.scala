package LIAStarSolver
import ap.SimpleAPI
import ap.parser.{IConstant, IFormula, IExpression}
import ap.util.Timer

import SatProcedure.SatProcedure

object TestTiming {

  case class TestCase(
      name: String,
      mkProcedure: () => SatProcedure
  )

  val benchmarks = Seq(
    TestCase(
      "empty f, 0 in g",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g = X(0) === 0 & X(1) === 0
        val f = IExpression.i(false)
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "empty f, 0 not in g",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g =
          (X(1) + 2 * X(0) >= 17) &
            (6 * X(0) - X(1) <= 47)
        val f = false
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "empty g",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g = false
        val f = true
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "single solution",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g = X(0) === 6 & X(1) === 3
        val f = X(0) === 2 & X(1) === 1
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "single point g unsat",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g = X(0) === 5 & X(1) === 3
        val f = X(0) === 2 & X(1) === 1
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "x plus y sat",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g = X(0) === 2 & X(1) === 7
        val f = X(0) + X(1) === 3
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "x plus y unsat",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g = X(0) === 4 & X(1) === 7
        val f = X(0) + X(1) === 3
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "g cone",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g =
          (X(1) + 2 * X(0) >= 17) &
            (6 * X(0) - X(1) <= 47)
        val f =
          (5 * X(0) + 2 * X(1) >= 17) &
            (3 * X(0) - X(1) <= 8) &
            (2 * X(0) + 3 * X(1) <= 20)
        SatProcedure(api, g, f, X)
      }
    ),

    TestCase(
      "unsat test",
      () => {
        val api = SimpleAPI.spawnWithAssertions
        val X =
          api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
        val g =
          (X(0) > 10 & X(1) === 1) |
            (X(0) <= 2 & X(0) + X(1) <= 2 & !(X(0) === 0 & X(1) === 0))
        val f =
          X(0) >= 1 &
            X(1) >= 2
        SatProcedure(api, g, f, X)
      }
    )
  )

  @main def runTestTiming(): Unit = {
    // JVM warm-up
    for (b <- benchmarks) {

      b.mkProcedure().checkFormulaWithTimingMeasurement()
    }
    Timer.reset
    for (b <- benchmarks) {
      println(s"=== ${b.name} ===")


      Timer.reset

      // Measured run
      b.mkProcedure().checkFormulaWithTimingMeasurement()

      println(Timer)
      Timer.reset
    }
    //println(Timer)
  }
}

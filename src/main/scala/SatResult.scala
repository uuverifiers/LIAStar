package LIAStarSolver.SatResult
import ap.parser.IConstant

sealed trait SatResult
type Model = Map[IConstant, Int]
case object Unsat extends SatResult
case class Sat(model: Model) extends SatResult


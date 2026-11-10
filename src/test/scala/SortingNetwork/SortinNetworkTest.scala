package LIAStarSolver

import ap.SimpleAPI
import ap.parser._
import ap.parser.IExpression._
import ap.parser.ITerm
import ap.util.Timer
import ap.SimpleAPI.ProverStatus
import ap.basetypes.IdealInt

import scala.util.Random

import LIAStarSolver.SatProcedure.SatProcedure

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SatResult._

//Use Notation from Knuths Book
def sortingNetwork(X: Seq[IConstant], Y: Seq[IConstant], api: SimpleAPI): Seq[IFormula] = {
  val res = Seq[IFormula]()
  val N = X.length
  if Y.length != N then throw new Exception("Wrong number of sorted bounds")
  val t = math.ceil(math.log(N)/math.log(2)).toInt
  val maxLayers = (t * (t + 1) / 2).toInt
  val layers = (0 to maxLayers).map(i => (0 to N - 1).map(j => api.createConstant(s"x$i$j")))
  //Initialize layers
  val init = for(i <- 0 to N -1) yield X(i) === layers(0)(i) & Y(i) === layers(maxLayers)(i)
  //Define compare and swap function
  def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
    val first = math.min(pos1, pos2)
    val second = math.max(pos1, pos2)
    ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
  }
  //Propagate equality over layers
  def propLayer(ind: Seq[Int], layer: Int) =
    (for(x <- ind) yield layers(layer + 1)(x) === layers(layer)(x)).fold(IBoolLit(true))(_ & _)

  //M1+M2 Initialisation
  val p = math.pow(2,t-1).toInt
  val q = math.pow(2,t-1).toInt
  val r = 0
  val d = p
  def M3(p: Int, q: Int, r: Int, d: Int, currlayer: Int): Seq[IFormula] = {
    //println(s"p=$p, q=$q, r=$r, d=$d")
    val body = {
      if currlayer < maxLayers then
        val compLow = (0 to N - d - 1).filter(i => (i & p) == r)
        val compInd = compLow.flatMap(i => Seq(i,i+d)).toSet
        val propInd = (0 to N-1).filterNot(compInd.contains(_))
        val compConstraints = compLow.map(i => compSwap(i, i+d, currlayer))
        val propConstraints = propLayer(propInd,currlayer)
        compConstraints:+ propConstraints
        else
          Seq.empty[IFormula]
    }
    //Check M5
    if q != p then
      body ++ M3(p, q/2, p, q-p, currlayer + 1)
    //Check M6
    else if (p/2).toInt == 0 then
      body
    else
      val p0 = (p / 2).toInt
      body ++ M3(p0, math.pow(2,t-1).toInt, 0, p0, currlayer + 1)
  }
  init ++ M3(p, q, r, d, 0)
}

def bijSorting(X: Seq[IConstant], Y: Seq[IConstant], api: SimpleAPI): Seq[IFormula] = {
  val n = X.length
  val P = (0 until n).map(i => api.createConstant(s"p$i").asInstanceOf[IConstant])
  val values: Seq[IFormula] = (0 until n).map(i => ((0 <= P(i)) & (P(i) <= IdealInt(n-1))))
  val inj: Seq[IFormula] = (0 until n).map(i => (0 until i).map(j => P(i) =/= P(j))).flatten
  val func = for(i <- 0 until n; j <- 0 until n) yield 
    (P(i) === IdealInt(j)) ==> (Y(i) === X(j))
  val sorted = (0 until n-1).map(i => (Y(i) <= Y(i+1)))
  values ++ inj ++ func ++ sorted
}

class SortingNetworkTest extends munit.FunSuite {
  test("Sorting Network Random Number Forward Propagation") {
    //Elements to be sorted
    val n = 1
    val numbers: Seq[Int] = (0 until n).map(_ => Random.nextInt())

    //Sorting Network
    val api: SimpleAPI = SimpleAPI.spawn
    val X = (0 until n).map(i => api.createConstant(s"x$i").asInstanceOf[IConstant])
    val Y = (0 until n).map(i => api.createConstant(s"y$i").asInstanceOf[IConstant])
    val init: Seq[IFormula] = for (i <- 0 until n) yield (X(i) === IdealInt(numbers(i)))
    
    val start = System.nanoTime()
    val fin = for (i <- 0 until n-1) yield (Y(i) <= Y(i+1))
    val intermediate: Seq[IFormula] = sortingNetwork(X,Y,api)  
    (init ++ intermediate ++ fin).foreach(api.addAssertion)
    val result = api.???
    val end = System.nanoTime()
    val t = end - start

    println(result)
    println(s"Time for sorting Network: ${t/1000000.0}ms")
    //for (i <- 0 until n) do println(s"Y($i)=${api.eval(Y(i))}")
    assert(result == ProverStatus.Sat)
    api.shutDown


    //bijection Sorting
    val api2: SimpleAPI = SimpleAPI.spawn
    val XAlt = (0 until n).map(i => api2.createConstant(s"xAlt$i").asInstanceOf[IConstant])
    val YAlt = (0 until n).map(i => api2.createConstant(s"yAlt$i").asInstanceOf[IConstant])
    val init2: Seq[IFormula] = for (i <- 0 until n) yield (XAlt(i) === IdealInt(numbers(i)))

    val start2 = System.nanoTime()
    val fin2 = for (i <- 0 until n-1) yield (YAlt(i) <= YAlt(i+1))
    val intermediate2: Seq[IFormula] = bijSorting(XAlt, YAlt, api2)
    (init2 ++ intermediate2 ++ fin2).foreach(api2.addAssertion)
    val result2 = api2.???
    val end2 = System.nanoTime()
    val t2 = end2 - start2

    println(s"Time for bijection Sorting: ${t2/1000000.0}ms")
    //for (i <- 0 until n) do println(s"YAlt($i)=${api2.eval(YAlt(i))}")
    assert(result2 == ProverStatus.Sat)
    api2.shutDown

    println(s"For $n random (fixed) values to be sorted:")
    if (t2 < t) then
      println(s"Bijection Sort is faster by ${(t-t2)/1000000.0}ms or ${(t-t2)/t.toDouble*100}% SpeedUp Factor ${t.toDouble/t2}")
    else
      println(s"Sorting Network is faster by ${(t2 - t)/1000000.0}ms or ${(t2-t)/t2.toDouble*100}% SpeedUp Factor ${t2.toDouble/t}")
    println("End Of First Test\n %%%%%%%%\n %%%%%%%%\n %%%%%%%%")

  }

  test("Sorting Network Random Number Backward Propagation") {
    //Elements to be sorted
    val n = 4
    val numbers: Seq[Int] = (0 until n).map(_ => Random.nextInt()).sorted
    val subset = Random.shuffle((0 until n).toList).take(Random.nextInt(n)).sorted
    //Sorting Network
    val api: SimpleAPI = SimpleAPI.spawn
    val X = (0 until n).map(i => api.createConstant(s"x$i").asInstanceOf[IConstant])
    val Y = (0 until n).map(i => api.createConstant(s"y$i").asInstanceOf[IConstant])
    val init: Seq[IFormula] = for(i <- subset) yield (Y(i) === IdealInt(numbers(i)))
    
    val start = System.nanoTime()
    val fin = for (i <- 0 until n-1) yield (Y(i) <= Y(i+1))
    val intermediate: Seq[IFormula] = sortingNetwork(X,Y,api)  
    (init ++ intermediate ++ fin).foreach(api.addAssertion)
    val result = api.???
    val end = System.nanoTime()
    val t = end - start

    println(result)
    println(s"Time for sorting Network: ${t/1000000.0}ms")
    //for (i <- 0 until n) do println(s"Y($i)=${api.eval(Y(i))}")
    assert(result == ProverStatus.Sat)
    api.shutDown


    //bijection Sorting
    val api2: SimpleAPI = SimpleAPI.spawn
    val XAlt = (0 until n).map(i => api2.createConstant(s"xAlt$i").asInstanceOf[IConstant])
    val YAlt = (0 until n).map(i => api2.createConstant(s"yAlt$i").asInstanceOf[IConstant])
    val init2: Seq[IFormula] = for (i <- 0 until n) yield (XAlt(i) === IdealInt(numbers(i)))

    val start2 = System.nanoTime()
    val fin2 = for (i <- 0 until n-1) yield (YAlt(i) <= YAlt(i+1))
    val intermediate2: Seq[IFormula] = bijSorting(XAlt, YAlt, api2)
    (init2 ++ intermediate2 ++ fin2).foreach(api2.addAssertion)
    val result2 = api2.???
    val end2 = System.nanoTime()
    val t2 = end2 - start2

    println(s"Time for bijection Sorting: ${t2/1000000.0}ms")
    //for (i <- 0 until n) do println(s"YAlt($i)=${api2.eval(YAlt(i))}")
    assert(result2 == ProverStatus.Sat)
    api2.shutDown

    println(s"For $n values to be sorted where the order position and value of ${subset.length} variables is knwon a priori then:")
    if (t2 < t) then
      println(s"Bijection Sort is faster by ${(t-t2)/1000000.0}ms or ${(t-t2)/t.toDouble*100}% SpeedUp Factor ${t.toDouble/t2}")
    else
      println(s"Sorting Network is faster by ${(t2 - t)/1000000.0}ms or ${(t2-t)/t2.toDouble*100}% SpeedUp Factor ${t2.toDouble/t}")

  }
}
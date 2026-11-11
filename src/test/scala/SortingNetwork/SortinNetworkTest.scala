package LIAStarSolver

import ap.SimpleAPI
import ap.parser._
import ap.parser.ITerm
import ap.SimpleAPI.ProverStatus
import ap.basetypes.IdealInt

import scala.util.Random

import LIAStarSolver.Sorting.SortingEncoding

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
    val intermediate: Seq[IFormula] = SortingEncoding.sortingNetwork(X, Y, api)
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
    val intermediate2: Seq[IFormula] = SortingEncoding.bijectionSorting(XAlt, YAlt, api2)
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
    val intermediate: Seq[IFormula] = SortingEncoding.sortingNetwork(X, Y, api)
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
    val intermediate2: Seq[IFormula] = SortingEncoding.bijectionSorting(XAlt, YAlt, api2)
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
package LIAStarSolver

import ap.SimpleAPI
import ap.parser._
import ap.parser.IExpression._
import ap.parser.ITerm
import ap.util.Timer

import LIAStarSolver.SatProcedure.SatProcedure

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SatResult._
import LIAStarSolver.Sorting.SortingEncoding

class BenchmarkTests extends munit.FunSuite {
  test("Sorting Network implementation") {
    println("Test running")
    val api: SimpleAPI = SimpleAPI.spawn
    val X = (0 to 15).map(i => api.createConstant(s"x$i").asInstanceOf[IConstant])
    val Y = (0 to 15).map(i => api.createConstant(s"y$i").asInstanceOf[IConstant])
    println(SortingEncoding.sortingNetwork(X, Y, api).fold(IBoolLit(true))(_ & _))
  }

  test("Two sums, sorting network, no read, linear f, SAT") {
    val testname = "Two sums, sorting network, no read, linear f, SAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i").asInstanceOf[IConstant]) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      (res === 5 * in)
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i").asInstanceOf[IConstant])

    //SORTING NETWORK
    //t*(t+1)/2 layers to sort for t minimal with 2^t >= N, here 3 plus start
    val maxLayers = 3  
    val layers = (0 to maxLayers).map(i => (0 to 3).map(j => api.createConstant(s"x$i$j")))

    //Connect Layers to unsorted and sorted variables
    val sortNetworkInit: Seq[IFormula] = {
      (0 to 3).map(i => (layers(0)(i) === X(i)) & (layers(maxLayers)(i) === Y(i)))
    }

    //Define compare and swap function
    def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
      val first = math.min(pos1, pos2)
      val second = math.max(pos1, pos2)
      ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
    }

    //Propagate equality over layers
    def propLayer(ind: Seq[Int], layer: Int) =
      (for(x <- ind) yield layers(layer + 1)(x) === layers(layer)(x)).fold(IBoolLit(true))(_ & _)

    //sorting network (Batcher's merge-exchange) constraints (can be added algorithmically depending on N, see Knuth 5.2.2)
    val sortConstraints: Seq[IFormula] = Seq(
      //first layer
      compSwap(0,2,0),
      compSwap(1,3,0),
      propLayer(Seq.empty,0),
      //second layer
      compSwap(0,1,1),
      compSwap(2,3,1),
      propLayer(Seq.empty,1),
      //third layer
      compSwap(1,2,2),
      propLayer(Seq(0,3),2)
    )
    println("Current Sorting Network")
    println(sortNetworkInit ++ sortConstraints)
    println("Knuths Algorithm")
    println(SortingEncoding.sortingNetwork(X, Y, api))
  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === 5,
        (v1 - v0) < 40
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortNetworkInit, sortConstraints, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(1)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

  test("Two sums, naive sorting, no read, linear f, SAT") {
    val testname = "Two sums, naive sorting, no read, linear f, SAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      (res === 5 * in)
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    // Naive sorting encoding for 4 elements
    val sortingConstraint: Seq[IFormula] = {

      // Y must be sorted
      val sorted =
        (Y(0) <= Y(1)) &
        (Y(1) <= Y(2)) &
        (Y(2) <= Y(3))

      // Y must be a permutation of X
      val permutations: IFormula =
        (0 to 3).permutations.map { p =>
          (0 to 3)
            .map(i => Y(i) === X(p(i)))
            .fold(IBoolLit(true))(_ & _)
        }.fold(IBoolLit(false))(_ | _)
      Seq(sorted, permutations)
    }

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === 5,
        (v1 - v0) < 40
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortingConstraint, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(1)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

  test("Two sums, sorting network, no read, linear f, UNSAT") {
    val testname = "Two sums, sorting network, no read, linear f, UNSAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      (res === 5 * in)
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    //SORTING NETWORK
    //t*(t+1)/2 layers to sort for t minimal with 2^t >= N, here 3 plus start
    val maxLayers = 3  
    val layers = (0 to maxLayers).map(i => (0 to 3).map(j => api.createConstant(s"x$i$j")))

    //Connect Layers to unsorted and sorted variables
    val sortNetworkInit: Seq[IFormula] = {
      (0 to 3).map(i => (layers(0)(i) === X(i)) & (layers(maxLayers)(i) === Y(i)))
    }

    //Define compare and swap function
    def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
      val first = math.min(pos1, pos2)
      val second = math.max(pos1, pos2)
      ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
    }

    //Propagate equality over layers
    def propLayer(ind: Seq[Int], layer: Int) =
      (for(x <- ind) yield layers(layer + 1)(x) === layers(layer)(x)).fold(IBoolLit(true))(_ & _)

    //sorting network (Batcher's merge-exchange) constraints (can be added algorithmically depending on N, see Knuth 5.2.2)
    val sortConstraints: Seq[IFormula] = Seq(
      //first layer
      compSwap(0,2,0),
      compSwap(1,3,0),
      propLayer(Seq.empty,0),
      //second layer
      compSwap(0,1,1),
      compSwap(2,3,1),
      propLayer(Seq.empty,1),
      //third layer
      compSwap(1,2,2),
      propLayer(Seq(0,3),2)
    )

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        X(0) + 1 === X(1),
        X(2) === X(0),
        X(3) === X(1),
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === 5,
        (v1 - v0) < 4
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortNetworkInit, sortConstraints, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

  test("Two sums, naive sorting, no read, linear f, UNSAT") {
    val testname = "Two sums, naive sorting, no read, linear f, UNSAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      (res === 5 * in)
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    // Naive sorting encoding for 4 elements
    val sortingConstraint: Seq[IFormula] = {

      // Y must be sorted
      val sorted =
        (Y(0) <= Y(1)) &
        (Y(1) <= Y(2)) &
        (Y(2) <= Y(3))

      // Y must be a permutation of X
      val permutations: IFormula =
        (0 to 3).permutations.map { p =>
          (0 to 3)
            .map(i => Y(i) === X(p(i)))
            .fold(IBoolLit(true))(_ & _)
        }.fold(IBoolLit(false))(_ | _)
      Seq(sorted, permutations)
    }

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        X(0) + 1 === X(1),
        X(2) === X(0),
        X(3) === X(1),
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === 5,
        (v1 - v0) < 4
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortingConstraint, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

  test("Two sums, sorting network, no read, case distinction f, SAT") {
    val testname = "Two sums, sorting network, no read, case distinction f, SAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      ((2 === in & res === 2 * in) | (2 =/= in & res === 5 * in))
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    //SORTING NETWORK
    //t*(t+1)/2 layers to sort for t minimal with 2^t >= N, here 3 plus start
    val maxLayers = 3  
    val layers = (0 to maxLayers).map(i => (0 to 3).map(j => api.createConstant(s"x$i$j")))

    //Connect Layers to unsorted and sorted variables
    val sortNetworkInit: Seq[IFormula] = {
      (0 to 3).map(i => (layers(0)(i) === X(i)) & (layers(maxLayers)(i) === Y(i)))
    }

    //Define compare and swap function
    def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
      val first = math.min(pos1, pos2)
      val second = math.max(pos1, pos2)
      ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
    }

    //Propagate equality over layers
    def propLayer(ind: Seq[Int], layer: Int) =
      (for(x <- ind) yield layers(layer + 1)(x) === layers(layer)(x)).fold(IBoolLit(true))(_ & _)

    //sorting network (Batcher's merge-exchange) constraints (can be added algorithmically depending on N, see Knuth 5.2.2)
    val sortConstraints: Seq[IFormula] = Seq(
      //first layer
      compSwap(0,2,0),
      compSwap(1,3,0),
      propLayer(Seq.empty,0),
      //second layer
      compSwap(0,1,1),
      compSwap(2,3,1),
      propLayer(Seq.empty,1),
      //third layer
      compSwap(1,2,2),
      propLayer(Seq(0,3),2)
    )

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        X(0) < X(2),
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === 5,
        v1 <= v0 + 13,
        v1 >= v0 + 11
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortNetworkInit, sortConstraints, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

  test("Two sums, naive sorting, no read, case distinction f, SAT") {
    val testname = "Two sums, naive sorting, no read, case distinction f, SAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      ((2 === in & res === 2 * in) | (2 =/= in & res === 5 * in))
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    // Naive sorting encoding for 4 elements
    val sortingConstraint: Seq[IFormula] = {
      // Y must be sorted
      val sorted =
        (Y(0) <= Y(1)) &
        (Y(1) <= Y(2)) &
        (Y(2) <= Y(3))
      // Y must be a permutation of X
      val permutations: IFormula =
        (0 to 3).permutations.map { p =>
          (0 to 3)
            .map(i => Y(i) === X(p(i)))
            .fold(IBoolLit(true))(_ & _)
        }.fold(IBoolLit(false))(_ | _)
      Seq(sorted, permutations)
    }

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        X(0) <= X(2),
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v1 <= v0 + 13,
        v1 >= v0 + 11
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortingConstraint, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

  test("Two sums, sorting network, no read, case distinction f, UNSAT") {
    val testname = "Two sums, sorting network, no read, case distinction f, UNSAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      ((2 === in & res === 2 * in) | (2 =/= in & res === 5 * in))
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    //SORTING NETWORK
    //t*(t+1)/2 layers to sort for t minimal with 2^t >= N, here 3 plus start
    val maxLayers = 3  
    val layers = (0 to maxLayers).map(i => (0 to 3).map(j => api.createConstant(s"x$i$j")))

    //Connect Layers to unsorted and sorted variables
    val sortNetworkInit: Seq[IFormula] = {
      (0 to 3).map(i => (layers(0)(i) === X(i)) & (layers(maxLayers)(i) === Y(i)))
    }

    //Define compare and swap function
    def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
      val first = math.min(pos1, pos2)
      val second = math.max(pos1, pos2)
      ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
    }

    //Propagate equality over layers
    def propLayer(ind: Seq[Int], layer: Int) =
      (for(x <- ind) yield layers(layer + 1)(x) === layers(layer)(x)).fold(IBoolLit(true))(_ & _)

    //sorting network (Batcher's merge-exchange) constraints (can be added algorithmically depending on N, see Knuth 5.2.2)
    val sortConstraints: Seq[IFormula] = Seq(
      //first layer
      compSwap(0,2,0),
      compSwap(1,3,0),
      propLayer(Seq.empty,0),
      //second layer
      compSwap(0,1,1),
      compSwap(2,3,1),
      propLayer(Seq.empty,1),
      //third layer
      compSwap(1,2,2),
      propLayer(Seq(0,3),2)
    )

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        X(0) < X(2),
        X(3) < X(1),
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === 5,
        v1 =/= 0,
        v1 - v0 === 0
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortNetworkInit, sortConstraints, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

  test("Two sums, naive sorting, no read, case distinction f, UNSAT") {
    val testname = "Two sums, naive sorting, no read, case distinction f, UNSAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      ((2 === in & res === 2 * in) | (2 =/= in & res === 5 * in))
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    // Naive sorting encoding for 4 elements
    val sortingConstraint: Seq[IFormula] = {
      // Y must be sorted
      val sorted =
        (Y(0) <= Y(1)) &
        (Y(1) <= Y(2)) &
        (Y(2) <= Y(3))
      // Y must be a permutation of X
      val permutations: IFormula =
        (0 to 3).permutations.map { p =>
          (0 to 3)
            .map(i => Y(i) === X(p(i)))
            .fold(IBoolLit(true))(_ & _)
        }.fold(IBoolLit(false))(_ | _)
      Seq(sorted, permutations)
    }

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        X(0) <= X(2),
        X(3) < X(1),
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === 5,
        v1 =/= 0,
        v1 - v0 === 0
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortingConstraint, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

  test("Two sums, sorting network, single read, case distinction f, SAT") {
    val testname = "Two sums, sorting network, single read, case distinction f, SAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]
    //a0[i], a1[i], i
    val a0i = api.createConstant("a0i").asInstanceOf[IConstant]
    val a1i = api.createConstant("a1i").asInstanceOf[IConstant]
    val indi = api.createConstant("indi").asInstanceOf[IConstant]
    


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      ((2 === in & res === 2 * in) | (2 =/= in & res === 5 * in))
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    //SORTING NETWORK
    //t*(t+1)/2 layers to sort for t minimal with 2^t >= N, here 3 plus start
    val maxLayers = 3  
    val layers = (0 to maxLayers).map(i => (0 to 3).map(j => api.createConstant(s"x$i$j")))

    //Connect Layers to unsorted and sorted variables
    val sortNetworkInit: Seq[IFormula] = {
      (0 to 3).map(i => (layers(0)(i) === X(i)) & (layers(maxLayers)(i) === Y(i)))
    }

    //Define compare and swap function
    def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
      val first = math.min(pos1, pos2)
      val second = math.max(pos1, pos2)
      ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
    }

    //Propagate equality over layers
    def propLayer(ind: Seq[Int], layer: Int) =
      (for(x <- ind) yield layers(layer + 1)(x) === layers(layer)(x)).fold(IBoolLit(true))(_ & _)

    //sorting network (Batcher's merge-exchange) constraints (can be added algorithmically depending on N, see Knuth 5.2.2)
    val sortConstraints: Seq[IFormula] = Seq(
      //first layer
      compSwap(0,2,0),
      compSwap(1,3,0),
      propLayer(Seq.empty,0),
      //second layer
      compSwap(0,1,1),
      compSwap(2,3,1),
      propLayer(Seq.empty,1),
      //third layer
      compSwap(1,2,2),
      propLayer(Seq(0,3),2)
    )

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        IFormulaITE(X(0) <= indi & indi < X(1),
          X(1) - X(0) === summands0 - 1 & v0 === sum0 + a0i,
          X(1) - X(0) === summands0 & v0 === sum0),
        IFormulaITE(X(2) <= indi & indi < X(3),
          X(3) - X(2) === summands1 - 1 & v0 === sum1 + a1i,
          X(3) - X(2) === summands1 & v0 === sum1),
        f(a0i,a1i),
        X(1) < X(2),
        v0 =/= 0,
        v1 =/= 0,
        X(0) <= indi,
        X(3) > indi
        //LIA other constraints
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortNetworkInit, sortConstraints, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"a0[${api.eval(indi)}]=${api.eval(a0i)}")
        println(s"a1[${api.eval(indi)}]=${api.eval(a1i)}")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }

  test("Two sums, naive sorting, single read, case distinction f, SAT") {
    val testname = "Two sums, naive sorting, single read, case distinction f, SAT"
    val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]
    //a0[i], a1[i], i
    val a0i = api.createConstant("a0i").asInstanceOf[IConstant]
    val a1i = api.createConstant("a1i").asInstanceOf[IConstant]
    val indi = api.createConstant("indi").asInstanceOf[IConstant]

    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      ((2 === in & res === 2 * in) | (2 =/= in & res === 5 * in))
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    // Naive sorting encoding for 4 elements
    val sortingConstraint: Seq[IFormula] = {
      // Y must be sorted
      val sorted =
        (Y(0) <= Y(1)) &
        (Y(1) <= Y(2)) &
        (Y(2) <= Y(3))
      // Y must be a permutation of X
      val permutations: IFormula =
        (0 to 3).permutations.map { p =>
          (0 to 3)
            .map(i => Y(i) === X(p(i)))
            .fold(IBoolLit(true))(_ & _)
        }.fold(IBoolLit(false))(_ | _)
      Seq(sorted, permutations)
    }

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        IFormulaITE(X(0) <= indi & indi < X(1),
          X(1) - X(0) === summands0 - 1 & v0 === sum0 + a0i,
          X(1) - X(0) === summands0 & v0 === sum0),
        IFormulaITE(X(2) <= indi & indi < X(3),
          X(3) - X(2) === summands1 - 1 & v0 === sum1 + a1i,
          X(3) - X(2) === summands1 & v0 === sum1),
        f(a0i,a1i),
        X(1) < X(2),
        v0 =/= 0,
        v1 =/= 0,
        X(0) <= indi,
        X(3) > indi
        //LIA other constraints
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortingConstraint, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    println(testname)
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(0)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(s"sum(a0,${api.eval(X(0))}, ${api.eval(X(1))}, ${api.eval(v0)})")
        println(s"sum(a1,${api.eval(X(2))}, ${api.eval(X(3))}, ${api.eval(v1)})")
        println(s"a0[${api.eval(indi)}]=${api.eval(a0i)}")
        println(s"a1[${api.eval(indi)}]=${api.eval(a1i)}")
        println(s"LIA Star parts: (${api.eval(Z0(0))},${api.eval(Z1(0))},${api.eval(D(0))}), (${api.eval(Z0(1))},${api.eval(Z1(1))},${api.eval(D(1))}), (${api.eval(Z0(2))},${api.eval(Z1(2))},${api.eval(D(2))})")
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
  }
}
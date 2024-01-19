package fun.scop.app.isr

import fun.scop.csp._
import fun.scop.sat._
import fun.scop.encode._
import Logger._
import java.lang.management.ManagementFactory

// import fun.scop.dsl._

case class IsrSolverTj05(p: IsrInstance, satsolver: SatSolver)
    extends IsrSolver(p, satsolver) {

  // val solver = CspSolver(CSP(), OrderEncode, satsolver, 0)
  val threadMXBean = ManagementFactory.getThreadMXBean
  val initCpuTime = threadMXBean.getCurrentThreadCpuTime
  val initRealTime = System.currentTimeMillis

  private[this] def currentTime = {
    val cpu = threadMXBean.getCurrentThreadCpuTime - initCpuTime
    val real = System.currentTimeMillis - initRealTime
    val realSEC = java.util.concurrent.TimeUnit.MILLISECONDS.toSeconds(real)
    val cpuSEC = java.util.concurrent.TimeUnit.NANOSECONDS.toSeconds(cpu)
    (realSEC, cpuSEC)
  }

  val V = p.graph.nodes.toSeq.sorted;
  val E = p.graph.arcs;
  val init = p.init;
  val goal0 = p.goal;
  val goal = goal0.filter(v => p.graph.nodes.contains(v))
  if (goal0.size != goal.size) {
    val diff = goal0.diff(goal)
    println(
      s"WARNING. There is missing goal nodes: ${diff.mkString("{", ", ", "}")}"
    )
  }

  var dimacsCounter = 1
  var numOfClauses = 0

  var encodedStep = 0

  var node: Map[(Int, Int), Int] = Map.empty
  var move01: Map[(Int, Int, Int), Int] = Map.empty
  var move10: Map[(Int, Int, Int), Int] = Map.empty
  var blockLit: Map[Int, Int] = Map.empty

  private[this] def log(str: String) = {

    val (real, cpu) = currentTime
    println(s"c ($cpu) $str")
  }

  private[this] def answer(str: String) = {
    println(s"a $str")
  }

  private[this] def issueAuxVar() = {
    val out = dimacsCounter
    dimacsCounter += 1
    out
  }
  private[this] def c(lits: Seq[Int]) = {
    // println(lits.mkString(" "))
    satsolver.addClause(lits.map(_.toLong))
    numOfClauses += 1
  }

  private[this] def addNodeVarAtK(k: Int) = {
    for (v <- V) {
      // println(s"node($v,$k)")
      node += (v, k) -> issueAuxVar()
    }

  }
  private[this] def addMoveVar01From_i_To_j(i: Int, j: Int) = {
    for (v <- V)
      move01 += (v, i, j) -> issueAuxVar()
  }
  private[this] def addMoveVar10From_i_To_j(i: Int, j: Int) = {
    for (v <- V)
      move10 += (v, i, j) -> issueAuxVar()
  }
  private[this] def defSpotVar(start: Int, end: Int) = {
    // println(s"per k variable: $start to $end")
    for (i <- start to end)
      addNodeVarAtK(i)
  }
  private[this] def defStepVar(start: Int, end: Int) = {
    // println(s"per k-1,k variable: $start to $end")
    for (i <- start to end) {
      addMoveVar01From_i_To_j(i - 1, i)
      addMoveVar10From_i_To_j(i - 1, i)
    }
  }

  private[this] def defSpotConstraint(start: Int, end: Int) = {
    for (i <- start to end) {
      for ((u, v) <- E)
        c(Seq(-node(u, i), -node(v, i)))
    }
  }

  private[this] def defAtMostOneLe4(lits: Seq[Int]): Unit = {
    for (i <- 0 until lits.size; j <- i + 1 until lits.size) {
      c(Seq(-lits(i), -lits(j)))
    }
  }

  private[this] def defAtMostOne(lits: Seq[Int]): Unit = {
    if (lits.size <= 4)
      defAtMostOneLe4(lits)
    else {
      val first3 = lits.take(3)
      val remains = lits.drop(3)
      val y = issueAuxVar()

      defAtMostOne(y +: first3)
      defAtMostOne(y +: remains)
    }
  }

  private[this] def sinz(lits: Seq[Int]) = {
    val n = lits.size
    def x(index: Int) = lits(index - 1)
    if (lits.size <= 2) {
      defAtMostOne(lits: Seq[Int])
    } else {
      val s = (1 to n - 1).map(i => i -> issueAuxVar()).toMap
      // -x1 v s1
      c(Seq(-x(1), s(1)))
      // -xn v s_n-1
      c(Seq(-x(n), -s(n - 1)))
      //
      for (i <- 2 until n) {
        c(Seq(-x(i), s(i)))
        c(Seq(-s(i - 1), s(i)))
        c(Seq(-x(i), -s(i - 1)))
      }
    }
  }

  private[this] def sinzK(
      lits: Seq[Int],
      k: Int,
      blockLits: Seq[Int] = Seq.empty
  ) = {
    val n = lits.size
    def x(index: Int) = lits(index - 1)

    // val s = (1 to n - 1).map(i => i -> issueAuxVar()).toMap

    val s =
      (for {
        i <- 1 to n - 1
        j <- 1 to k
        aux = issueAuxVar()
      } yield (i, j) -> aux).toMap

    // -x1 v s1,1
    c(Seq(-x(1), s(1, 1)) ++ blockLits)

    // -s1,j
    for (j <- 2 to k)
      c(Seq(-s(1, j)) ++ blockLits)

    for (i <- 2 to n - 1) {
      // -xi v si,1
      c(Seq(-x(i), s(i, 1)) ++ blockLits)
      // -si-1,1 v si,1
      c(Seq(-s(i - 1, 1), s(i, 1)) ++ blockLits)

      for (j <- 2 to k) {
        // -xi v -si-1,j-1 v si,j
        c(Seq(-x(i), -s(i - 1, j - 1), s(i, j)) ++ blockLits)
        // -si-1,j v si,j
        c(Seq(-s(i - 1, j), s(i, j)) ++ blockLits)
      }

      // -xi v -si-1,k
      c(Seq(-x(i), -s(i - 1, k)) ++ blockLits)

    }

    //
    // -xn v s_n-1,k
    c(Seq(-x(n), -s(n - 1, k)) ++ blockLits)

  }

  private[this] def getDiffInGoalTokens(i: Int, j: Int) = {

    // c(Seq(-node(v,i),node(v,j),aux)) は不要

    for {
      v <- goal
      aux = issueAuxVar()
      // unit = c(Seq(node(v, i), -node(v, j), aux)) // j にトークンがあって，i になければ aux
      unit = c(Seq(node(v, i), aux)) // j にトークンがあって，i になければ aux
    } yield aux
  }

  private[this] def hint(k: Int) = {
    val nof_tokens = goal.size

    val min = scala.math.max(0, k - nof_tokens - 1)
    val max = k - 1

    for (i <- min to max) {
      // 違いを表す p を集める

      val ps: Seq[Int] = goal.map(v => -node(v, i)) // getDiffInGoalTokens(i, k)

      // p <= k-i
      sinzK(ps, k - i, Seq(-blockLit(k)))
    }

  }

  private[this] def exactOne(lits: Seq[Int]) = {
    c(lits)
    sinz(lits)
  }

  private[this] def defStepConstraint(start: Int, end: Int) = {
    for (i <- start to end) {
      // println(s"${i - 1} to $i")
      for (u <- V) {
        c(Seq(-node(u, i - 1), node(u, i), move10(u, i - 1, i)))
        c(Seq(node(u, i - 1), -move10(u, i - 1, i)))
        c(Seq(-node(u, i), -move10(u, i - 1, i)))

        c(Seq(node(u, i - 1), -node(u, i), move01(u, i - 1, i)))
        c(Seq(-node(u, i - 1), -move01(u, i - 1, i)))
        c(Seq(node(u, i), -move01(u, i - 1, i)))
      }
      exactOne(V.map(v => move10(v, i - 1, i)))
      exactOne(V.map(v => move01(v, i - 1, i)))

    }
  }

  private[this] def twoStatesAreDifferent(i: Int, j: Int) = {
    // val c = Or(V.map { v => node(v, i) !== node(v, j) })
    // solver.addCtr(c)
  }

  private[this] def anyTwoStatesAreDifferent(k: Int) = {
    for (i <- 0 until k)
      twoStatesAreDifferent(i, k)
  }

  private[this] def baseCSP(k: Int) = {

    if (k == 0) {
      defSpotVar(encodedStep, 0)
      defSpotConstraint(encodedStep, 0)
      encodedStep = 0
    } else {
      val start = encodedStep + 1
      defSpotVar(start, k)
      defStepVar(start, k)
      defSpotConstraint(start, k)
      defStepConstraint(start, k)
      // anyTwoStatesAreDifferent(k) // 1つずつインクリメントすることを仮定している
      encodedStep = k
    }

  }

  private[this] def initCSP() = {
    for (v <- V)
      if (init.contains(v))
        c(Seq(node(v, 0)))
      else
        c(Seq(-node(v, 0)))
  }

  private[this] def goalCSP(k: Int) = {
    blockLit += k -> issueAuxVar()

    for (v <- V)
      if (goal.contains(v))
        c(Seq(-blockLit(k), node(v, k)))
      else
        c(Seq(-blockLit(k), -node(v, k)))
  }

  def printSolution(k: Int) = {
    for (i <- 0 to k) {
      /*
      if (i > 0) {
        log(
          s"${V.filter(v0 => satsolver.model(move10(v0, i - 1, i)) > 0).sorted.mkString(" ")} -> ${V
            .filter(v0 => satsolver.model(move01(v0, i - 1, i)) > 0)
            .sorted
            .mkString(" ")}"
        )
      }*/
      answer(
        V.filter(v0 => satsolver.model(node(v0, i)) > 0).sorted.mkString(" ")
      )
    }

  }

  def solve(): Option[Boolean] = {
    baseCSP(0)
    initCSP()

    for (k <- 1 to Int.MaxValue) {

      baseCSP(k)
      goalCSP(k)
      hint(k)

      val assumptions =
        (1 to k).map(i => if (i < k) -blockLit(i) else blockLit(i)).toSeq
      val resBugHunting = satsolver.solve(assumptions)
      if (resBugHunting.get) {
        log(s"step $k SAT ${dimacsCounter} ${numOfClauses}")
        answer(s"YES")
        printSolution(k)

        solutionSeq = Some(
          for (i <- 0 to k)
            yield V.filter(v => satsolver.model(node(v, i)) > 0)
        )

        return Some(true)
      } else {
        log(s"step $k UNSAT ${dimacsCounter} ${numOfClauses}")
        c(Seq(-blockLit(k)))
        /*
        val resMoreMoveExists = solver.solve
        if (!resMoreMoveExists) {
          answer(s"UNSAT")
          return Some(false)
        }
         */
      }
    }
    return None
  }

}

object IsrSolverTj05 {
  def main(args: Array[String]) = {

    val instance = IsrInstance.fromFile(args(0), args(1))

    println(s"#Nodes: ${instance.graph.nodes.size}")
    println(s"#Edges: ${instance.graph.arcs.size}")

    val satsolver = new PureIpasirSatSolver(args(2), args(3))

    val isrs = IsrSolverTj05(instance, satsolver)

    isrs.solve()

    val s = isrs.solutionSeq match {
      case Some(seq) => {
        seq.map { line =>
          line.toSet
        }.toArray
      }
      case _ => Array.empty
    }

    // println(s.mkString(" "))

  }
}

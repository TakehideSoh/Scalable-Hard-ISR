package fun.scop.app.isr

import fun.scop.csp._
import fun.scop.sat._
import fun.scop.encode._
import Logger._

// import fun.scop.dsl._

case class IsrSolverTj02(p: IsrInstance, satsolver: SatSolver)
    extends IsrSolver(p, satsolver) {

  val solver = CspSolver(CSP(), OrderEncode, satsolver, 0)

  val V = p.graph.nodes.toSeq.sorted;
  val E = p.graph.arcs;
  val init = p.init;
  val goal = p.goal;

  var encodedStep = 0

  var node: Map[(Int, Int), Var] = Map.empty
  var move01: Map[(Int, Int, Int), Var] = Map.empty
  var move10: Map[(Int, Int, Int), Var] = Map.empty
  var blockLit: Map[Int, Var] = Map.empty

  private[this] def log(str: String) = {
    println(s"c $str")
  }

  private[this] def answer(str: String) = {
    println(s"a $str")
  }

  private[this] def addNodeVarAtK(k: Int) = {
    for (v <- V) {
      val x: Var = Var("node")(v, k)
      x.setDom(IntDomain(0, 1))
      solver.csp.addVar(x)
      node += (v, k) -> x
    }
  }
  private[this] def addMoveVar01From_i_To_j(i: Int, j: Int) = {
    for (v <- V) {
      val x: Var = Var("move01")(v, i, j)
      x.setDom(IntDomain(0, 1))
      solver.csp.addVar(x)
      move01 += (v, i, j) -> x
    }
  }
  private[this] def addMoveVar10From_i_To_j(i: Int, j: Int) = {
    for (v <- V) {
      val x: Var = Var("move10")(v, i, j)
      x.setDom(IntDomain(0, 1))
      solver.csp.addVar(x)
      move10 += (v, i, j) -> x
    }
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
        solver.addCtr(Or(node(u, i) < 1, node(v, i) < 1))
    }
  }
  private[this] def defStepConstraint(start: Int, end: Int) = {
    for (i <- start to end) {
      // println(s"${i - 1} to $i")
      for (u <- V) {
        solver.addCtr(
          (Gt(node(u, i - 1), node(u, i))) <==> (move10(u, i - 1, i) >= 1)
        )
        solver.addCtr(
          (Lt(node(u, i - 1), node(u, i))) <==> (move01(u, i - 1, i) >= 1)
        )
      }
      solver.addCtr(Add(V.map(v => move10(v, i - 1, i))) === 1)
      solver.addCtr(Add(V.map(v => move01(v, i - 1, i))) === 1)
    }
  }

  private[this] def twoStatesAreDifferent(i: Int, j: Int) = {
    val c = Or(V.map { v => node(v, i) !== node(v, j) })
    solver.addCtr(c)
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
      anyTwoStatesAreDifferent(k) // 1つずつインクリメントすることを仮定している
      encodedStep = k
    }

  }

  private[this] def initCSP() = {
    for (v <- V)
      if (init.contains(v))
        solver.addCtr(node(v, 0) === 1)
      else
        solver.addCtr(node(v, 0) === 0)
  }

  private[this] def goalCSP(k: Int) = {
    val x = Var("blockLit")(k)
    x.setDom(IntDomain(0, 1))
    solver.addVar(x)
    blockLit += k -> x

    for (v <- V)
      if (goal.contains(v))
        solver.addCtr((x > 0) ==> (node(v, k) === 1))
      else
        solver.addCtr((x > 0) ==> (node(v, k) === 0))
  }

  private[this] def getDimacsIndexForActivation(k: Int) = {
    solver.encoder.getDimacsIndex(blockLit(k) >= 1).get
  }

  def solutionToString(k: Int, a: Assignment) = {
    for (i <- 0 to k) {
      if (i > 0) {
        log(
          s"${V.filter(v0 => a(move10(v0, i - 1, i)) > 0).sorted.mkString(" ")} -> ${V
            .filter(v0 => a(move01(v0, i - 1, i)) > 0)
            .sorted
            .mkString(" ")}"
        )
      }
      answer(V.filter(v0 => a(node(v0, i)) > 0).sorted.mkString(" "))
    }

  }

  def solve(): Option[Boolean] = {
    baseCSP(0)
    initCSP()

    for (k <- 1 to Int.MaxValue) {
      log(s"step $k")
      baseCSP(k)
      goalCSP(k)
      solver.encode
      val resBugHunting = solver.solve(Seq(getDimacsIndexForActivation(k)))
      if (resBugHunting) {
        answer(s"SAT")
        solutionToString(k, solver.solution.get)
        solutionSeq = Some(
          for (i <- 0 to k)
            yield V.filter(v => solver.solution.get(node(v, i)) > 0)
        )
        return Some(true)
      } else {
        solver.addCtr(blockLit(k) < 1)
        val resMoreMoveExists = solver.solve
        if (!resMoreMoveExists) {
          answer(s"UNSAT")
          return Some(false)
        }
      }
    }
    return None
  }

}

object IsrSolverTj02 {
  def main(args: Array[String]) = {

    val instance = IsrInstance.fromFile(args(0), args(1))

    val isrs = IsrSolverTj02(instance, Sat4j())

    isrs.solve()
    val s = isrs.solutionSeq match {
      case Some(seq) => {
        seq.map { line =>
          line.toSet
        }.toArray
      }
      case _ => Array.empty
    }

    println(s.mkString(" "))

  }
}

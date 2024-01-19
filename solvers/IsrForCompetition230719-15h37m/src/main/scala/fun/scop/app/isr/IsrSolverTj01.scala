package fun.scop.app.isr

import fun.scop.csp._
import fun.scop.sat._
import fun.scop.encode._
import Logger._

case class IsrSolverTj01(p: IsrInstance, satsolver: SatSolver)
    extends IsrSolver(p, satsolver) {

  val V = p.graph.nodes.toSeq.sorted;
  val E = p.graph.arcs;
  val init = p.init;
  val goal = p.goal;

  //    new JnaSatSolver(
  //    libraryName = "glueminisat225",
  //    libraryPath = "/Users/soh/app/iSATLibrary-1.0.4/src/glueminisat-2.2.5"
  //  )

  def createCSP(solver: CspSolver, k: Int) = {

    solver.csp.clear
    solver.encoder.init

    val steps = (0 to k).toSeq

    /*
     * 変数の定義
     */
    /** (1-1) 0-1変数の定義: 頂点 v, 状態 s にトークンがあると 1 */
    val N =
      (for {
        v <- V
        s <- steps
      } yield (v, s) -> solver.addVar(Var(s"Node$v@$s", IntDomain(0, 1)))).toMap

    val to0map = (for {
      s <- steps
      u <- V
    } yield (u, s) -> solver.addVar(
      Var(s"to0_${u}_${s}", IntDomain(0, 1))
    )).toMap

    val to1map = (for {
      s <- steps
      u <- V
    } yield (u, s) -> solver.addVar(
      Var(s"to1_${u}_${s}", IntDomain(0, 1))
    )).toMap

    /** ======================= (1) 解空間の定義
      * =======================
      */
    /** (1-2) 制約の定義: 隣接する頂点 u, v は同時にトークンを持たない */
    for ((u, v) <- E; s <- steps)
      solver.addCtr(!And(N(u, s) === 1, N(v, s) === 1))

    /** ======================= (2) 遷移の定義
      * =======================
      */
    /** (2-1) トークンが 　　(a) 1 から 0 に変化, 　　(b) 0 から 1 に変化 したときに 0-1 変数 to0, to1 を 1
      * にする制約．
      */
    for (u <- V; s <- steps.dropRight(1)) {
      solver.addCtr(
        (N(u, s) === 1 && N(u, s + 1) === 0) <==> (to0map(u, s) === 1)
      )
      solver.addCtr(
        (N(u, s) === 0 && N(u, s + 1) === 1) <==> (to1map(u, s) === 1)
      )
    }

    /** (2-2) トークンが 　　(a) 1 から 0 に変化, 　　(b) 0 から 1 に変化 するのは1遷移でそれぞれちょうど 1 にする制約
      */
    for (s <- steps.dropRight(1)) {
      solver.addCtr(Add(V.map(to0map(_, s))) === 1)
      solver.addCtr(Add(V.map(to1map(_, s))) === 1)
    }

    /** ======================= (3) init, goal の定義
      * =======================
      */
    /** (3-1) initの定義 */
    for (v <- V)
      if (init.contains(v))
        solver.addCtr(N(v, 0) === 1)
      else
        solver.addCtr(N(v, 0) === 0)

    /** (3-2) goalの定義 */
    for (v <- V)
      if (goal.contains(v))
        solver.addCtr(N(v, k) === 1)
      else
        solver.addCtr(N(v, k) === 0)
    N
  }

  private[this] def search(k: Int): Boolean = {
    try {
      val solver = CspSolver(CSP(), new HybridEncoder, satsolver, 2)
      val N = createCSP(solver, k)
      val result = solver.find

      val nofVars = solver.satsolver.nofVars
      val nofClauses = solver.satsolver.nofClss

      log(s"k:$k #SatVar:$nofVars #SatClause:$nofClauses")

      if (result) {
        val solution = solver.solution.get
        solutionSeq = Some(
          for (i <- 0 to k) yield V.filter(v => solution(N(v, i)) > 0)
        )
        true
      } else
        false
    } catch {
      case e: fun.scop.ScopEmptyClauseFound => {
        log(s"k:$k EmptyClauseFound")
        false
      }
    }
  }

  def solve(): Option[Boolean] = {

    var isUNSAT = true
    var k = 1

    while (isUNSAT) {
      isUNSAT = !search(k)

      if (!isUNSAT)
        log(s"k:$k SAT")
      else
        log(s"k:$k UNSAT")

      k += 1
    }

    if (solutionSeq.nonEmpty) {
      solutionSeq.get.foreach { s => println(s.mkString("a ", " ", "")) }
      log(s"length: ${k - 1}")
      println("s SATISFIABLE")
      return Some(true)
    }

    None

  }

}

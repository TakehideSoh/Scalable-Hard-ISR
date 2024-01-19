package fun.scop.app.isr

import fun.scop.csp._
import fun.scop.sat._
import fun.scop.encode._
import Logger._

abstract class IsrSolver(p: IsrInstance, satsolver: SatSolver) {
  def solve(): Option[Boolean]
  var solutionSeq: Option[Seq[Seq[Int]]] = None
}

object IsrSolver {

  var optionMap = Map.empty[String, String]

  def parseOptions(arguments: List[String]): List[String] = arguments match {
    case "-isrsolver" :: arg :: rest => {
      optionMap += "isrsolver" -> arg
      parseOptions(rest)
    }
    case "-satsolver" :: arg :: rest => {
      optionMap += "satsolver" -> arg
      parseOptions(rest)
    }
    case _ =>
      arguments
  }

  def test() = {
    main(
      Array(
        "-satsolver /Users/soh/app/cadical-sc2020-45029f8/build/cadical",
        "-isrsolver tj01",
        "/Users/soh/02_prog/reconf-solver/dataset/US_states/us48.col",
        "/Users/soh/02_prog/reconf-solver/dataset/US_states/us48_tj_step050_tokens02_bound070_seed1827.txt"
      )
    )
  }

  def main(args: Array[String]): Unit = {
    val input = parseOptions(args.toList)

    val graphFile = input(0)
    //val graphFile = "/Users/soh/02_prog/coreSolver/examples/toy.col"
    val instanceFile = input(1)
    // val instanceFile = "/Users/soh/02_prog/coreSolver/examples/toy_ex1.txt" // args(1)

    log(s"GraphFile:$graphFile")
    log(s"InstanceFile:$instanceFile")
    val instance = IsrInstance.fromFile(graphFile, instanceFile)

    val (nofNode, nofEdge, nofInit, iratio, nofGoal, gratio) =
      instance.getStats()
    log(
      s"#Node:$nofNode, #Edge:$nofEdge, #Init:$nofInit, InitRatio:$iratio, #Goal:$nofGoal, GoalRatio:$gratio"
    )

    // println(instance)

    val satsolver = optionMap.getOrElse("satsolver", "sat4j") match {
      case "sat4j" => Sat4j()
      case path    => ExtSatSolver(path)
    }
    log(s"SatSolver: $satsolver")
    val isrsolver = optionMap.getOrElse("isrsolver", "tj01") match {
      case "tj01" => IsrSolverTj01(instance, satsolver)
      case "tj02" => IsrSolverTj02(instance, satsolver)
      case "ts01" => IsrSolverTs01(instance, satsolver)
    }
    log(s"IsrSolver: ${optionMap.getOrElse("isrsolver", "tj01")}")

    isrsolver.solve()

  }

}

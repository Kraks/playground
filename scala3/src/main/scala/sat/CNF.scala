package sat

import java.io.File
import scala.io.Source
import scala.util.Random

object CNFExamples {
  /** (x1 ∨ x2 ∨ -x3 ∨ x6) ∧
    * (-x2 ∨ x4) ∧
    * (-x1 ∨ -x5) ∧
    * (-x1 ∨ x2 ∨ x3 ∨ -x4 ∨ x5) ∧
    * (-x3) ∧ (x2 ∨ x5) ∧
    * (-x5) ∧ (x1)
    */
  val example_1 = Formula(List(Clause(List(1, 2, -3, 6)),
                               Clause(List(-2, 4)),
                               Clause(List(-1, -5)),
                               Clause(List(-1, 2, 3, -4, 5)),
                               Clause(List(-3)), Clause(List(2, 5)),
                               Clause(List(-5)), Clause(List(1))))

  val example_2 = Formula(List(Clause(List(1)),
                               Clause(List(-1)),
                               Clause(List(1, 2))))

  val unsat_ex1 = Formula(List(
    Clause(List(1, 2)),
    Clause(List(1, -2)),
    Clause(List(-1, 3)),
    Clause(List(-1, -3))))
}

object DIMACSParser {
  def parseLines(lines: Iterator[String]): Formula = {
    val cs = for (line <- lines if
                  !(line.startsWith("c") || line.startsWith("p") ||
                      line.startsWith("0") || line.startsWith("%") || line.isEmpty)) yield {
      val ns = line.split(" ").filter(_.nonEmpty).map(_.toInt).toList
      assert(ns.last == 0)
      Clause(ns.dropRight(1))
    }
    Formula(cs.toList)
  }

  def parse(input: String): Formula = parseLines(input.split("\\r?\\n").iterator)

  def parseFromResource(filePath: String): Formula = parseLines(Source.fromResource(filePath).getLines)

  def parseFromPath(filePath: String): Formula = parseLines(Source.fromFile(filePath).getLines)
}

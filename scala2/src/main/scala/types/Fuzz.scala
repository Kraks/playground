package fuzz

import scala.util.Random

object Fuzz {
  type Grammar = Map[String, List[List[String]]]
  val exprGrammar: Grammar = Map(
    "<start>" -> List(List("<expr>")),
    "<expr>" -> List(
      List("<term>", "+", "<expr>"),
      List("<term>", "-", "<expr>"),
      List("<term>")),
    "<term>" -> List(
      List("<factor>", "*", "<term>"),
      List("<factor>", "/", "<term>"),
      List("<factor>")),
    "<factor>" -> List(
      List("+", "<factor>"),
      List("-", "<factor>"),
      List("(", "<expr>", ")"),
      List("<int>", ".", "<int>"),
      List("<int>")),
    "<int>" -> List(
      List("<digit>", "<int>"),
      List("<digit>")),
    "<digit>" -> List(
      List("0"), List("1"), List("2"), List("3"), List("4"),
      List("5"), List("6"), List("7"), List("8"), List("9"))
  )

  implicit class ListOps[T](xs: List[T]) {
    def rndSelect: T = xs(Random.nextInt(xs.size))
  }

  def genKey(g: Grammar, key: String): String = {
    if (g.contains(key)) genAlt(g, g(key).rndSelect)
    else {
      //println("not contain " + key)
      key
    }
  }

  def genAlt(g: Grammar, alt: List[String]): String = {
    alt.map(genKey(g, _)).mkString
  }

  def main(args: Array[String]): Unit = {
    println(genKey(exprGrammar, "<factor>"))
  }

}

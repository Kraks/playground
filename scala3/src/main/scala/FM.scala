package fmelimination

enum Factor:
  case Const(c: Int)
  case Var(x: String)
  case Mult(c: Int, x: String)

import Factor.*

case class Ineq(lhs: List[Factor]) {
  def +(rhs: Factor): Ineq = Ineq(lhs :+ rhs)
}

case class System(ineqs: List[Ineq])

extension (x: Int)
  def +(y: Factor): Ineq = Ineq(List(Const(x), y))
  def *(y: String): Factor = Mult(x, y)

extension (f: Factor)
  def +(g: Factor): Ineq = Ineq(List(f, g))

@main def test = {
  val c1: Ineq = 3 + 2 * "b" + 1 * "c" // >= 0

}
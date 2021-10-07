package squidexample

object IR extends squid.ir.SimpleAST
import IR.Predef._
import IR.Quasicodes._

object Example {
  def power(n: Int, x: Double): Double = {
    if (n == 0) 1.0
    else x * power(n-1, x)
  }

  def spower(n: Int, x: ClosedCode[Double]): ClosedCode[Double] = {
    if (n > 0) code"$x * ${spower(n-1, x)}"
    else code"1.0"
  }

  def spower1[C](n: Int, x: Code[Double, C]): Code[Double, C] = {
    if (n > 0) code"$x * ${spower1(n-1, x)}"
    else code"1.0"
  }

  def optimize[C](prg: Code[Double, C]): Code[Double, C] = {
    prg rewrite {
      case code"($e: Double) * 1.0" => e
    }
  }

 /*
  def f[C](n: Int): Code[Int => Int, C] = {
    val x: Int = n
    code{ (y: Int) => y + x }
  }
  */

  def main(args: Array[String]) {
    val power3 = spower(3, code"0.5")
    println(power3)
    println(optimize(power3))
    println(power3.compile)

    // spower(3, code"?x:Double") // compile-time error

    val another_power3 = spower1(3, code"?x:Double")
    println(another_power3)
    println(optimize(another_power3))
    //another_power3.compile // compile-time error

    val closed_power3 = code"""(x: Double) => $${ another_power3 }""" // x matches
    println(closed_power3)

    val closed_power3_1 = code{ (x: Double) => ${ spower1(3, code{x}) } }
    println(closed_power3_1)
  }
}

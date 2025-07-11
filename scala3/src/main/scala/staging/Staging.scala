package staging

import scala.quoted.*

given staging.Compiler = staging.Compiler.make(this.getClass.getClassLoader)

def unrolledPowerCode(x: Expr[Double], n: Int)(using Quotes): Expr[Double] =
  if n == 0 then '{ 1.0 }
  else if n == 1 then x
  else '{ $x * ${ unrolledPowerCode(x, n-1) } }

def singletonList[T: Type](x: Expr[T])(using Quotes): Expr[List[T]] =
  '{ List($x) }

def emptyList[T](using Type[T], Quotes): Expr[List[T]] =
  '{ Nil }

/*
trait ToExpr[T]:
  def apply(x: T)(using Quotes): Expr[T]
*/

given OptionToExpr[T: Type: ToExpr]: ToExpr[Option[T]] with
  def apply(opt: Option[T])(using Quotes): Expr[Option[T]] =
    opt match
      case Some(x) => '{ Some[T]( ${Expr(x)} ) }
      case None => '{ None }

def powerCode(x: Expr[Double], n: Expr[Int])(using Quotes): Expr[Double] =
  n match
    case Expr(m) => unrolledPowerCode(x, m)
    case _ => '{ Math.pow($x, $n.toDouble) }

inline def powerMacro(x: Double, inline n: Int): Double =
  ${ powerCode('x, 'n) }

//def power2(x: Double): Double = powerMacro(x, 2)

def specPower(n: Int): Double => Double = staging.run {
  val stagedPower: Expr[Double => Double] =
    '{ (x: Double) => ${unrolledPowerCode('x, n)} }
  println(stagedPower.show)
  stagedPower
}

def dup(using Quotes): Expr[Int] = {
  def plus(x: Expr[Int])(using Quotes): Expr[Int] = {
    '{ $x + $x }
  }
  def letPlus(x: Expr[Int])(using Quotes): Expr[Int] = {
    '{ println("world")
       val n = $x // let-insertion needs to properly maintain relative order
       n + n }
  }
  val n = '{ println("hello"); 3 }
  val y = letPlus(n) // plus( '{ println("hello"); 3} )
  println(y.show)
  y

  /*
  // after erasure
  def letPlus(x: Int): Int = {
    println("world")
    x + x
  }
  val n = { println("hello"); 3 }
  val y = letPlus(n) // plus( '{ println("hello"); 3} )
  */
}

case class Mut(var x: Int)

def dupStore(using Quotes): Expr[Int] = {
  def plus(v: Expr[Mut])(using Quotes): Expr[Int] = '{
    ${v}.x = 4
    ${v}.x
  }
  val n = '{ Mut(3) }
  val y = plus(n)
  println(y.show)
  y
}

/*
def stuck(using Quotes): Expr[Int => Int] = {
  val t = '{
    // definition at level 1, accessing x at level 0
    (x: Int) => ${ ((y: Int) => '{1})( ((_: Int)=>0)(x) ) }
  }
  t
}
*/

@main def main: Unit = {
  val pow3 = specPower(3)
  println(pow3(3))

  // code/effect duplication
  {
    val y = staging.run { dup }
    println(y)
  }

  {
    val y = staging.run { dupStore }
    println(y)
  }

  {
    val y = staging.run { dup }
    println(y)
  }

}

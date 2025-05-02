package thermo

/* Scala implementation using "thermometer continuations" from
 *   Capturing the future by replaying the past (functional pearl)
 *   https://dl.acm.org/doi/10.1145/3236771
 * Based on its Java artifact: https://github.com/jkoppel/thermometer-continuations
 * Written and translate to Scala by Guannan Wei
 */

trait Block[A] {
  def apply: A
}

trait Monad[M[_]] {
  def pure[A](x: A): M[A]
  def bind[A, B](m: M[A], f: A => M[B]): M[B]
}

object Monad {
  def apply[M[_]](implicit m: Monad[M]): Monad[M] = m
  implicit class MonadOps[M[_]: Monad, A](m: M[A]) {
    def bind[B](f: A => M[B]): M[B] = Monad[M].bind(m, f)
  }
}

trait Control[Ans] {
  def reset(block: Block[Ans]): Ans
  def reset(block: => Ans): Ans = reset(new Block[Ans] { def apply = block })
  def shift[A](f: (A => Ans) => Ans): A
}

case class ThermoCont[Ans]() extends Control[Ans] {
  abstract class Frame
  case class Return(x: Any) extends Frame
  case object Enter extends Frame

  case class ResetState(block: Block[Ans], past: List[Frame], future: List[Frame])

  case class Done(val ans: Any) extends RuntimeException

  var past: List[Frame] = List()
  var future: List[Frame] = List()
  var nest: List[ResetState] = List()

  var curExpr: Block[Ans] = null

  def runWithFuture(f: Block[Ans], fFuture: List[Frame]): Ans = {
    nest = ResetState(curExpr, past, future)::nest
    past = List()
    future = fFuture
    curExpr = f
    var result: Option[Ans] = None
    try {
      result = Some(f.apply)
    } catch {
      case Done(ans) => result = Some(ans.asInstanceOf[Ans])
    }
    val prev: ResetState = nest.head
    nest = nest.tail
    curExpr = prev.block
    past = prev.past
    future = prev.future
    return result.get
  }

  def reset(block: Block[Ans]): Ans = runWithFuture(block, List())
  def shift[A](f: (A => Ans) => Ans): A = {
    val fr: Option[Frame] = 
      if (future.isEmpty) None
      else { 
        val f = future.head
        future = future.tail
        Some(f)
      }
    fr match {
      case Some(Return(x)) =>
        past = Return(x)::past
        x.asInstanceOf[A]
      case None | Some(Enter) =>
        val newFuture: List[Frame] = past.reverse
        val ourExpr: Block[Ans] = curExpr
        val k: A => Ans = a => { runWithFuture(ourExpr, Return(a)::newFuture) }
        past = Enter::past
        val result: Ans = f(k)
        throw Done(result)
    }
  }
}

abstract class RMonad[M[_]: Monad] {
  def reflect[A](x: M[A]): A
  def reify[A](f: Block[A]): M[A]
  def reify[A](f: => A): M[A] = reify(new Block[A] { def apply = f })
}

case class Represent[M[_]: Monad]() extends RMonad[M] {
  import Monad._
  private val cont: Control[M[Any]] = ThermoCont()

  def reflect[A](x: M[A]): A = cont.shift(k => x.bind(k))
  def reify[A](f: Block[A]): M[A] = 
    cont.reset(Monad[M].pure(f.apply.asInstanceOf[Any])).bind((x: Any) => Monad[M].pure(x.asInstanceOf[A]))
}

object Nondet {
  implicit object ListM extends Monad[List] {
    def pure[A](x: A): List[A] = List(x)
    def bind[A, B](m: List[A], f: A => List[B]): List[B] = m.flatMap(f)
  }
  private val rm: RMonad[List] = Represent[List]
  def choose[A](xs: List[A]): A = rm.reflect(xs)
  def withNondet[A](f: => A): List[A] = rm.reify(f)
}

object Example {
  def main(args: Array[String]): Unit = {
    val c: Control[Int] = ThermoCont()
    import c.{reset, shift}
  
    println(1 + reset {
      val x = shift[Int] { k => k(k(5)) }
      x * 2
    })
    
    import Nondet._
    println(withNondet {
      val x = choose(List(3, 4)) 
      val y = choose(List(5, 6))
      x * y
    })
  }
}

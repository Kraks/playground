package duality.sort

object Sec1 {
  // foldRight also works here
  def insertSort(xs: List[Int]): List[Int] = xs.foldLeft(List[Int]())(insert)
  def insert(xs: List[Int], x: Int): List[Int] = {
    val (ys, zs) = xs.partition(_ <= x)
    ys ++ List(x) ++ zs
  }

  def unfoldRight[A, B](f: B => Option[(A, B)], b: B): List[A] = ???

  def delete[T](xs: List[T], x: T): List[T] = {
    val (before, atAndAfter) = xs.span(_ != x)
    before ++ atAndAfter.drop(1)
  }

  def select(xs: List[Int]): Option[(Int, List[Int])] =
    if (xs.isEmpty) None 
    else {
      val min = xs.min
      val ys = delete(xs, min)
      Some((min, ys))
    }

  def selectSort(xs: List[Int]): List[Int] = unfoldRight(select, xs)

  def main(args: Array[String]): Unit = {
    val xs = List(1, 3, 2, 10, 4, 3, 5)
    println(insertSort(xs))
  }
}

object Sec2 {
  abstract class List[+S]
  case object Nil extends List[Nothing]
  case class Cons[S](hd: Int, tl: S) extends List[S]

  case class Fix[F[_]](out: F[Fix[F]])
  
  val xs: Fix[List] = Fix[List](Nil)
  val ys: Fix[List] = Fix[List](Cons[Fix[List]](1, Fix[List](Nil)))
  val zs: Fix[List] = Fix[List](Cons(1, Fix[List](Cons(2, Fix[List](Cons(3, Fix[List](Nil)))))))
  val unsorted: Fix[List] = Fix[List](Cons(3, Fix[List](Cons(2, Fix[List](Cons(1, Fix[List](Nil)))))))

  trait Functor[F[_]] {
    def map[A, B](f: A => B)(fa: F[A]): F[B]
  }

  object Functor {
    def apply[F[_]](implicit F: Functor[F]) = F
  }

  implicit val ListFunctor = new Functor[List] {
    def map[A, B](f: A => B)(fa: List[A]): List[B] = fa match {
      case Nil => Nil
      case Cons(hd, tl) => Cons(hd, f(tl))
    }
  }

  implicit class FunctorOps[F[_]: Functor, A](xs: F[A]) {
    def map[B](f: A => B): F[B] = Functor[F].map(f)(xs)
  }

  def fold[F[_]: Functor, A](f: F[A] => A)(ff: Fix[F]): A =
    f(ff.out.map(fold[F, A](f)))

  def unfold[F[_]: Functor, A](f: A => F[A])(a: A): Fix[F] = 
    Fix(f(a).map(unfold[F, A](f)))
}

object Sec3 {
  import Sec2._

  def c: List[Fix[List]] => List[List[Fix[List]]] = ???
  def sort1: Fix[List] => Fix[List] = fold(unfold(c))

  def naiveInsert: List[Fix[List]] => List[List[Fix[List]]] = {
    case Nil => Nil
    case Cons(x, Fix(Nil)) => Cons(x, Nil)
    case Cons(x, Fix(Cons(y, rest))) =>
      if (x <= y) Cons(x, Cons(y, rest))
      else Cons(y, Cons(x, rest))
  }

  def naiveInsertSort: Fix[List] => Fix[List] = fold(unfold(naiveInsert))

  def a: List[List[Fix[List]]] => List[Fix[List]] = ???
  def sort2: Fix[List] => Fix[List] = unfold(fold(a))

  def bubble: List[List[Fix[List]]] => List[Fix[List]] = {
    case Nil => Nil
    case Cons(x, Nil) => Cons(x, Fix[List](Nil))
    case Cons(x, Cons(y, rest)) =>
      if (x <= y) Cons(x, Fix[List](Cons(y, rest)))
      else Cons(y, Fix[List](Cons(x, rest)))
  }

  def bubbleSort: Fix[List] => Fix[List] = unfold(fold(bubble))

  // a further generalization

  def swap[X]: List[List[X]] => List[List[X]] = {
    case Nil => Nil
    case Cons(a, Nil) => Cons(a, Nil)
    case Cons(a, Cons(b, rest)) =>
      if (a <= b) Cons(a, Cons(b, rest))
      else Cons(b, Cons(a, rest))
  }

  def naiveInsertSort2: Fix[List] => Fix[List] =
    //fold[List, Fix[List]](unfold[List, List[Fix[List]]]
    fold(unfold((a: List[Fix[List]]) => swap[Fix[List]](a.map(_.out))))

  def bubbleSort2: Fix[List] => Fix[List] =
    unfold(fold((a: List[List[Fix[List]]]) => swap[Fix[List]](a).map(Fix(_))))

  def main(args: Array[String]): Unit = {
    println(naiveInsertSort(unsorted))
    println(bubbleSort(unsorted))

    println(naiveInsertSort2(unsorted))
    println(bubbleSort2(unsorted))
  }
}

object Sec4 {
  import Sec2._
  import Sec3._

  implicit class Fun1Ops[A, B](f: A => B) {
    def △[C](g: A => C): A => (B, C) = a => (f(a), g(a))
    def ▽[C](g: C => B): Either[A, C] => B = {
      case Left(a) => f(a)
      case Right(c) => g(c)
    }
  }

  def f: Int => Int = x => x + 1
  def g: Int => String = x => x.toString
  def h: Int => (Int, String) = f △ g

  def id[A]: A => A = a => a

  // Paramorphism

  def para[F[_]: Functor, A](f: F[(Fix[F], A)] => A): Fix[F] => A = ff =>
    // id △ para(f): Fix[F] => (Fix[F], A)
    f(ff.out.map(id △ para(f)))

  import scala.collection.immutable.{List => SList}
  def suf: List[(Fix[List], SList[Fix[List]])] => SList[Fix[List]] = {
    case Nil => SList()
    case Cons(n, (l, ls)) => l::ls
  }
  def suffixes: Fix[List] => SList[Fix[List]] = para(suf)

  def para2[F[_]: Functor, A](f: F[(Fix[F], A)] => A): Fix[F] => A = ff => ???

  // Apomorphism
}

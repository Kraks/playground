package absinterp

// Lattices and Abstract Domains

trait Lattice[T]:
  def bot: T
  def top: T
  extension (x: T)
    def ⊑(y: T): Boolean
    def ⊔(y: T): T
    def ⊓(y: T): T

trait AbsDomain[T] extends Lattice[T]:
  extension (x: T)
    def ▽(y: T): T
    def △(y: T): T

given IntLattice: Lattice[Int] with
  def bot: Int = Int.MinValue
  def top: Int = Int.MaxValue
  extension (x: Int)
    def ⊑(y: Int): Boolean = x <= y
    def ⊔(y: Int): Int = math.max(x, y)
    def ⊓(y: Int): Int = math.min(x, y)

given DoubleLattice: Lattice[Double] with
  def bot: Double = Double.NegativeInfinity
  def top: Double = Double.PositiveInfinity
  extension (x: Double)
    def ⊑(y: Double): Boolean = x <= y
    def ⊔(y: Double): Double = math.max(x, y)
    def ⊓(y: Double): Double = math.min(x, y)

given ProductLattice[A: Lattice, B: Lattice]: Lattice[(A, B)] with
  val la: Lattice[A] = summon[Lattice[A]]
  val lb: Lattice[B] = summon[Lattice[B]]
  def bot: (A, B) = (la.bot, lb.bot)
  def top: (A, B) = (la.top, lb.top)
  extension (l1: (A, B))
    def ⊑(l2: (A, B)): Boolean = l1._1 ⊑ l2._1 && l1._2 ⊑ l2._2
    def ⊔(l2: (A, B)): (A, B) = (l1._1 ⊔ l2._1, l1._2 ⊔ l2._2)
    def ⊓(l2: (A, B)): (A, B) = (l1._1 ⊓ l2._1, l1._2 ⊓ l2._2)

given ProductAbsDomain[A: AbsDomain, B: AbsDomain]: AbsDomain[(A, B)] with
  val pl: ProductLattice[A, B] = summon[ProductLattice[A, B]]
  export pl.*
  extension (x: (A, B))
    def ▽(y: (A, B)): (A, B) = (x._1 ▽ y._1, x._2 ▽ y._2)
    def △(y: (A, B)): (A, B) = (x._1 △ y._1, x._2 △ y._2)

given MapLattice[K, V: Lattice]: Lattice[Map[K, V]] with
  val lv: Lattice[V] = summon[Lattice[V]]
  def bot: Map[K, V] = Map[K, V]()
  def top: Map[K, V] = throw new RuntimeException("No representation of top map")
  extension (m1: Map[K, V])
    def ⊑(m2: Map[K, V]): Boolean =
      m1.forall { case (k, v) => v ⊑ m2.getOrElse(k, lv.bot) }
    def ⊔(m2: Map[K, V]): Map[K, V] =
      m1.foldLeft(m2) { case (m, (k, v)) => m + (k -> v ⊔ m.getOrElse(k, lv.bot)) }
    def ⊓(m2: Map[K, V]): Map[K, V] =
      m1.keySet.intersect(m2.keySet).foldLeft(Map[K,V]()) { case (m, k) => m + (k -> m1(k) ⊓ m2(k)) }

given MapAbsDomain[K, V: AbsDomain]: AbsDomain[Map[K, V]] with
  val ml: MapLattice[K, V] = summon[MapLattice[K, V]]
  export ml.*
  extension (m1: Map[K, V])
    def ▽(m2: Map[K, V]): Map[K, V] =
      m1.foldLeft(m2) { case (m, (k, v)) => m + (k -> v ▽ m.getOrElse(k, lv.bot)) }
    def △(m2: Map[K, V]): Map[K, V] =
      m1.keySet.intersect(m2.keySet).foldLeft(Map[K,V]()) { case (m, k) => m + (k -> m1(k) △ m2(k)) }

// Interval

case class Interval private (lb: Double, ub: Double):
  def toConst: Option[Int] = if (lb == ub) Some(lb.toInt) else None

object Interval:
  def make(lb: Double, ub: Double): Interval =
    if (ub < lb) Interval(Double.PositiveInfinity, Double.NegativeInfinity)
    else Interval(lb, ub)
  def from(is: Int*): Interval = Interval(is.min.toDouble, is.max.toDouble)

given IntervalLattice: Lattice[Interval] with
  val dl = summon[Lattice[Double]]
  def bot = Interval.make(dl.top, dl.bot)
  def top = Interval.make(dl.bot, dl.top)
  extension (l1: Interval)
    def ⊑(l2: Interval) = l2.lb ⊑ l1.lb && l1.ub ⊑ l2.ub
    def ⊔(l2: Interval) = Interval.make(l1.lb ⊓ l2.lb, l1.ub ⊔ l2.ub)
    def ⊓(l2: Interval) = Interval.make(l1.lb ⊔ l2.lb, l1.ub ⊓ l2.ub)

given IntervalAbsDomain: AbsDomain[Interval] with
  export IntervalLattice.*
  extension (l1: Interval)
    def ▽(l2: Interval): Interval =
      if (l1 == bot) l2
      else if (l2 == bot) l1
      else Interval.make(if (l1.lb ⊑ l2.lb) l1.lb else Double.NegativeInfinity,
                         if (l2.ub ⊑ l1.ub) l1.ub else Double.PositiveInfinity)
    def △(l2: Interval): Interval =
      if (l1 == bot) bot
      else if (l2 == bot) bot
      else Interval.make(if (l1.lb == Double.NegativeInfinity) l2.lb else l1.lb,
                         if (l1.ub == Double.PositiveInfinity) l2.ub else l1.ub)

given IntervalArith: Arith[Interval] with
  val bot = summon[Lattice[Interval]].bot
  extension (x: Interval)
    def +(y: Interval): Interval =
      if (x == bot || y == bot) bot
      else Interval.make(x.lb + y.lb, x.ub + y.ub)
    def -(y: Interval): Interval =
      if (x == bot || y == bot) bot
      else Interval.make(x.lb - y.ub, x.ub - y.lb)
    def *(y: Interval): Interval =
      if (x == bot || y == bot) bot
      else {
        val Interval(lb1, ub1) = x
        val Interval(lb2, ub2) = y
        val arr = List[Double](lb1 * lb2, lb1 * ub2, ub1 * lb2, ub1 * ub2)
        Interval.make(arr.min, arr.max)
      }
    def /(y: Interval): Interval =
      if (x == bot || y == bot) bot
      else if (y.toConst == Some(0)) bot
      else {
        val rhs = y match
          case Interval(lb2, ub2) if !(lb2 <= 0 && 0 <= ub2) =>
            Interval.make(1/ub2, 1/lb2)
          case Interval(lb2, 0) =>
            Interval.make(Double.NegativeInfinity, 1/lb2)
          case Interval(0, ub2) =>
            Interval.make(1/ub2, Double.PositiveInfinity)
          case  _ => Interval.make(Double.NegativeInfinity, Double.PositiveInfinity)
        x * rhs
      }
    def <(y: Interval): Interval = 
      if (x == bot || y == bot) bot
      else {
        val Interval(lb1, ub1) = x
        val Interval(lb2, ub2) = y
        if (ub1 < lb2) Interval.from(1)
        else if (lb1 > ub2) Interval.from(0)
        else Interval.from(0, 1)
      }
    def ≡(y: Interval): Interval = (x.toConst, y.toConst) match
      case (Some(v1), Some(v2)) =>
        if (v1 == v2) Interval.from(1) else Interval.from(0)
      case (_, _) => Interval.from(0, 1)

trait NumAbsDomain[T] extends AbsDomain[T] with Arith[T]

given IntervalNumAbsDomain: NumAbsDomain[Interval] with
  export IntervalArith.{+, -, `*`, /, <, ≡}
  export IntervalAbsDomain.{bot, top, ⊑, ⊔, ⊓, ▽, △}

// Language

enum Expr:
  case Lit(i: Int)
  case Var(x: String)
  case BinOp(op: String, e1: Expr, e2: Expr) 

enum Stmt:
  case Skip
  case Assign(x: String, e: Expr)
  case Seq(s1: Stmt, s2: Stmt)
  case Cond(e: Expr, s1: Stmt, s2: Stmt)
  case While(e: Expr, s: Stmt)

import Expr._
import Stmt._

// Concrete Interpreter

case class NumV(i: Int)
type Value = NumV

given Conversion[Int, Value] with
  def apply(i: Int): Value = NumV(i)

trait Arith[A]:
  extension (a: A)
    def +(b: A): A
    def -(b: A): A
    def *(b: A): A
    def /(b: A): A
    def <(b: A): A
    def ≡(b: A): A

given NumVArith: Arith[NumV] with
  extension (x: NumV)
    def +(y: NumV): NumV = x.i + y.i
    def -(y: NumV): NumV = x.i - y.i
    def *(y: NumV): NumV = x.i * y.i
    def /(y: NumV): NumV = x.i / y.i
    def <(y: NumV): NumV = if (x.i < y.i) 1 else 0
    def ≡(y: NumV): NumV = if (x.i == y.i) 1 else 0

type Store = Map[String, Value]

def evalOp[T: Arith](op: String, v1: T, v2: T): T =
  op match
    case "+" => v1 + v2
    case "-" => v1 - v2
    case "*" => v1 * v2
    case "/" => v1 / v2
    case "<" => v1 < v2
    case ">" => v2 < v1
    case "=" => v1 ≡ v2
    case _ => throw new RuntimeException("Unsupported operation")

def genEvalOp[T: Arith](op: String, v1: T, v2: T): T = evalOp[T](op, v1, v2)

def eval(s: Expr, σ: Store): Value =
  s match
    case Var(x) => σ(x)
    case Lit(i) => NumV(i)
    case BinOp(op, e1, e2) => evalOp(op, eval(e1, σ), eval(e2, σ))

def fix[A, B](f: (A => B) => A => B)(x: A): B = f(fix(f))(x)

def exec(s: Stmt, σ: Store): Store =
  s match
    case Skip => σ
    case Assign(x, e) => σ + (x -> eval(e, σ))
    case Seq(s1, s2) =>
      exec(s2, exec(s1, σ))
    case Cond(e, s1, s2) =>
      val NumV(c) = eval(e, σ)
      if (c == 1) exec(s1, σ) else exec(s2, σ)
    case While(e, s) =>
      def loop(rec: Store => Store): Store => Store = { σ =>
        val NumV(c) = eval(e, σ)
        if (c == 1) rec(exec(s, σ)) else σ
      }
      fix(loop)(σ)
      /*
      def loop(σ: Store): Store = {
        val NumV(c) = eval(e, σ)
        if (c == 1) loop(exec(s, σ)) else σ
      }
      loop(σ)
      */
      /*
      if (c == 1) exec(While(e, s), exec(s, σ))
      else σ
      */

// Abstract Interpreter

type AbsVal = Interval
type AbsStore = Map[String, AbsVal]

def absEvalOp[T: Arith](op: String, i1: T, i2: T): T = evalOp[T](op, i1, i2)

def absEval(e: Expr, σ: AbsStore): AbsVal =
  e match
    case Var(x) => if (σ.contains(x)) σ(x) else summon[Lattice[AbsVal]].bot
    case Lit(i) => Interval.from(i)
    case BinOp(op, e1, e2) => absEvalOp(op, absEval(e1, σ), absEval(e2, σ))

def kleene0[T: AbsDomain](f: T => T)(t: T): T =
  val next = f(t)
  if (next ⊑ t) t else kleene0(f)(t ▽ next)

def kleene[T: AbsDomain](f: (T => T) => T => T)(t: T): T =
  var acc: T = summon[AbsDomain[T]].bot
  def iter(t: T): T = {
    if (t ⊑ acc) acc
    else {
      acc = acc ▽ t
      f(iter)(acc)
    }
  }
  iter(t)

val bot = summon[Lattice[AbsStore]].bot

def absExec(s: Stmt, σ: AbsStore): AbsStore =
  s match
    case Skip => σ
    case Assign(x, e) => σ ⊔ Map(x -> absEval(e, σ))
    case Seq(s1, s2) =>
      absExec(s2, absExec(s1, σ))
    case Cond(e, s1, s2) =>
      val c = absEval(e, σ)
      val thn = if (Interval.from(1) ⊑ c) absExec(s1, σ) else bot
      val els = if (!(c ⊑ Interval.from(1))) absExec(s2, σ) else bot
      thn ⊔ els
    case While(e, s) =>
      def loop(rec: AbsStore => AbsStore)(σ: AbsStore): AbsStore = {
        if (Interval.from(1) ⊑ absEval(e, σ)) rec(absExec(s, σ))
        else σ
      }
      kleene(loop)(σ)
      /*
      def loop(σ: AbsStore): AbsStore = {
        if (Interval.from(1) ⊑ absEval(e, σ)) absExec(s, σ)
        else σ
      }
      kleene0(loop)(σ)
       */

object Examples {
  // input: x, b
  val powerWhile =
    Seq(Assign("res", Lit(1)),
      While(BinOp("<", Lit(0), Var("x")),
        Seq(Assign("res", BinOp("*", Var("b"), Var("res"))),
          Assign("x", BinOp("-", Var("x"), Lit(1))))))

  // input: x
  /* 
   while (1) {
   x = x - 1
   if (x = 0) skip else skip
   }
   */
  val nonTerm1 =
    While(Lit(1),
      Seq(Assign("x", BinOp("-", Var("x"), Lit(1))),
        Cond(BinOp("=", Var("x"), Lit(0)),
          Skip,
          Skip)))

  val condProg =
    Cond(BinOp("=", Var("x"), Lit(1)),
      Assign("y", Lit(2)),
      Assign("y", Lit(10)))

  val condUndef =
    Cond(Var("x"),
      Assign("y", Lit(2)),
      Assign("y", Lit(10)))

  val bound =
    Seq(Assign("x", Lit(1)),
      While(BinOp("<", Var("x"), Lit(100)),
        Assign("x", BinOp("+", Var("x"), Lit(1)))))

  // input: x
  val nonTerm2 = While(Lit(1), Assign("x", BinOp("-", Var("x"), Lit(1))))

  val nonTerm3 = While(Lit(1), Assign("x", BinOp("+", Var("x"), Lit(1))))

  val undef = Assign("x", BinOp("+", Var("x"), Var("y")))
}

object Test {
  import Examples._
  def main(args: Array[String]): Unit = {
    println(summon[Lattice[Interval]].bot * Interval.from(3, 4))
    println(Interval.make(1, 10) ⊓ Interval.make(11, 15))
    println(summon[Lattice[Interval]].bot ⊓ Interval.make(11, 15))
    println(summon[Lattice[Interval]].bot ⊔ Interval.make(11, 15))
    println(Interval.make(11, 15) ⊔ summon[Lattice[Interval]].bot)

    println(summon[Lattice[Interval]].bot △ Interval.make(11, 15))
    println(Interval.make(11, 15) △ summon[Lattice[Interval]].bot)

    println(summon[Lattice[Interval]].bot ▽ Interval.make(11, 15))
    println(Interval.make(11, 15) ▽ summon[Lattice[Interval]].bot)

    println(Interval.make(11, 15) / Interval.from(-1, 1))
    println(Interval.make(11, 15) / Interval.from(0))

    println(summon[Lattice[Interval]].bot < Interval.from(-1, 1))
    println(summon[Lattice[Interval]].bot < summon[Lattice[Interval]].bot)
    println(Interval.from(-1, 1) < summon[Lattice[Interval]].bot)

    println(exec(powerWhile, Map("x" -> NumV(10), "b" -> NumV(2))))

    println(absExec(powerWhile, Map("x" -> Interval.from(10), "b" -> Interval.from(2))))

    println(absExec(nonTerm1, Map("x" -> Interval.from(100))))
    println(absExec(nonTerm2, Map("x" -> Interval.from(100))))
    println(absExec(nonTerm3, Map("x" -> Interval.from(100))))
    println(absExec(nonTerm3, Map("x" -> summon[Lattice[Interval]].top)))
    println(absExec(undef, Map("y" -> Interval.from(1))))
    println(absExec(condProg, Map("x" -> summon[Lattice[Interval]].top)))
    println(absExec(condUndef, Map()))
  }
}

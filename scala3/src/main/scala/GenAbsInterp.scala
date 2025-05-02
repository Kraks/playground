package absinterp

import Expr._
import Stmt._

trait Domain[D] {
  def lift(i: Int): D
  def evalOp(op: String, d1: D, d2: D): D
  def cond[S[_]: St](c: D, thn: => S[D], els: => S[D]): S[D]
}

trait St[S[_]] {
  extension[D: Domain](σ: S[D])
    def apply(x: String): D
    def update(x: String, d: D): S[D]
  def fix[D: Domain](f: (S[D] => S[D]) => S[D] => S[D])(t: S[D]): S[D]
}

object GenInterp {
  def eval[D: Domain, S[_]: St](s: Expr, σ: S[D]): D = {
    val d = summon[Domain[D]]
    s match {
      case Var(x) => σ(x)
      case Lit(i) => d.lift(i)
      case BinOp(op, e1, e2) => d.evalOp(op, eval(e1, σ), eval(e2, σ))
    }
  }
  def exec[D: Domain, S[_]: St](s: Stmt, σ: S[D]): S[D] =
    val d = summon[Domain[D]]
    s match {
      case Skip => σ
      case Assign(x, e) => σ.update(x, eval(e, σ))
      case Seq(s1, s2) => exec(s2, exec(s1, σ))
      case Cond(e, s1, s2) =>
        d.cond(eval(e, σ), exec(s1, σ), exec(s2, σ))
      case While(e, s) =>
        def loop(rec: S[D] => S[D])(σ: S[D]): S[D] = {
          d.cond(eval(e, σ), rec(exec(s, σ)), σ)
        }
        fix(loop)(σ)
    }
}

object ConcreteInterp {
  given ValDomain: Domain[NumV] with
    def lift(i: Int) = NumV(i)
    def evalOp(op: String, v1: NumV, v2: NumV) = genEvalOp[NumV](op, v1, v2)
    def cond[S[_]: St](c: NumV, thn: => S[NumV], els: => S[NumV]) = {
      val NumV(v) = c
      if (v == 1) thn else els
    }
}



/*
def lfpCache[A: AbsDomain, B: AbsDomain](f: (A => B) => A => B)(x: A): B = {
  var previous: (A, B) = summon[AbsDomain[(A, B)]].bot
  var current: (A, B) = summon[AbsDomain[(A, B)]].bot
  def loop(x: A): B = {
    if (x ⊑ current._1) current._2
    else {
      val last = previous._2
      current = current ▽ (x -> last)
      //current = current ⊔ (x -> last)
      val now = f(loop)(x)
      current = current ▽ (x -> now)
      //current = current ⊔ (x -> now)
      current._2
    }
  }
  def iter(x: A): B = {
    println(s"before $previous, $current")
    previous = current
    current = summon[AbsDomain[(A, B)]].bot
    val res = loop(x)
    println(s"after $previous, $current")
    if (previous == current) res
    else iter(x)
  }
  iter(x)
}
 */

def kleeneNarrow[T: AbsDomain](f: T => T)(t: T): T =
  val next = f(t)
  if (t ⊑ next) t else kleeneNarrow(f)(t △ next)

object TestNarrow {
  import Examples._
  def main(args: Array[String]): Unit = {
    println("===narrowing===")
    val r = absExec(bound, Map())
    println(r)
    println(kleeneNarrow(s => absExec(bound, s))(r))
  }
}

package nbe

import scala.reflect._

enum Expr:
  case Var(x: String)
  case Lam(x: String, body: Expr)
  case App(e1: Expr, e2: Expr)

var count: Int = 0
def fresh: String = { val t = count; count += 1; s"x$t" }

object NotTypefulNbE {
  enum Type:
    case Base
    case Arrow(t1: Type, t2: Type)

  enum Term:
    case Var(x: Val)
    case Lam(f: Val => Term)
    case App(t1: Term, t2: Term)

  enum Val:
    case VFun(f: Val => Val)
    case VBase(b: At)

  enum Nf:
    case NLam(f: Val => Nf)
    case NAt(a: At)
  enum At:
    case AApp(a: At, nf: Nf)
    case AVar(x: Val)

  import Type._, Term._, Val._, Nf._, At._

  def eval(t: Term): Val = t match {
    case Var(x) => x
    case Lam(f) => VFun(x => eval(f(x)))
    case App(t1, t2) =>
      val VFun(f) = eval(t1)
      f(eval(t2))
  }

  def reify(ty: Type, v: Val): Nf =
    (ty, v) match {
      case (Arrow(t1, t2), VFun(f)) => NLam(x => reify(t2, f(reflect(t1, AVar(x)))))
      case (Base, VBase(b)) => NAt(b)
    }

  def reflect(ty: Type, a: At): Val =
    ty match {
      case Arrow(t1, t2) => VFun(x => reflect(t2, AApp(a, reify(t1, x))))
      case Base => VBase(a)
    }

  def nbe(ty: Type, t: Term): Nf = reify(ty, eval(t))

  def main(args: Array[String]): Unit = {
    val k = Lam(x => Lam(y => Var(x)))
    val kk = App(k, k)
    println(nbe(Arrow(Base, Arrow(Base, Arrow(Base, Base))), kk))

  }
}

object NbE {
  // From Second FP of TDPE
  import Expr._

  trait RR[A]:
    def reify(a: A): Expr
    def reflect(e: Expr): A

  type Base = Expr
  given baseRR: RR[Base] with
    def reify(x: Expr) = x
    def reflect(x: Expr) = x

  given arrowRR[A, B](using rr1: RR[A], rr2: RR[B]): RR[A => B] with
    def reify(f: A => B): Expr =
      val x = fresh
      Lam(x, rr2.reify(f(rr1.reflect(Var(x)))))
    def reflect(e: Expr): A => B =
      v => rr2.reflect(App(e, rr1.reify(v)))

  def reify[T: RR](v: T): Expr = summon[RR[T]].reify(v)
  def reflect[T: RR](v: Expr): T = summon[RR[T]].reflect(v)

  def nbe[T](e: Expr)(using rr: RR[T]): Expr = reify[T](reflect[T](e))

  def main(args: Array[String]): Unit = {
    println(reify[Base](Var(fresh)))
    println(reify[Base => Base]((x: Base) => x))

    def K[A, B]: A => B => A = x => y => x
    def S[A, B, C]: (A => B => C) => (A => B) => A => C =
      x => y => z => x(z)(y(z))

    // get the term representation of the normal form of K(K)
    println(reify[Base => Base => Base => Base](K(K)))
    val KK = reflect[Base => Base => Base => Base](reify[Base => Base => Base => Base](K(K)))
    println(KK)
    println(KK(Var(fresh))(Var(fresh))(Var(fresh)))
    println(reify[Base => Base](K(K)(Var(fresh))(Var(fresh))))
    val SKK = reify[Base => Base](S(K)(K))
    println(SKK)
    val SKK2 = reify[(Base => Base) => Base => Base](S(K)(K))
    println(SKK2)

    def repk: Base = Lam("x", Lam("y", Var("x")))
    def repkk: Base = App(repk, repk)
    println(reify(reflect(repkk)))
    //println(nbe[Base => Base => Base => Base](repkk))
  }
}

object NbE_Wiki {
  enum Type:
    case Base
    case Arrow(t1: Type, t2: Type)

  enum Sem:
    case Neu(t: Expr)
    case Fun(f: Sem => Sem)

  import Type._; import Sem._; import Expr._

  def reflect(t: Type, e: Expr): Sem =
    t match {
      case Base => Neu(e)
      case Arrow(t1, t2) => Fun(x => reflect(t2, App(e, reify(t1, x))))
    }

  def reify(t: Type, s: Sem): Expr =
    t match {
      case Base => s.asInstanceOf[Neu].t
      case Arrow(t1, t2) =>
        val x = fresh
        Lam(x, reify(t2, s.asInstanceOf[Fun].f(reflect(t1, Var(x)))))
    }

  def eval(e: Expr, ρ: Map[String, Sem]): Sem =
    e match {
      case Var(x) => ρ(x)
      case Lam(x, body) => Fun(v => eval(body, ρ + (x → v)))
      case App(e1, e2) =>
        eval(e1, ρ) match { case Fun(f) => f(eval(e2, ρ)) }
    }

  def nbe(t: Type, e: Expr): Expr = reify(t, eval(e, Map()))
}

object NBE1 {
  import Expr._

  enum Type:
    case Base
    case Arrow[T1 <: Type, T2 <: Type](t1: T1, t2: T2)
  import Type._

  type Rep[T] = T match
    case Base.type => Expr
    case Arrow[t1, t2] => Rep[t1] => Rep[t2]

  var count: Int = 0
  def fresh: String = { val t = count; count += 1; s"x$t" }

  def reify(t: Type, e: Rep[t.type]): Expr =
    t match {
      case Base => e.asInstanceOf[Expr]
      case Arrow(t1, t2) =>
        val x = fresh
        val f = e.asInstanceOf[Function1[Rep[t1.type], Rep[t2.type]]]
        Lam(x, reify(t2, f(reflect(t1, Var(x)))))
    }

  def reflect(t: Type, e: Expr): Rep[t.type] =
    t match {
      case Base => e.asInstanceOf[Rep[t.type]]
      case Arrow(t1, t2) =>
        val f = { (x: Rep[t1.type]) =>
          reflect(t2, App(e, reify(t1, x)))
        }
        f.asInstanceOf[Rep[t.type]]
    }

  // Doesn't work
  //def main(args: Array[String]): Unit = {
    //println(reify(Base, Var(fresh)))
    //println(reify(Arrow[Base.type, Base.type](Base, Base), { (x: Expr) => x }))
  //}
}

object NBE2 {
  import Expr._
  import Type._

  enum Type:
    case Base
    case Arrow[T1 <: Type, T2 <: Type](t1: T1, t2: T2)
  import Type._

  type Rep[T] = T match
    case Base.type => Expr
    case Arrow[t1, t2] => Rep[t1] => Rep[t2]

  var count: Int = 0
  def fresh: String = { val t = count; count += 1; s"x$t" }
  //reify[Base.type](Var(fresh))
  //reify[Arrow[Base.type, Base.type]]{ (x: Expr) => x }

  /*
  def reify[T](e: Rep[T]): Expr =
    e match {
      case (e: Expr) => e
      case (f: Function1[Rep[t1], Rep[t2]]) =>
        val x = fresh
        Lam(x, reify[t2](f(reflect[t1](Var(x)))))
    }
  */
}

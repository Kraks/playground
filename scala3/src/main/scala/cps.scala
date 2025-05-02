package cps

trait Exp
case class App(e1: Exp, e2: Exp) extends Exp {
  override def toString: String = s"[$e1@$e2]"
}

trait Val extends Exp
case class Var(x: String) extends Val {
  override def toString: String = x
}
case class Lam(x: String, e: Exp) extends Val {
  override def toString: String = s"(λ$x.$e)"
}

case class Redex(v1: Val, v2: Val)

trait Cont
case class Halt() extends Cont
case class Arg(arg: Exp, k: Cont) extends Cont
case class Fun(v: Val, k: Cont) extends Cont

object Examples {
  // [(λx.e)@[(λy.[(λz.c)@[a@b]])@d]]
  // (λk0.[[(λy.(λk1.[[a@b]@(λw2.[[(λz.(λk3.[k3@c]))@w2]@(λw4.[k1@w4])])]))@d]@(λw5.[[(λx.(λk6.[k6@e]))@w5]@(λw7.[k0@w7])])])
  val e0 = App(Lam("x", Var("e")),
               App(Lam("y", App(Lam("z", Var("c")),
                                App(Var("a"), Var("b")))),
                   Var("d")))

}

import Examples._

object Counter {
  var x: Int = 0
  def fresh(prefix: String = "x"): String = {
    val n = x
    x += 1
    s"$prefix$n"
  }
  def reset: Unit = x = 0
}

import Counter._

object Decompose {
  def decompose(e: Exp): Val | (Cont, Redex) = decompose0(e, Halt())

  private def decompose0(e: Exp, k: Cont): Val | (Cont, Redex) =
    e match
      case v: Val => decompose_aux(k, v)
      case App(e1, e2) => decompose0(e1, Arg(e2, k))

  private def decompose_aux(k: Cont, v: Val): Val | (Cont, Redex) =
    k match
      case Halt() => v
      case Arg(e, k) => decompose0(e, Fun(v, k))
      case Fun(f, k) => (k, Redex(f, v))
}

object Compose {
  def plugin(k: Cont, e: Exp): Exp = k match
    case Halt() => e
    case Arg(e1, k) => plugin(k, App(e, e1))
    case Fun(f, k) => plugin(k, App(f, e))
}

import Decompose._
import Compose._

// Sec 2.1
// Definition 1 -- Implicit context-based CPS transformation

object ImplicitContextBasedCPS {
  def E(e: Exp, k: Var): Exp = e match
    case v: Val => App(k, V(v))
    case _ =>
      val (c, Redex(v0, v1)) = decompose(e)
      App(App(V(v0), V(v1)), C(c, k))
  def V(v: Val): Val = v match
    case v: Var => v
    case Lam(x, e) =>
      val k = fresh("k")
      Lam(x, Lam(k, E(e, Var(k))))
  def C(c: Cont, k: Var): Val =
    val w = fresh("w")
    Lam(w, E(plugin(c, Var(w)), k))
  def transform(e: Exp): Exp =
    Counter.reset
    val k = fresh("k")
    Lam(k, E(e, Var(k)))
}

// Definition 2 -- Explicit context-based CPS transformation

object ExplicitContextBasedCPS {
  def E(v: Val|(Cont,Redex), k: Var): Exp = v match
    case v: Val => App(k, V(v))
    case (c, Redex(v0, v1)) =>
      App(App(V(v0), V(v1)), C(c, k))
  def V(v: Val): Val = v match
    case v: Var => v
    case Lam(x, e) =>
      val k = fresh("k")
      Lam(x, Lam(k, E(decompose(e), Var(k))))
  def C(c: Cont, k: Var): Val =
    val w = fresh("w")
    Lam(w, E(decompose(plugin(c, Var(w))), k))
  def transform(e: Exp): Exp =
    Counter.reset
    val k = fresh("k")
    Lam(k, E(decompose(e), Var(k)))
}

// Refocus

object Refocus {
  def refocus(e: Exp, c: Cont): Val|(Cont,Redex) = e match
    case v: Val => refocus0(c, v)
    case App(e0, e1) => refocus(e0, Arg(e1, c))
  def refocus0(c: Cont, v: Val): Val|(Cont,Redex) = c match
    case Halt() => v
    case Arg(e1, k) => refocus(e1, Fun(v, k))
    case Fun(v0, k) => (k, Redex(v0, v))
}

import Refocus._

// Definition 3 -- Context-based CPS transformation, refocused

object RefocusedContextBasedCPS {
  def E(v: Val|(Cont,Redex), k: Var): Exp = v match
    case v: Val => App(k, V(v))
    case (c, Redex(v0, v1)) =>
      App(App(V(v0), V(v1)), C(c, k))
  def V(v: Val): Val = v match
    case v: Var => v
    case Lam(x, e) =>
      val k = fresh("k")
      Lam(x, Lam(k, E(refocus(e, Halt()), Var(k))))
  def C(c: Cont, k: Var): Val =
    val w = fresh("w")
    Lam(w, E(refocus(Var(w), c), k))
  def transform(e: Exp): Exp =
    Counter.reset
    val k = fresh("k")
    Lam(k, E(refocus(e, Halt()), Var(k)))
}

// Definition 4 -- Context-based CPS transformation, fused

object FusedContextBasedCPS {
  def fusedE(e: Exp, c: Cont, k: Var): Exp = e match
    case v: Val => fusedE0(c, v, k)
    case App(e0, e1) => fusedE(e0, Arg(e1, c), k)
  def fusedE0(c: Cont, v: Val, k: Var): Exp = c match
    case Halt() => App(k, V(v))
    case Arg(e1, c) => fusedE(e1, Fun(v, c), k)
    case Fun(v0, c) => App(App(V(v0), V(v)), C(c, k))
  def V(v: Val): Val = v match
    case v: Var => v
    case Lam(x, e) =>
      val k = fresh("k")
      Lam(x, Lam(k, fusedE(e, Halt(), Var(k))))
  def C(c: Cont, k: Var): Val =
    val w = fresh("w")
    Lam(w, fusedE(Var(w), c, k))
  def transform(e: Exp): Exp =
    Counter.reset
    val k = fresh("k")
    Lam(k, fusedE(e, Halt(), Var(k)))
}

// Definition 5 -- Context-based CPS transformation, refunctionalized

object RefunContextBasedCPS {
  def E(e: Exp, k: Val => Exp): Exp = e match
    case v: Val => k(v)
    case App(e0, e1) => E(e0, u0 => E(e1, u1 => App(App(V(u0), V(u1)), C(k))))
  def V(v: Val): Val = v match
    case v: Var => v
    case Lam(x, e) =>
      val k = fresh("k")
      Lam(x, Lam(k, E(e, u => App(Var(k), V(u)))))
  def C(k: Val => Exp): Val =
    val w = fresh("w")
    Lam(w, k(Var(w)))
  def transform(e: Exp): Exp =
    Counter.reset
    val k = fresh("k")
    Lam(k, E(e, u => App(Var(k), V(u))))
}

// Definition 6 -- Higher-order CPS transformation

object HigherOrderCPS {
  type SExp = Exp
  type SVal = Val
  type TExp = Exp
  type TVal = Val
  def E(e: SExp, k: TVal => TExp): TExp = e match
    case v: Val => k(V(v))
    case App(e0, e1) =>
      E(e0, u0 => E(e1, u1 => App(App(u0, u1), C(k))))
  def V(v: SVal): TVal = v match
    case v: Var => v
    case Lam(x, e) =>
      val k = fresh("k")
      Lam(x, Lam(k, E(e, u => App(Var(k), u))))
  def C(k: TVal => TExp): TVal =
    val w = fresh("w")
    Lam(w, k(Var(w)))
  def transform(e: Exp): Exp =
    Counter.reset
    val k = fresh("k")
    Lam(k, E(e, u => App(Var(k), u)))
}

object Test {
  def main(args: Array[String]) = {
    println(e0)
    println(ImplicitContextBasedCPS.transform(e0))
    println(ExplicitContextBasedCPS.transform(e0))
    println(RefocusedContextBasedCPS.transform(e0))
    println(FusedContextBasedCPS.transform(e0))
    println(RefunContextBasedCPS.transform(e0))
    println(HigherOrderCPS.transform(e0))
  }
}

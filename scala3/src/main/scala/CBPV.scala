package cbpv

// Syntax

enum Val:
  case Unit
  case Var(x: String)
  case Pair(x: Val, y: Val)
  case Lam(x: String, e: Comp)
  case Thunk(e: Comp)

enum Comp:
  case Ret(v: Val)
  case Let(x: String, c1: Comp, c2: Comp)
  case Force(v: Val)
  case App(f: Val, arg: Val)

// Runtime value

enum RtVal:
  case VUnit
  case VPair(x: RtVal, y: RtVal)
  case VThunk(c: Comp, env: Env)
  case VClo(x: String, e: Comp, env: Env)

type Env = Map[String, RtVal]

import Val.*
import Comp.*
import RtVal.*

def eval(v: Val, ρ: Env): RtVal = v match
  case Unit => VUnit
  case Var(x) => ρ(x)
  case Pair(x, y) => VPair(eval(x, ρ), eval(y, ρ))
  case Lam(x, e) => VClo(x, e, ρ)
  case Thunk(e) => VThunk(e, ρ)

def eval(c: Comp, ρ: Env): RtVal = c match
  case Ret(v) => eval(v, ρ)
  case Let(x, c1, c2) =>
    val v1 = eval(c1, ρ)
    eval(c2, ρ + (x -> v1))
  case Force(v) =>
    val VThunk(c, ρ1) = eval(v, ρ)
    eval(c, ρ1)
  case App(f, arg) =>
    val VClo(x, e, ρ1) = eval(f, ρ)
    eval(e, ρ1 + (x -> eval(arg, ρ)))

// embedding CBV into CBPV

enum LC:
  case Unit
  case Var(x: String)
  case Lam(x: String, e: LC)
  case App(e1: LC, e2: LC)

var counter = 0
def fresh(prefix: String): String =
  counter += 1
  s"${prefix}_$counter"

package cbv {
  /*
  ⟦x⟧ = return x
  ⟦λx.e⟧ = return (λx.⟦e⟧)
  ⟦e1 e2⟧ = let f = ⟦e1⟧ in
            let arg = ⟦e2⟧ in
            f arg
  */
  def translate(e: LC): Comp = e match
    case LC.Unit => Ret(Unit)
    case LC.Var(x) => Ret(Var(x))
    case LC.Lam(x, e) => Ret(Lam(x, translate(e)))
    case LC.App(e1, e2) =>
      val f = fresh("f")
      val x = fresh("x")
      Let(f, translate(e1),
        Let(x, translate(e2),
          App(Var(f), Var(x))))
}

package cbn {
  /*
  ⟦x⟧ = force x
  ⟦λx.e⟧ = return (λx.⟦e⟧)
  ⟦e1 e2⟧ = let f = ⟦e1⟧ in
            f thunk(⟦e2⟧)
  */
  def translate(e: LC): Comp = e match
    case LC.Unit => Ret(Unit)
    case LC.Var(x) => Force(Var(x))
    case LC.Lam(x, e) => Ret(Lam(x, translate(e)))
    case LC.App(e1, e2) =>
      val f = fresh("f")
      Let(f, translate(e1),
        App(Var(f), Thunk(translate(e2))))
}

@main
def test: Unit =
  val id = LC.Lam("x", LC.Var("x"))
  val arg = LC.App(LC.Lam("y", LC.Var("y")), LC.Lam("z", LC.Var("z")))
  val e = LC.App(id, arg)

  val omega = {
    val inner = LC.Lam("y", LC.App(LC.Var("y"), LC.Var("y")))
    LC.App(inner, inner)
  }
  val e2 = LC.App(LC.Lam("x", LC.Unit), omega)
  {
    // CBV would not terminate
    val c = eval(cbv.translate(e2), Map())
    println(s"cbv: $c")
  }

  {
    val c = eval(cbn.translate(e2), Map())
    println(s"cbn: $c")
  }

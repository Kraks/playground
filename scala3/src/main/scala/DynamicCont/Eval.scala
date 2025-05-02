package dyanmic.continuation
package evaluator
// Fig 3, the definitional cbv evaluator with F (Control) and # (Prompt)

enum Term:
  case Var(x: String)
  case Lam(x: String, e: Term)
  case App(e1: Term, e2: Term)
  case Prompt(e: Term)
  case Control(x: String, e: Term)

case class Val(f: (Val, Cont1, Trail, Cont2) => Val)
case class Cont1(apply: (Val, Trail, Cont2) => Val)
type Cont2 = Val => Val
type Trail = List[Cont1]

val k1_init: Cont1 = Cont1((v, t, k2) => t match
  case Nil => k2(v)
  case k1::t1 => k1.apply(v, t1, k2)
)
val k2_init: Cont2 = v => v

import Term._
import Val._

def eval(e: Term, ρ: Map[String, Val], k1: Cont1, t: Trail, k2: Cont2): Val =
  e match
    case Var(x) => k1.apply(ρ(x), t, k2)
    case Lam(x, e) => k1.apply(Val((v, k1, t, k2) => eval(e, ρ + (x -> v), k1, t, k2)), t, k2)
    case App(e1, e2) => eval(e1, ρ, Cont1((v0, t, k2) => eval(e2, ρ, Cont1((v1, t, k2) => v0.f(v1, k1, t, k2)), t, k2)), t, k2)
    case Prompt(e) => eval(e, ρ, k1_init, Nil, v => k1.apply(v, t, k2))
    case Control(x, e) => eval(e, ρ + (x -> Val((v, k1_, t_, k2) => k1.apply(v, t ++ (k1_ :: t_), k2))), k1, Nil, k2)
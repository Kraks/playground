package callcc

object Syntax {
  abstract class Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class CallCC(k: String, e: Expr) extends Expr
}

object BigStep {
  import Syntax._

  abstract class Value
  case class FuncV(f: Value => (Value => Value) => Value) extends Value
  case class ContV(k: Value => Value) extends Value

  type Env = Map[String, Value]

  def interp(e: Expr, ρ: Env, κ: Value => Value): Value =
    e match {
      case Var(x) =>
        ρ(x)
      case Lam(x, body) =>
        FuncV(v => κ => interp(body, ρ + (x → v), κ))
      case App(e1, e2) =>
        interp(e1, ρ, {
          case FuncV(f) => interp(e2, ρ, v2 => f(v2)(κ))
          case ContV(κ_*) => interp(e2, ρ, κ_*)
        })
      case CallCC(k, e) =>
        interp(e, ρ + (k → ContV(κ)), κ)
    }
}

object CEK {
  import Syntax._

  abstract class Value
  case class ClosV(λ: Lam, ρ: Env) extends Value
  case class ContV(κ: Kont) extends Value

  abstract class Kont
  case class MtK() extends Kont
  case class FunK(v: Value, κ: Kont) extends Kont
  case class ArgK(arg: Expr, κ: Kont) extends Kont

  type Env = Map[String, Value]
  type State = (Expr, Env, Kont)

  def step(s: State): State = s match {
    case (Var(x), ρ, κ) => ρ(x) match {
      case ClosV(λ, ρ_*) => (λ, ρ_*, κ)
    }
    case (v@Lam(_, _), ρ, FunK(ClosV(Lam(x, body), ρ_*), κ)) =>
      ???
    case (App(e1, e2), ρ, κ) =>
      ???
  }
}

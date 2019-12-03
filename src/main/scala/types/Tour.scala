package types.tour

object Basic {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr

  trait Value
  case class FunV(f: Value ⇒ Value) extends Value

  type Env = Map[String, Value]

  def interp(e: Expr, ρ: Env): Value = e match {
    case Var(x) ⇒ ρ(x)
    case Lam(x, body) ⇒ FunV(v ⇒ interp(body, ρ + (x → v)))
    case App(e1, e2) ⇒ interp(e1, ρ) match {
      case FunV(f) ⇒ f(interp(e2, ρ))
    }
  }
}

object BasicDefunc {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr

  trait Value
  case class FunV(λ: Lam, ρ: Env) extends Value

  type Env = Map[String, Value]

  def interp(e: Expr, ρ: Env): Value = e match {
    case Var(x) ⇒ ρ(x)
    case Lam(x, body) ⇒ FunV(Lam(x, body), ρ)
    case App(e1, e2) ⇒ interp(e1, ρ) match {
      case FunV(Lam(x, body), ρ_*) ⇒
        interp(body, ρ_* + (x → interp(e2, ρ)))
    }
  }
}

object BasicWithData {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Lit(i: Int) extends Expr
  case class Aop(op: String, e1: Expr, e2: Expr) extends Expr

  trait Value
  case class FunV(f: Value ⇒ Value) extends Value
  case class IntV(x: Int) extends Value

  type Env = Map[String, Value]

  def interp(e: Expr, ρ: Env): Value = e match {
    case Var(x) ⇒ ρ(x)
    case Lam(x, body) ⇒ FunV(v ⇒ interp(body, ρ + (x → v)))
    case App(e1, e2) ⇒ interp(e1, ρ) match {
      case FunV(f) ⇒ f(interp(e2, ρ))
    }
    case Lit(i) ⇒ IntV(i)
    case Aop("+", e1, e2) ⇒
      (interp(e1, ρ), interp(e2, ρ)) match {
        case (IntV(v1), IntV(v2)) => IntV(v1 + v2)
      }
  }
}

object BasicWithDataAndState {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Lit(i: Int) extends Expr
  case class Aop(op: String, e1: Expr, e2: Expr) extends Expr
  case class Seq(e1: Expr, e2: Expr) extends Expr
  case class Assign(x: String, e: Expr) extends Expr
  case class Let(x: String, e: Expr, body: Expr) extends Expr
  case class If0(cnd: Expr, thn: Expr, els: Expr) extends Expr
  case class Letrec(x: String, e: Expr, body: Expr) extends Expr

  type Addr = Int
  type Env = Map[String, Addr]
  type Heap = Map[Addr, Value]
  type Result = (Value, Heap)

  def alloc(σ: Heap): Addr = σ.size + 1

  trait Value
  case class FunV(f: (Value, Heap) ⇒ (Value, Heap)) extends Value
  case class IntV(x: Int) extends Value
  case class BotV() extends Value

  def interp(e: Expr, ρ: Env, σ: Heap): Result = e match {
    case Var(x) ⇒ (σ(ρ(x)), σ)
    case Lam(x, body) ⇒ (FunV({
      case (v, σ) ⇒
        val α = alloc(σ)
        interp(body, ρ + (x → α), σ + (α → v))
    }), σ)
    case App(e1, e2) ⇒ interp(e1, ρ, σ) match {
      case (FunV(f), σ_*) ⇒ interp(e2, ρ, σ_*) match {
        case (v, σ_**) ⇒ f(v, σ_**)
      }
    }
    case Lit(i) ⇒ (IntV(i), σ)
    case Aop("+", e1, e2) ⇒ interp(e1, ρ, σ) match {
      case (IntV(v1), σ_*) ⇒ interp(e2, ρ, σ_*) match {
        case (IntV(v2), σ_**) ⇒ (IntV(v1 + v2), σ_**)
      }
    }
    case Aop("*", e1, e2) ⇒ interp(e1, ρ, σ) match {
      case (IntV(v1), σ_*) ⇒ interp(e2, ρ, σ_*) match {
        case (IntV(v2), σ_**) ⇒ (IntV(v1 * v2), σ_**)
      }
    }
    case Aop("-", e1, e2) ⇒ interp(e1, ρ, σ) match {
      case (IntV(v1), σ_*) ⇒ interp(e2, ρ, σ_*) match {
        case (IntV(v2), σ_**) ⇒ (IntV(v1 - v2), σ_**)
      }
    }
    case Seq(e1, e2) ⇒ interp(e1, ρ, σ) match {
      case (_, σ_*) ⇒ interp(e2, ρ, σ_*)
    }
    case Assign(x, e) ⇒ interp(e, ρ, σ) match {
      case (v, σ_*) ⇒ (v, σ_* + (ρ(x) → v))
    }
    case Let(x, e, body) ⇒ interp(e, ρ, σ) match {
      case (v, σ_*) ⇒
        val α = alloc(σ_*)
        val ρ_* = ρ + (x → α)
        val σ_** = σ_* + (α → v)
        interp(body, ρ_*, σ_**)
    }
    case If0(cnd, thn, els) ⇒ interp(cnd, ρ, σ) match {
      case (IntV(0), σ_*) ⇒ interp(thn, ρ, σ_*)
      case (IntV(_), σ_*) ⇒ interp(els, ρ, σ_*)
    }
    case Letrec(x, e, body) ⇒
      val α = alloc(σ)
      val ρ_* = ρ + (x → α)
      val σ_* = σ + (α → BotV())
      interp(e, ρ_*, σ_*) match {
        case (v, σ_**) ⇒
          val σ_*** = σ_** + (α → v)
          interp(body, ρ_*, σ_***)
      }
  }

  def main(args: Array[String]) = {
    val fact = Letrec("fact",
      Lam("x",
        If0(Var("x"), Lit(1),
          Aop("*", Var("x"), App(Var("fact"), Aop("-", Var("x"), Lit(1)))))),
      App(Var("fact"), Lit(5)))
    println(interp(fact, Map(), Map()))

    val nonterm = Letrec("x",
      Aop("+", Var("x"), Lit(1)),
      Var("x"))
    //println(interp(nonterm, Map(), Map()))
  }
}


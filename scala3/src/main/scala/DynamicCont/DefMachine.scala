package dynamic.continuation
package definition.machine
// A Dynamic Continuation-Passing Style for Dynamic Delimited Continuations
// https://dl.acm.org/doi/pdf/10.1145/2794078

// the definitional cbv abstract machine with F (Control) and # (Prompt)

enum Term:
  case Var(x: String)
  case Lam(x: String, e: Term)
  case App(e1: Term, e2: Term)
  case Prompt(e: Term)
  case Control(x: String, e: Term)
  case Shift(x: String, e: Term)

type Env = Map[String, Value]

enum Value:
  case Clo(x: String, e: Term, ρ: Env)
  case Cont(c: Ctx)

enum Ctx:
  case End()
  case Arg(e: Term, ρ: Env, c: Ctx)
  case Fun(v: Value, c: Ctx)

extension (c1: Ctx)
  def ★(c2: Ctx): Ctx = c1 match {
    case End() => c2
    case Arg(e, ρ, c1) => Arg(e, ρ, c1 ★ c2)
    case Fun(v, c1) => Fun(v, c1 ★ c2)
  }

import Term._
import Value._
import Ctx._

type MCtx = List[Ctx]

// evaluation state
case class EState(e: Term, ρ: Env, κ: Ctx, γ: MCtx)
// continuation state
case class CState(κ: Ctx, v: Value, γ: MCtx)
// meta-continuation state
case class MState(γ: MCtx, v: Value)

type State = EState | CState | MState

def step(s: EState): EState | CState = s match {
  case EState(Var(x), ρ, κ, γ) => CState(κ, ρ(x), γ)
  case EState(Lam(x, e), ρ, κ, γ) => CState(κ, Clo(x, e, ρ), γ)
  case EState(App(e1, e2), ρ, κ, γ) => EState(e1, ρ, Arg(e2, ρ, κ), γ)
  case EState(Prompt(e), ρ, κ, γ) => EState(e, ρ, End(), κ :: γ)
  case EState(Control(x, e), ρ, κ, γ) => EState(e, ρ + (x -> Cont(κ)), End(), γ)
}

def step(s: CState): State = s match {
  case CState(End(), v, γ) => MState(γ, v)
  case CState(Arg(e, ρ, κ), v, γ) => EState(e, ρ, Fun(v, κ), γ)
  case CState(Fun(Clo(x, e, ρ), κ), v, γ) => EState(e, ρ + (x -> v), κ, γ)
  case CState(Fun(Cont(κ1), κ2), v, γ) => CState(κ1 ★ κ2, v, γ)
  case CState(Fun(Cont(κ1), κ2), v, γ) => CState(κ1, v, κ2 :: γ)
}

def step(s: MState): CState | Value = s match {
  case MState(Nil, v) => v
  case MState(κ :: γ, v) => CState(κ, v, γ)
}

def inject(e: Term): EState = EState(e, Map(), End(), Nil)

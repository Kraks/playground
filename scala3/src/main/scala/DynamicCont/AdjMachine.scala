package dynamic.continuation
package adjusted.machine

// A Dynamic Continuation-Passing Style for Dynamic Delimited Continuations
// https://dl.acm.org/doi/pdf/10.1145/2794078

// Fig 2, the "adjusted" cbv abstract machine with F (Control) and # (Prompt)

enum Term:
  case Var(x: String)
  case Lam(x: String, e: Term)
  case App(e1: Term, e2: Term)
  case Prompt(e: Term)
  case Control(x: String, e: Term)

enum Value:
  case Clo(x: String, e: Term, ρ: Env)
  case Cont(c: Ctx, t: Trail)

enum Ctx:
  case End()
  case Arg(e: Term, ρ: Env, c: Ctx)
  case Fun(v: Value, c: Ctx)

type Trail = List[Ctx]

type MCtx = List[(Ctx, Trail)]

import Term._
import Value._
import Ctx._

type Env = Map[String, Value]

// evaluation state
case class EState(e: Term, ρ: Env, κ: Ctx, τ: Trail, γ: MCtx)
// continuation state
case class CState(κ: Ctx, v: Value, τ: Trail, γ: MCtx)
// trail-continuation state
case class TState(τ: Trail, v: Value, γ: MCtx)
// meta-continuation state
case class MState(γ: MCtx, v: Value)

def step(s: EState): EState | CState = s match {
  case EState(Var(x), ρ, κ, τ, γ) => CState(κ, ρ(x), τ, γ)
  case EState(Lam(x, e), ρ, κ, τ, γ) => CState(κ, Clo(x, e, ρ), τ, γ)
  case EState(App(e1, e2), ρ, κ, τ, γ) => EState(e1, ρ, Arg(e2, ρ, κ), τ, γ)
  case EState(Prompt(e), ρ, κ, τ, γ) => EState(e, ρ, End(), Nil, (κ, τ) :: γ)
  case EState(Control(x, e), ρ, κ, τ, γ) => EState(e, ρ + (x -> Cont(κ, τ)), End(), Nil, γ)
}

def step(s: CState): TState | EState | CState = s match {
  case CState(End(), v, τ, γ) => TState(τ, v, γ)
  case CState(Arg(e, ρ, κ), v, τ, γ) => EState(e, ρ, Fun(v, κ), τ, γ)
  case CState(Fun(Clo(x, e, ρ), κ), v, τ, γ) => EState(e, ρ + (x -> v), κ, τ, γ)
  case CState(Fun(Cont(κ1, τ1), κ2), v, τ, γ) => CState(κ1, v, τ1 ++ (κ2 :: τ), γ)
}

def step(s: TState): CState | MState = s match {
  case TState(Nil, v, γ) => MState(γ, v)
  case TState(κ::τ, v, γ) => CState(κ, v, τ, γ)
}

def step(s: MState): CState | Value = s match {
  case MState(Nil, v) => v
  case MState((κ, τ)::γ, v) => CState(κ, v, τ, γ)
}

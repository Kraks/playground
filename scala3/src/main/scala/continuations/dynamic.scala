package continuation.dynamic
// A Dynamic Continuation-Passing Style for Dynamic Delimited Continuations
// https://dl.acm.org/doi/pdf/10.1145/2794078

enum Term:
  case Var(x: String)
  case Lam(x: String, e: Term)
  case App(e1: Term, e2: Term)
  case Prompt(e: Term)
  case Control(x: String, e: Term)
  case Shift(x: String, e: Term)
  case Shift0(x: String, e: Term)
  case Control0(x: String, e: Term)
import Term._

package adjusted.machine {

// Fig 2, the "adjusted" cbv abstract machine with F (Control) and # (Prompt)

enum Value:
  case Clo(x: String, e: Term, ρ: Env)
  case Cont(c: Ctx, t: Trail)
  case ContS(c: Ctx, t: Trail) // for continuations captured by shift/shift0

enum Ctx:
  case End()
  case Arg(e: Term, ρ: Env, c: Ctx)
  case Fun(v: Value, c: Ctx)

type Trail = List[Ctx]

type MCtx = List[(Ctx, Trail)]

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

def step(s: EState): EState | CState = s match
  case EState(Var(x), ρ, κ, τ, γ) =>
    CState(κ, ρ(x), τ, γ)
  case EState(Lam(x, e), ρ, κ, τ, γ) =>
    CState(κ, Clo(x, e, ρ), τ, γ)
  case EState(App(e1, e2), ρ, κ, τ, γ) =>
    EState(e1, ρ, Arg(e2, ρ, κ), τ, γ)
  case EState(Prompt(e), ρ, κ, τ, γ) =>
    EState(e, ρ, End(), Nil, (κ, τ) :: γ)
  case EState(Control(x, e), ρ, κ, τ, γ) =>
    // control/+F- inserts a reset/prompt around the body `e`
    EState(e, ρ + (x -> Cont(κ, τ)), End(), Nil, γ)
  case EState(Shift(x, e), ρ, κ, τ, γ) =>
    // shift/+F+ inserts a reset/prompt around the body `e`
    EState(e, ρ + (x -> ContS(κ, τ)), End(), Nil, γ)
  case EState(Control0(x, e), ρ, κ, τ, (κ1, τ1)::γ) =>
    // control0/-F- does not delimit the body `e` with a reset/prompt
    EState(e, ρ + (x -> Cont(κ, τ)), κ1, τ1, γ)
  case EState(Shift0(x, e), ρ, κ, τ, (κ1, τ1)::γ) =>
    // shift0/-F+ does not delimit the body `e` with a reset/prompt
    EState(e, ρ + (x -> ContS(κ, τ)), κ1, τ1, γ)

def step(s: CState): TState | EState | CState = s match
  case CState(End(), v, τ, γ) =>
    TState(τ, v, γ)
  case CState(Arg(e, ρ, κ), v, τ, γ) =>
    EState(e, ρ, Fun(v, κ), τ, γ)
  case CState(Fun(Clo(x, e, ρ), κ), v, τ, γ) =>
    EState(e, ρ + (x -> v), κ, τ, γ)
  case CState(Fun(Cont(κ1, τ1), κ2), v, τ, γ) =>
    // at the call-site of a control/control0-captured continuation, there is no reset/prompt guard
    CState(κ1, v, τ1 ++ (κ2 :: τ), γ)
  case CState(Fun(ContS(κ1, τ1), κ2), v, τ, γ) =>
    // at the call-site of a shift/shift0-captured continuation, we guard with a reset
    CState(κ1, v, τ1, (κ2, τ)::γ)

def step(s: TState): CState | MState = s match
  case TState(Nil, v, γ) => MState(γ, v)
  case TState(κ::τ, v, γ) => CState(κ, v, τ, γ)

def step(s: MState): CState | Value = s match
  case MState(Nil, v) => v
  case MState((κ, τ)::γ, v) => CState(κ, v, τ, γ)

}

package definition.machine {
// Fig 1, the definitional cbv abstract machine with F (Control) and # (Prompt)

type Env = Map[String, Value]

enum Value:
  case Clo(x: String, e: Term, ρ: Env)
  case DCont(c: Ctx) // continuations captured by control
  case SCont(c: Ctx) // continuations captured by shift
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

def step(s: EState): EState | CState = s match
  case EState(Var(x), ρ, κ, γ) => CState(κ, ρ(x), γ)
  case EState(Lam(x, e), ρ, κ, γ) => CState(κ, Clo(x, e, ρ), γ)
  case EState(App(e1, e2), ρ, κ, γ) => EState(e1, ρ, Arg(e2, ρ, κ), γ)
  case EState(Prompt(e), ρ, κ, γ) => EState(e, ρ, End(), κ :: γ)
  case EState(Control(x, e), ρ, κ, γ) => EState(e, ρ + (x -> DCont(κ)), End(), γ)
  case EState(Shift(x, e), ρ, κ, γ) => EState(e, ρ + (x -> SCont(κ)), End(), γ)

def step(s: CState): State = s match
  case CState(End(), v, γ) => MState(γ, v)
  case CState(Arg(e, ρ, κ), v, γ) => EState(e, ρ, Fun(v, κ), γ)
  case CState(Fun(Clo(x, e, ρ), κ), v, γ) => EState(e, ρ + (x -> v), κ, γ)
  /* control captures a delimited continuation κ1, the current continuation κ2
   * can be accessed from κ1 by using another control.
   */
  case CState(Fun(DCont(κ1), κ2), v, γ) => CState(κ1 ★ κ2, v, γ)
  /* shift captures a delimited continuation κ1, the current continuation κ2
   * cannot be accessed from κ1 by using another shift.
   */
  case CState(Fun(SCont(κ1), κ2), v, γ) => CState(κ1, v, κ2 :: γ)

def step(s: MState): CState | Value = s match
  case MState(Nil, v) => v
  case MState(κ :: γ, v) => CState(κ, v, γ)

def inject(e: Term): EState = EState(e, Map(), End(), Nil)
}

package evaluator {
// Fig 3, the definitional cbv evaluator with F (Control) and # (Prompt)

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

}

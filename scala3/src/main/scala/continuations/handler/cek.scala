package continuation.handler.cek

// Liberating Effects with Rows and Handlers, Daniel Hillerstrom and Sam Lindley

import continuation.handler.syntax.*
import Value.*
import Comp.*
import Handler.*

// Runtime structures

enum RValue:
  case IntV(i: Int)
  case CloV(x: String, e: Comp, env: Env)
  case KntV(k: Cont)

case class HanClo(env: Env, h: Handler)
case class Frame(pureK: PCont, h: HanClo)
case class PFrame(x: String, e: Comp, env: Env)

type Cont = List[Frame]
type PCont = List[PFrame]

type Env = Map[String, RValue]

enum State:
  case PState(e: Comp, env: Env, k: Cont)
  case EState(e: Comp, env: Env, k1: Cont, k2: Cont)

import RValue.*
import State.*

//def inject(e: Comp): State = PState(e, Map.empty, List(Frame(List(), HanClo(Map.empty, Return("x", Ret(Var("x")))))))

def inject(e: Comp): State = PState(Handle(e, Return("x", Ret(Var("x")))), Map.empty, List())

def prim(op: String, v1: RValue, v2: RValue): RValue = (v1, v2) match
  case (IntV(i), IntV(j)) => op match
    case "+" => IntV(i+j)
    case "-" => IntV(i-j)
    case "*" => IntV(i*j)
    case "/" => IntV(i/j)

def eval(v: Value, env: Env): RValue = v match
  case Num(i) => IntV(i)
  case Var(x) => env(x)
  case Lam(x, e) => CloV(x, e, env)
  case Prim(op, v1, v2) => prim(op, eval(v1, env), eval(v2, env))

def isDone(s: State): Boolean = s match
  case PState(Ret(_), _, Nil) => true
  case _ => false

def extract(s: State): RValue = s match
  case PState(Ret(v), env, Nil) => eval(v, env)

def step(s: State): State = s match
  case PState(App(v1, v2), env, k) =>
    eval(v1, env) match
      case CloV(x, e, env1) => PState(e, env1 + (x -> eval(v2, env)), k)
      case KntV(k1) => PState(Ret(v2), env, k1 ++ k)
  case PState(Let(x, rhs, body), env, Frame(p, h)::k) =>
    PState(rhs, env, Frame(PFrame(x, body, env)::p, h)::k)
  case PState(Handle(e, h), env, k) =>
    PState(e, env, Frame(List(), HanClo(env, h))::k)
  case PState(Ret(v), env, Frame(PFrame(x, e, env1)::pf, h)::k) =>
    PState(e, env1 + (x -> eval(v, env)), Frame(pf, h)::k)
  case PState(Ret(v), env, Frame(List(), HanClo(env1, h))::k) =>
    val Return(x, e) = retOf(h)
    PState(e, env1 + (x -> eval(v, env)), k)
  case PState(Do(l, v), env, k) =>
    EState(Do(l, v), env, k, Nil)
  case EState(Do(l, v), env, (f@Frame(pf, HanClo(env1, h)))::k, k1) =>
    opOf(h, l) match
      case Some(Op(_, x, c, body, _)) =>
        val newEnv = env1 + (x -> eval(v, env)) + (c -> KntV(k1 ++ List(f)))
        PState(body, newEnv, k)
      case None =>
        EState(Do(l, v), env, k, k1 ++ List(f))

def drive(s: State): State =
  println(s)
  if isDone(s) then s else drive(step(s))

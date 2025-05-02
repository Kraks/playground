package continuation.handler.cesk

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

type Addr = Int
type Env = Map[String, Addr]
type Store = Map[Addr, RValue]

enum State:
  case PState(e: Comp, env: Env, st: Store, k: Cont)
  case EState(e: Comp, env: Env, st: Store, k1: Cont, k2: Cont)

import RValue.*
import State.*

def inject(e: Comp): State = PState(e, Map.empty, Map.empty, List(Frame(List(), HanClo(Map.empty, Return("x", Ret(Var("x")))))))

def prim(op: String, v1: RValue, v2: RValue): RValue = (v1, v2) match
  case (IntV(i), IntV(j)) => op match
    case "+" => IntV(i+j)
    case "-" => IntV(i-j)
    case "*" => IntV(i*j)
    case "/" => IntV(i/j)

def eval(v: Value, env: Env, st: Store): RValue = v match
  case Num(i) => IntV(i)
  case Var(x) => st(env(x))
  case Lam(x, e) => CloV(x, e, env)
  case Prim(op, v1, v2) => prim(op, eval(v1, env, st), eval(v2, env, st))

def isDone(s: State): Boolean = s match
  case PState(Ret(_), _, _, Nil) => true
  case _ => false

def extract(s: State): RValue = s match
  case PState(Ret(v), env, st, Nil) => eval(v, env, st)

def alloc(st: Store): Addr = st.size

def step(s: State): State = s match
  case PState(App(v1, v2), env, st, k) =>
    eval(v1, env, st) match
      case CloV(x, e, env1) =>
        val addr = alloc(st)
        PState(e, env1 + (x -> addr), st + (addr -> eval(v2, env, st)), k)
      case KntV(k1) => PState(Ret(v2), env, st, k1 ++ k)
  case PState(Let(x, rhs, body), env, st, Frame(p, h)::k) =>
    PState(rhs, env, st, Frame(PFrame(x, body, env)::p, h)::k)
  case PState(Handle(e, h), env, st, k) =>
    PState(e, env, st, Frame(List(), HanClo(env, h))::k)
  case PState(Ret(v), env, st, Frame(PFrame(x, e, env1)::pf, h)::k) =>
    val addr = alloc(st)
    PState(e, env1 + (x -> addr), st + (addr -> eval(v, env, st)), Frame(pf, h)::k)
  case PState(Ret(v), env, st, Frame(List(), HanClo(env1, h))::k) =>
    val Return(x, e) = retOf(h)
    val addr = alloc(st)
    PState(e, env1 + (x -> addr), st + (addr -> eval(v, env, st)), k)
  case PState(Do(l, v), env, st, k) =>
    EState(Do(l, v), env, st, k, Nil)
  case EState(Do(l, v), env, st, (f@Frame(pf, HanClo(env1, h)))::k, k1) =>
    opOf(h, l) match
      case Some(Op(_, x, c, body, _)) =>
        val addr1 = alloc(st)
        val addr2 = alloc(st) + 1
        val newEnv = env1 + (x -> addr1) + (c -> addr2)
        val newSt = st + (addr1 -> eval(v, env, st)) + (addr2 -> KntV(k1 ++ List(f)))
        PState(body, newEnv, newSt, k)
      case None =>
        EState(Do(l, v), env, st, k, k1 ++ List(f))

def drive(s: State): State =
  println(s)
  if isDone(s) then s else drive(step(s))
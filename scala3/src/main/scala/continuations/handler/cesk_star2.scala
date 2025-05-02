package continuation.handler.ceskStar2

// Note: in this variant, we have continuations instead of
// continuation addresses (vs cesk_star.scala) in a state.

import continuation.handler.syntax.*
import Value.*
import Comp.*
import Handler.*

// Runtime structures

enum RValue:
  case IntV(i: Int)
  case CloV(x: String, e: Comp, env: Env)
  case KntV(k: Cont)
  case PKntV(k: PCont)

// XXX: could make handler a proper value
case class HanClo(env: Env, h: Handler)

enum Cont:
  case MtK
  case Frame(pureK: Addr/*for PCont*/, h: HanClo, k: Addr/*for Cont*/)
enum PCont:
  case MtPK
  case PFrame(x: String, e: Comp, env: Env, k: Addr/*for PCont*/)

enum Addr:
  case BAddr(a: Int)
  case KAddr(a: Int)
type Env = Map[String, Addr]
type Store = Map[Addr, RValue]

enum State:
  case PState(e: Comp, env: Env, st: Store, k: Cont)
  case EState(e: Comp, env: Env, st: Store, k1: Cont, k2: Cont)

import RValue.*
import Cont.*
import PCont.*
import State.*
import Addr.*

val mtPKAddr = KAddr(0)
val mtKAddr = KAddr(1)
val st0 = Map(mtPKAddr -> PKntV(MtPK), mtKAddr -> KntV(MtK))

def inject(e: Comp): State =
  PState(Handle(e, Return("x", Ret(Var("x")))), Map.empty, st0, MtK)

def kappend(k1: Cont, k2: Cont, st: Store): (Cont, Store) = k1 match
  case MtK => (k2, st)
  case Frame(p, h, kaddr) =>
    val KntV(ks) = st(kaddr)
    val (k3, newSt) = kappend(ks, k2, st)
    val kaddr1 = kalloc(newSt)
    val newSt1 = newSt + (kaddr1 -> KntV(k3))
    (Frame(p, h, kaddr1), newSt1)

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

def addrOf(v: Value, env: Env): Addr = v match
  case Var(x) => env(x)

def isDone(s: State): Boolean = s match
  case PState(Ret(_), _, st, MtK) => true
  case _ => false

def extract(s: State): RValue = s match
  case PState(Ret(v), env, st, MtK) => eval(v, env, st)

def kalloc(st: Store): Addr = KAddr(st.size)
def balloc(st: Store): Addr = BAddr(st.size)

def step(s: State): State = s match
  case PState(App(v1, v2), env, st, k) =>
    eval(v1, env, st) match
      case CloV(x, e, env1) =>
        val addr = balloc(st)
        PState(e, env1 + (x -> addr), st + (addr -> eval(v2, env, st)), k)
      case KntV(k1) =>
        val (newK, newSt) = kappend(k1, k, st)
        PState(Ret(v2), env, newSt, newK)
  case PState(Let(x, rhs, body), env, st, Frame(p, h, k)) =>
    val pf = PKntV(PFrame(x, body, env, p))
    val pa = kalloc(st)
    val st1 = st + (pa -> pf)
    PState(rhs, env, st1, Frame(pa, h, k))
  case PState(Handle(e, h), env, st, k) =>
    val ka = kalloc(st)
    PState(e, env, st + (ka -> KntV(k)), Frame(mtPKAddr, HanClo(env, h), ka))
  case PState(Ret(v), env, st, Frame(pa, ho, krest)) =>
    st(pa) match
      case PKntV(PFrame(x, e, env1, p1)) =>
        val baddr = balloc(st)
        val newSt = st + (baddr -> eval(v, env, st))
        PState(e, env1 + (x -> baddr), newSt, Frame(p1, ho, krest))
      case PKntV(MtPK) =>
        val HanClo(env1, h) = ho
        val Return(x, e) = retOf(h)
        val addr = balloc(st)
        val KntV(k) = st(krest)
        PState(e, env1 + (x -> addr), st + (addr -> eval(v, env, st)), k)
  case PState(Do(l, v), env, st, k) =>
    EState(Do(l, v), env, st, k, MtK)
  case EState(Do(l, v), env, st, f@Frame(pf, HanClo(env1, h), k), k2) =>
    val KntV(kk) = st(k)
    opOf(h, l) match
      case Some(Op(_, x, c, body, _)) =>
        val baddr = balloc(st)
        val st1 = st + (baddr -> eval(v, env, st))
        val (newK, st2) = kappend(k2, Frame(pf, HanClo(env1, h), mtKAddr), st1)
        println("newK: " + newK)
        val kaddr = kalloc(st2)
        val st3 = st2 + (kaddr -> KntV(newK))
        val newEnv = env1 + (x -> baddr) + (c -> kaddr)
        PState(body, newEnv, st3, kk)
      case None =>
        val (newK, st1) = kappend(k2, Frame(pf, HanClo(env1, h), mtKAddr), st)
        EState(Do(l, v), env, st1, kk, newK)

def drive(s: State, i: Int): State =
  if (i <= 0) s
  else
    println(s)
    if isDone(s) then s else drive(step(s), i-1)

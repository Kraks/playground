package continuation.handler.ceskStar

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
  case PState(e: Comp, env: Env, st: Store, k: Addr)
  case EState(e: Comp, env: Env, st: Store, k1: Addr, k2: Addr)

import RValue.*
import Cont.*
import PCont.*
import State.*
import Addr.*

def kappend(k1: Addr, k2: Addr, st: Store): (Addr, Store) =
  st(k1) match
    case KntV(MtK) => (k2, st)
    case KntV(Frame(p, h, k)) =>
      val (lastAddr, newSt) = kappend(k, k2, st)
      val newAddr = kalloc(newSt)
      val newSt1 = newSt + (newAddr -> KntV(Frame(p, h, lastAddr)))
      (newAddr, newSt1)

val mtPKAddr = KAddr(0)
val mtKAddr = KAddr(1)
/*
def inject(e: Comp): State =
  val kaddr2 = KAddr(2)
  val cont0 = Frame(mtPKAddr, HanClo(Map.empty, Return("x", Ret(Var("x")))), mtKAddr)
  val st0 = Map(mtPKAddr -> PKntV(MtPK), mtKAddr -> KntV(MtK), kaddr2 -> KntV(cont0))
  PState(e, Map.empty, st0, kaddr2)
*/

def inject(e: Comp): State =
  val st0 = Map(mtPKAddr -> PKntV(MtPK), mtKAddr -> KntV(MtK))
  PState(Handle(e, Return("x", Ret(Var("x")))), Map.empty, st0, mtKAddr)

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
  case PState(Ret(_), _, st, kaddr) if st(kaddr) == KntV(MtK) => true
  case _ => false

def extract(s: State): RValue = s match
  case PState(Ret(v), env, st, kaddr) if st(kaddr) == KntV(MtK) => eval(v, env, st)

def kalloc(st: Store): Addr = KAddr(st.size)
def balloc(st: Store): Addr = BAddr(st.size)

def step(s: State): State = s match
  case PState(App(v1, v2), env, st, kaddr) =>
    eval(v1, env, st) match
      case CloV(x, e, env1) =>
        val addr = balloc(st)
        PState(e, env1 + (x -> addr), st + (addr -> eval(v2, env, st)), kaddr)
      case KntV(k1) =>
        val (newKaddr, newSt) = kappend(addrOf(v1, env), kaddr, st)
        PState(Ret(v2), env, newSt, newKaddr)
  case PState(Let(x, rhs, body), env, st, kaddr) =>
    val KntV(Frame(p, h, k)) = st(kaddr)
    val pf = PKntV(PFrame(x, body, env, p))
    val pa = kalloc(st)
    val st1 = st + (pa -> pf)
    val kf = KntV(Frame(pa, h, k))
    val ka = kalloc(st1)
    PState(rhs, env, st1 + (ka -> kf), ka)
  case PState(Handle(e, h), env, st, kaddr) =>
    val ka = kalloc(st)
    val kf = KntV(Frame(mtPKAddr, HanClo(env, h), kaddr))
    PState(e, env, st + (ka -> kf), ka)
  case PState(Ret(v), env, st, kaddr) =>
    val KntV(Frame(pa, ho, krest)) = st(kaddr)
    st(pa) match
      case PKntV(PFrame(x, e, env1, p1)) =>
        val baddr = balloc(st)
        val newSt = st + (baddr -> eval(v, env, st))
        val newKaddr = kalloc(newSt)
        val newSt1 = newSt + (newKaddr -> KntV(Frame(p1, ho, krest)))
        PState(e, env1 + (x -> baddr), newSt1, newKaddr)
      case PKntV(MtPK) =>
        val HanClo(env1, h) = ho
        val Return(x, e) = retOf(h)
        val addr = balloc(st)
        PState(e, env1 + (x -> addr), st + (addr -> eval(v, env, st)), krest)
  case PState(Do(l, v), env, st, kaddr) =>
    EState(Do(l, v), env, st, kaddr, mtKAddr)
  case EState(Do(l, v), env, st, kaddr, kaddr1) =>
    val KntV(f@Frame(pf, HanClo(env1, h), k)) = st(kaddr)
    opOf(h, l) match
      case Some(Op(_, x, c, body, _)) =>
        val baddr = balloc(st)
        val st1 = st + (baddr -> eval(v, env, st))
        val kaddr2 = kalloc(st1)
        val st2 = st1 + (kaddr2 -> KntV(Frame(pf, HanClo(env1, h), mtKAddr)))
        val (kaddr3, newSt) = kappend(kaddr1, kaddr2, st2)
        val newEnv = env1 + (x -> baddr) + (c -> kaddr3)
        PState(body, newEnv, newSt, k)
      case None =>
        val kaddr2 = kalloc(st)
        val st1 = st + (kaddr2 -> KntV(Frame(pf, HanClo(env1, h), mtKAddr)))
        val (kaddr3, st3) = kappend(kaddr1, kaddr2, st1)
        EState(Do(l, v), env, st3, k, kaddr3)

def drive(s: State, i: Int): State =
  if (i <= 0) s
  else
    println(s)
    if isDone(s) then s else drive(step(s), i-1)

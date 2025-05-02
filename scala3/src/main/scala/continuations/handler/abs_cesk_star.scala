package continuation.handler.absCeskStar

import continuation.handler.syntax.*
import Value.*
import Comp.*
import Handler.*

enum RValue:
  case IntV()
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
  case BAddr(x: String) // 0-cfa-like monovariant address
  case KAddr(e: Comp)   // monovariant continuation address where e is the target expression
  case PKAddr(e: Comp)   // monovariant continuation address where e is the target expression

type AValue = Set[RValue]

type Env = Map[String, Addr]
type Store = Map[Addr, AValue]

enum State:
  case PState(e: Comp, env: Env, st: Store, k: Addr)
  case EState(e: Comp, env: Env, st: Store, k1: Addr, k2: Addr)

import RValue.*
import Cont.*
import PCont.*
import State.*
import Addr.*

trait Lattice[T]:
  def bot: T
  def top: T
  extension (x: T)
    def ⊑(y: T): Boolean
    def ⊔(y: T): T
    def ⊓(y: T): T

given AbsValueLattice: Lattice[AValue] with
  def bot: AValue = Set()
  def top: AValue = ???
  extension (x: AValue)
    def ⊑(y: AValue): Boolean = x.subsetOf(y)
    def ⊔(y: AValue): AValue = x ++ y
    def ⊓(y: AValue): AValue = x.intersect(y)

given MapLattice[K, V: Lattice]: Lattice[Map[K, V]] with
  val lv: Lattice[V] = summon[Lattice[V]]
  def bot: Map[K, V] = Map[K, V]()
  def top: Map[K, V] = throw new RuntimeException("No representation of top map")
  extension (m1: Map[K, V])
    def ⊑(m2: Map[K, V]): Boolean =
      m1.forall { case (k, v) => v ⊑ m2.getOrElse(k, lv.bot) }
    def ⊔(m2: Map[K, V]): Map[K, V] =
      m1.foldLeft(m2) { case (m, (k, v)) => m + (k -> v ⊔ m.getOrElse(k, lv.bot)) }
    def ⊓(m2: Map[K, V]): Map[K, V] =
      m1.keySet.intersect(m2.keySet).foldLeft(Map[K,V]()) {
        case (m, k) => m + (k -> m1(k) ⊓ m2(k))
      }

extension (st: Store)
  def apply(a: Addr): AValue = st.getOrElse(a, AbsValueLattice.bot)
  def +(av: (Addr, AValue)): Store = st ⊔ Map(av._1 -> av._2)

def eval(v: Value, env: Env, st: Store): AValue = v match
  case Num(i) => Set(IntV())
  case Var(x) => st(env(x))
  case Lam(x, e) => Set(CloV(x, e, env))
  case Prim(op, v1, v2) => Set(IntV())

def prim(op: String, v1: RValue, v2: RValue): RValue = IntV()

def kalloc(e: Comp): Addr = KAddr(e)
def pkalloc(e: Comp): Addr = KAddr(e)
def balloc(x: String): Addr = BAddr(x)

def addrOf(v: Value, env: Env): Addr = v match
  case Var(x) => env(x)

// In the concrete setting, the continuation is a linked list
// of frames, and the last element of each frame is an address
// pointing to next frame. It is straightforward to append.

// In the abstract setting, an address points to a set of frames,
// and the last element of each frame further points to a set of frames...
// So starting from an address, we have a tree of frames. Each path
// from this tree represents a concrete continuation.
// So to append, we need to append k2 to every leaf frame.
// All intermediate frames need to be reallocated.

// Question: what's the allocation for intermediate address?

/*
def kappend(k1: Addr, k2: Addr, st: Store): (Addr, Store) =
  st(k1) match
    case KntV(MtK) => (k2, st)
    case KntV(Frame(p, h, k)) =>
      val (lastAddr, newSt) = kappend(k, k2, st)
      val newAddr = kalloc(newSt)
      val newSt1 = newSt + (newAddr -> KntV(Frame(p, h, lastAddr)))
      (newAddr, newSt1)
*/

// Note: use null as a special halting address
val mtPKAddr = PKAddr(null)
val mtKAddr = KAddr(null)
def inject(e: Comp): State =
  val st0 = Map(mtPKAddr -> Set(PKntV(MtPK)), mtKAddr -> Set(KntV(MtK)))
  PState(Handle(e, Return("x", Ret(Var("x")))), Map.empty, st0, mtKAddr)

def step(s: State): Set[State] = s match
  case PState(App(v1, v2), env, st, kaddr) =>
    for {
      v1 <- eval(v1, env, st)
    } yield v1 match
      case CloV(x, e, env1) =>
        val addr = balloc(x)
        PState(e, env1 + (x -> addr), st + (addr -> eval(v2, env, st)), kaddr)
      case KntV(k1) =>
        val (newKaddr, newSt) = ??? //kappend(addrOf(v1, env), kaddr, st)
        PState(Ret(v2), env, newSt, newKaddr)
  /*
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
  */

def drive(todo: List[State], seen: Set[State]): Set[State] = todo match
  case Nil ⇒ seen
  case hd::tl if seen.contains(hd) ⇒ drive(tl, seen)
  case hd::tl ⇒ drive(step(hd).toList ++ tl, seen + hd)

def analyze(e: Comp): Set[State] = drive(List(inject(e)), Set())
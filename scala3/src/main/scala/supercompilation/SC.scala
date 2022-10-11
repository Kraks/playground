package supercompilation

// Code for Bolingbroke & Peyton Jones "Supercompilation by Evaluation"

import collection.mutable.ListBuffer
import collection.mutable.HashMap

var tagCount: Int = 0

type Tag = Int

trait Expr {
  val tag: Tag = try tagCount finally { tagCount += 1 }
}
trait Value extends Expr
case class Lit(v: Int) extends Value
case class Lam(x: String, e: Expr) extends Value
case class Cons(c: String, vs: List[Var]) extends Value

case class Var(x: String) extends Expr
case class App(e1: Expr, v: Var) extends Expr
case class BinOp(op: String, e1: Expr, e2: Expr) extends Expr
case class Let(x: String, rhs: Expr, body: Expr) extends Expr
case class Case(e: Expr, ps: List[(Pattern, Expr)]) extends Expr

// Currying App with multiple arguments
def apps(e1: Expr, vs: List[Var]): Expr = vs.drop(1).foldLeft(App(e1, vs(0)))(App(_, _))

trait Pattern
case class LitPat(v: Int) extends Pattern
case class ConsPat(c: String, vs: List[Var]) extends Pattern

trait Frame(tag: Tag) {
  def getTag: Tag = tag
}
case class UpdateK(x: String, tag: Tag) extends Frame(tag)
case class AppK(arg: Var, tag: Tag) extends Frame(tag)
case class CaseK(ps: List[(Pattern, Expr)], tag: Tag) extends Frame(tag)
case class BinOpRhsK(op: String, rhs: Expr, tag: Tag) extends Frame(tag)
case class BinOpLhsK(op: String, lhs: Value, tag: Tag) extends Frame(tag)

type Heap = Map[String, Expr]
type Stack = List[Frame]

val mtHistory: History = List[State]()
val mtHeap: Heap = Map[String, Expr]()

def heapTagBag(h: Heap): List[Tag] = h.values.map(_.tag).toList
def stackTagBag(s: Stack): List[Tag] = s.map(_.getTag).toList
case class State(h: Heap, e: Expr, s: Stack) {
  def tagBag: List[Tag] =
    List(e.tag * 2) ++
    heapTagBag(h).map(_ * 3) ++
    stackTagBag(s).map(_ * 5)
  def <=(other: State): Boolean =
    val t1 = this.tagBag
    val t2 = other.tagBag
    t1.toSet == t2.toSet && t1.size <= t2.size
}
def inject(e: Expr): State = State(mtHeap, e, List())

type History = List[State]

trait TermRes
case class Stop() extends TermRes
case class Continue(h: History) extends TermRes

case class Promise(name: Var, fvs: List[Var], s: State)

// the "ScpM" state monad using native effects
var count: Int = 0
val promises: ListBuffer[Promise] = new ListBuffer[Promise]()
val bindings: HashMap[Var, Expr] = new HashMap[Var, Expr]()

def getPromises: List[Promise] = promises.toList
def putPromise(p: Promise): Unit = promises.addOne(p)
def freshName(x: String = "x"): Var = try Var(x + count) finally { count += 1 }
def bind(v: Var, e: Expr): Unit = bindings(v) = e
def reset(): Unit = {
  count = 0
  promises.clear()
  bindings.clear()
}

def freeVars(s: State): List[Var] = ???

def rebuild(s: State): Expr = ???

def primop(op: String, v1: Value, v2: Value): Value =
  val Lit(n1) = v1
  val Lit(n2) = v2
  op match
    case "+" => Lit(n1 + n2)
    case "-" => Lit(n1 - n2)
    case "*" => Lit(n1 * n2)
    case "/" => Lit(n1 / n2)

def consMatch(ps: List[(Pattern, Expr)], v: Cons): Option[(Pattern, Expr)] =
  val Cons(c, _) = v
  ps match {
    case Nil => None
    case (p@(ConsPat(`c`, xs), e))::ps => Some(p)
    case _::ps => consMatch(ps, v)
  }

def litMatch(ps: List[(Pattern, Expr)], v: Lit): Option[Expr] =
  val Lit(n) = v
  ps match {
    case Nil => None
    case (LitPat(`n`), e)::ps => Some(e)
    case _::ps => litMatch(ps, v)
  }

def step(s: State): Option[State] = s match
  case State(h, e@Var(x), k) if h.contains(x) =>
    Some(State(h - x, h(x), UpdateK(x, e.tag)::k))
  case State(h, v, UpdateK(x, _)::k) if v.isInstanceOf[Value] =>
    Some(State(h + (x -> v), v, k))
  case State(h, a@App(e, x), k) =>
    Some(State(h, e, AppK(x, a.tag)::k))
  case State(h, Lam(x, e), AppK(y, _)::k) =>
    // Note: this is a bit different from the paper's operational semantics where asumes x and y are equal
    Some(State(h + (x -> y), e, k))
  case State(h, e@BinOp(op, e1, e2), k) =>
    Some(State(h, e1, BinOpRhsK(op, e2, e.tag)::k))
  case State(h, v, BinOpRhsK(op, e, t)::k) if v.isInstanceOf[Value] =>
    Some(State(h, e, BinOpLhsK(op, v.asInstanceOf[Value], t)::k))
  case State(h, v2, BinOpLhsK(op, v1, _)::k) if v2.isInstanceOf[Value] =>
    Some(State(h, primop(op, v1, v2.asInstanceOf[Value]), k))
  case State(h, c@Case(e, ps), k) =>
    Some(State(h, e, CaseK(ps, c.tag)::k))
  case State(h, v@Cons(c, xs), CaseK(ps, _)::k) =>
    consMatch(ps, v) match {
      case Some((ConsPat(_, ys), e)) =>
        Some(State(ys.zip(xs).foldLeft(h) { case (h, (x, v)) => h + (x.x -> v) }, e, k))
      case None => None
    }
  case State(h, v@Lit(n), CaseK(ps, _)::k) =>
    litMatch(ps, v) match {
      case Some(e) => Some(State(h, e, k))
      case None => None
    }
  case State(h, Let(x, rhs, body), k) =>
    Some(State(h + (x -> rhs), body, k))
  case _ => None

def reduce(s: State): State = 
  def intermediate(s: State): Boolean = !s.e.isInstanceOf[Var]
  def drive(h: History, s: State): State =
    step(s) match
      case Some(s1) => 
        if (intermediate(s1)) drive(h, s1)
        else terminate(h, s1) match
          case Stop() => s1 
          case Continue(h1) => drive(h1, s1)
      case None => s
  drive(mtHistory, s)

def split(f: State => Expr): State => Expr = ???

def terminate(h: History, s: State): TermRes =
  if (h.exists(_ <= s)) Stop()
  else Continue(s::h)

def stateMatch(s1: State, s2: State): Option[Map[Var, Var]] = ???

def memo(f: State => Expr)(s: State): Expr = 
  val ps = getPromises
  val res = 
    for p <- ps
        Some(rn) <- List(stateMatch(p.s, s))
    yield apps(p.name, p.fvs.map(rn))
  if (res.nonEmpty) res(0)
  else {
    val x = freshName()
    
    ???
  }

def sc(h: History, s: State): Expr = {
  def scHelper(h: History, s: State): Expr = terminate(h, s) match
    case Continue(h0) => split(sc(h0, _))(reduce(s))
    case Stop() => split(sc(h, _))(s)
  memo(scHelper(h, _))(s)
}

def start(e: Expr): Expr = {
  reset()
  sc(mtHistory, inject(e))
}



object Test {
  def main(args: Array[String]): Unit = {
    val e = App(Lam("x", BinOp("+", Var("x"), Lit(1))), Var("y"))
    println(e.tag)
    println(e.e1.tag)
  }
}

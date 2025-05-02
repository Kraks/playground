package supercompilation

// Code for Bolingbroke & Peyton Jones "Supercompilation by Evaluation"

import collection.mutable.ListBuffer
import collection.mutable.HashMap

var tagCount: Int = 0

trait Expr {
  val tag: Int = try tagCount finally { tagCount += 1 }
}
trait Value

case class Var(x: String) extends Expr
case class Lit(v: Any) extends Expr with Value
case class Lam(x: String, e: Expr) extends Expr with Value
case class Cons(c: String, vs: List[Var]) extends Expr with Value
case class App(e1: Expr, v: Var) extends Expr
case class BinOp(op: String, e1: Expr, e2: Expr) extends Expr
case class Let(x: String, rhs: Expr, body: Expr) extends Expr
case class Case(e: Expr, ps: List[(Pattern, Expr)]) extends Expr

trait Pattern
case class LitPat(v: Any) extends Pattern 
case class ConsPat(c: String, vs: List[Var]) extends Pattern 

trait Frame
case class UpdateK(x: Var) extends Frame
case class AppK(arg: Var) extends Frame
case class CaseK(ps: List[(Pattern, Expr)]) extends Frame
case class BinOpRhsK(rhs: Expr) extends Frame
case class BinOpLhsK(lhs: Value) extends Frame

type Heap = Map[String, Expr]
type Stack = List[Frame]

val mtHistory: History = List[State]()
val mtHeap: Heap = Map[String, Expr]()

case class State(h: Heap, e: Expr, s: Stack)
def inject(e: Expr): State = State(mtHeap, e, List())

type History = List[State]

trait TermRes
case class Stop() extends TermRes 
case class Continue(h: History) extends TermRes

case class Promise(name: Var, fvs: List[Var], s: State)

// the "ScpM" monad
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

def reduce(s: State): State = ???

def split(f: State => Expr): State => Expr = ???

def terminate(h: History, s: State): TermRes = ???

def memo(f: State => Expr): State => Expr = ???

def stateMatch(s1: State, s2: State): Option[Var => Var] = ???

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
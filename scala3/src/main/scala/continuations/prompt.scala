// from A monadic framework for delimited continuations, Dyvbig et al.
package continuation.prompt

enum Expr:
  case Var(x: String)
  case Lit(i: Int)
  case BinOp(op: String, e1: Expr, e2: Expr)
  case Cond(e1: Expr, e2: Expr, e3: Expr)
  case Lam(x: String, e: Expr)
  case App(e1: Expr, e2: Expr)
  case NewPrompt()
  case PushPrompt(pt: Expr, e: Expr)
  case WithSubCont(pt: Expr, f: Expr)
  case PushSubCont(k: Expr, e: Expr)

import Expr._

/*
  (\p. 2 + pushPrompt p
          (if withSubCont p (\k. (pushSubCont k #f) + (pushSubCont k #t))
           then 3
           else 4))
  (newPrompt)
->
  2 + ((pushSubCont k #f) + (pushSubCont k #t))
  where k = if [] then 3 else 4
->
  9
*/
val example = App(Lam("p",
  BinOp("+", Lit(2),
    PushPrompt(Var("p"),
      Cond(WithSubCont(Var("p"), Lam("k",
        BinOp("+", PushSubCont(Var("k"), Lit(0)), PushSubCont(Var("k"), Lit(1))))
      ),
      Lit(3),
      Lit(4))))),
  NewPrompt())

def withTopPrompt(e: Expr): Expr =
  App(Lam("p0", PushPrompt(Var("p0"), e)), NewPrompt())

// within injected body e:
def withCont(e: Expr): Expr =
  WithSubCont(Var("p0"), Lam("k", PushPrompt(Var("p0"), App(e, Var("k")))))

def reifyA(k: Expr): Expr =
  Lam("v", abort(PushSubCont(k, Var("v"))))
// Lam("v", withCont(Lam("_", PushSubCont(k, Var("v")))))
// Lam("v", WithSubCont(Var("p0"),
//  Lam("k1", PushPrompt(Var("p0"),
//   PushSubCont(k, Var("v"))))))

def abort(e: Expr): Expr = withCont(Lam("_", e))
// WithSubCont(Var("p0"), Lam("k", PushPrompt(Var("p0"), e)))

def calcc: Expr =
  Lam("f", withCont(Lam("k",
    PushSubCont(Var("k"), App(Var("f"), reifyA(Var("k")))))))

// Felleisen's C operator aborts the current continuation
// when it captures the continuation
def C: Expr =
  Lam("f", withCont(Lam("k", App(Var("f"), reifyA(Var("k"))))))

def reify(k: Expr): Expr =
  Lam("v", PushSubCont(k, Var("v")))

// Felleisen's F operator, the captured continuation is composable
def F: Expr =
  Lam("f", withCont(Lam("k", App(Var("f"), reify(Var("k"))))))

def reifyP(p: Expr, k: Expr): Expr =
  Lam("v", PushPrompt(p, PushSubCont(k, Var("v"))))

// Section 3.3

enum Value:
  case NumV(i: Int)
  case CloV(x: String, e: Expr, env: Env)
  case PromptV(p: Int)
  case ContV(m: MCont)
import Value.*

enum DCont:
  case HaltK
  case ArgK(d: DCont, e: Expr)
  case FunK(v: CloV, d: DCont)
  case PushPromptK(d: DCont, e: Expr)
  case PushSubContK(d: DCont, e: Expr)
  case WithSubContK1(d: DCont, e: Expr)
  case WithSubContK2(p: PromptV, d: DCont)
  case CondK(d: DCont, thn: Expr, els: Expr)
  case BinOpK1(op: String, d: DCont, e: Expr)
  case BinOpK2(op: String, v: Value, d: DCont)
import DCont.*

type MCont = List[PromptV | DCont]

type Env = Map[String, Value]

case class State(e: Expr|Value, s: Env, d: DCont, m: MCont, p: Int)

def step: State => State =
  // Searching for a redex
  case State(App(e1, e2), s, d, m, q) =>
    State(e1, s, ArgK(d, e2), m, q)
  case State(v: CloV, s, ArgK(d, e), m, q) =>
    State(e, s, FunK(v, d), m, q)
  case State(PushPrompt(e1, e2), s, d, m, q) =>
    State(e1, s, PushPromptK(d, e2), m, q)
  case State(WithSubCont(e1, e2), s, d, m, q) =>
    State(e1, s, WithSubContK1(d, e2), m, q)
  case State(p: PromptV, s, WithSubContK1(d, e), m, q) =>
    State(e, s, WithSubContK2(p, d), m, q)
  case State(PushSubCont(k, e), s, d, m, q) =>
    State(k, s, PushSubContK(d, e), m, q)
  case State(Cond(e1, e2, e3), s, d, m, q) =>
    State(e1, s, CondK(d, e2, e3), m, q)
  case State(BinOp(op, e1, e2), s, d, m, q) =>
    State(e1, s, BinOpK1(op, d, e2), m, q)
  case State(v: NumV, s, BinOpK1(op, d, e), m, q) =>
    State(e, s, BinOpK2(op, v, d), m, q)
  // Atomic expressions
  case State(Lit(i), s, d, m, q) =>
    State(NumV(i), s, d, m, q)
  case State(Lam(x, e), s, d, m, q) =>
    State(CloV(x, e, s), s, d, m, q)
  case State(NewPrompt(), s, d, m, q) =>
    State(PromptV(q), s, d, m, q+1)
  case State(Var(x), s, d, m, q) =>
    State(s(x), s, d, m, q)
  // Executing a redex
  case State(v: Value, s, FunK(CloV(x, e, s1), d), m, q) =>
    State(e, s1 + (x -> v), d, m, q)
  case State(p: PromptV, s, PushPromptK(d, e), m, q) =>
    State(e, s, HaltK, p::d::m, q)
  case State(CloV(x, e, s1), s, WithSubContK2(p, d), m, q) =>
    val i = m.indexOf(p)
    State(e, s1 + (x -> ContV(d::m.take(i))), HaltK, m.drop(i+1), q)
  case State(ContV(m1), s, PushSubContK(d, e), m, q) =>
    State(e, s, HaltK, m1++(d::m), q)
  case State(NumV(i), s, CondK(d, thn, els), m, q) =>
    State(if i == 0 then els else thn, s, d, m, q)
  case State(NumV(i), s, BinOpK2("+", NumV(j), d), m, q) =>
    State(NumV(i+j), s, d, m, q)
  // Returning a value
  case State(v: Value, s, HaltK, PromptV(_)::m, q) =>
    State(v, s, HaltK, m, q)
  case State(v: Value, s, HaltK, (k: DCont)::m, q) =>
    State(v, s, k, m, q)

def isFinal(s: State): Boolean = s match
  case State(_: Value, _, HaltK, Nil, _) => true
  case _ => false

def drive(e: State): State = if isFinal(e) then e else drive(step(e))

@main def testStateMachine: Unit = {
  println("testStateMachine")
  println(drive(State(example, Map(), HaltK, Nil, 0)))
}
package continuation.handler.syntax

// Syntax

enum Value:
  case Num(i: Int)
  case Var(x: String)
  case Lam(x: String, e: Comp)
  case Prim(op: String, v1: Value, v2: Value)

enum Comp:
  case App(v1: Value, v2: Value)
  case Ret(v: Value)
  case Let(x: String, rhs: Comp, body: Comp)
  case Do(l: String, v: Value)
  case Handle(e: Comp, h: Handler)

enum Handler:
  case Return(x: String, e: Comp)
  case Op(l: String, x: String, k: String, body: Comp, h: Handler)

import Value.*
import Comp.*
import Handler.*

def retOf(h: Handler): Return =
  h match
    case Return(x, e) => Return(x, e)
    case Op(_, _, _, _, h1) => retOf(h1)

def opOf(h: Handler, l: String): Option[Op] =
  h match
    case Return(_, _) => None
    case Op(`l`, x, k, body, _) => Some(Op(l, x, k, body, h))
    case Op(l1, _, _, _, h1) => opOf(h1, l)

/*
handle
  let x = do tw 0
  ret (x * 2)
with
  case tw _ k =>
    let t1 = k 2
    let t2 = k 3
    ret (t1 + t2)
  return r => ret r
*/
val p1 = Handle(
  Let("x", Do("tw", Num(0)),
    Ret(Prim("*", Var("x"), Num(2)))),
  Op("tw", "_", "k",
    Let("t1", App(Var("k"), Num(2)),
    Let("t2", App(Var("k"), Num(3)),
    Ret(Prim("+", Var("t1"), Var("t2"))))),
    Return("r", Ret(Var("r")))))

/*
handle
  let x = do tw 0
  ret (x * 2)
with
  case tw _ k =>
    let t1 = k 2
    ret t1
  return r => ret r
*/
val p2 = Handle(
  Let("x", Do("tw", Num(0)),
    Ret(Prim("*", Var("x"), Num(2)))),
  Op("tw", "_", "k",
    Let("t1", App(Var("k"), Num(2)),
    Ret(Var("t1"))),
    Return("r", Ret(Var("r")))))

/*
handle
  let x = do eff 42
  let y = do eff 100
  ret (x + y)
with
  case eff x k =>
    let r = k (x + 1)
    ret r
  return r => ret r
*/
val p3 = Handle(
  Let("x", Do("eff", Num(42)),
  Let("y", Do("eff", Num(100)),
  Ret(Prim("+", Var("x"), Var("y"))))),
  Op("eff", "x", "k",
    Let("r", App(Var("k"), Prim("+", Var("x"), Num(1))),
      Ret(Var("r"))),
    Return("r", Ret(Var("r")))))

/*
handle
  let x = do add1 10
  let y = do mul2 20
  ret (x + y)
with
  case add1 x k =>
    let r = k (x + 1)
    ret r
  case mul2 x k =>
    let r = k (x * 2)
    ret r
  return r => ret r
*/
val p4 = Handle(
  Let("x", Do("add1", Num(10)),
  Let("y", Do("mul2", Num(20)),
  Ret(Prim("+", Var("x"), Var("y"))))),
  Op("add1", "x", "k",
    Let("r", App(Var("k"), Prim("+", Var("x"), Num(1))),
      Ret(Var("r"))),
  Op("mul2", "x", "k",
    Let("r", App(Var("k"), Prim("*", Var("x"), Num(2))),
      Ret(Var("r"))),
  Return("r", Ret(Var("r"))))))

/*
handle
  handle
    let x = do add1 10
    let y = do mul2 20
    ret (x + y)
  with
    case add1 x k =>
      let r = k (x + 1)
      ret r
    return r => ret r
with
  case mul2 x k =>
    let r = k (x * 2)
    ret r
  return r => ret r
*/
val p5 = Handle(
  Handle(
    Let("x", Do("add1", Num(10)),
    Let("y", Do("mul2", Num(20)),
    Ret(Prim("+", Var("x"), Var("y"))))),
    Op("add1", "x", "k",
      Let("r", App(Var("k"), Prim("+", Var("x"), Num(1))),
        Ret(Var("r"))),
      Return("r", Ret(Var("r"))))),
  Op("mul2", "x", "k",
    Let("r", App(Var("k"), Prim("*", Var("x"), Num(2))),
      Ret(Var("r"))),
    Return("r", Ret(Var("r")))))

/*
handle
  let x = do eff 0
  ret (x * 2)
with
  case eff x k => ret 42
  return r => ret r
*/
val p6 = Handle(
  Let("x", Do("eff", Num(0)),
    Ret(Prim("*", Var("x"), Num(2)))),
  Op("eff", "x", "k", Ret(Num(42)), Return("r", Ret(Var("r")))))
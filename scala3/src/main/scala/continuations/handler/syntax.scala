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
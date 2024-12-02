package cps.effhandler
// https://www.is.ocha.ac.jp/~asai/jpapers/ppl/fujii22.pdf

enum Term:
  case Num(n: Int)
  case Plus(e1: Term, e2: Term)
  case Var(x: String)
  case Lam(x: String, e: Term)
  case App(e1: Term, e2: Term)
  case TryWith(e1: Term, x: String, k: String, t2: Term)
  case Call(e: Term)

enum Val:
  case NumV(n: Int)
  case FunV(f: (Val, Cont, Trail, MCont) => Val)
case class Cont(k: (Val, Trail, MCont) => Val)

case object MtTrail
type Trail = MtTrail.type | Cont
case class Handler(h: (Val, Val, Cont, Trail, MCont) => Val)
type MCont = List[(Cont, Trail, Handler)]

import Term._
import Val._

val idCont: Cont = Cont((v: Val, t: Trail, m: MCont) =>
  t match
    case MtTrail => m match
      case Nil => v
      case (c, t, h) :: m => c.k(v, t, m)
    case c: Cont => c.k(v, MtTrail, m))

extension (c: Cont)
  def ::(t: Trail): Trail = t match
    case MtTrail => c
    case c1: Cont => Cont((v, t1, m) => c.k(v, c1 :: t1, m))

extension (t1: Trail)
  def ++(t2: Trail): Trail = t1 match
    case MtTrail => t2
    case c1: Cont => c1 :: t2

type Env = Map[String, Val]

def eval(e: Term, env: Env, c: Cont, t: Trail, m: MCont): Val =
  e match
    case Num(n) => c.k(NumV(n), t, m)
    case Plus(e1, e2) =>
      eval(e1, env, Cont((v1, t1, m1) =>
        eval(e2, env, Cont((v2, t2, m2) =>
          (v1, v2) match
            case (NumV(n1), NumV(n2)) => c.k(NumV(n1 + n2), t2, m2)),
        t1, m1)),
      t, m)
    case Var(x) => c.k(env(x), t, m)
    case Lam(x, e) =>
      val f = FunV((v, c, t, m) => eval(e, env + (x -> v), c, t, m))
      c.k(f, t, m)
    case App(e1, e2) =>
      eval(e1, env, Cont((v1, t1, m1) =>
        eval(e2, env, Cont((v2, t2, m2) =>
          v1 match
            case FunV(f) => f(v2, c, t2, m2)),
        t1, m1)),
      t, m)
    case TryWith(e1, x, k, e2) =>
      val h = Handler((v, vr, c1, t1, m1) => eval(e2, env + (x -> v) + (k -> vr), c1, t1, m1))
      eval(e1, env, idCont, MtTrail, (c, t, h) :: m)
    case Call(e) =>
      eval(e, env, Cont { case (v, t2, (c0, t0, h)::m0) =>
        val vrD = FunV((v1, c1, t1, m1) => c.k(v1, t2, (c1, t1, h)::m1))
        val vrS = FunV((v1, c1, t1, m1) => c.k(v1, t2 ++ (c1 :: t1), m1))
        h.h(v, vrD, c0, t0, m0)
      }, t, m)

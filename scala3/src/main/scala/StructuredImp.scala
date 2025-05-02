package structured.heap

// https://continuation.passing.style/static/papers/closedform19.pdf

import collection.mutable.HashMap

enum Expr:
  case Const(x: Int|Boolean)
  case Addr(x: String)
  case BinOp(op: String, e1: Expr, e2: Expr)
  case FieldRead(e1: Expr, e2: Expr)

enum Stmt:
  case Alloc(x: String)
  case Assign(e1: Expr, e2: Expr, e3: Expr)
  case Cond(e1: Expr, s1: Stmt, s2: Stmt)
  case While(e: Expr, s: Stmt)
  case Seq(s1: Stmt, s2: Stmt)
  case Skip()
  case Abort()

import Expr._
import Stmt._

val fieldId: HashMap[String, Int] = new HashMap()

object SyntaxSugar:
  def assert(e: Expr): Stmt =
    Cond(e, Skip(), Abort())
  def assign(x: String, e: Expr): Stmt =
    Assign(Addr(x), Const(0), e)
  def deref(x: String): Expr = FieldRead(Addr(x), Const(0))
  extension (e: Expr)
    def get(x: String): Expr = FieldRead(e, Const(fieldId(x)))

enum Ctx:
  case CRoot()
  case CThen(c: Ctx)
  case CElse(c: Ctx)
  case CFst(c: Ctx)
  case CSnd(c: Ctx)
  case CWhile(c: Ctx, n: Int)

import Ctx._

enum Loc:
  case SLoc(x: String)
  case DLoc(c: Ctx)

import Loc._

enum Value:
  case VInt(i: Int)
  case VBool(b: Boolean)
  case VLoc(l: Loc)

import Value._

type Obj = Map[Int, Value]
type Sto = Map[Loc, Obj]

def eval(σ: Sto, e: Expr): Value = e match {
  case Const(x: Int) => VInt(x)
  case Const(b: Boolean) => VBool(b)
  case BinOp("+", e1, e2) =>
    val VInt(i1) = eval(σ, e1)
    val VInt(i2) = eval(σ, e2)
    VInt(i1 + i2)
  case FieldRead(e1, e2) =>
    val VLoc(ℓ) = eval(σ, e1)
    val VInt(n) = eval(σ, e2)
    σ(ℓ)(n)
}

def iter(σ: Sto, c: Ctx, e: Expr, s: Stmt, n: Int): Sto =
  if (n == 0) σ
  else {
    val σ0 = iter(σ, c, e, s, n-1)
    val VBool(b) = eval(σ0, e)
    if (b) exec(σ0, CWhile(c, n-1), s)
    else ???
  }

def exec(σ: Sto, c: Ctx, s: Stmt): Sto = s match {
  case Alloc(x: String) =>
    σ + (SLoc(x) -> Map(0 -> VLoc(DLoc(c)))) + (DLoc(c) -> Map())
  case Assign(e1, e2, e3) =>
    val VLoc(ℓ) = eval(σ, e1)
    val VInt(n) = eval(σ, e2)
    σ + (ℓ -> (σ(ℓ) + (n -> eval(σ, e3))))
  case Cond(e, s1, s2) =>
    val VBool(b) = eval(σ, e)
    if (b) exec(σ, CThen(c), s1)
    else exec(σ, CElse(c), s2)
  case While(e, s) =>
    val n: Int = ??? // This has to be guess, rending this relational semantics non-executable
    val σ0 = iter(σ, c, e, s, n)
    val VBool(b) = eval(σ0, e)
    if (!b) σ0 else ???
  case Seq(s1, s2) => exec(exec(σ, CFst(c), s1), CSnd(c), s2)
  case Skip() => σ
}

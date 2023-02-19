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

/* Figure 4, relational big-step semantics */

object Relational {
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
}

/* Figure 5, functional semantics */

object Functional {
  extension[T](t: Option[T])
    def >>=[U](f: T => Option[U]): Option[U] = t.flatMap(f)

  def toNat(v: Value): Option[Int] = v match
    case VInt(i) => Some(i)
    case _ => None
  def toBool(v: Value): Option[Boolean] = v match
    case VBool(b) => Some(b)
    case _ => None
  def toLoc(v: Value): Option[Loc] = v match
    case VLoc(l) => Some(l)
    case _ => None

  def primEval(op: String, i1: Int, i2: Int): Int = op match {
    case "+" => i1 + i2
    case "-" => i1 - i2
    case "*" => i1 * i2
    case "/" => i1 / i2
  }
  def predEval(op: String, i1: Int, i2: Int): Boolean = op match {
    case ">" => i1 > i2
    case ">=" => i1 >= i2
    case "<=" => i1 <= i2
    case "<" => i1 < i2
    case "==" => i1 == i2
  }
  def arithOp(op: String) = Set("+", "-", "*", "/")(op)
  def predOp(op: String) = Set(">", ">=", "<=", "<", "==")(op)

  def eval(e: Expr)(σ: Sto): Option[Value] = e match {
    case Const(x: Int) => Some(VInt(x))
    case Const(b: Boolean) => Some(VBool(b))
    case Addr(x) => Some(VLoc(SLoc(x)))
    case BinOp(op, e1, e2) if arithOp(op) =>
      for {
        i1 <- eval(e1)(σ) >>= toNat
        i2 <- eval(e2)(σ) >>= toNat
      } yield VInt(primEval(op, i1, i2))
    case BinOp(op, e1, e2) if predOp(op) =>
      for {
        i1 <- eval(e1)(σ) >>= toNat
        i2 <- eval(e2)(σ) >>= toNat
      } yield VBool(predEval(op, i1, i2))
    case FieldRead(e1, e2) =>
      for {
        l <- eval(e1)(σ) >>= toLoc
        n <- eval(e2)(σ) >>= toNat
        o <- σ.get(l)
      } yield o(n)
  }

  def iter(e: Expr, s: Stmt)(σ: Sto, c: Ctx)(n: Int): Option[Sto] = {
    def aux(n: Int): Option[Sto] =
      if (n == 0) Some(σ)
      else for {
        σ0 <- aux(n-1)
        case true <- eval(e)(σ0) >>= toBool
        σ1 <- exec(s)(σ0, CWhile(c, n-1))
      } yield σ1
    aux(n)
  }

  def ♯(f: Int => Boolean): Int = {
    def g(i: Int): Int = if (f(i)) i else g(i+1)
    g(0)
  }

  def exec(s: Stmt)(σ: Sto, c: Ctx): Option[Sto] = s match {
    case Alloc(x: String) =>
      Some(σ + (SLoc(x) -> Map(0 -> VLoc(DLoc(c)))) + (DLoc(c) -> Map()))
    case Assign(e1, e2, e3) =>
      for {
        ℓ <- eval(e1)(σ) >>= toLoc
        n <- eval(e2)(σ) >>= toNat
        v <- eval(e3)(σ)
        o <- σ.get(ℓ)
      } yield σ + (ℓ -> (o + (n -> v)))
    case Cond(e, s1, s2) =>
      for {
        b <- eval(e)(σ) >>= toBool
        v <- if (b) exec(s1)(σ, CThen(c)) else exec(s2)(σ, CElse(c))
      } yield v
    case While(e, s) =>
      val n = ♯ { i =>
        val t = for {
          σ0 <- iter(e, s)(σ, c)(i)
          b <- eval(e)(σ0) >>= toBool
        } yield !b
        t.getOrElse(true)
      }
      iter(e, s)(σ, c)(n)
    case Seq(s1, s2) =>
      for {
        σ0 <- exec(s1)(σ, CFst(c))
        σ1 <- exec(s2)(σ0, CSnd(c))
      } yield σ1
    case Skip() => Some(σ)
    case Abort() => None
  }

  def run(s: Stmt): Option[Sto] = exec(s)(Map(), CRoot())
}

object TestFunctional {
  import SyntaxSugar._
  import Functional._

  def main(args: Array[String]): Unit = {
    // 2^10
    val x = Const(10)
    val body = Seq(assign("res", BinOp("*", Const(2), deref("res"))),
      assign("x", BinOp("-", deref("x"), Const(1))))
    val p =
      Seq(
        Alloc("x"),
        Seq(Alloc("res"),
          Seq(assign("x", x),
            Seq(assign("res", Const(1)),
              While(BinOp("<", Const(0), deref("x")), body)))))
    println(run(p))
  }
}

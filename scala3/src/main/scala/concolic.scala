package concolic

import scala.io.AnsiColor

type Label = String

trait Value
case class Var(x: String) extends Value
case class IntV(x: Int) extends Value

trait Expr
case class BinOp(op: String, v1: Value, v2: Value) extends Expr
case class Call(f: String, arg: Value) extends Expr

trait Inst
case class Assign(x: String, e: Expr) extends Inst
case class Seq(i1: Inst, i2: Inst) extends Inst
case class Error() extends Inst

trait Term
case class Cond(v: Value, l1: Label, l2: Label) extends Term
case class Jump(l: Label) extends Term
case class Return(v: Value) extends Term

case class Block(l: Label, i: Inst, t: Term)
case class Func(name: String, arg: String, blocks: List[Block])
case class Program(functions: List[Func])

object Helper {
  def toSeq(xs: List[Inst]): Inst = xs match {
    case Nil => Error()
    case x :: Nil => x
    case x :: xs => Seq(x, toSeq(xs))
  }
  def findFun(f: String)(using p: Program): Func =
    p.functions.find(_.name == f).get
  def findBlock(l: Label)(using p: Program): Block =
    p.functions.flatMap(_.blocks).find(_.l == l).get
  def findMain(using p: Program): Func = findFun("main")
}

// Concrete semantics

class Concrete {
  import Helper._

  type PrimValue = IntV

  case class State(s: Map[Var, PrimValue]) {
    def apply(x: Value): PrimValue = x match {
      case x@Var(_) => s(x)
      case v@IntV(_) => v
    }
    def +(xv: (Var, PrimValue)): State = State(s + xv)
  }

  type Ans = (PrimValue, State)
  type Cont[A] = (PrimValue, State) => A
  type LocalCont[A] = State => A

  def primEval(op: String, n1: PrimValue, n2: PrimValue): PrimValue =
    op match {
      case "+" => IntV(n1.x + n2.x)
      case "-" => IntV(n1.x - n2.x)
      case "*" => IntV(n1.x * n2.x)
      case "/" => IntV(n1.x / n2.x)
    }

  def eval[A](e: Expr, s: State, k: Cont[A])(using p: Program): A = e match {
    case BinOp(op, v1, v2) => k(primEval(op, s(v1), s(v2)), s)
    case Call(f, v) => runFunc(findFun(f), s(v), s, k)
  }

  def exec[A](i: Inst, s: State, k: LocalCont[A])(using p: Program): A = i match {
    case Assign(x, e) => eval(e, s, (v, s) => k(s + (Var(x) -> v)))
    case Seq(i1, i2) => exec(i1, s, s => exec(i2, s, k))
    case Error() => throw new RuntimeException("Error")
  }

  def term[A](t: Term, s: State, k: Cont[A])(using p: Program): A = t match {
    case Cond(v, l1, l2) =>
      if (s(v).x == 1) runBlock(findBlock(l1), s, k)
      else runBlock(findBlock(l2), s, k)
    case Jump(l) =>
      runBlock(findBlock(l), s, k)
    case Return(v) =>
      k(s(v), s)
  }

  def runBlock[A](b: Block, s: State, k: Cont[A])(using p: Program): A =
    exec(b.i, s, s => term(b.t, s, k))

  def runFunc[A](f: Func, v: IntV, s: State, k: Cont[A])(using p: Program): A =
    runBlock(f.blocks(0), s + (Var(f.arg) -> v), k)

  def runProg(p: Program, v: IntV): Ans =
    runFunc(findMain(using p), v, State(Map()), (v, s) => (v, s))(using p)
}

// Partial symbolic semantics

abstract class Symbolic {
  import Helper._

  val concreteEval = new Concrete

  trait SymV
  case class SymVar(x: String) extends SymV
  case class SymOp(op: String, args: List[PrimValue]) extends SymV

  type PrimValue = IntV | SymV
  case class State(s: Map[Var, PrimValue], pc: Set[SymV]) {
    def apply(x: Value): PrimValue = x match {
      case x@Var(_) => s(x)
      case v@IntV(_) => v
    }
    def +(xv: (Var, PrimValue)): State = State(s + xv, pc)
    def +(c: SymV): State = State(s, pc + c)
  }

  type Cont[A] = (PrimValue, State) => A
  type LocalCont[A] = State => A
  type Ans = (PrimValue, State)

  def primEval(op: String, v1: PrimValue, v2: PrimValue): PrimValue =
    (v1, v2) match {
      case (s1: SymV, s2) => SymOp(op, List(s1, s2))
      case (s1, s2: SymV) => SymOp(op, List(s1, s2))
      case (v1: IntV, v2: IntV) => concreteEval.primEval(op, v1, v2)
    }

  def eval[A](e: Expr, s: State, k: Cont[A])(using p: Program): A = e match {
    case BinOp(op, v1, v2) => k(primEval(op, s(v1), s(v2)), s)
    case Call(f, v) => runFunc(findFun(f), s(v), s, k)
  }

  def exec[A](i: Inst, s: State, k: LocalCont[A])(using p: Program): A = i match {
    case Assign(x, e) => eval(e, s, (v, s) => k(s + (Var(x) -> v)))
    case Seq(i1, i2) => exec(i1, s, s => exec(i2, s, k))
    case Error() => throw new RuntimeException("Error")
  }

  def term[A](t: Term, s: State, k: Cont[A])(using p: Program): A

  def runBlock[A](b: Block, s: State, k: Cont[A])(using p: Program): A =
    exec(b.i, s, s => term(b.t, s, k))

  def runFunc[A](f: Func, v: PrimValue, s: State, k: Cont[A])(using p: Program): A =
    runBlock(f.blocks(0), s + (Var(f.arg) -> v), k)

  def runProg(p: Program, v: PrimValue): Ans =
    runFunc(findMain(using p), v, State(Map(), Set()), (v, s) => (v, s))(using p)
}

// A monolithic concolic interpreter
class Concolic_Mono {
  import Helper._

  trait SymV
  case class SymVar(x: String) extends SymV
  case class SymOp(op: String, args: List[PrimValue]) extends SymV

  type PrimValue = IntV | SymV

  case class CState(s: Map[Var, IntV]) {
    def apply(x: Value): IntV = x match {
      case x@Var(_) => s(x)
      case v@IntV(_) => v
    }
    def +(xv: (Var, IntV)): CState = CState(s + xv)
  }
  case class SState(s: Map[Var, PrimValue], pc: Set[SymV]) {
    def apply(x: Value): PrimValue = x match {
      case x@Var(_) => s(x)
      case v@IntV(_) => v
    }
    def +(xv: (Var, PrimValue)): SState = SState(s + xv, pc)
    def +(c: SymV): SState = SState(s, pc + c)
  }
  case class State(c: CState, s: SState)

  type Cont[A] = (IntV, PrimValue, State) => A
  type LocalCont[A] = State => A
  type Ans = (IntV, PrimValue, State)

  def primEval_c(op: String, n1: IntV, n2: IntV): IntV =
    op match {
      case "+" => IntV(n1.x + n2.x)
      case "-" => IntV(n1.x - n2.x)
      case "*" => IntV(n1.x * n2.x)
      case "/" => IntV(n1.x / n2.x)
    }

  def primEval_s(op: String, v1: PrimValue, v2: PrimValue): PrimValue =
    (v1, v2) match {
      case (s1: SymV, s2) => SymOp(op, List(s1, s2))
      case (s1, s2: SymV) => SymOp(op, List(s1, s2))
      case (v1: IntV, v2: IntV) => primEval_c(op, v1, v2)
    }

  def eval[A](e: Expr, s: State, k: Cont[A])(using p: Program): A = e match {
    case BinOp(op, v1, v2) => k(primEval_c(op, s.c(v1), s.c(v2)), primEval_s(op, s.s(v1), s.s(v2)), s)
    case Call(f, v) => runFunc(findFun(f), s.c(v), s.s(v), s, k)
  }

  def exec[A](i: Inst, s: State, k: LocalCont[A])(using p: Program): A = i match {
    case Assign(x, e) => eval(e, s, (v_c, v_s, s) => k(State(s.c + (Var(x) -> v_c), s.s + (Var(x) -> v_s))))
    case Seq(i1, i2) => exec(i1, s, s => exec(i2, s, k))
    case Error() => throw new RuntimeException("Error")
  }

  def term[A](t: Term, s: State, k: Cont[A])(using p: Program): A = t match {
    case Cond(v, l1, l2) =>
      if (s.c(v).x == 1) runBlock(findBlock(l1), s, k)
      else runBlock(findBlock(l2), s, k)
    case Jump(l) =>
      runBlock(findBlock(l), s, k)
    case Return(v) =>
      k(s.c(v), s.s(v), s)
  }

  def runBlock[A](b: Block, s: State, k: Cont[A])(using p: Program): A =
    exec(b.i, s, s => term(b.t, s, k))

  def runFunc[A](f: Func, v_c: IntV, v_s: PrimValue, s: State, k: Cont[A])(using p: Program): A =
    runBlock(f.blocks(0), State(s.c + (Var(f.arg) -> v_c), s.s + (Var(f.arg) -> v_s)), k)

  val state0 = State(CState(Map()), SState(Map(), Set()))
  def runProg(p: Program, v_c: IntV, v_s: PrimValue): Ans =
    runFunc(findMain(using p), v_c, v_s, state0, (cv, sv, s) => (cv, sv, s))(using p)
}

// A concolic interpreter by composition
class Concolic2 { concolic =>
  import Helper._

  val C = new Concrete
  val S = new Symbolic { q =>
    def term[A](t: Term, s: q.State, k: q.Cont[A])(using p: Program): A = ???
    //def runBlock[A](b: Block, s: q.State, k: q.Cont[A])(using p: Program): A = ???
  }

  type State = (C.State, S.State)
  type Ans = (S.PrimValue, State)
  type Cont = (S.PrimValue, State) => Ans

  def term(t: Term, s: State, k: Cont)(using p: Program): Ans = t match {
    case Cond(v, l1, l2) =>
      if (s._1(v).x == 1) runBlock(findBlock(l1), s, k)
      else runBlock(findBlock(l2), s, k)
    case Jump(l) =>
      runBlock(findBlock(l), s, k)
    case Return(v) =>
      k(s._2(v), s)
  }

  def runBlock(b: Block, s: State, k: Cont)(using p: Program): Ans =
    C.exec(b.i, s._1, cs => S.exec(b.i, s._2, ss => term(b.t, (cs, ss), k)))
}

object Test {
  import Helper._

  val p = Program(List(
    Func("f", "x", List(
      Block("b0", ???, ???),
      Block("b1", ???, ???)
    )),
    Func("g", "y", List(
      Block("b2", ???, ???),
      Block("b3", ???, ???)
    ))
  ))
}
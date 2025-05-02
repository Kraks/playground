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
class ConcolicMono {
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
      if (s.c(v).x == 1) runBlock(findBlock(l1), State(s.c, s.s + SymOp("=", List(s.s(v), IntV(1)))), k)
      else runBlock(findBlock(l2), State(s.c, s.s + SymOp("!=", List(s.s(v), IntV(1)))), k)
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

  enum SymV:
    case SymVar(x: String)
    case SymOp(op: String, args: List[PrimValue])
  import SymV.*

  type PrimValue = IntV | SymV

  case class CState(s: Map[Var, IntV]) {
    def apply(x: Value): IntV = x match
      case x@Var(_) => s(x)
      case v@IntV(_) => v
    def +(xv: (Var, IntV)): CState = CState(s + xv)
  }
  case class SState(s: Map[Var, PrimValue], pc: Set[SymV]) {
    def apply(x: Value): PrimValue = x match
      case x@Var(_) => s(x)
      case v@IntV(_) => v
    def +(xv: (Var, PrimValue)): SState = SState(s + xv, pc)
    def +(c: SymV): SState = SState(s, pc + c)
  }

  def primEval_c(op: String, n1: IntV, n2: IntV): IntV =
    op match
      case "+" => IntV(n1.x + n2.x)
      case "-" => IntV(n1.x - n2.x)
      case "*" => IntV(n1.x * n2.x)
      case "/" => IntV(n1.x / n2.x)

  def primEval_s(op: String, v1: PrimValue, v2: PrimValue): PrimValue =
    (v1, v2) match
      case (s1: SymV, s2) => SymOp(op, List(s1, s2))
      case (s1, s2: SymV) => SymOp(op, List(s1, s2))
      case (v1: IntV, v2: IntV) => primEval_c(op, v1, v2)

  type CCont[A] = (IntV, CState) => A
  type SCont[A] = (PrimValue, SState) => A
  type Cont[A] = (IntV, PrimValue, CState, SState) => A

  type LocalCCont[A] = CState => A
  type LocalSCont[A] = SState => A
  type LocalCont[A] = (CState, SState) => A

  def eval_c[A](e: Expr, s: CState, k: CCont[A])(using p: Program): A = e match {
    case BinOp(op, v1, v2) => k(primEval_c(op, s(v1), s(v2)), s)
    case Call(f, v) => runFunc_c(findFun(f), s(v), s, k)
  }

  def eval_s[A](e: Expr, s: SState, k: SCont[A])(using p: Program): A = e match {
    case BinOp(op, v1, v2) => k(primEval_s(op, s(v1), s(v2)), s)
    case Call(f, v) => runFunc_s(findFun(f), s(v), s, k)
  }

  // XXX: who calls this?
  /*
  def eval[A](e: Expr, cs: CState, ss: SState, k: Cont[A])(using p: Program): A = e match {
    case BinOp(op, v1, v2) =>
      eval_c(e, cs, (cv, cs) => eval_s(e, ss, (sv, ss) => k(cv, sv, cs, ss)))
    case Call(f, v) => runFunc(findFun(f), cs(v), ss(v), cs, ss, k)
  }
  */

  def exec_c[A](i: Inst, s: CState, k: LocalCCont[A])(using p: Program): A = i match {
    case Assign(x, e) => eval_c(e, s, (v, s) => k(s + (Var(x) -> v)))
    case Seq(i1, i2) => exec_c(i1, s, s => exec_c(i2, s, k))
    case Error() => throw new RuntimeException("Error")
  }

  def exec_s[A](i: Inst, s: SState, k: LocalSCont[A])(using p: Program): A = i match {
    case Assign(x, e) => eval_s(e, s, (v, s) => k(s + (Var(x) -> v)))
    case Seq(i1, i2) => exec_s(i1, s, s => exec_s(i2, s, k))
    case Error() => throw new RuntimeException("Error")
  }

  /*
  def exec[A](i: Inst, cs: CState, ss: SState, k: LocalCont[A])(using p: Program): A =
    exec_c(i, cs, cs => exec_s(i, ss, ss => k(cs, ss)))
  */

  def term_c[A](t: Term, s: CState, k: CCont[A])(using p: Program): A = t match {
    case Cond(v, l1, l2) =>
      if (s(v).x == 1) runBlock_c(findBlock(l1), s, k)
      else runBlock_c(findBlock(l2), s, k)
    case Jump(l) =>
      runBlock_c(findBlock(l), s, k)
    case Return(v) =>
      k(s(v), s)
  }

  def term_s[A](t: Term, s: SState, k: SCont[A])(using p: Program): A = t match {
    case Cond(v, l1, l2) =>
      ???
    case Jump(l) =>
      runBlock_s(findBlock(l), s, k)
    case Return(v) =>
      k(s(v), s)
  }

  def runBlock_c[A](b: Block, s: CState, k: CCont[A])(using p: Program): A =
    exec_c(b.i, s, s => term_c(b.t, s, k))

  def runBlock_s[A](b: Block, s: SState, k: SCont[A])(using p: Program): A =
    exec_s(b.i, s, s => term_s(b.t, s, k))

  // XXX: who calls this?
  //def runBlock[A](b: Block, cs: CState, ss: SState, k: Cont[A])(using p: Program): A =
  //  runBlock_c(b, cs, (v_c, cs) => runBlock_s(b, ss, (v_s, ss) => k(v_c, v_s, cs, ss)))

  def runFunc_c[A](f: Func, v: IntV, s: CState, k: CCont[A])(using p: Program): A =
    runBlock_c(f.blocks(0), s + (Var(f.arg) -> v), k)

  def runFunc_s[A](f: Func, v: PrimValue, s: SState, k: SCont[A])(using p: Program): A =
    runBlock_s(f.blocks(0), s + (Var(f.arg) -> v), k)

  def runFunc[A](f: Func, v_c: IntV, v_s: PrimValue, cs: CState, ss: SState, k: Cont[A])(using p: Program): A =
    runFunc_c(f, v_c, cs, (v_c, cs) => runFunc_s(f, v_s, ss, (v_s, ss) => k(v_c, v_s, cs, ss)))
}

object Test {
  import Helper._

  val p = Program(List(
    Func("f", "x", List(
      Block("b0",
        Seq(
          Assign("y1", BinOp("+", Var("x"), IntV(1))),
          Assign("y2", BinOp("-", Var("y1"), IntV(1)))),
        Cond(Var("y2"), "b1", "b2")),
      Block("b1", Assign("z", BinOp("*", Var("y2"), IntV(2))), Return(Var("z"))),
      Block("b2", Assign("z", BinOp("*", Var("y2"), IntV(3))), Return(Var("z")))
    )),
    Func("main", "a", List(
      Block("b0", Assign("r", Call("f", Var("a"))), Return(Var("r")))
    ))
  ))

  def main(args: Array[String]): Unit = {
    val C = new Concrete
    println(C.runProg(p, IntV(42)))

    val CM = new ConcolicMono
    println(CM.runProg(p, IntV(42), CM.SymVar("a")))
  }
}
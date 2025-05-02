package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>

import org.scalatest._
import funsuite._

import Expr._
import Stmt._
import Value._
import Examples._
import Stage._

val top = summon[Lattice[Interval]].top
val bot = summon[Lattice[Interval]].bot
given mtFunEnv: FunEnv = Map()

class TestPartialAbstract extends AnyFunSuite {
  // Partial abstract interpreter should work on all static/non-modular cases

  test("add1-static") {
    assert(partialAbsRun(add1, "add1", top) == top)
    assert(partialAbsRun(add1, "add1", Interval.from(0, 5)) == Interval.make(1, 6))
  }

  test("branch-static") {
    assert(partialAbsRun(branch, "branch", top) == Interval.make(1, 2))
    assert(partialAbsRun(branch, "branch", Interval.from(5)) == Interval.from(2))
  }

  test("powerWhile-static") {
    assert(partialAbsRun(powerWhile, "power", top, top) == top)
    assert(partialAbsRun(powerWhile, "power", Interval.from(2), Interval.from(10)) == Interval.make(1, Double.PositiveInfinity))
    assert(partialAbsRun(powerWhile, "power", Interval.from(1), top) == Interval.from(1))
    assert(partialAbsRun(powerWhile, "power", Interval.from(2), top) == Interval.make(1, Double.PositiveInfinity))
  }

  test("nonTerm1-static") {
    assert(partialAbsRun(nonTerm1, "main", top) == Interval.make(0, 1))
  }

  test("nonTerm2-static") {
    assert(partialAbsRun(nonTerm2, "main", top) == Interval.make(0, 0))
  }

  test("noLoop-static") {
    assert(partialAbsRun(noLoop, "main", top) == Interval.make(1, 1))
  }

  test("seq1-dyn") {
    val (code, ret) = session {
      // initial store = dyn
      // x := 1
      // y := 2
      partialAbsExec(SSeq(Assign("x", Lit(1)), Assign("y", Lit(2))), fresh)
    }
    assert(code == """let x1 = ⊔(x0,Map(x -> Interval(1.0,1.0)))
let x2 = ⊔(x1,Map(y -> Interval(2.0,2.0)))""")
    assert(ret == (None, Sym(2)))
  }

  test("seq2-dyn") {
    val (code, ret) = session {
      // initial store = {a -> dyn}
      // x := a + 1
      // y := 2
      partialAbsExec(SSeq(Assign("x", BinOp("+", Var("a"), Lit(1))), Assign("y", Lit(2))), Map("a" -> fresh))
    }
    assert(code == """let x1 = +(x0,Interval(1.0,1.0))""")
    assert(ret == (None, Map("a" -> Sym(0), "x" -> Sym(1), "y" -> Interval.make(2.0,2.0))))
  }

  test("seq3-dyn") {
    session {
      // initial store = {a -> dyn}
      // x := a + 1
      // y := 2 + 3
      // z := y * 2
      partialAbsExec(SSeq(
        Assign("x", BinOp("+", Var("a"), Lit(1))),
        SSeq(Assign("y", BinOp("+", Lit(2), Lit(3))),
          Assign("z", BinOp("*", Var("y"), Lit(2))))), Map("a" -> fresh))
    }
  }

  test("ret-dyn") {
    session {
      // initial store = {a -> dyn}
      // return a + 1
      // y := 2 + 3
      // z := y * 2
      partialAbsExec(SSeq(
        Ret(BinOp("+", Var("a"), Lit(1))),
        SSeq(Assign("y", BinOp("+", Lit(2), Lit(3))),
          Assign("z", BinOp("*", Var("y"), Lit(2))))), Map("a" -> fresh))
    }
  }

  test("cond-dyn") {
    session {
      // initial store = {x -> dyn}
      // if (1 = 1) { a := 1 + x } else { b := 1 - x }
      val p = Cond(BinOp("=", Lit(1), Lit(1)),
        Assign("a", BinOp("+", Lit(1), Var("x"))),
        Assign("b", BinOp("-", Lit(1), Var("x"))))
      partialAbsExec(p, Map("x" -> fresh))
    }
  }

  test("cond-mix-sta-dyn1") {
    session {
      // initial store = {c -> ⊤, x -> dyn}
      // if (c) { a := 1 + x } else { b := 1 - x }
      val p = Cond(Var("c"),
        Assign("a", BinOp("+", Lit(1), Var("x"))),
        Assign("b", BinOp("-", Lit(1), Var("x"))))
      partialAbsExec(p, Map("c" -> top, "x" -> fresh))
    }
  }

  test("cond-mix-sta-dyn-join") {
    session {
      // initial store = {c -> ⊤, x -> dyn}
      // if (c) { a := 1 + x } else { a := 1 - x }
      val p = Cond(Var("c"),
        Assign("a", BinOp("+", Lit(1), Var("x"))),
        Assign("a", BinOp("-", Lit(1), Var("x"))))
      partialAbsExec(p, Map("c" -> top, "x" -> fresh))
    }
  }

  test("cond-dyn-join") {
    session {
      // initial store = {c -> dyn, x -> dyn}
      // if (c) { a := 1 + x } else { a := 1 - x }
      val p = Cond(Var("c"),
        Assign("a", BinOp("+", Lit(1), Var("x"))),
        Assign("a", BinOp("-", Lit(1), Var("x"))))
      partialAbsExec(p, Map("c" -> fresh, "x" -> fresh))
    }
  }

  test("cond-dyn-join-ret") {
    session {
      // initial store = {c -> dyn, x -> dyn}
      // if (c) { a := 1 + x } else { a := 1 - x }
      // return a
      val p = SSeq(
        Cond(Var("c"),
          Assign("a", BinOp("+", Lit(1), Var("x"))),
          Assign("a", BinOp("-", Lit(1), Var("x")))),
        Ret(Var("a")))
      partialAbsExec(p, Map("c" -> fresh, "x" -> fresh))
    }
  }

  test("loop-dyn-cond") {
    session {
      // initial store = {c -> dyn}
      // while(c = 1) {
      //   c := c - 1
      //   a := 1 + 2
      // }
      val p = While(BinOp("=", Var("c"), Lit(1)),
        SSeq(Assign("c", BinOp("-", Var("c"), Lit(1))),
          Assign("a", BinOp("+", Lit(1), Lit(2)))))
        partialAbsExec(p, Map("c" -> fresh))
    }
  }

  test("loop-dyn-body") {
    session {
      // XXX: improve binding time
      // initial store = {c -> 10, x -> dyn}
      // while(0 < c) {
      //   if (5 < c) c := c - 1
      //   else c := x
      // }
      val p = While(BinOp("<", Lit(0), Var("c")),
        Cond(BinOp("<", Lit(5), Var("c")),
          Assign("c", BinOp("-", Var("c"), Lit(1))),
          Assign("c", Var("x"))))
        partialAbsExec(p, Map("c" -> Interval.from(10), "x" -> fresh))
    }
  }
}

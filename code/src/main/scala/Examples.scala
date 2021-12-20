package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>
// Some example programs

import Expr._
import Stmt._
import Value._

object Examples {
  val add1 = FunDef("add1", List("x"), Ret(BinOp("+", Var("x"), Lit(1))))

  val branch = FunDef("branch", List("x"),
    SSeq(
      Cond(BinOp("=", Var("x"), Lit(0)),
        Assign("y", Lit(1)),
        Assign("y", Lit(2))),
      Ret(Var("y"))))

  val power = FunDef("power", List("b", "x"),
    Cond(BinOp("=", Var("x"), Lit(0)),
      Ret(Lit(1)),
      Ret(BinOp("*", Var("b"), Call("power", List(Var("b"), BinOp("-", Var("x"), Lit(1))))))))

  val powerMult = Program(List(
    FunDef("power", List("b", "x"),
      Cond(BinOp("=", Var("x"), Lit(0)),
        Ret(Lit(1)),
        Ret(Call("mult", List(Var("b"), Call("power", List(Var("b"), BinOp("-", Var("x"), Lit(1))))))))),
    FunDef("mult", List("x", "y"),
      Ret(BinOp("*", Var("x"), Var("y"))))))

  val powerWhile = FunDef("power", List("b", "x"),
    SSeq(Assign("res", Lit(1)),
      SSeq(While(BinOp("<", Lit(0), Var("x")),
        SSeq(Assign("res", BinOp("*", Var("b"), Var("res"))),
          Assign("x", BinOp("-", Var("x"), Lit(1))))),
        Ret(Var("res")))))

  val earlyRet = FunDef("main", List("x"),
    SSeq(
      Cond(BinOp("=", Var("x"), Lit(0)),
        Ret(Lit(1)),
        Assign("x", BinOp("+", Var("x"), Lit(1)))),
      Ret(Var("x"))))

  val nonTerm1 = FunDef("main", List("x"),
    SSeq(
      While(Lit(1),
        SSeq(Assign("x", BinOp("-", Var("x"), Lit(1))),
          Cond(BinOp("=", Var("x"), Lit(0)),
            Ret(Lit(1)),
            Skip))),
      Ret(Lit(0))))

  val nonTerm2 = FunDef("main", List("x"),
    SSeq(
      While(Lit(1),
        Assign("x", BinOp("-", Var("x"), Lit(1)))),
      Ret(Lit(0))))

  val noLoop = FunDef("main", List("x"),
    SSeq(
      While(Lit(0),
        Assign("x", BinOp("-", Var("x"), Lit(1)))),
      Ret(Lit(1))))
}

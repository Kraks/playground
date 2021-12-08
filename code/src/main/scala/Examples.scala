package compositional

// Some example programs

import Expr._
import Stmt._
import Value._

object Examples {
  val add1 = FunDef("add1", List("x"), Ret(BinOp("+", Var("x"), Lit(1))))

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

  val earlyRet = FunDef("main", List("x"),
    SSeq(
      Cond(BinOp("=", Var("x"), Lit(0)),
        Ret(Lit(1)),
        Assign("x", BinOp("+", Var("x"), Lit(1)))),
      Ret(Var("x"))))

}
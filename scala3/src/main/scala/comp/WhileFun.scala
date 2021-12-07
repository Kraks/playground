package compositional

// A simple first-order functional language based on While

enum Expr:
  case Var(x: String)
  case Lit(i: Int)
  case BinOp(op: String, e1: Expr, e2: Expr) 
  case Call(fname: String, arg: List[Expr])

enum Stmt:
  case Skip
  case Assign(x: String, e: Expr)
  case SSeq(s1: Stmt, s2: Stmt)
  case Cond(e: Expr, s1: Stmt, s2: Stmt)
  case While(e: Expr, s: Stmt)
  case Ret(e: Expr)

enum Value:
  case IntV(i: Int)

import Expr._
import Stmt._
import Value._

case class FunDef(fname: String, params: List[String], body: Stmt)

def foldStmts(stmts: List[Stmt]): Stmt = 
  stmts match {
    case Nil => Skip
    case s::stmts => SSeq(s, foldStmts(stmts))
  }

case class Program(funs: List[FunDef]) {
  def funEnv: Map[String, FunDef] = funs.map(fd => (fd.fname, fd)).toMap
  def apply(fname: String): FunDef = funEnv(fname)
}

given Conversion[FunDef, Program] with
  def apply(f: FunDef): Program = Program(List(f))

object Examples {
  val add1 = FunDef("add1", List("x"), Ret(BinOp("+", Var("x"), Lit(1))))

  val power = FunDef("power", List("b", "x"),
    Cond(BinOp("=", Var("x"), Lit(0)),
      Ret(Lit(1)),
      Ret(BinOp("*", Var("b"), Call("power", List(Var("b"), BinOp("-", Var("x"), Lit(1))))))))

  def main(args: Array[String]): Unit = {
    println(run(add1, "add1", IntV(1)))
    println(run(power, "power", IntV(2), IntV(10)))
  }
}


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

import Expr._
import Stmt._

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

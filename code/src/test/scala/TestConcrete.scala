package compositional

import org.scalatest._
import funsuite._

import Expr._
import Stmt._
import Value._
import Examples._
import compositional.{run => runConcrete}

class TestConcrete extends AnyFunSuite {
  assert(runConcrete(add1, "add1", IntV(1)) == IntV(2))
  assert(runConcrete(power, "power", IntV(2), IntV(10)) == IntV(1024))
  assert(runConcrete(powerMult, "power", IntV(2), IntV(10)) == IntV(1024))
  assert(runConcrete(earlyRet, "main", IntV(0)) == IntV(1))
  assert(runConcrete(earlyRet, "main", IntV(1)) == IntV(2))
}


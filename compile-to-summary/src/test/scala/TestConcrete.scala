package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>

import org.scalatest._
import funsuite._

import Expr._
import Stmt._
import Value._
import Examples._
import compositional.{run => runConcrete}

class TestConcrete extends AnyFunSuite {
  test("add1") {
    assert(runConcrete(add1, "add1", IntV(1)) == IntV(2))
  }
  test("powerRec") {
    assert(runConcrete(power, "power", IntV(2), IntV(10)) == IntV(1024))
  }
  test("powerRecMult") {
    assert(runConcrete(powerMult, "power", IntV(2), IntV(10)) == IntV(1024))
  }
  test("powerWhile") {
    assert(runConcrete(powerWhile, "power", IntV(2), IntV(10)) == IntV(1024))
  }
  test("earlyRet") {
    assert(runConcrete(earlyRet, "main", IntV(0)) == IntV(1))
    assert(runConcrete(earlyRet, "main", IntV(1)) == IntV(2))
  }
}

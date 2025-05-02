package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>

import org.scalatest._
import funsuite._

import Expr._
import Stmt._
import Value._
import Examples._

val top = summon[Lattice[Interval]].top
val bot = summon[Lattice[Interval]].bot

class TestInterval extends AnyFunSuite {
  test("add") {
    assert(Interval.from(1) + Interval.from(2) == Interval.from(3))
    assert(Interval.from(1, 2) + Interval.from(2, 3) == Interval.from(3, 5))
    assert(top + Interval.from(2, 3) == top)
    assert(bot + Interval.from(2, 3) == bot)
  }

  test("mult/div") {
    // BMI example: https://en.wikipedia.org/wiki/Interval_arithmetic#Multiple_intervals
    assert(
      (Interval.make(79.5, 80.5) / (Interval.make(1.785, 1.795) * Interval.make(1.785, 1.795)))
        ⊑ Interval.make(24.673, 25.266)
    )
  }

  test("ordering") {
    assert(bot ⊑ top)
    assert(Interval.make(20, 10) ⊑ top)
    assert(Interval.make(20, 10) ⊑ bot)
    assert(bot ⊑ Interval.from(0))
    assert(bot ⊑ Interval.from(0, 100))
    assert(Interval.from(0) ⊑ top)
    assert(Interval.from(0, 100) ⊑ top)
  }

  test("join") {
    assert(Interval.from(0, 100) ⊔ Interval.from(-50, 50) == Interval.from(-50, 100))
    assert(Interval.from(0, 10) ⊔ Interval.from(20, 30) == Interval.from(0, 30))
    assert(top ⊔ Interval.from(20, 30) == top)
    assert(bot ⊔ Interval.from(20, 30) == Interval.from(20, 30))
  }

  test("meet") {
    assert(Interval.from(0, 10) ⊓ Interval.from(20, 30) == Interval.make(20, 10))
    assert(Interval.from(0, 20) ⊓ Interval.from(10, 30) == Interval.from(10, 20))
    assert(top ⊓ Interval.from(10, 30) == Interval.from(10, 30))
    assert(bot ⊓ Interval.from(10, 30) == bot)
  }
}

class TestAbstract extends AnyFunSuite {
  test("add1") {
    assert(absRun(add1, "add1", top) == top)
    assert(absRun(add1, "add1", Interval.from(0, 5)) == Interval.make(1, 6))
  }

  test("branch") {
    assert(absRun(branch, "branch", top) == Interval.make(1, 2))
    assert(absRun(branch, "branch", Interval.from(5)) == Interval.from(2))
  }

  test("powerWhile") {
    assert(absRun(powerWhile, "power", top, top) == top)
    assert(absRun(powerWhile, "power", Interval.from(2), Interval.from(10)) == Interval.make(1, Double.PositiveInfinity))
    assert(absRun(powerWhile, "power", Interval.from(1), top) == Interval.from(1))
    assert(absRun(powerWhile, "power", Interval.from(2), top) == Interval.make(1, Double.PositiveInfinity))
  }

  test("nonTerm1") {
    assert(absRun(nonTerm1, "main", top) == Interval.make(0, 1))
  }

  test("nonTerm2") {
    assert(absRun(nonTerm2, "main", top) == Interval.make(0, 0))
  }

  test("noLoop") {
    assert(absRun(noLoop, "main", top) == Interval.make(1, 1))
  }
}

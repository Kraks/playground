package ad

package forward {
  case class Dual(n: Double, grad: Double)
  given Conversion[Double, Dual] = new Dual(_, 1.0)
  extension (x: Dual)
    def +(y: Dual): Dual = Dual(x.n + y.n, x.grad + y.grad)
    def -(y: Dual): Dual = Dual(x.n - y.n, x.grad - y.grad)
    def *(y: Dual): Dual = Dual(x.n * y.n, x.n * y.grad + y.n * x.grad)

  def primal(f: Dual => Dual): Double => Double = x => f(x).n
  def deriv(f: Dual => Dual): Double => Double = x => f(x).grad

  def testDeriv(f: Dual => Dual, fStr: String, d: Double => Double, dStr: String) =
    for (x <- -10 to 10) {
      println(s"deriv($fStr)($x): ${deriv(f)(x)}, $dStr($x): ${d(x)}")
    }

  @main def test() = {
    testDeriv((x: Dual) => x * x, "x^2", (x: Double) => 2 * x, "2x")
  }
}

package backward {
  import scala.collection.mutable.ListBuffer

  case class Dual(var n: Double, var grad: Double)
  given Conversion[Double, Dual] = new Dual(_, 1.0)

  def dual(x: Double): Dual = Dual(x, 0)

  val tape: ListBuffer[() => Unit] = ListBuffer()

  extension (x: Dual)
    def +(y: Dual): Dual = {
      val z = dual(x.n + y.n)
      tape += (() => { x.grad += z.grad; y.grad += z.grad })
      z
    }
    def -(y: Dual): Dual = {
      val z = dual(x.n - y.n)
      tape += (() => { x.grad -= z.grad; y.grad -= z.grad })
      z
    }
    def *(y: Dual): Dual = {
      val z = dual(x.n * y.n)
      tape += (() => { x.grad += y.n * z.grad; y.grad += x.n * z.grad })
      z
    }

  def grad(f: Dual => Dual): Double => Double = x => {
    val dx = dual(x)
    val dz = f(dx)
    dz.grad = 1
    for (t <- tape.reverse) t()
    tape.clear
    dx.grad
  }

  def testGrad(f: Dual => Dual, fStr: String, d: Double => Double, dStr: String) =
    for (x <- -10 to 10) {
      println(s"deriv($fStr)($x): ${grad(f)(x)}, $dStr($x): ${d(x)}")
    }

  @main def test() = {
    testGrad((x: Dual) => x * x, "x^2", (x: Double) => 2 * x, "2x")
  }
}

package gradient {
  import backward._
  import scala.collection.mutable.ListBuffer

  val params: ListBuffer[Dual] = ListBuffer()
  def param(x: Double): Dual = {
    val dx = Dual(x, 0)
    params += dx
    dx
  }

  def compute(loss: () => Dual): Dual = {
    tape.clear
    val d = loss()
    d.grad = 1
    for (t <- tape.reverse) t()
    d
  }

  var lr = 0.0001

  def optimize(loss: () => Dual): Dual = {
    val d = compute(loss)
    for (i <- 0 until params.size) {
      val p = params(i)
      p.n -= lr * p.grad
      p.grad = 0
    }
    d
  }
}

package linearreg {
  import backward._
  import gradient._

  val a0 = param(0)
  val a1 = param(1)
  def approx(x: Dual): Dual = a1 * x + a0
  def approxStr = s"${a1.n}x + ${a0.n}"

  val data = List((40, 120), (160, 40))

  def loss(): Dual = {
    var total = dual(0)
    for (i <- 0 until data.size) {
      val x = dual(data(i)._1)
      val y = dual(data(i)._2)
      val d = y - approx(x)
      total = total + d * d
    }
    total * dual(1.0/data.size)
  }

  @main def test() = {
    lr = 0.00001
    for (i <- 0 to 100000) {
      optimize(loss)
      println(approxStr)
    }
    println(s"approx(40) = ${approx(dual(40.0)).n}")
    println(s"approx(160) = ${approx(dual(160.0)).n}")
  }
}

package momentum {
  import backward._
  import scala.collection.mutable.ListBuffer

  val params: ListBuffer[Dual] = ListBuffer()
  def param(x: Double): Dual = {
    val dx = Dual(x, 0)
    params += dx
    dx
  }

  var γ = 0.9
  var lr = 0.0001

  def compute(loss: () => Dual): Dual = {
    tape.clear
    val d = loss()
    d.grad = 1
    for (t <- tape.reverse) t()
    d
  }
  
  def optimize(loss: () => Dual): Dual = {
    val d = compute(loss)
    for (i <- 0 until params.size) {
      val p = params(i)
      val v = lastV1(i)
      val v1 = γ * v + lr * p.grad
      p.n -= v1
      lastV1(i) = v1
      p.grad = 0
    }
    d
  }

  val a0 = param(0)
  val a1 = param(1)

  val lastV1 = params.map(x => 0.0)
  def approx(x: Dual): Dual = a1 * x + a0
  def approxStr = s"${a1.n}x + ${a0.n}"

  val data = List((40, 120), (160, 40))

  def loss(): Dual = {
    var total = dual(0)
    for (i <- 0 until data.size) {
      val x = dual(data(i)._1)
      val y = dual(data(i)._2)
      val d = y - approx(x)
      total = total + d * d
    }
    total * dual(1.0/data.size)
  }

  @main def test() = {
    lr = 0.00001
    for (i <- 0 to 100000) {
      optimize(loss)
      println(approxStr)
    }
    println(s"approx(40) = ${approx(dual(40.0)).n}")
    println(s"approx(160) = ${approx(dual(160.0)).n}")
  }
}

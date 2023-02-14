import scala.util.continuations._

object DelimitedCont {
  def main(args: Array[String]): Unit = {
    reset {
      1 + shift { cf: (Int=>Int) =>
        val eleven = cf(10)
        println(eleven)
        val oneHundredOne = cf(100)
        println(oneHundredOne)
        oneHundredOne
      }
    }
  }
}

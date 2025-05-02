package staging

object Staging {
  type Rep[T] = String
  
  implicit def Int2RepInt(x: Int): Rep[Int] = x.toString
  implicit class RepIntOps(x: Rep[Int]) {
    def *(y: Rep[Int]): Rep[Int] = x + "*" + y
  }

  def power(x: Int, b: Rep[Int]): Rep[Int] = 
    if (x == 0) 1 else b * power(x-1, b)

  def main(args: Array[String]): Unit = {
    println(power(3, "b*b*b"))
  }
}

object StagingLMS {
  var n: Int = 0
  def fresh: String = {
    val m = n
    n = n + 1
    "x" + m
  }
  case class Sym(id: String)
  
  case class Exp(rator: String, rands: List[Any])
  case class Let(x: String, e: Exp)
  
  var lets: List[Let] = List()
  
  def reflect(e: Exp): Sym = {
    val id = fresh
    lets = lets :+ Let(id, e)
    Sym(id)
  }

  type Rep[T] = Sym
  
  implicit def Int2RepInt(x: Int): Rep[Int] = reflect(Exp("id", List(x)))
  implicit class RepIntOps(x: Rep[Int]) {
    def *(y: Rep[Int]): Rep[Int] = reflect(Exp("*", List(x, y)))
  }

  def power(x: Int, b: Rep[Int]): Rep[Int] = 
    if (x == 0) 1 else b * power(x-1, b)
  
  def main(args: Array[String]): Unit = {
    val result = power(3, Sym("b"))
    println(lets)
    println(result)
  }
}

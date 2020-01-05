package types.crypto

import scala.math.Integral.Implicits._

object RSA {
  def extended_gcd(a: BigInt, b: BigInt): (BigInt, BigInt) = {
    if (a % b == 0) (0, 1)
    else {
      val (x, y) = extended_gcd(b, a % b)
      (y, x - (y * (a /% b)._1))
    }
  }

  def module_inverse(a: BigInt, n: BigInt): BigInt = {
    val (x, _) = extended_gcd(a, n)
    x % n
  }

  def square(x: BigInt): BigInt = x * x

  def totient(p: BigInt, q: BigInt): BigInt = (p - 1) * (q - 1)

  def modulo_power(base: BigInt, exp: BigInt, n: BigInt): BigInt =
    if (exp == 0) 1
    else {
      if (exp % 2 != 0) (base * modulo_power(base, exp-1, n)) % n
      else square(modulo_power(base, exp/2, n)) % n
    }

  def is_legal_public_exponent(e: BigInt, p: BigInt, q: BigInt): Boolean = 
    (1 < e) && (e < totient(p, q)) && (1 == e.gcd(totient(p, q)))

  def private_exponent(e: BigInt, p: BigInt, q: BigInt): BigInt =
    if (is_legal_public_exponent(e, p, q)) module_inverse(e, totient(p, q))
    else throw new Exception("Not valid")

  def encrypt(m: BigInt, e: BigInt, n: BigInt): BigInt = 
    if (m > n) throw new Exception("The modulus is too small")
    else modulo_power(m, e, n)

  def decrypt(c: BigInt, d: BigInt, n: BigInt): BigInt =
    modulo_power(c, d, n)

  def main(args: Array[String]): Unit = {
    // test extended_gcd
    // extended-gcd(a,b) = (x,y), such that a*x + b*y = gcd(a,b)
    for (i <- (1 to 100).map(BigInt(_))) {
      for (j <- (1 to 100).map(BigInt(_))) {
        val (x, y) = extended_gcd(i, j)
        assert(i * x + j * y == (i gcd j))
      }
    }
  
    val p: BigInt = 41 // a large prime
    val q: BigInt = 47 // another large prime
    def n: BigInt = p * q // the public modulus

    def e: BigInt = 7 // the public exponent
    def d: BigInt = private_exponent(e, p, q) // the private exponent

    def msg: BigInt = 42
    def ciphermsg: BigInt = encrypt(msg, e, n)
    println(s"cipher msg: $ciphermsg")
    def demsg: BigInt = decrypt(ciphermsg, d, n)
    assert(msg == demsg)
  }
}

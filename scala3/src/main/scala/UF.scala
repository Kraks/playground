package unionfind

import scala.collection.mutable.ArrayBuffer

case class UF(n: Int) {
  require(n >= 0)

  val parent: Array[Int] = (0 until n).toArray
  val rank: Array[Byte] = Array.fill[Byte](n)(0)
  var count: Int = n

  def find(p: Int): Int = {
    var t = p
    while (t != parent(t)) {
      parent(t) = parent(parent(t))
      t = parent(t)
    }
    t
  }

  def connected(p: Int, q: Int): Boolean = find(p) == find(q)

  def union(p: Int, q: Int): Unit = {
    val rootP = find(p)
    val rootQ = find(q)
    if (rootP == rootQ) return
    if (rank(rootP) < rank(rootQ)) parent(rootP) = rootQ
    else if (rank(rootP) > rank(rootQ)) parent(rootQ) = rootP
    else {
      parent(rootQ) = rootP
      rank(rootP) = (rank(rootP) + 1).toByte
    }
    count -= 1
  }
}

object UFTest {
  def main(args: Array[String]): Unit = {
    val n = io.StdIn.readInt
    val uf = new UF(n)

  }
}

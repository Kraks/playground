package sat

import java.io.File
import scala.io.Source
import scala.annotation._

import DIMACSParser._

import java.io.PrintStream
import java.io.OutputStream
import java.io.ByteArrayOutputStream

object TestSolver {
  import Utils._
  def main(args: Array[String]): Unit = {
    val bench50 = test(50, 218)(_)
    //time { bench50(f => dpli(f, List()).nonEmpty) }
    time { bench50(f => dpll(f, List()).nonEmpty) }
    //time { bench50(f => dp(f, List()).nonEmpty) }
  }
}

object Utils {
  def getListOfFiles(d: File, ext: String): List[File] = {
    if (d.exists && d.isDirectory) d.listFiles.filter(_.isFile).filter(_.getName.endsWith(ext)).toList
    else List[File]()
  }
  def getListOfFiles(dirPath: String, ext: String): List[File] = getListOfFiles(new File(dirPath), ext)

  def getCNFFromFolder(dir: String): List[String] = getListOfFiles(dir, "cnf").map(_.getPath)
  def getCNFFromFolder(d: File): List[String] = getListOfFiles(d, "cnf").map(_.getPath)

  def test(nVar: Int, nClause: Int)(solve: Formula => Boolean): Unit = {
    val sats: List[String] = getCNFFromFolder(s"src/main/resources/uf${nVar}-${nClause}")
    val unsats: List[String] = getCNFFromFolder(s"src/main/resources/uuf${nVar}-${nClause}")
    for (f <- sats) {
      println(s"Check SAT $f")
      assert(solve(parseFromPath(f)))
    }
    for (f <- unsats) {
      println(s"Check UNSAT $f")
      assert(!solve(parseFromPath(f)))
    }
  }

  def time[R](block: => R): (R, Double) = {
    val t0 = System.nanoTime()
    val result = block
    val t1 = System.nanoTime()
    val t = (t1 - t0) / 1000000.0 //to ms
    //val t = (t1 - t0) / 1000000000.0 //to ms
    println("Elapsed time: " + t + "ms")
    (result, t)
  }
}

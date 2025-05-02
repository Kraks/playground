package quantum

// Following the Scheme Pearl paper on Quantum Continuation by Choudhury, Agapiev and Sabry

import scala.util.continuations._

object QuantumContSim {
  abstract class Exp
  case class Wire(pos: Int) extends Exp
  case class Bit(b: Boolean) extends Exp

  abstract class Gate
  // The Toffoli/Controlled-Controlled-Not gate
  case class CCX(x: Exp, y: Exp, z: Exp) extends Gate
  // The Hadamard gate
  case class H(x: Exp) extends Gate
  // The Not gate
  def X(x: Exp): Gate = CCX(Bit(true), Bit(true), x)
  // The Controlled-Not gate
  def CX(y: Exp, z: Exp): Gate = CCX(Bit(true), y, z)

  implicit def intToExp(i: Int): Exp = Wire(i)
  implicit def intToBool(i: Int): Boolean = if (i == 0) false else true

  case class State(d: Double, bs: Vector[Boolean])

  type Circuit = List[Gate]

  // Accumulate states and their probability amplitudes
  type Ans = Map[Vector[Boolean], Double]

  val hscale: Double = 1.0 / math.sqrt(2.0)

  def isSet(bs: Vector[Boolean], x: Exp): Boolean = x match {
    case Wire(pos) => bs(pos)
    case Bit(b) => b
  }

  def neg(bs: Vector[Boolean], x: Exp): Vector[Boolean] = x match {
    case Wire(pos) => bs.updated(pos, !bs(pos))
  }

  def collect(x: State, y: State): State @cps[Ans] = shift { k =>
    val a = k(x)
    val b = k(y)
    a.foldLeft(b) { case (m, (k, v)) => m + (k -> (m.getOrElse(k, 0.0)+v)) }
  }

  def evalGate(g: Gate, v: State): State @cps[Ans] = {
    val State(d, bs) = v
    g match {
      case CCX(x, y, z) if isSet(bs, x) && isSet(bs, y) => State(d, neg(bs, z))
      case CCX(x, y, z) => v
      case H(x) if isSet(bs, x) =>
        collect(State(hscale * d, neg(bs, x)), State(-1.0 * hscale * d, bs))
      case H(x) =>
        collect(State(hscale * d, bs), State(hscale * d, neg(bs, x)))
      case _ => throw new Exception("Invalid gate")
    }
  }

  def evalCircuit(c: Circuit, v: State): State @cps[Ans] =
    if (c.isEmpty) v else evalCircuit(c.tail, evalGate(c.head, v))

  def runCircuit(c: Circuit, v: State): Ans = reset {
    val State(d, bs) = evalCircuit(c, v)
    Map(bs -> d)
  }

  def prettyPrint(m: Ans): Unit = {
    m.filter(kv => math.abs(kv._2) > 0.001).foreach { case (k, v) =>
      val p = (if (v > 0) "+" else "") + f"$v%.3f"
      val vs = k.map(x => if (x) "1" else "0").mkString
      print(s"$p|$vs⟩ ")
    }
    println()
  }

  def main(args: Array[String]): Unit = {
    val circuit1: Circuit = List(
      H(0),
      CX(0, 1)
    )
    prettyPrint(runCircuit(circuit1, State(1.0, Vector(0, 0))))

    val circuit2: Circuit = List(
      H(0),
      X(0),
      H(0)
    )
    prettyPrint(runCircuit(circuit2, State(1.0, Vector(0))))

    val simon: Circuit = List(
      H(0),
      H(1),
      CX(0, 2),
      CX(0, 3),
      CX(1, 2),
      CX(1, 3),
      H(0),
      H(1)
    )
    prettyPrint(runCircuit(simon, State(1.0, Vector(0, 0, 0, 0))))
  }
}



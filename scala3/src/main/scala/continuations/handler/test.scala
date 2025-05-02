package continuation.handler
import continuation.handler.syntax.*

@main def test(): Unit = {
  {
    import continuation.handler.cek.*
    import RValue.*
    assert(extract(drive(inject(p2))) == IntV(4))
    assert(extract(drive(inject(p1))) == IntV(10))
    assert(extract(drive(inject(p3))) == IntV(144))
    assert(extract(drive(inject(p4))) == IntV(51))
    assert(extract(drive(inject(p5))) == IntV(51))
    assert(extract(drive(inject(p6))) == IntV(42))
  }

  {
    import continuation.handler.cesk.*
    import RValue.*
    assert(extract(drive(inject(p2))) == IntV(4))
    assert(extract(drive(inject(p1))) == IntV(10))
    assert(extract(drive(inject(p3))) == IntV(144))
    assert(extract(drive(inject(p4))) == IntV(51))
    assert(extract(drive(inject(p5))) == IntV(51))
    assert(extract(drive(inject(p6))) == IntV(42))
  }

  {
    import continuation.handler.ceskStar.*
    import RValue.*

    val n = 100
    assert(extract(drive(inject(p2), n)) == IntV(4))
    assert(extract(drive(inject(p1), n)) == IntV(10))
    assert(extract(drive(inject(p3), n)) == IntV(144))
    assert(extract(drive(inject(p4), n)) == IntV(51))
    assert(extract(drive(inject(p5), n)) == IntV(51))
    assert(extract(drive(inject(p6), n)) == IntV(42))
  }
}
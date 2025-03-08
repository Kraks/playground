package zipper

// The Zipper, Gerard Huet, 1997

enum Tree[+T]:
  case Item(x: T)
  case Section(items: List[Tree[T]])
import Tree.*

enum Path[+T]:
  case Top
  case Node(lefts: List[Tree[T]], up: Path[T], rights: List[Tree[T]])
import Path.*

case class Loc[T](t: Tree[T], p: Path[T])

def goLeft[T]: Loc[T] => Loc[T] =
  case Loc(t, Top) => throw new Exception("left of top")
  case Loc(t, Node(l::ls, up, rs)) => Loc(l, Node(ls, up, t::rs))
  case Loc(t, Node(List(), up, rs)) => throw new Exception("left of first")

def goRight[T]: Loc[T] => Loc[T] =
  case Loc(t, Top) => throw new Exception("right of top")
  case Loc(t, Node(ls, up, r::rs)) => Loc(r, Node(t::ls, up, rs))
  case Loc(t, Node(ls, up, List())) => throw new Exception("right of last")

def goUp[T]: Loc[T] => Loc[T] =
  case Loc(t, Top) => throw new Exception("up of top")
  case Loc(t, Node(ls, up, rs)) => Loc(Section(ls.reverse ++ (t::rs)), up)

def goDown[T]: Loc[T] => Loc[T] =
  case Loc(Item(_), _) => throw new Exception("down of item")
  case Loc(Section(t::ts), p) => Loc(t, Node(List(), p, ts))
  case Loc(Section(List()), _) => throw new Exception("down of empty")

// a * b + c * d
val ex1 = Section(List(
  Section(List(Item("a"), Item("*"), Item("b"))),
  Item("+"),
  Section(List(Item("c"), Item("*"), Item("d")))))

// location of the second mult
val loc1 = Loc(
  Item("*"),
  Node(
    List(Item("c")),
    Node(
      List(Item("+"), Section(List(Item("a"), Item("*"), Item("b")))),
      Top,
      List()
    ),
    List(Item("d"))
  )
)

@main def test() = {
  println(goLeft(loc1))
  /*
    Loc(
      Item(c),
      Node(
        List(),
        Node(
          List(Item(+), Section(List(Item(a), Item(*), Item(b)))),
          Top,
          List()
        ),
        List(Item(*), Item(d)))
    )
  */

  println(goUp(loc1))
}
package compositional

// An abstract domain to model return behavior with higher precision

enum RetVal:
  case NoRet
  case MustRet(v: AbsValue)
  case MayRet(v: AbsValue)

import RetVal._

given RetValLattice(using lav: Lattice[AbsValue]): Lattice[RetVal] with
  def bot: RetVal = NoRet
  def top: RetVal = MayRet(lav.top)
  extension (l1: RetVal)
    def ⊑(l2: RetVal): Boolean =
      (l1, l2) match {
        case (NoRet, _) => true
        case (_, NoRet) => false
        case (MustRet(v1), MustRet(v2)) => v1 ⊑ v2
        case (MustRet(v1), MayRet(v2)) => v1 ⊑ v2
        case (MayRet(v1), MustRet(v2)) => false
        case (MayRet(v1), MayRet(v2)) => v1 ⊑ v2
      }
    def ⊔(l2: RetVal): RetVal =
      (l1, l2) match {
        case (NoRet, _) => l2
        case (_, NoRet) => l1
        case (MustRet(v1), MustRet(v2)) => MustRet(v1 ⊔ v2)
        case (MustRet(v1), MayRet(v2)) => MayRet(v1 ⊔ v2)
        case (MayRet(v1), MustRet(v2)) => MayRet(v1 ⊔ v2)
        case (MayRet(v1), MayRet(v2)) => MayRet(v1 ⊔ v2)
      }
    def ⊓(l2: RetVal): RetVal = 
      (l1, l2) match {
        case (NoRet, _) => NoRet
        case (_, NoRet) => NoRet
        case (MustRet(v1), MustRet(v2)) => MustRet(v1 ⊓ v2)
        case (MustRet(v1), MayRet(v2)) => MustRet(v1 ⊓ v2)
        case (MayRet(v1), MustRet(v2)) => MustRet(v1 ⊓ v2)
        case (MayRet(v1), MayRet(v2)) => MayRet(v1 ⊓ v2)
      }


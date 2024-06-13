package partially.static.data

enum BindingTime:
  case Sta()
  case Dyn()

import BindingTime._

enum BT[T <: BindingTime]:
  case BTSta extends BT[Sta]
  case BTDyn extends BT[Dyn]

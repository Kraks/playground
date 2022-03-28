data Expr = EInt Int
          | EInc
          | EApp Expr Expr

tinc = EApp EInc (EApp EInc (EInt 2)) -- inc (inc 2)

data Dom = DError
         | DInt Int
         | DBool Bool
         | DFun (Dom -> Dom)

eval :: Expr -> Dom
eval (EInt x) = DInt x
eval EInc = DFun $ \x -> case x of
                           DInt n -> DInt (succ n)
                           _      -> DError
eval (EApp e1 e2) = case eval e1 of
  DFun f -> f (eval e2)
  _      -> DError


-- http://www.haskellforall.com/2012/06/you-could-have-invented-free-monads.html

data Toy b next =
    Output b next
  | Bell next
  | Done

{-
data Fix f = Fix (f (Fix f))

ex1 :: Fix (Toy Char)
ex1 = Fix (Output 'A' (Fix Done))

ex2 :: Fix (Toy Char)
ex2 = Fix (Bell (Fix (Output 'A' (Fix Done))))
--}

------

data FixE f e = Fix (f (FixE f e))
              | Throw e

catch :: (Functor f) => FixE f e1 -> (e1 -> FixE f e2) -> FixE f e2
catch (Fix x) f = Fix (fmap (flip catch f) x)
catch (Throw e) f = f e

instance Functor (Toy b) where
  fmap f (Output x next) = Output x (f next)
  fmap f (Bell     next) = Bell     (f next)
  fmap f  Done           = Done

data IncompleteExcpt = IncompleteExcpt

subroutine :: FixE (Toy Char) IncompleteExcpt
subroutine = Fix (Output 'A' (Throw IncompleteExcpt))

program :: FixE (Toy Char) e
program = subroutine `catch` (\_ -> Fix (Bell (Fix Done)))

-------

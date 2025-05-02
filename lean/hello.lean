#eval 1 + 2

#check "Hello"

def add1(n : Nat) : Nat := n + 1

#eval add1 3

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

def isZero (n : MyNat) : Bool :=
  match n with
  | MyNat.zero => true
  | MyNat.succ k => false

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')


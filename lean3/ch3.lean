/- Lean 3 code -/

/- 3.1 prop as types -/

namespace mylogic
  constant and : Prop → Prop → Prop
  constant or : Prop → Prop → Prop
  constant not : Prop → Prop → Prop
  constant implies : Prop → Prop → Prop
end mylogic

#check Prop
variables p q r : Prop
#check and p q
#check or p q
#check implies (and p q) (and p q)
#reduce implies (and p q) (and p q)

constant Proof : Prop → Type
constant and_comm' : Π p q : Prop,
  Proof (implies (and p q) (and q p))
#check and_comm p q

constant modus_ponens : Π p q : Prop,
  Proof (p → q) → Proof p → Proof q

constant implies_intro : Π p q : Prop,
  (Proof p → Proof q) → Proof (p → q)

/- Prop is syntactic sugar for Sort 0,
   Type u is also syntatic sugar for Sort (u+1).
-/
#check Prop
#check Sort 0

#check Type
#check Sort 1

#check Type 1
#check Sort 2

/- 3.2 Working with Props as Types -/

constants m n : Prop
theorem t1 : m → n → m := λ hm : m, λ hn : n, hm
#print t1

lemma t1' : m → n → m :=
  assume hm : m,
  assume hn : n,
  show m, from hm
#print t1'

theorem t1'' (hm : m) (hn : n) : m := hm
#check t1''

axiom hm : m
theorem t2 : n → m := t1 hm

-- Generalized t1
theorem t1''' (m n : Prop) (hm : m) (hn : n) : m := hm
#check t1'''

-- If p and q have been declared as variables,
-- Lean will generalize them for us automatically.
theorem t1'''' : ∀ (p q : Prop), p → q → p :=
  λ (p q : Prop) (hp : p) (hq : q), hp

variables s : Prop
#check t1''' p q
#check t1''' r s

variable h : r → s
#check t1''' (r → s) (s → r) h

theorem t3 (h1 : q → r) (h2 : p → q) : p → r :=
assume h3 : p,
show r, from h1 (h2 h3)

/- 3.3 Propositional Logic -/

#check p → q → p ∧ q
#check ¬ p → p ↔ false
#check p ∨ q → q ∨ p

/- Conjunction -/

example (hp : p) (hq : q) : p ∧ q :=
  and.intro hp hq

#check assume(hp : p) (hq : q), and.intro hp hq

example (h : p ∧ q) : p := and.elim_left h
example (h : p ∧ q) : q := and.elim_right h

example (h : p ∧ q) : q ∧ p :=
  and.intro (and.right h) (and.left h)

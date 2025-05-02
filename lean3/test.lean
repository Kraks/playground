/- Lean 3 code -/

constants p q : Prop
theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
#print t1

lemma t1' : p → q → p :=
  assume hp : p,
  assume hq : q,
  show p, from hp
#print t1'

theorem t1'' (hp : p) (hq : q) : p := hp
#check t1''

axiom hp : p
--theorem t2 : q → p := t1 hp

theorem t1''' (p q : Prop) (hp : p) (hq : q) : p := hp
#check t1'''

theorem t2 : q → p := t1'' hp
variable {p q r : Prop}

theorem t1 : p -> q -> p :=
  fun hp : p => fun hq : q => hp

#print t1

theorem t1' : p -> q -> p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

#print t1'

theorem t1'' (hp : p) (hq : q) : p := hp

#print t1''

axiom hp : p

theorem t2 : q → p := t1 hp

axiom unsound : False
theorem ex : 1 = 0 := False.elim unsound

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

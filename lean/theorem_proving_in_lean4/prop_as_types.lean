-- Chapter 3

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

variable (s : Prop)

theorem t3 (h1 : q -> r) (h2 : p -> q) : p -> r :=
  fun h3 : p => show r from h1 (h2 h3)

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

-- Conjunction

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

variable (xs : List Nat)

#check List.length xs
#check xs.length

-- Disjunction

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

-- Negation

example (hpq : p -> q) (nq : ¬q) : ¬p :=
  fun hp : p =>
    show False from nq (hpq hp)

example (hp : p) (hnp : ¬p) : q :=
  False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q :=
  absurd hp hnp
example (hnp : ¬p) (hq : q) (hqp : q -> p) : r :=
  absurd (hqp hq) hnp

-- Logical equivalence

theorem and_swap : p ∧ q <-> q ∧ p :=
  Iff.intro
    (fun h : p /\ q =>
      show q /\ p from ⟨h.right, h.left⟩)
    (fun h : q /\ p =>
      show p /\ q from ⟨h.right, h.left⟩)

theorem and_swap' : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

-- Auxiliary subgoals

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from ⟨hq, hp⟩
  show q from And.right h

-- Classical logic

-- Chapter 4

example (α : Type) (p q : α → Prop) :
  (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    fun h =>
    fun y : α =>
    show p y from (h y).left

-- Equality

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α β : Type)

section
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)
  example : a = d :=
    Eq.trans hab (Eq.trans (Eq.symm hcb) hcd)
  -- or the projectio notation:
  example : a = d :=
    hab.trans (hcb.symm.trans hcd)
end

example (f : α → β) (a : α) : (fun x => f x) a = f a :=
  Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
-- rfl is a notation for `Eq.refl _` defined in the library
example : 2 + 3 = 5 := rfl

-- substituting h2[a ↦ b] = p b
-- or, in Coq this would be a rewrite.
example (α : Type) (a b : α) (p : α -> Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

-- ▸ (\t) is a macro using Eq.subst and Eq.symm
example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b := h1 ▸ h2

section
  variable (a b : α)
  variable (f g : α → Nat)
  variable (h₁ : a = b)
  variable (h₂ : f = g)
  -- congruences defined using subst
  -- a = b -> f a = f b
  example : f a = f b := congrArg f h₁
  -- f = g -> f a = g b
  example : f a = g a := congrFun h₂ a
  -- a = b -> f = g -> f a = g b
  example : f a = g b := congr h₂ h₁
end

#check Eq.subst
-- Eq.subst requires an implicit argument {motive : α → Prop},
-- to infer such an argument lean uses incomplete higher-order unification.

example (x y : Nat) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 := Nat.mul_add (x + y) x y
  have h2 := (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

-- Calculational proofs

section
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)
  include a b c d e h1 h2 h3 h4

  theorem T : a = e :=
    calc
      a = b := h1
      _ = c + 1 := h2
      _ = d + 1 := congrArg Nat.succ h3
      _ = 1 + d := Nat.add_comm d 1
      _ = e := Eq.symm h4

  theorem T' : a = e :=
    calc
      a = b := by rw [h1]
      _ = c + 1 := by rw [h2]
      _ = d + 1 := by rw [h3]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e := by rw [h4]

  theorem T'' : a = e :=
    by rw [h1, h2, h3, Nat.add_comm, h4]

  theorem T''' : a = e :=
    by simp [h1, h2, h3, Nat.add_comm, h4]
end

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

-- calc with Trans instances

def divides (x y : Nat) : Prop := ∃ k, k * x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k1, d1⟩ := h₁
  let ⟨k2, d2⟩ := h₂
  ⟨k1 * k2, by rw [Nat.mul_comm k1 k2, Nat.mul_assoc, d1, d2]⟩

def divides_mul (x k : Nat) : divides x (k * x) := ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h1 : divides x y) (h2 : y = z) : divides x (2 * z) :=
  calc
    divides x y := h1
    _ = z := h2
    divides _ (2 * z) := divides_mul ..

infix:50 " ∣ " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x ∣ y   := h₁
    _ = z   := h₂
    _ ∣ 2*z := divides_mul ..

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

-- Existential quantifier

example : ∃ x : Nat, x > 0 := Exists.intro 1 (Nat.zero_lt_succ 0)

example (x : Nat) (h : x > 0) : ∃ y, y < x := Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

/- Lean 3 code -/

/- declare some constants -/
constant m : nat
constant n : nat
constants b1 b2 : bool

/- check their types -/
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check tt

constant f : nat → nat
constant f' : ℕ → ℕ
#check f'
constant p : ℕ × ℕ
#check p
#check p.fst
constant p' : ℕ × ℕ × ℕ
#check p'
#check p'.snd.snd

constant F : (ℕ → ℕ) → ℕ
#check F
#check F f

/- 2.2 Types as Objects -/

#check nat
#check nat → nat
#check (ℕ → ℕ) → ℕ

constants α β γ : Type
constant F' : Type → Type
#check F' α
#check prod α β
#check α × β
#check list α

#check Type
#check Type 0
#check Type 1
#check Type 2

#check Prop

#check list
#check prod
#check (×)

universe u
constant myu : Type u
#check myu

/- Function Abstraction and Evaluation -/

#check fun x : ℕ, x + 5
#check λ x : ℕ, x + 5

constants a1 a2 : α
constants c1 c2 : β

constant h : α → β
#check λ x : α, h x
#check λ g : β, h

#check λ b : β, λ x : α, x
#check λ (b : β)(x : α), b

#check λ (α β : Type)(b : β)(x : α), x

#check (∘)
#check (∘)(∘)
#check (∘)(∘)(∘)(∘)

constant a : α
constant f1 : α → β
constant f2 : β → γ
constant f3 : α → α
#check (λ (Q R S : Type)
          (v : R → S)
          (u : Q → R)
          (x : Q), v (u x)) α β γ f2 f1 a
#reduce (λ (Q R S : Type)
           (v : R → S)
           (u : Q → R)
           (x : Q), v (u x)) α β γ f2 f1 a

#print "reducing pairs"
#reduce (1, 2).1
#reduce (1, 2, 3).2
#reduce tt && ff
#reduce b1 && ff

#reduce n + 0
#reduce 0 + n
#reduce n + 1

#eval 123 * 456
#eval 3.14 * 2 -- float?

/- Introducing Definitions -/

def foo : (ℕ → ℕ) → ℕ := λ f, f 0
def foo' := λ f : ℕ → ℕ, f 0
#check foo
#print foo

def double (x : ℕ) := x + x
#print double
#check double
#reduce double 3
#eval double 3

def square (x : ℕ) := x * x
#print square
#check square 3
#reduce square 3    -- 9

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)
#reduce do_twice double 2

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
#check compose

def quadruple (x : ℕ) : ℕ := compose ℕ ℕ ℕ double double x

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ :=
    λ (x : α)(y : β), f (x, y)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ :=
    λ (p : α × β), f p.1 p.2

/- Local Definitions -/

#check let y := 2 + 2 in y * y
#reduce let y := 2 + 2 in y * y

def t (x : ℕ) : ℕ :=
  let y := x + x in y * y

#reduce t 3

def bar := let a := ℕ in
  λ x : a, x + 2
#check bar

/- Variables and Sections -/

def do_twice' (α : Type) (h : α → α) (x : α) : α := h (h x)

section useful
  variables (α β γ : Type)

  def do_twice'' (h : α → α) (x : α) : α := h (h x)

  variables (g : β → γ) (f : α → β) (h : α → α)
  variables (x : α)
  def do_twice''' := h (h x)

  #print do_twice'''
end useful

variables (x : β)

/- Namespaces -/

namespace foo
  def a : ℕ := 5
  def f (x : ℕ) : ℕ := x + 1
  def fa := f a
  #check fa
  #print "Indside foo"
end foo

#check foo.fa
open foo
#check fa

#check list.nil
#check list.cons
#check list.append

-- Reopen a namespace
namespace foo
  def ffa := f (f a)
end foo

#check foo.ffa

/- Dependent Types -/

namespace hidden
  universe myu
  constant list  : Type myu → Type myu
  constant cons  : Π α : Type myu, α → list α → list α
  constant nil   : Π α : Type myu, list α
  constant head  : Π a : Type myu, list α → α
  constant tail  : Π a : Type myu, list α → list α
  constant append : Π a : Type myu, list α → list α → list α
end hidden

open list
#check list
#check cons
#check @cons
#check @nil
#check @tail
#check @append

constant vec : Type u → ℕ → Type u
namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons : Π (α : Type u) (n : ℕ),
    α → vec α n → vec α (n + 1)
  constant append : Π (α : Type u) (n m : ℕ),
    vec α m → vec α n → vec α (n + m)
end vec

-- Sigma types, Σ x : α, β x
-- sigma.mk a b where a : α and b : β

namespace dp
  variable α : Type
  variable β : α → Type
  variable a : α
  variable b : β a

  #check sigma.mk
  #check @sigma.mk

  #check sigma.mk a b
  #check (sigma.mk a b).1
  #check (sigma.mk a b).2

  #reduce (sigma.mk a b).1
  #reduce (sigma.mk a b).2
end dp

/- Implicit Arguments -/

open hidden
variable α : Type
variable a : α
#check cons _ a (nil _)

namespace mylist
  constant list : Type u → Type u
  constant cons : Π {α : Type u}, α → list α → list α
  constant nil : Π {α : Type u}, list α
  constant append : Π {α : Type u}, list α → list α → list α
end mylist

#check mylist.cons a mylist.nil
variables l1 l2 : mylist.list α
#check mylist.append (mylist.cons a mylist.nil) l1

def ident {α : Type u} (x : α) := x
#check ident
#check ident a
#check (ident : ℕ → ℕ)

#check 2
#check (2 : ℤ)
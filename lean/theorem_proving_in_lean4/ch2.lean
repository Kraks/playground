-- Chapter 2

-- Simple type theory

def m: Nat := 1
def n: Nat := 0
def b1: Bool := true
def b2: Bool := false

#check n + 0

-- Types and objects

#check Nat
#check Nat -> Nat
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check Type
#check Type 1

universe u

def H(α : Type u): Type u := Prod α α

#check H

-- def H.{u} (a : Type u): Type u := sorry

-- Function abstraction

#eval (λ x : Nat => x + 5) 10    -- 15
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

def pi := 3.141592654

-- Local definition

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

#check compose

-- Namespaces

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

#check Foo.a

open Foo
#check a

-- implicit arguments

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"

#check List.nil
#check id

#check (List.nil : List Nat)
#check (id : Nat → Nat)

-- provide implicit arguments explicitly
#check @id
#check @id Nat
#check @id Bool true

-- https://lean-lang.org/lean4/doc/examples/deBruijn.lean.html

-- Heterogeneous lists
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
| nil : HList β []
| cons : β i → HList β is → HList β (i :: is)

-- overload List.cons
infix:67 " :: " => HList.cons
-- [] for the empty list
notation "[" "]" => HList.nil

inductive Member : α → List α -> Type
| head : Member a (a :: as)
| tail : Member a bs → Member a (b :: bs)

def HList.get : HList β is → Member i is → β i
| a :: as, .head => a
| a :: as, .tail h => as.get h

inductive Ty where
| nat
| fn : Ty → Ty → Ty

@[reducible] def Ty.denote : Ty -> Type
| nat => Nat
| fn a b => a.denote → b.denote

inductive Term : List Ty -> Ty -> Type
| var : Member ty ctx -> Term ctx ty
| const : Nat -> Term ctx .nat
| plus : Term ctx .nat -> Term ctx .nat -> Term ctx .nat
| app : Term ctx (.fn dom ran) -> Term ctx dom -> Term ctx ran
| lam : Term (dom :: ctx) ran -> Term ctx (.fn dom ran)
| «let» : Term ctx ty₁ -> Term (ty₁ :: ctx) ty₂ -> Term ctx ty₂

open Ty Term Member

def add : Term [] (fn nat (fn nat nat)) :=
  lam (lam (plus (var (tail head)) (var head)))

def three : Term [] nat :=
  app (app add (const 1)) (const 2)

@[simp] def Term.denote : Term ctx ty -> HList Ty.denote ctx -> ty.denote
| var h, ρ => ρ.get h
| const m, _ => m
| plus a b, ρ => a.denote ρ + b.denote ρ
| app f a, ρ => f.denote ρ (a.denote ρ)
| lam b, ρ => fun x => b.denote (x :: ρ)
| «let» a b, ρ => b.denote (a.denote ρ :: ρ)

example : three.denote [] = 3 := rfl

@[simp] def Term.constFold : Term ctx ty -> Term ctx ty
| const n => const n
| var h => var h
| app f a => app f.constFold a.constFold
| lam b => lam b.constFold
| «let» a b => «let» a.constFold b.constFold
| plus a b =>
  match a.constFold, b.constFold with
  | const n, const m => const (n + m)
  | a', b' => plus a' b'

theorem Term.constFold_sound (e : Term ctx ty) :
  e.constFold.denote ρ = e.denote ρ := by
  induction e with
  | const n => simp
  | var h => simp
  | plus a b iha ihb =>
    simp
    split
    next he1 he2 => simp [<- iha, <- ihb, he1, he2]
    next => simp [iha, ihb]
  | app f a => simp [*]
  | lam b => simp [*]
  | «let» a b iha ihb => simp [*]



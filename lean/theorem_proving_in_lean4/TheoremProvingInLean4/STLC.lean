inductive ty : Type
| unit : ty
| arrow : ty → ty → ty

inductive tm : Type
| bvar : Nat → tm
| fvar : Nat → tm
| abs : tm → tm
| app : tm → tm → tm

@[simp]
def subst (src : Nat) (tgt : tm) : tm → tm
| .bvar i => .bvar i
| .fvar i => if i = src then tgt else .fvar i
| .abs t => .abs (subst src tgt t)
| .app t₁ t₂ => .app (subst src tgt t₁) (subst src tgt t₂)

example :
  subst 0 (.fvar 1) (.abs (.app (.bvar 0) (.fvar 0))) =
  .abs (.app (.bvar 0) (.fvar 1)) := by
  simp

def fv (t: tm): Set Nat
| .bvar i => {}
| .fvar i => {i}
| .abs t => fv t
| .app t₁ t₂ => fv t₁ ∪ fv t₂

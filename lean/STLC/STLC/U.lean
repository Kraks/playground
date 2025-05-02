import Mathlib.Data.Finset.Sort
import STLC.Env

namespace U

inductive ty : Type
| bool : ty
| arrow : ty → ty → ty
| code : ty → ty

inductive tm : Type
| tru : tm
| fls : tm
| bvar : ℕ → tm
| fvar : ℕ → tm
| abs : tm → tm
| app : tm → tm → tm
| quo : tm → tm
| esc : tm → tm
| run : tm → tm

-- exact level: the nesting depth of escapes
@[simp]
def lv : tm → ℕ
| .tru | .fls => 0
| .bvar _ => 0
| .fvar _ => 0
| .abs t => lv t
| .app t1 t2 => max (lv t1) (lv t2)
| .quo t => max (lv t - 1) 0
| .esc t => lv t + 1
| .run t => lv t

@[simp]
def closedF (t: tm) (n: ℕ) : Prop :=
  match t with
  | .tru | .fls => true
  | .bvar _ => true
  | .fvar x => x < n
  | .abs t1 => closedF t1 n
  | .app t11 t12 => closedF t11 n ∧ closedF t12 n
  | .quo t1 => closedF t1 n
  | .esc t1 => closedF t1 n
  | .run t1 => closedF t1 n

@[simp]
def closedB (t: tm) (n: ℕ) : Prop :=
  match t with
  | .tru | .fls => true
  | .bvar x => x < n
  | .fvar _ => true
  | .abs t1 => closedB t1 (n + 1)
  | .app t11 t12 => closedB t11 n ∧ closedB t12 n
  | .quo t1 => closedB t1 n
  | .esc t1 => closedB t1 n
  | .run t1 => closedB t1 n

inductive value : ℕ → tm → Prop
| fls : value 0 .fls
| tru : value 0 .tru
| abs : ∀ t, lv t = 0 → value 0 (.abs t)
| code : ∀ t, lv t = 0 → value 0 (.quo t)
| expr : ∀ t i, lv t = i → value (i+1) t

def expr i := ∀ (t : tm), lv t ≤ i

def topWf e := lv e = 0 ∧ closedF e 0 ∧ closedB e 0

def erase (t : tm) : tm :=
  match t with
  | .tru => .tru
  | .fls => .fls
  | .bvar x => .bvar x
  | .fvar x => .fvar x
  | .abs t1 => .abs (erase t1)
  | .app t11 t12 => .app (erase t11) (erase t12)
  | .quo t1 => erase t1
  | .esc t1 => erase t1
  | .run t1 => erase t1

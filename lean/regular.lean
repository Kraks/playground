open Sum
open Option

inductive Op where
| Plus
| Minus
| Mult
deriving Repr

inductive AExpr where
| ENat : Nat -> AExpr
| EVar : String -> AExpr
| EBinOp : Op -> AExpr -> AExpr -> AExpr
deriving Repr

inductive BExpr where
| BLess : AExpr -> AExpr -> BExpr
| BNand : BExpr -> BExpr -> BExpr
deriving Repr

@[reducible] def Expr := AExpr ⊕ BExpr

@[reducible] def Label := Nat

mutual
  inductive Stmt : Type where
  | Skip
  | Assign (x: String) (rhs : Expr)
  | Cond (cnd : BExpr) (thn : LabStmt) (els : LabStmt)
  | While (e: BExpr) (body: LabStmt)
  | Sequ (s₁ : LabStmt) (s₂ : LabStmt)
  inductive LabStmt : Type where
  | LStmt (ℓ : Label) (s : Stmt)
end

deriving instance Repr for Stmt, LabStmt

inductive Value : Type where
| NatV (n : Nat)
| BoolV (b : Bool)
/-
instance : Repr Expr where
  reprPrec e n := match e with
  | Sum.inl a => reprPrec a n
  | Sum.inr b => reprPrec b n
-/

open Op
open AExpr
open BExpr
open Stmt
open LabStmt
open Value

#eval (LStmt 0 Skip)

#eval (inl (ENat 3) : AExpr ⊕ BExpr)
#eval (EVar "x")

@[reducible] def Store := String -> Option Value

def aeval (e : AExpr) (σ : Store): Option Value := match e with
| ENat n => NatV n
| EVar x => σ x
| EBinOp op e₁ e₂ =>
  match op with
  | Plus =>
    (match (aeval e₁ σ, aeval e₂ σ) with
    | (some (NatV v1), some (NatV v2)) => some (NatV (v1 + v2))
    | _ => none)
  | Mult =>
    match (aeval e₁ σ, aeval e₂ σ) with
    | (some (NatV v1), some (NatV v2)) => some (NatV (v1 * v2))
    | _ => none
  | Minus =>
    match (aeval e₁ σ, aeval e₂ σ) with
    | (some (NatV v1), some (NatV v2)) => some (NatV (v1 - v2))
    | _ => none

def beval (b : BExpr) (σ : Store): Option Value := match b with
| BLess e₁ e₂ =>
  match (aeval e₁ σ, aeval e₂ σ) with
  | (NatV v₁, NatV v₂) => BoolV (Nat.ble v₁ v₂)
  | _ => none
| BNand b₁ b₂ => sorry

def eval (e : Expr) (σ : Store): Option Value := match e with
| inl a => aeval a σ
| inr b => beval b σ

-- Note: this is a partial function. Could modeled with a fuel argument too
partial def exec (ls: LabStmt) (σ : Store) : Option Store := match ls with
| LStmt ℓ s => match s with
  | Skip => σ
  | Assign x rhs => fun (y: String) => if (x == y) then eval rhs σ else σ x
  | Cond cnd thn els =>
    match beval cnd σ with
    | BoolV b => if (b) then exec thn σ else exec els σ
    | _ => none
  | While cnd body =>
    match beval cnd σ with
    | BoolV b =>
      match (if (b) then exec body σ else σ) with
      | some σ₁ => exec ls σ₁
      | none => none
    | _ => none
  | Sequ s₁ s₂ =>
    match (exec s₁ σ) with
    | some σ₁ => exec s₂ σ₁
    | none => none

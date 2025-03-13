inductive Expr : Type
| Lit : Nat -> Expr
| Add : Expr -> Expr -> Expr

def eval (e : Expr) (k : Nat -> Nat): Nat :=
  match e with
  | Expr.Lit n => n
  | Expr.Add e1 e2 =>
    eval e1 (fun v1 => eval e2 (fun v2 => k (v1 + v2)))

-- https://lean-lang.org/lean4/doc/examples/bintree.lean.html

inductive Tree (β : Type v) where
| leaf
| node (left : Tree β) (key: Nat) (value : β) (right : Tree β)
deriving Repr

def Tree.contains (t : Tree β) (k : Nat) : Bool :=
  match t with
  | leaf => false
  | node left key value right =>
    if k < key then left.contains k
    else if k > key then right.contains k
    else true

def Tree.find? (t : Tree β) (k : Nat) : Option β :=
  match t with
  | leaf => none
  | node left key value right =>
    if k < key then left.find? k
    else if k > key then right.find? k
    else some value

def Tree.insert (t : Tree β) (k : Nat) (v : β) : Tree β :=
  match t with
  | leaf => node leaf k v leaf
  | node left key value right =>
    if k < key then node (left.insert k v) key value right
    else if k > key then node left key value (right.insert k v)
    else node left k v right

def Tree.toList (t : Tree β) : List (Nat × β) :=
  match t with
  | leaf => []
  | node l k v r => l.toList ++ [(k, v)] ++ r.toList

def Tree.toListTR (t : Tree β) : List (Nat × β) :=
  go t []
  where
  go (t : Tree β) (acc : List (Nat × β)) : List (Nat × β) :=
    match t with
    | leaf => acc
    | node l k v r => go l ((k, v) :: go r acc)

theorem Tree.toList_eq_toListTR (t : Tree β) :
  t.toList = t.toListTR := by
  simp [toListTR, go t []]
  where
  go (t : Tree β) (acc: List (Nat × β)) : toListTR.go t acc = t.toList ++ acc := by
    induction t generalizing acc with
    | leaf => simp [toListTR.go, toList]
    | node l k v r => simp [toListTR.go, toList, *, List.append_assoc]

@[csimp] theorem Tree.toList_eq_toListTR_csimp : @Tree.toList = @Tree.toListTR :=
  by
    funext β t
    apply toList_eq_toListTR

inductive ForallTree (p : Nat → β → Prop) : Tree β → Prop
| leaf : ForallTree p .leaf
| node : ForallTree p left ->
         p key value ->
         ForallTree p right ->
         ForallTree p (.node left key value righ)

local macro "have_eq " lhs:term:max rhs:term:max : tactic =>
  `(tactic|
    (have h : $lhs = $rhs :=
       by simp_arith at *; apply Nat.le_antisymm <;> assumption
     try subst $lhs))

-- by_cases followed by simp using all hypotheses
local macro "by_cases' " e:term : tactic =>
  `(tactic| by_cases $e <;> simp [*])

-- instruct the simplifier to reduce given definitions
-- or apply rewrite theorems.
attribute [local simp] Tree.insert

theorem Tree.forall_insert_of_forall
  (h₁ : ForallTree p t) (h₂ : p key value) : ForallTree p (t.insert key value) := by
  induction h₁ with
  | leaf => exact .node .leaf h₂ .leaf
  | node hl hp hr ihl ihr =>
   rename Nat => k
   by_cases' key < k
   . exact .node ihl hp hr
   . by_cases' k < key
     . exact .node hl hp ihr
     . have_eq key k
       exact .node hl h₂ hr


Require Import Cpdt.CpdtTactics.

Check (fun x : nat => x).

Check (fun x : True => x).

Check I.

Check (fun _ : False => I).

(* Enumeration *)

Inductive unit : Set := tt.

Theorem unit_singleton : forall x : unit, x = tt.
Proof.
  induction x. reflexivity.
Qed.

Check unit_ind.

(* Set: the type of normal types, the values of Set are programs.
 * Prop: the type of logical propositions, the values of Prop are proofs
 *)

Inductive EmptySet : Set := .

Theorem the_sky_is_falling : forall x : EmptySet, 2 + 2 = 5.
Proof.
  intros. destruct x.
Qed.

Check EmptySet_ind.

Definition e2u (e : EmptySet) : unit := match e with end.

Inductive bool : Set :=
| true
| false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition negb' (b : bool) : bool :=
  if b then false else true.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
Proof.
  destruct b; simpl; reflexivity.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
  destruct b; discriminate.
Qed.

Check bool_ind.

(* Simple Recursive Types *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition isZero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Theorem O_plus_n : forall n : nat, plus O n = n.
  intro; reflexivity.
Qed.

Theorem n_plus_O : forall n : nat, plus n O = n.
  induction n; simpl; auto.
  rewrite IHn. reflexivity.
Qed.

Check nat_ind.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
  intros. inversion H. auto.
Qed.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
    | NNil => O
    | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
    | NNil => ls2
    | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_napp : forall ls1 ls2 : nat_list,
    nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
  induction ls1; crush.
Qed.

Check nat_list_ind.

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
    | NLeaf => S O
    | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (t1 t2 : nat_btree) : nat_btree :=
  match t1 with
  | NLeaf => NNode t2 O NLeaf
  | NNode t1' n t2' => NNode (nsplice t1' t2) n t2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
  induction n1; crush.
Qed.

Hint Rewrite n_plus_O plus_assoc.

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree,
    nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1).
  induction tr1; crush.
Qed.

Check nat_btree_ind.

(* Parameterized Types *)

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.
  

  Fixpoint length (ls : list) : nat :=
    match ls with
      | Nil => O
      | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall ls1 ls2 : list, length (app ls1 ls2)
    = plus (length ls1) (length ls2).
    induction ls1; crush.
  Qed.

End list.

Arguments Nil {T}.

Print list.

Check length.

Check list_ind.

(* Mutually Inductive Types *)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list
with odd_list : Set :=
| OCons : nat -> even_list -> odd_list
.

Fixpoint elength (el : even_list) : nat :=
  match el with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end
with olength (ol : odd_list) : nat :=
  match ol with
  | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end
with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

Check even_list_mut.
Check odd_list_mut.

Theorem n_plus_O' : forall n, plus n O = n.
  apply nat_ind.
  Undo.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

Theorem elength_eapp : forall el1 el2 : even_list,
    elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  apply (even_list_mut
           (fun el1 : even_list => forall el2 : even_list,
                elength (eapp el1 el2) = plus (elength el1) (elength el2))
           (fun ol : odd_list => forall el : even_list,
                olength (oapp ol el) = plus (olength ol) (elength el))).
  - intros. simpl. reflexivity.
  - intros. simpl. f_equal. rewrite H. reflexivity.
  - intros. simpl. f_equal. rewrite H. reflexivity.
Qed.

(* Reflexive Types *)

(* Encoding the syntax of first-order logic *)

Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula -> pformula -> pformula
.

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
  | Truth => True
  | Falsehood => False
  | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula
.

Example forall_refl : formula := Forall (fun x => Eq x x).

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
    | Eq n1 n2 => n1 = n2
    | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f : formula) : formula :=
  match f with
    | Eq n1 n2 => Eq n2 n1
    | And f1 f2 => And (swapper f2) (swapper f1)
    | Forall f' => Forall (fun n => swapper (f' n))
  end.

Theorem swapper_preserves_truth : forall f, formulaDenote f -> formulaDenote (swapper f).
  induction f; crush.
Qed.

Check formula_ind.

(* An Interlude on Induction Principles *)

Print nat_ind.  (* Prop *)
Print nat_rect. (* Type *)
Print nat_rec.  (* Set *)

(* Type is a supertype of Set and Prop *)

Fixpoint plus_recursive (n : nat) : nat -> nat :=
  match n with
    | O => fun m => m
    | S n' => fun m => S (plus_recursive n' m)
  end.

Definition plus_rec : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun _ rec m => S (rec m)).

Theorem plus_equivalent : plus_recursive = plus_rec.
  reflexivity.
Qed.



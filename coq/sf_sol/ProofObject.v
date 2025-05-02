Set Warnings "-notation-overridden,-parsing".
Require Import IndProp.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros. simpl.
  apply ev_SS. apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

(* Programming with Tactics *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Show Proof.
Defined.

Print add1.
Compute add1 2.

Theorem add1' : forall n : nat, nat.
Proof.
  intros.
  Show Proof.
  apply S.
  Show Proof.
  apply n.
  Show Proof.
Qed.

(* Logical Connectives as Inductive Types *)

Module Props.

(* Conjunction *)

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Print prod.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros. split.
  - intros [HP HQ]. split.
    apply HQ.
    apply HP.
  - intros [HQ HP]. split.
    apply HP.
    apply HQ.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(* Exercise *)

Definition conj_fact : forall P Q R,
  P /\ Q -> Q /\ R -> P /\ R.
intros P Q R [HP HQ] [HQ' HR].
apply conj.
apply HP. apply HR.
Defined.

(* Disjunction *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.

(* Exercise *)

Definition or_com : forall P Q, P \/ Q -> Q \/ P :=
  fun (P: Prop) => fun (Q : Prop) =>
    fun (PQ : P \/ Q) => match PQ with
      | or_introl P => or_intror P
      | or_intror Q => or_introl Q
      end.

(* Existential Quantification *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* Exercise *)
Check ev_SS 0 ev_0.
Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) (S 0) (ev_SS 0 ev_0).

(* True and False *)

Inductive True : Prop :=
  | I : True.
Inductive False : Prop :=.

End Props.

(* Equality *)

Module MyEquality.

Inductive eq {X : Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.


Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

(* Exercises *)

Lemma leibniz_equality: forall (X: Type) (x y: X),
  eq x y -> forall P: X -> Prop, P x -> P y.
Proof.
  intros. destruct H. apply H0.
Qed.

(* The reflexivity tactic that we have used to prove 
   equalities up to now is essentially just short-hand 
   for apply eq_refl. *)

Lemma four : 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X : Type) (x : X), []++[x] = x::[] :=
  fun (X : Type) (x : X) => eq_refl [x].

(* Inversion, Again *)

(* In general, the inversion tactic
   takes a hypothesis H whose type P is inductively defined, and,
   for each constructor C in P's definition,
     1. generates a new subgoal in which we assume H was built with C,
     2. adds the arguments of C to the context of the subgoal as extra hypotheses,
     3. matches the conclusion of C against the current goal and calculates a se
        of equalities that must hold in order for C to be applicable,
     4. adds these equalities to the context
     5. if the equalities are not satisfiable, immediately solves the subgoal.
*)

End MyEquality.

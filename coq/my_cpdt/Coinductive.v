Require Import List.
Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Infinite Data *)

Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

(* recursive definitions use values of recursive inductive types,
co-recursive definitions build values of co-inductive types. *)

(* a stream of all zeros *)
CoFixpoint zeroes : stream nat := Cons 0 zeroes.

(* streams that alternate between true and false*)

CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

(* finite approximation of a stream *)

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with 
    | Cons h t => h :: approx t n'
    end
  end.

Eval simpl in approx zeroes 10.

(* Fixpoints consume values of inductive types, with restrictions on which
  arguments may be passed in recursive calls. Dually, co-fixpoints produce values
  of co-inductive types, with restrictions on what may be done with the results of
  co-recursive calls. *)

(* every co-recursive call must be a direct argument to a constructor of the
   co-inductive type we are generating *)

Section map.
  Variables A B : Type.
  Variable f : A -> B.
  CoFixpoint map (s : stream A) : stream B :=
    match s with
    | Cons h t => Cons (f h) (map t)
    end.
End map.

Section interleave.
  Variable A : Type.
  CoFixpoint interleave (s1 s2 : stream A): stream A :=
    match s1, s2 with
    | Cons h1 t1, Cons h2 t2 =>
      Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Section map'.
  Variables A B : Type.
  Variable f : A -> B.
  (* This won't work *)
  (* CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
    *)
End map'.

(* Infinite Proof *)

CoFixpoint ones : stream nat := Cons 1 ones.

Definition ones' := map S zeroes.

Theorem ones_eq : ones = ones'.
Proof.
  (* unprovable. eq can only be used for finite syntactic arguments *)
  Abort.

Section stream_eq.
  Variable A : Type.
  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2 ->
    stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Theorem ones_eq : stream_eq ones ones'.
Proof.
  cofix ones_eq.
  assumption. (* violating the guardedness condition *)
  Undo.
  Abort.

Definition frob A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A), s = frob s.
Proof.
  destruct s; reflexivity.
Qed.

Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  simpl.
  constructor.
  assumption.
Qed.

Definition tl A (s : stream A) : stream A :=
  match s with
    | Cons _ s' => s'
  end.

Definition hd A (s : stream A) : A :=
  match s with
    | Cons x _ => x
  end.

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.
  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).
  
  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
  Proof.
    cofix stream_eq_coind; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd H).
    intro. simpl in H0. rewrite H0.
    constructor. apply stream_eq_coind.
    apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

Print stream_eq_coind.

  Theorem ones_eq'' : stream_eq ones ones'.
  Proof. 
    apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); intros.
    - crush. (* TODO: what does thid do? *)
    - crush.
    - crush.
  Qed.


      
      

     
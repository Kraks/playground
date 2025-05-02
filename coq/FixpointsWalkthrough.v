
Section Sets.

  (* Extensional: Enumeration *)
  (* Seen this style of definition before... *)
  Definition Set' (A : Type) := list A.

  (* Intensional: Characteristic 'Function' *)
  Definition Bool_Set (A : Type) := A -> bool.

  (* Definition evens' : Bool_Set nat := evenb. *)

  Definition In_b {A} (a : A) (e : Bool_Set A) : Prop :=
    e a = true.

  Definition Same_Set' {A} (e1 e2 : Bool_Set A) : Prop :=
    forall x, e1 x = e2 x.

  (* How to define Intersection, Union, Subset ? *)
  Definition Union' {A} (e1 e2 : Bool_Set A) : Bool_Set A :=
    fun x => orb (e1 x) (e2 x).

  Definition Intersection' {A} (e1 e2 : Bool_Set A)
    : Bool_Set A :=
    fun x => andb (e1 x) (e2 x).

  Definition Subset' {A} (e1 e2 : Bool_Set A) : Prop :=
    forall x, In_b e1 x -> In_b e2 x.

  (* This encoding of sets means membership is always decideable! *)
  
End Sets.

Section Fixpoints.

  (* Propositional analogues to definitions from above. *)

  Definition PSet (A : Type) := A -> Prop.
  
  Definition In {A} (a : A) (e : PSet A) : Prop := e a.
  Notation "x '∈' e" := (In x e) (at level 60).

  Definition Subset {A} (e1 e2 : PSet A) : Prop :=
    forall x, x ∈ e1 -> x ∈ e2.
  
  Notation "s1 ⊆ s2" := (Subset s1 s2) (at level 60).
  
  Context {U : Type}. (* The universal set, i.e. our domain of discourse. *)
  Variable F : (PSet U) -> PSet U. (* Our generating function--
  takes a set of Us and builds a new set.*)

  (* A generator function is monotone if it preserves the subset
  relation on its argument. *)
  Definition Monotone_F : Prop :=
    forall (S S' : PSet U),
      S ⊆ S' -> F S ⊆ F S'.
  
  Definition FClosed (S : PSet U) : Prop := F S ⊆ S.
  
  Definition FConsistent (S : PSet U) : Prop := S ⊆ F S.
  
  Definition FixedPoint (S : PSet U) : Prop :=
    S ⊆ F S /\ F S ⊆ S.

  (* The least fixed point of a monotone generator function exists,
   and it is the intersection of all F-closed sets. *)
  Definition LFP : PSet U :=
    fun a => forall S, FClosed S -> S a.

  (* The greatest fixed point of a generator function exists, 
   and it is the union of all F-consistent sets. *)
  Definition GFP : PSet U :=
    fun a => exists S, FConsistent S /\ S a.

  Lemma GFP_is_FConsistent 
    : Monotone_F -> FConsistent GFP.
  Proof.
    intros F_Monotone. 
    unfold FConsistent.
    intros ? ?.
    (* By the definition of GFP, there must be some F-consistent set, X, that contains x *)
    destruct H as [X [? ?] ]. 
    (* Since X is F-consistent, by definition x is a member of F X. *)
    apply H in H0.
    (* We have now established that F X ⊆ F GFP: *)
    revert x H0; fold (Subset (F X) (F GFP)).
    (* Since F is monotone, it suffices to show that X ⊆ GFP *)
    eapply F_Monotone.
    (* To show X ⊆ GFP, we just need to show that every x in X is in GFP *)
    intros ? ?.
    (* By definition, x is an element of GFP if it is a member of an
    F-consistent set. By assumption, x is in X and F is F-consistent,
    so we're done!*)
    unfold In, GFP.
    eexists X.
    eauto.
  Qed.
  
  Lemma GFP_is_FClosed 
    : Monotone_F -> FClosed GFP.
  Proof.
    intros F_Monotone ? ?.
    (* By our previous lemma, we know that GFP ⊆ F GFP. By monotonicity of 
       F, F GFP ⊆ F (F GFP). *)
    assert (F GFP ⊆ F (F GFP)).
    { apply F_Monotone.
      apply GFP_is_FConsistent.
      eassumption. }
    (* By definition, this means F GFP is F-consistent. *)
    assert (FConsistent (F GFP)).
    { intros ? ?.
      apply H0.
      assumption. }
    (* Since F is a member of an F-consistent set, it must be a member
    of GFP.*)
    unfold In, GFP.
    exists (F GFP).
    eauto.
  Qed.
  
  Theorem GFP_is_FixedPoint
    : Monotone_F -> FixedPoint GFP.
  Proof.
    intro F_Monotone.
    unfold FixedPoint.
    split.
    - apply GFP_is_FConsistent; eauto.
    - apply GFP_is_FClosed; eauto.
  Qed.
  
  Theorem LFP_is_FClosed
    : Monotone_F -> FClosed LFP.
  Proof.
  Admitted.
    
  Theorem LFP_is_FConsistent
    : Monotone_F -> FConsistent LFP.
  Proof.
  Admitted.

  Theorem LFP_is_FixedPoint
    : Monotone_F -> FixedPoint LFP.
  Proof.
    intro F_Monotone.
    unfold FixedPoint.
    split.
    - apply LFP_is_FConsistent; eauto.
    - apply LFP_is_FClosed; eauto.
  Qed.
  
  Lemma Ind 
    : forall (Ind : PSet U),
      FClosed Ind -> forall a, LFP a -> Ind a.
  Proof.
    unfold LFP, FClosed; intros; eapply H0; eauto.
  Qed.
  
  Lemma CoInd 
    : forall (Ind : PSet U),
      FConsistent Ind -> forall a, Ind a -> GFP a.
  Proof.
    unfold GFP, FConsistent; intros; eauto.
  Qed.

End Fixpoints.

Inductive isEven : nat -> Prop :=
| isEvenZero : isEven 0
| isEvenSS : forall (n : nat), isEven n -> isEven (S (S n)).
  
Definition isEven_F : PSet nat -> PSet nat :=
  fun X n => (n = 0) \/ (exists n', X n' /\ n = S (S n')).

Definition isEven' := LFP isEven_F.

Theorem isEven_eqv : forall n,
    isEven n <-> isEven' n.
Proof.
  split; intro.
  - induction H.
    + unfold isEven', LFP. 
      intros.
      apply H.
      unfold isEven_F, In; intuition.
    + unfold isEven', LFP. 
      intros.
      apply H0.
      unfold isEven_F, In; right.
      eexists; intuition.
      unfold isEven' in IHisEven.
      apply IHisEven in H0; eauto.
  - unfold LFP in H. eapply Ind; try eassumption.
    intros ? ?; unfold In in *.
    destruct H0 as [ | [n' [? ?] ] ]; subst.
    + econstructor.
    + econstructor.
      eassumption.
Qed.

(* Start coinduction chapter from CPDT here. *)

Section stream.
  Context (A : Type).

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

Arguments Cons {A} _ _.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

(** We can also define a stream that alternates between [true] and [false]. *)

CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

(** Co-inductive values are fair game as arguments to recursive
functions, and we can use that fact to write a function to take a
finite approximation of a stream. *)

Fixpoint approx {A} (s : stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx t n'
      end
  end.

Eval simpl in approx zeroes 10.

Eval simpl in approx trues_falses 10.

Fail CoFixpoint looper : stream nat := looper.

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

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
      | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Section map'.
  Variables A B : Type.
  Variable f : A -> B.

  Fail CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.

End map'.

Definition tl A (s : stream A) : stream A :=
  match s with
    | Cons _ s' => s'
  end.

Fail CoFixpoint bad : stream nat := tl _ (Cons 0 bad).

Fail CoFixpoint bad : stream nat := bad.

(** * Infinite Proofs *)

(** Let us say we want to give two different definitions of a stream
of all ones, and then we want to prove that they are equivalent. *)

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map _ _ S zeroes.

(** The obvious statement of the equality is this: *)

Theorem ones_eq : ones = ones'.
  
Abort.

Section stream_eq.
  Context {A : Type}.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2
    -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Theorem ones_eq : stream_eq ones ones'.

  cofix ones_eq.

  assumption.

  Undo.
  simpl.

Abort.

(** First, we need to define a function that seems pointless at first glance. *)

Definition frob {A} (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

(** Next, we need to prove a theorem that seems equally pointless. *)

Theorem frob_eq : forall {A} (s : stream A), s = frob s.
  destruct s; reflexivity.
Qed.

(** But, miraculously, this theorem turns out to be just what we needed. *)

Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.

  (** We can use the theorem to rewrite the two streams. *)

  rewrite (frob_eq ones).
  rewrite (frob_eq ones').

  simpl.

  constructor.

  assumption.
Qed.

Require Coq.Setoids.Setoid.

Definition stream_eq_F {A : Type} : PSet (stream A * stream A) -> PSet (stream A * stream A) :=
  fun X s => exists h t1 t2, In (t1, t2) X /\ fst s = (Cons h t1) /\ snd s = (Cons h t2).

Definition stream_eq' {A} := GFP (@stream_eq_F A).

Theorem ones_eq' : stream_eq' (ones, ones').
  unfold stream_eq'.
  eapply CoInd.
  unfold FConsistent, Subset, In.
  intros [t1 t2].
  instantiate (1 := fun s => s = (ones, ones')).
  simpl; intros.
  injection H; intros.
  subst.
  unfold stream_eq_F.
  eexists 1, ones, ones'; intuition.
  simpl; rewrite (frob_eq ones) at 1; reflexivity.
  simpl; rewrite (frob_eq ones') at 1; reflexivity.
  reflexivity.
Qed.

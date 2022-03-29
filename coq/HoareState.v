(* 
 * Code for The Hoare State Monad (Proof Pearl), Wouter Swierstra
 * Reference: 
 *   https://webspace.science.uu.nl/~swier004//publications/2009-tphols.v 
 *)

Require Import Program.
Require Import Arith.
Require Import List.
Require Import Psatz.

Inductive Tree (a : Set) : Set :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Arguments Leaf [a] _.
Arguments Node [a] _ _.

Compute Node (Leaf 2) (Leaf 1).

Module Sec2_TheStateMonad.

  Fixpoint relabel {a : Set} (t : Tree a) (s : nat) : Tree nat * nat :=
    match t with
    | Leaf _ => (Leaf s, 1 + s)
    | Node l r =>
        let (l', s') := relabel l s in
        let (r', s'') := relabel r s' in
        (Node l' r', s'')
    end.

  Compute relabel (Node (Leaf 100) (Leaf 34)) 0.
  Compute relabel (Node (Leaf 123) (Leaf 567)) 0.
  
  Definition State (s a : Set) : Type := s -> a * s.
  Definition ret (s a : Set) : a -> State s a :=
    fun x => fun s => (x, s).
  Definition bind (s a b : Set) : State s a -> (a -> State s b) -> State s b :=
    fun c1 c2 => fun s1 => let (x, s2) := c1 s1 in c2 x s2.

  Arguments ret [s a] _ _.
  Arguments bind [s a b] _ _ _.

  Notation "e1 '>>=' e2" := (bind e1 e2) (at level 80, right associativity).
  Notation "e1 '>>' e2" := (bind e1 (fun _ => e2)) (at level 80, right associativity).

  Definition get (s : Set) : State s s := fun s => (s, s).
  Definition put (s : Set) : s -> State s unit := fun s => fun _ => (tt, s).

  Arguments get {s}.
  Arguments put {s}.

  Fixpoint relabelM {a : Set} (t : Tree a) : State nat (Tree nat) :=
    match t with
    | Leaf _ => get >>= fun n =>
               put (S n) >>
               ret (Leaf n)
    | Node l r => relabelM l >>= fun l' =>
                 relabelM r >>= fun r' =>
                 ret (Node l' r')
    end.

  Compute relabelM (Node (Leaf 456) (Leaf 123)) 0.

End Sec2_TheStateMonad.

Module Sec3_TheChallenge.
  Import Sec2_TheStateMonad.
  (* 
   * How can we prove relabelM is correct? 
   * What's the specification of relabelM?
   *)

  Fixpoint flatten {a : Set} (t : Tree a) : list a :=
    match t with
    | Leaf x => x :: nil
    | Node l r => flatten l ++ flatten r
    end.
  
  Lemma relabelM_correct : forall {a : Set} (t : Tree a) (n : nat),
      NoDup (flatten (fst (relabelM t n))).
  Proof. Admitted.

  (* The flatten result tree corresponds to some list *)
  (* No duplication in this flatten tree *)
  (* The invariance of tree shape *)
 
End Sec3_TheChallenge.

Module Sec456.

  (* Strong specification: the type of the relabelM function
   * should capture its behavior.
   *)

  Definition Pre (s : Set) : Type := s -> Prop.
  Definition Post (s a : Set) : Type := s -> a -> s -> Prop.

  (* Requires an initial state that satisfies a given precondition.
   * Guarantees that the resulting pair satisfies a postcondition
   * relating the initial state (i), resulting value (x), and final state (f).
   *)
  Program Definition HoareState (s : Set) (pre : Pre s) (a : Set) (post : Post s a) : Set :=
    forall i : { t : s | pre t }, { (x, f) : a * s | post i x f }.
  
  (* Now defining `ret` and `bind` of HoareState *)

  Definition top {s : Set} : @Pre s := fun s => True.

  Program Definition ret (s : Set) (a : Set) :
    forall x, HoareState s top a (fun i y f => i = f /\ y = x) :=
    fun x => fun s => (x, s).

  (* First try of `bind`:
   * HoareState1 P1 a Q1 -> (a -> HoareState P2 b Q2) -> HoareStae ... b ...
   * P2 and Q2 cannot use the result of the first computation, so let's generalize it:
   * HoareState1 P1 a Q1 -> 
     (forall (x : a), (a -> HoareState (P2 x) b (Q2 x)) -> 
     HoareStae ... b ...
   *)

  (* What should be the precondition and postcondition of the _composite_ computation (... b ...)?
     - its precondition should contain the precondition of the _first_ computation:
         P1 s1

     - it should also contain that the postcondition of the _first_ computation implies
       the precondition of the _second_ computation:
         forall x s2, Q1 s1 x s2 -> P2 x s2
     
     - Thus combining them obtains the precondition:
         (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)

     - its postcondition existentially quantifies the state and value after _first_ computation,
       so that they satisfies Q1:
         exists x, exists s2, Q1 s1 x s2
       
     - its postcondition should also satisfy the postcondition of the _second_ computation,
         (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3)
   *)

  Program Definition bind : forall s a b P1 P2 Q1 Q2,
      (HoareState s P1 a Q1) ->
      (forall (x : a), HoareState s (P2 x) b (Q2 x)) ->
      HoareState s
                 (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
                 b
                 (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3)
    := fun s a b P1 P2 Q1 Q2 =>
       fun c1 c2 s1 => match c1 s1 with (x, s2) => c2 x s2 end.
  
  Next Obligation.
  Proof.
    apply p0. destruct c1 as [H1 H2]. simpl in *. subst. apply H2.
  Defined.
  Next Obligation.
  Proof with simpl in *.
    destruct c1 as [H1 H2]... destruct c2 as [[b0 s0] P2rh]...
    subst. exists x, s2. intuition.
  Defined.
  
  Arguments ret [s a] _ _.
  Arguments bind [s a b] {P1 P2 Q1 Q2} _ _ _ .

  Notation "e1 '>>=' e2" := (bind e1 e2) (at level 80, right associativity).
  Notation "e1 '>>' e2" := (bind e1 (fun _ => e2)) (at level 80, right associativity).

  Program Definition get (s : Set) :
    HoareState s top s (fun i x f => i = f /\ x = i)
    := fun s => (s, s).

  Program Definition put (s : Set) (x : s) :
    HoareState s top unit (fun _ _ f => f = x)
    := fun _ => (tt, x).

  Arguments get {s} _.
  Arguments put {s} _ _.

  (* That's it! *)

  (* Revisiting relabelM *)

  Fixpoint size {a : Set} (t : Tree a) : nat :=
    match t with
    | Leaf x => 1
    | Node l r => size l + size r
    end.
  
  Fixpoint flatten {a : Set} (t : Tree a) : list a :=
    match t with
    | Leaf x => x :: nil
    | Node l r => flatten l ++ flatten r
    end.

  Fixpoint seq (x n : nat) : list nat :=
    match n with
    | 0 => nil
    | S k => x :: seq (S x) k
    end.

  Compute seq 5 10.
  Compute seq 0 8.

  Lemma SeqSplit : forall y x z, seq x (y + z) = seq x y ++ seq (x + y) z.
  Proof with simpl; auto.
    induction y... intros x z... rewrite IHy, plus_Snm_nSm...
  Qed.

  Program Fixpoint relabelM {a : Set} (t : Tree a) :
    HoareState nat top (Tree nat)
               (fun i t f => f = i + size t /\ flatten t = seq i (size t))
    := match t with
       | Leaf _ => get >>= fun n =>
                  put (S n) >>
                  ret (Leaf n)
       | Node l r => relabelM l >>= fun l' =>
                    relabelM r >>= fun r' =>
                    ret (Node l' r')
       end.
  Next Obligation.
  Proof. intuition. Defined.
  Next Obligation.
  Proof with simpl in *; auto.
    destruct_call (bind (s := nat))...
    clear relabelM l r H.
    destruct_conjs...
    (* now we must prove that the postcondition holds for the tree 
     * Node l r under the assumption that it holds for recursive 
     * calls to l and r *)   
    rename y into l, H1 into r, H into lState, H3 into rState.
    rename H0 into sizeL, H4 into sizeR, H2 into flattenL, H7 into flattenR.
    rename H5 into finalState, H6 into finalRes.
    rewrite finalRes.
    split...
    - lia.
    - rewrite flattenL, flattenR, sizeL, SeqSplit...
  Defined.

  (* Section 6 *)
  
  (* How can we prove the result t satisfies Nodup (flatten t)? *)
  (* We need to weaken the postcondition and 
     strengthen the precondition explicitly, by using `do` *)
  
  Program Definition do (s a : Set) (P1 P2 : Pre s) (Q1 Q2 : Post s a) :
    (forall i, P2 i -> P1 i) -> (forall i x f, Q1 i x f -> Q2 i x f) ->
    HoareState s P1 a Q1 -> HoareState s P2 a Q2
    := fun str wkn c => c.
  Next Obligation.
  Proof with simpl; auto.
    destruct_call c... destruct x0 as [x1 f]...
  Defined.

  (* See complete proof in
     https://webspace.science.uu.nl/~swier004//publications/2009-tphols.v 
   *)
  
End Sec456.

(* Some following related work:
   - F*
   - Dijkstra Monads for Free (POPL 17)
   - Dijkstra Monads for All (ICFP 19)
   - A Predicate Transformer Semantics for Effects (ICFP 19)
   ...
*)

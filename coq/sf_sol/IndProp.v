Set Warnings "-notation-overridden,-parsing". 

Require Coq.omega.Omega.
Require Export Logic.

(* Inductively Defined Propositions *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n: nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros H.
  apply ev_SS. apply ev_SS.
  apply H.
Qed.

(* Exercise *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros.
  induction n.
  + simpl. apply ev_0.
  + simpl. apply ev_SS. apply IHn.
Qed.

(* Using Evidence in Proofs *)

Theorem ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  apply E'.
Qed.


Theorem one_not_even : ~ ev 1.
Proof. intros H. inversion H. Qed.

(* Exercise *)
Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3.
Qed.

Lemma ev_even_firsttry: forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E.
  inversion E as [| n' E'].
  - exists 0. reflexivity.
  - assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I.
    Admitted.

(* Induction on Evidence *)

Lemma ev_even : forall n, ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E.
  - exists 0. simpl. reflexivity.
  - destruct IHE.
    rewrite H. exists (S x). reflexivity.
Qed.

Theorem ev_even_iff: forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - apply ev_even.
  - intros [k H]. rewrite H. apply ev_double.
Qed.

(* Exercises *)

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
  intros.
  induction H.
  - simpl. apply H0.
  - simpl. apply ev_SS. apply IHev.
Qed.

Inductive ev' : nat -> Prop := 
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros. split.
  - intro H. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply IHev'1.
      * apply IHev'2.
  - intro H. induction H.
    + apply ev'_0.
    + assert ((S (S n)) = 2 + n).
      { simpl. reflexivity. }
      rewrite H0. apply ev'_sum.
      * apply ev'_2.
      * apply IHev.
Qed.

Theorem ev_ev_ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Hnm Hn.
  induction Hn.
  - simpl in Hnm. apply Hnm.
  - simpl in Hnm. inversion Hnm.
    apply IHHn. apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  apply ev_sum with (n:=n+m) (m:=n+p) in Hnm.
  replace ((n+m) + (n+p)) with ((n + n) + (m + p)) in Hnm.
  replace (n+n) with (double n) in Hnm.
  apply ev_ev_ev with (m := m+p) in Hnm.
  - apply Hnm.
  - replace (double n + (m + p) + (m + p)) with (double n + ((m + p) + (m + p))).
    replace  (m + p + (m + p)) with (double (m + p)).
    + apply ev_sum.
      apply ev_double.
      apply ev_double.
    + apply double_plus with (n := m+p).
    + apply plus_assoc with (n := double n).
  - apply double_plus.
  - rewrite <- plus_assoc.
    replace (n + (m + p)) with (m + (n + p)).
    + rewrite plus_assoc. reflexivity.
    + apply plus_swap.
  - apply Hnp.
Qed.

(* Inductive Relations *)

Module Playground.

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1: 3 <= 3.
Proof. apply le_n. Qed.

Theorem test_le2: 3 <= 6.
Proof. apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3: (2 <= 1) -> 2 + 2 <= 5.
Proof.
  intros H. inversion H. inversion H2.
Qed.

End Playground.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
| sq : forall n, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn : forall n, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall n, ev (S n) -> next_even n (S n)
| ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(* Exercises *)

Inductive total_relation : nat -> nat -> Prop :=
| tr : forall n m, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  rewrite <- H in H0.
  assumption.
Qed.

Lemma o_le_n : forall n, 0 <= n.
Proof.
  intro n.
  induction n.
  - reflexivity.
  - rewrite IHn. apply le_S. reflexivity.
Qed.

Lemma n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
  - reflexivity.
  - apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m-> n <= m.
Proof.
  intros.
  inversion H. 
  - apply le_n.
  - apply le_trans with (n := S n).
    + apply le_S. apply le_n.
    + apply H1.
Qed.
  
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction a.
  - simpl. apply o_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros.
  split.
  - apply le_trans with (n := S(n1 + n2)).
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply H.
  - apply le_trans with (n := S(n1 + n2)).
    + apply n_le_m__Sn_le_Sm. rewrite plus_comm.
      apply le_plus_l.
    + apply H.
Qed.
  
Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros.
  apply le_trans with (n := m).
  - apply H.
  - apply le_S. apply le_n.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n.
  induction n.
  - intros. apply o_le_n.
  - intros. simpl in H.
    destruct m.
    + inversion H.
    + apply n_le_m__Sn_le_Sm. apply IHn. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> leb n m = true.
Proof.
  intros n.
  induction n.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct m.
    + inversion H.
    +  apply IHn. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  rewrite <- H0. apply H.
Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0 
| c2 : forall m n o, R m n o -> R (S m) n (S o)
| c3 : forall m n o, R m n o -> R m (S n) (S o)
| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5 : forall m n o, R m n o -> R n m o.

Example R112 : R 1 1 2.
Proof. apply c2. apply c3. apply c1. Qed.

Example R226 : R 2 2 6.
Proof. Abort.

Definition fR : nat -> nat -> nat. Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof. Admitted. 

End R.

(* TODO: Exercise: 4 stars, advanced (subsequence) *)

(* TODO: Exercise: 2 stars, optional (R_provability2) *)

(* Case Study: Regular Expressions *)

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall s1 re1 re2,
              exp_match s1 re2 ->
              exp_match s1 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1;2] =~ App (Char 1) (Char 2).
Proof. 
  apply (MApp [1] _ [2] _).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1;2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x::xs => App (Char x) (reg_exp_of_list xs)
  end.

Example reg_exp_ex4 : [1;2;3] =~ reg_exp_of_list [1;2;3].
Proof.
  simpl.
  apply (MApp [1]).
  - apply MChar.
  - apply (MApp [2]).
    + apply MChar.
    + apply (MApp [3]).
      * apply MChar.
      * apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : @reg_exp T),
  s =~ re -> s =~ Star re.
Proof.
  intros.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(* Exercises *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros. destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros. apply H. simpl.
      right. apply H0.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split.
  - intros. generalize dependent s1. induction s2.
    + intros. simpl in H. inversion H. reflexivity.
    + intros. simpl in H. inversion H. inversion H3.
      apply f_equal. apply IHs2. apply H4.
  - intros. generalize dependent s1. induction s2.
    + intros. simpl. rewrite H. apply MEmpty.
    + intros. simpl. rewrite H. apply (MApp [x] _).
      * apply MChar.
      * apply IHs2. reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
match re with
| EmptySet => []
| EmptyStr => []
| Char x => [x]
| App re1 re2 => re_chars re1 ++ re_chars re2
| Union re1 re2 => re_chars re1 ++ re_chars re2
| Star re => re_chars re
end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros.
  induction H.
  - simpl. inversion H0.
  - apply H0.
  - simpl. rewrite in_app_iff. rewrite in_app_iff in H0.
    destruct H0.
    + left. apply IHexp_match1. apply H0.
    + right. apply IHexp_match2. apply H0.
  - simpl. rewrite in_app_iff. left. apply IHexp_match. apply H0.
  - simpl. rewrite in_app_iff. right. apply IHexp_match. apply H0.
  - destruct H0.
  - simpl. rewrite in_app_iff in H0.
    destruct H0.
    + apply IHexp_match1. apply H0.
    + apply IHexp_match2. apply H0.
Qed.

(* Exercise *)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
match re with
| EmptySet => false
| EmptyStr => true
| Char _ => true
| App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
| Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
| Star re => true
end.


Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.	
  intros. split.
  - intros H. induction re.
    + simpl. inversion H. inversion H0.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. apply andb_true_iff.
      split.
      * inversion H. apply IHre1. inversion H0. exists s1. apply H4.
      * inversion H. apply IHre2. inversion H0. exists s2. apply H5.
    + simpl. apply orb_true_iff.
      inversion H. inversion H0. 
      * left. apply IHre1. exists x. apply H3.
      * right. apply IHre2. exists x. apply H3.
    + simpl. reflexivity.
  - intros. induction re. 
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + inversion H. apply andb_true_iff in H1. destruct H1.
      pose proof IHre1 H0.
      pose proof IHre2 H1.
      destruct H2, H3. exists (x ++ x0).
      apply MApp. apply H2. apply H3.
    + inversion H. apply orb_true_iff in H1. destruct H1.
      * pose proof IHre1 H0. destruct H1. exists x.
        apply MUnionL. apply H1.
      * pose proof IHre2 H0. destruct H1. exists x.
        apply MUnionR. apply H1.
    + exists nil. apply MStar0.
Qed.

(* The remember Tactic *)

(* remember e as x causes Coq to (1) replace all occurrences 
   of the expression e by the variable x, and (2) add an 
   equation x = e to the context. *)

Lemma star_app : forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'. intros. apply H.
  - inversion Heqre'. intros.
    rewrite H0 in IH2, Hmatch1.
    rewrite <- app_assoc. apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H.
Qed.

(* Exercise *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re -> exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - exists []. split.
    + simpl. reflexivity.
    + intros. inversion H.
  - inversion Heqre'.
    rewrite H2 in IHexp_match2.
    assert (H' : Star re = Star re). { reflexivity. }
    destruct (IHexp_match2 H') as [ss [H1' H2']].
    exists (s1 :: ss). simpl.
    rewrite H1'. split.
    + reflexivity.
    + intros s [H3 | H3].
      * rewrite <- H3. rewrite <- H2. apply H.
      * apply H2'. apply H3.
Qed.

Module Pumping.

(* any sufficiently long string s matching a regula
   expression re can be "pumped" by repeating some middle 
   section of s an arbitrary number of times to produce 
   a new string also matching re. *)

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.
  
Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus : forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. apply app_assoc.
Qed.

Import Coq.omega.Omega.

Lemma pumping: forall T (re : @reg_exp T) s,
  s =~ re -> pumping_constant re <= length s ->
  exists s1 s2 s3, s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch.
  - simpl. omega.
  - simpl. omega.
  - Admitted.
  
End Pumping.

(* Case Study: Improving Reflection *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~P -> reflect P false.
  
Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros contra. inversion contra.
Qed.

(* Exercise *)

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros. inversion H.
  - split.
    + intros. reflexivity.
    + intros. apply H0.
  - split.
    + intros. intuition.
    + intros. inversion H2.
Qed.

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l.
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_natP n x).
    + intros. rewrite H. left. reflexivity.
    + intros. right. apply IHl. apply H0.
Qed.

(* TODO: Exercise *)

(* TODO: Additional Exercises *)
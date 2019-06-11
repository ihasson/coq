Require Export Logic.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4': ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
    ev (double n).
Proof.
  intros n.
  induction n as [| n' Hn].
  -  apply ev_0.
  -  apply ev_SS. apply Hn.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'. Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the E=ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev_even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H.
  apply evSS_ev in H1. assumption.
Qed.

Theorem SSSSev_even' : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E'].
  inversion E' as [| n'' E''].
  apply E''.
Qed.


Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H as [| n' H'].
  inversion H' as [| n'' H'']. inversion H''.
Qed.

Lemma ev_even_firsttry : forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.
    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'.  exists (S k'). reflexivity. }
    apply I.
Abort.

Lemma ev_even : forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists(S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
    ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En as [|n' En'].
  - simpl. assumption.
  - simpl. apply ev_SS. assumption.
Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - (* -> *)  intros E. induction E.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. assumption. assumption.
  - (* <- *) intros E. induction E.
    + apply ev'_0.
    + assert (S (S n) = 2 + n) as H.
      { induction n.
        - reflexivity.
        - reflexivity.
      }
      rewrite H. apply ev'_sum.
      { apply ev'_2. }
      { assumption. }
Qed.

Theorem ev_ev__ev : forall n m,
    ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H0 H1. induction H1.
  - assumption.
  - apply IHev.
    assert (S (S n) + m = S (S (n + m))) as H.
    { reflexivity. }
    rewrite H in H0. apply evSS_ev in H0.
    assumption.
Qed.

Theorem ev_plus_plus: forall n m p,
    ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  assert (ev (n+m) -> ev ((n+p)+(m+p))) as H.
  { intros H. rewrite (plus_comm n p). rewrite (plus_comm m p).
    rewrite plus_swap. rewrite plus_assoc. rewrite plus_assoc.
    rewrite <- double_plus. rewrite <- (plus_assoc (double p) n m).
    apply ev_sum. apply ev_double. assumption. }
  apply H in Hnm. apply (ev_ev__ev (n+p)). assumption.
  assumption.
Qed.

Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

  Notation "m <= n" := (le m n) .

  Theorem test_le1 :
    3 <= 3.
  Proof.
    apply le_n. Qed.

  Theorem test_le2 :
    3<=6.
  Proof.
    apply le_S. apply le_S. apply le_S. apply le_n. Qed.

  Theorem test_le3 :
    (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros H. inversion H. inversion H2. Qed.

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
| sq : forall n : nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall n, ev (S n) -> next_even n (S n)
| ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  tr_nm : forall (n m : nat), total_relation n m.

Inductive empty_relation : nat -> nat -> Prop :=
  er_nm : forall (n m : nat), n = m /\ n <> m -> empty_relation n m.

Lemma er_test : forall n m, ~ empty_relation n m.
Proof.
  intros n m. unfold not. intros H.
  inversion H. inversion H0. rewrite H3 in H4.
  unfold not in H4. apply H4. reflexivity.
Qed.

(* do these later Exercise: 3 stars, optional (le_exercises) *)

(* skipping to Case Study: Regular Expressions. *)

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
    exp_match s1 re1 ->
    exp_match s2 re2 ->
    exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
    exp_match s1 re1 ->
    exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
    exp_match s2 re2 ->
    exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
    exp_match s1 re ->
    exp_match s2 (Star re) ->
    exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1;2;3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
    ~ (s =~ EmptySet).
Proof.
  intros T s. unfold not. intros H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
    s =~ re1 \/ s =~ re2 ->
    s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H.
  - apply MUnionL. assumption.
  - apply MUnionR. assumption.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
    (forall s, In s ss -> s =~ re) ->
    fold app ss []  =~ Star re.
Proof.
  intros T ss re H.
  rewrite <- (app_nil_r _ ss).
  - induction ss. 
    + simpl. apply MStar0.
    + apply (MStarApp).
      { apply H. simpl. left. reflexivity. }
      { apply IHss. intros. apply H. simpl. right. assumption. }
  Qed. 

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  Admitted.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
    s =~ re ->
    In x s ->
    In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
      | x'
      | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
      | s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
      | re|s1 s2 re Hmatch IH1 Hmatch2 IH2].
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool.

Admitted.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
    (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
Admitted.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [| x' | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH| re1 s2' re2 Hmatch IH
        | re'' | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) inversion Heqre'.
  - (* MChar *) inversion Heqre'.
  - (* MApp *) inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
  - (* MStar0 *) inversion Heqre'. intros s H. apply H.
  - (* MStarApp *)
    inversion Heqre'. rewrite  H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * simpl. assumption.
Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
    s =~ Star re ->
    exists ss : list (list T),
      s = fold app ss []
      /\ forall s', In s' ss ->  s' =~re.
Proof.
  intros T s r H.
  remember (Star r) as r'.
  induction H as [| | | | |r'|s s' r'' H _ H' IH'];
    try (inversion Heqr' as [Heq]).
  - exists [ ]. split.
    + simpl. reflexivity.
    + intros s F. inversion F.
    - subst; apply IH' in Heqr'; destruct Heqr' as [x Hx]; clear IH'.
  destruct Hx as [Hfs' Hxr]; subst; clear H'.
  (*
    After performing the substitutions we have only 1 possible
    choice for instantiating the existential variable because
    we have to satisfy [s ++ fold app x [ ] = fold app ss [ ]].
    This means the only choice for [ss] is [s :: x] so that's what
    we instantiate with and the rest follows from typical backward
    chaining.
  *)
  exists (s :: x); split; simpl; trivial.
  intros s' H''; destruct H''.
  subst; trivial.
  apply Hxr; trivial.
  Qed.
(*
  intros T s re H.
  remember (Star re) as re'. remember s as s'.
  induction H.
  - exists []. split.
    + reflexivity.
    + inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - exists []. split.
    + simpl. reflexivity.
    + intros. inversion H.
  - exists ([s1] ++ [s2]). simpl. split.
    + rewrite -> app_nil_r. reflexivity.
    + inversion Heqre'. intros.
      induction s'.
      * simpl.
        { destruct H1.
          + rewrite <- H1. rewrite <- H2. assumption.
          + simpl. destruct H1. rewrite <- H1. rewrite <- H2.
            apply MStar1 in H.
  *)      
Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.
(*
https://dev.to/davidk01/preliminary-impressions-of-software-foundations-n9i
 *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof. Admitted.
(*  Require Import Coq.omega.Omega.
  Proof.
    intros T re s Hmatch.
    induction Hmatch
       as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    - (* MEmpty *)
      simpl. omega.
    - (* MChar *)
      simpl. omega.
    - (* MApp *)
      simpl; rewrite -> app_length; intro H; apply sum_leq in H; destruct H.
      (* [pumping_constant re1 <= length s1] *)
      apply IH1 in H.
      destruct H as [x0 [x1 [x2]]];
        destruct H as [Hs' [Hs'' Hs''']]; clear IH1; clear IH2; subst.
      (*
        If you look at the equations that must be satisfies then we
        don't have a choice about how to instantiate things. This is
        the only possible option that will work.
       *)
      exists (x0), (x1), (x2 ++ s2).
      split. repeat (rewrite <- app_assoc). trivial.
      split. trivial.
      intros. repeat (rewrite ->

*)

(*      intros s. simpl (pumping_constant (App re1 re2)) in s.
      inversion s.
      + simpl. generalize dependent s. rewrite <- H0. simpl.
      remember 
      + generalize dependent s1.
      simpl. inversion Hmatch1.
      + intros. simpl.
        simpl (length([]++s2)) in IH1. rewrite H0.
        rewrite <- H0 in IH1.
        simpl (pumping_constant EmptyStr) in IH1.
        simpl.*)
      (* MUnionL *)
      (* MUnionR *)
      (* MStar0 *)
      (* MStarApp *)
End Pumping.

Theorem filter_not_empty_In : forall n l,
    filter (beq_nat n) l <> [] ->
    In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  - intros H'.
    inversion H.
    + reflexivity.
    + rewrite H1. contradiction.
  - intros H'.
    inversion H.
    + assumption.
    + rewrite H' in H1. discriminate.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
  Proof. 


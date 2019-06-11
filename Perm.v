Add LoadPath "~/Documents/vfa" as VFA.
Require Import Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.

Check Nat.lt.
Check lt.
Check Nat.ltb.
Locate "_ < _".
Locate "<?".

Check Nat.ltb_lt.

Notation "a >=? b" := (Nat.leb b a)
                        (at level 70, only parsing) : nat_scope.
Notation "a >? b" := (Nat.ltb b a)
                       (at level 70, only parsing) : nat_scope.
Notation " a =? b" := (beq_nat a b)
                        (at level 70) : nat_scope.

Print reflect.

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Example reflect_example1: forall a, (if a<? 5 then a else 2) < 6.
Proof.
  intros. destruct (blt_reflect a 5) as [H|H].
  * omega.
  * omega.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
      [ | try first [apply not_lt in H | apply not_le in H]]].

Example reflect_example2: forall a, (if a<?5 then a else 2) < 6.
Proof.
  intros. bdestruct (a<?5).
  * omega.
  * omega.
Qed.

Module Exploration1.

  Theorem bogus_subtraction: ~(forall k:nat, k>k-3).
  Proof.
    intro.
    specialize (H O).
    simpl in H. inversion H.
  Qed.
  
  Theorem omega_example1:
    forall i j k,
      i < j -> ~(k - 3 <= j) ->
      k > i.
  Proof.
    intros.
    apply not_le in H0.
    unfold gt in H0.
    unfold gt.
    Search (_ < _ -> _ <= _ -> _ < _).
    apply lt_le_trans with j.
    apply H.
    apply le_
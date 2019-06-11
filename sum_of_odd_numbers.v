Require Import Arith.

Fixpoint sum_odd_n (n:nat) : nat :=
  match n with
    O => O
  | S p => 1 + 2*p + sum_odd_n p
  end.
Search (Nat.mul).

Lemma sum_odd_n_p : forall (n:nat), sum_odd_n (n:nat) = n*n.
  induction n.
  simpl. reflexivity.
  simpl. rewrite IHn. ring.
Qed.

Fixpoint sum_n (n:nat) : nat :=
  match n with
    0 => 0
  | S p => 1 + p + sum_n p
  end.

Compute sum_n 3.
Search mult.
(*
Nat.mul_succ_r: forall n m : nat, n * S m = n * m + n
Nat.mul_succ_l: forall n m : nat, S n * m = n * m + m
 *)

Lemma sum_n_helper : forall n : nat,
  2 * sum_n (S n) = 2 * (S n) + 2 * sum_n n.
Proof.
  intros n. simpl. ring.
Qed.

Theorem sum_n_formula : forall n, 2 * sum_n n = (n*(n+1)).
Proof.
  intros n.
  induction n as [| k IH].
  - (* base case n = 0 *)
    simpl. reflexivity.
  - (* inductive case *)
    rewrite -> sum_n_helper.
    rewrite IH.
    ring.
Qed.

Lemma div_helper : forall a b c : nat,
  c <> 0 -> c * a = b -> a = b / c.
Proof.
  intros a b c neq eq.
  rewrite <- eq.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul.
  trivial.
  assumption.
Qed.

(* need to figure out how to do this without the ring tactic. *) 
(*Require Import QArith.*)

Theorem sum_n_formula2 : forall n : nat , sum_n n = (n * (n+1)/2)%nat .
Proof.
  intros n.
  apply div_helper.
  - discriminate.
  - rewrite sum_n_formula.
    simpl. reflexivity.
Qed.

Theorem plus_comm: forall a b,
    a+b = b+a.
Proof.
  intros a b. ring.
Qed.

Theorem foil : forall a b c d,
    (a+b) * (c+d) = a*c+b*c + a*d + b*d.
Proof.
  intros a b c d. ring.
Qed.

Require Import ZArith.
Open Scope Z_scope.

Theorem sub_add_1 : forall a :Z, a -1 + 1 = a.
Proof.
  intros a. ring.
Qed.

Close Scope Z_scope.

Require Import Field.
Require Import Qcanon.
Open Scope Qc_scope.

Theorem frac_qc: forall x y z : Qc, z<> 0 -> (x+y)/z = x/z + y/z.
Proof.
  intros x y z z_not_0.
  field. assumption.
Qed.

Close Scope Qc_scope.
(*
Module RealExample.

  Require Import Reals.
  Open Scope R_scope.

  Theorem frac_r : forall x y z, z<>0 -> (x+y) / z = x/z + y/z.
  Proof.
    intros x y z z_not_0.
    field. assumption.
  Qed.

  
  Close Scope R_scope.
End RealExample.
*)
(*
Open Scope R_scope.

Theorem *)
Search (_:N N _:N).
Compute Nat.pow 2 O.

Fixpoint pow_series_2_n (k: nat) : nat :=
  match k with
    O => O
  | S p => (Nat.pow 2 p) + (pow_series_2_n p) 
  end.

Compute pow_series_2_n 2.
Compute O + O.

Theorem sum_2_pow_n: forall n: 
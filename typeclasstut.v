Require Import ZArith.
(*Require Import Coq.Arith.Even. *)
Require Import Nat.
Open Scope Z_scope.
Require Import FunInd.

Fixpoint power (x:Z)(n:nat):=
  match n with 0%nat => 1
          | S p => x * power x p
  end.

Compute power 2 40.
Search nat.
(*
Function binary_power_mult (acc x:Z)(n:nat)
         {measure (fun i=>i) n} : Z
(* acc * (power x n) *) :=
  match n with 0%nat => acc
          | _ => if Nat.Even n Nat.Odd n
                 then binary_power_mult
                        acc (x * x) (Nat.div2 n)
                 else binary_power_mult
                        (acc * x) (x * x) (Nat.div2 n)
  end.
Proof.
  intros; apply lt_div2; auto with arith.
  intros; apply lt_div2; auto with arith.
Defined.
*)

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
(*
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
*)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma test : True.
Proof.
  pose f x y := x + y.
Abort.

Compute (fun n => n+1) 2.

(*Definition f := fun n => n+1.*)

Definition f (n : nat) : nat := n+1.
Compute f 3.

About f.

Print f.

Check f 3.

(*Check f (fun x : nat => x + 1). *)

Eval compute in f 3.

Definition g (n m : nat) : nat := n + m * 2.

About g.

Definition h (n : nat) : nat -> nat := fun m => n + m * 2.

About h.

Print g.
Print h.

Check g 3.

Eval compute in g 2 3.

Definition repeat_twice (g : nat -> nat) : nat -> nat :=
  fun x => g (g x).

Eval compute in repeat_twice f 2.

Eval compute in
    let n := 33 :nat in
    let e := n + n + n in
        e + e + e.

Print bool.

Print nat.

Definition twoVthree (b : bool) := if b then 2 else 3.

Eval compute in twoVthree true.
Eval compute in twoVthree false.

Definition andb (b1 b2 : bool) := if b1 then b2 else false.
Definition orb (b1 b2 : bool) := if b1 then true else b2.

Check fun n => f n.+1.

Definition predn n := if n is p.+1 then p else n.

Eval compute in predn 5.

Definition pred5 n :=
  if n is u.+1.+1.+1.+1.+1 then u else O.

Definition three_patterns n :=
  match n with
    u.+1.+1.+1.+1.+1 => u
  | v.+1 => v
  | O => n
  end.

Definition same_bool b1 b2 :=
  match b1, b2 with
  | true, true => true
  | false , false => true
  | _, _ => false
  end.

Fixpoint addn n m :=
  if n is p.+1 then (addn p m).+1 else m.

Fixpoint subn m n : nat :=
  match m, n with
  | p.+1, q.+1 => subn p q
  | _, _ => m
  end.

Fixpoint eqn m n :=
  match m, n with
  | O, O => true
  | p.+1, q.+1 => eqn p q
  | _, _ => false
  end.

Notation "x == y" := (eqn x y).

Eval compute in O == O.
Eval compute in 1 == S O.
Eval compute in 1 == 0.+1.
Eval compute in 2 == S 0.
Eval compute in 2 == 1.+1.
Eval compute in 2 == addn 1 0.+1.

Definition leq m n := m-n == 0.
  


Require Import ZArith.
Require Import Arith.
Require Import Bool.

(*Open Scope Z.*)
Open Scope Z_scope.

Locate "_ * _".
Print Scope Z_scope.

Print Scope nat_scope.

Check 33%nat.
Check 0%nat.
Check 33.

Open Scope nat_scope.
Check 33.
Check 0.

Open Scope Z_scope.
Check 33.
Check -33.
Check 33%nat.

Check true.
Check false.

Check plus.
Check Zplus.
Check negb.
Check orb.

Check (((ifb (negb false)) true) false).

Open Scope nat_scope.
Unset Printing Notations.
Check (5*(5-4)*7).
Set Printing Notations.

Check fun n:nat => (n*n*n)%nat.

Check fun a b c:Z => (b*b-4*a*c)%Z.
Check fun (f g:nat -> nat)(n:nat) => g (f n).

Check fun n p : nat => (let diff := n-p in
                        let square := diff*diff in
                        square * (square+n))%nat.

Definition t1 :=
  fun n:nat => let s := plus n (S n) in mult n (mult s s).

Parameter max_int : Z.

Compute max_int.
Open Scope Z_scope.
Definition min_int := 1-max_int.

Print min_int.

Section binomial_def.
  Variables a b: Z.
  Definition binomial z:Z := a*z + b.
  Section trinomial_def.
    Variable c:Z.
    Definition trinomial z:Z := (binomial z)*z + c.
  End trinomial_def.
End binomial_def.
Print binomial.
Print trinomial.

Compute binomial 1 0 1.
Compute trinomial 1 2 3 4.
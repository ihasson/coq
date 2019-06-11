
Require Import ZArith.
Require Import QArith_base.
(*
Definition half : Q := (Qmake 1%Z 2%positive).
Print half.
Compute Qmake (-1) 2.
Print positive.
Check 12%positive.

Check xH.
Compute (1#3%positive%Q).
 *)
(*Print f_equal.*)

Search ( _ * _ <= _ * _).

Structure Group :=
  {
    G :> Set;
    id : G;
    op : G -> G -> G;
    inv : G -> G;

    op_assoc : forall (x y z : G) , op x (op y z) = op (op x y) z;
    op_inv_l : forall (x : G) , id = op (inv x) x;
    op_inv_r: forall (x : G) , id = op x (inv x);
    op_id_l : forall (x : G) , x = op id x;
    op_id_r : forall (x : G) , x = op x id
  }.


Arguments id {g}.
Arguments op {g} _ _.
Arguments inv {g} _.

Notation "x * y" := (op x y) (at level 50, left associativity).


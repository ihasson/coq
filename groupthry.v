
Require Ring.

Definition GF2_ring:
  Ring_theory.ring_theory false true xorb andb xorb (fun x => x) (@eq bool).
Proof.
  apply Ring_theory.mk_rt;
    solve[now intros [] | now intros [] [] | now intros [] [] []].
Qed.

Structure group :=
  {
    G :> Set;
    id : G;
    op : G -> G -> G;
    inv : G -> G;

    op_assoc : forall (x y z : G), op x (op y z) =  op (op x y) z ;
    op_inv_l : forall (x : G), id = op (inv x) x;
(*    op_inv_l : forall (x : G), op (inv x) x = id; *)
    op_id_l : forall (x : G), x = op id x
  }.
Print Build_group.

Example trivial_group : group.
refine (Build_group unit tt (fun _ _ => tt) (fun _ => tt) _ _ _ ).
- intros. auto.
- intros. auto.
- intros. destruct x. trivial.
Defined.

Require Import Coq.ZArith.BinInt.
Open Scope Z.

Search Z.
(*
Example Z_add_group : group.
refine (Build_group Z (0 : Z) Z.add Z.opp
                    Z.add_assoc (Z.add_opp_diag_l) _ ) .
- trivial.
Defined.
 *)
Check Build_group.
 Check Ring_theory.mk_rt.
Search Z.
Definition myZring:
  Ring_theory.ring_theory 0 1 Z.add Z.mul Z.sub Z.opp Z.eq .
  
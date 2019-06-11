Require Import DepList.
Require Import MoreSpecif.
Require Import CpdtTactics.
Require Import List.
Record constructor : Type := Con {
                                 nonrecursive : Type;
                                 recursive : nat
                               }.

Definition datatype := list constructor.

Definition Empty_set_dt : datatype := nil.
Definition unit_dt : datatype := Con unit 0 :: nil.
Definition bool_dt : datatype := Con unit 0 :: Con unit 0 :: nil.
Definition nat_dt : datatype := Con unit 0 :: Con unit 1 :: nil.
Definition list_dt (A : Type) : datatype := Con unit 0 :: Con A 1 :: nil.

Section tree.
  Variable A : Type.

  Inductive tree : Type :=
  | Leaf : A -> tree
  | Node : tree -> tree -> tree.
End tree.

Definition tree_dt (A : Type) : datatype := Con A 0 :: Con unit 2 :: nil.

Section denote.
  Variable T : Type.

  Definition constructorDenote (c : constructor) :=
    nonrecursive c -> ilist T (recursive c) -> T.

  Definition datatypeDenote := hlist constructorDenote.

End denote.

Notation "[ v , r ~> x ]" := ((fun v r => x) : constructorDenote _ (Con _ _)).

Definition Empty_set_den : datatypeDenote Empty_set Empty_set_dt := HNil.
Definition unit_den : datatypeDenote unit unit_dt :=
  [_, _ ~> tt] ::: HNil.
Definition bool_den : datatypeDenote bool bool_dt :=
  [_, _ ~> true] ::: [_, _ ~> false] ::: HNil.
(*
Definition nat_den : datatypeDenote nat nat_dt :=
  [_, _ ~> O] ::: [_, r ~> S (hd r)] ::: HNil.
 *)

Compute (hd  1 2).
Definition nat_den : datatypeDenote nat nat_dt :=
  [_, _ ~> O] ::: [_, r ~> S (hd r)] ::: HNil.
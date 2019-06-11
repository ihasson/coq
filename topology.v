(* See github.com/andrejbaur for more details on getting started. *)

Definition P (A : Type) := A -> Prop.

Notation "{ x : A | P }" := (fun x : A => P).

Definition singleton {A : Type} (x : A) := {y:A | x = y}.

Definition subset {A : Type} (u v : P A) :=
  forall x : A, u x -> v x.

Notation "u <= v" := (subset u v).

Definition disjoint {A : Type} (u v : P A) :=
  forall x, ~(u x /\ v x).

Notation "'all' x : U , P" := (forall x, U x -> P) (at level 20, x at level 99).

Notation "'some' x : U , P" := (exists x, U x /\ P) (at level 20, x at level 99).

Definition union {A : Type} (S : P (P A)) :=
  {x : A | some U : S, U x }.

Definition inter {A : Type} (u v : P A) :=
  {x : A | u x /\ v x}.

Notation "u * v" := (inter u v).

Definition empty {A : Type} := { x : A | False}.
Definition full {A : Type} := { x : A | True}.

Structure topology (A : Type) :=
  {
    open :> P A -> Prop ;
    empty_open : open empty ;
    full_open : open full;
    inter_open : all u : open, all v :open, open (u * v);
    union_open : forall S, S<= open -> open (union S)
  }.

Definition discrete (A : Type) : topology A.
Proof.
  exists full ; firstorder.
Defined.

Definition T1 {A : Type} (T : topology A) :=
  forall x y : A,
    x <> y ->
    some u : T, (u x /\ ~(u y)).

Definition hausdorff {A : Type} (T : topology A) :=
  forall x y : A,
    x <> y ->
    some u : T, some v : T,
  (u x /\ v y /\ disjoint u v).

Lemma discrete_hausdorff {A : Type} : hausdorff (discrete A).
Proof.
  intros x y N.
  exists { z : A | x = z}; split ; [exact I | idtac].
  exists { z : A | y = z}; split ; [exact I | idtac].
  repeat split ; auto.
  intros z [? ?].
  absurd (x = y); auto.
  transitivity z ; auto.
Qed.

Lemma hausdorff_is_T1 {A : Type} (T : topology A):
  hausdorff T -> T1 T.
Proof.
  intros H x y N.
  destruct (H x y N) as [u [? [v [? [? [? G]]]]]].
  exists u ; repeat split ; auto.
  intro.
  absurd (u y /\ v y); auto.
Qed.

Definition indiscrete (A : Type) : topology A.
Proof.
  exists { u : P A | forall x : A, u x -> (forall y : A, u y) }; firstorder.
Defined.

Lemma indiscrete_least (A : Type) (T : topology A) :
  (forall (X : Type) (s t : P X), s <= t -> t <= s -> s = t) ->
  indiscrete A <= T.
Proof.
  intros ext u H.
  assert (G : (u = union { v : P A | T v /\ some x : v, u x })).
  - apply ext.
    + intros x ?. exists full; firstorder using full_open.
    + intros x [v [[? [y [? ?]]] ?]] ; now apply (H y).
  - rewrite G ; apply union_open ; firstorder.
Qed.

Definition particular {A : Type} (x : A) : topology A.
Proof.
  exists { u : P A | (exists y, u y) -> u x } ; firstorder.
Qed.

(* the topology generated by a family B of subsets that are 
   closed under finite intersections. *)
Definition base {A : Type} (B : P (P A)) :
  B full -> (all u : B, all v : B, B (u * v)) -> topology A.
Proof.
  intros H G.
  exists { u : P A | forall x, u x <-> some v : B, (v x /\ v <= u) }.
  - firstorder.
  - firstorder.
  - intros u Hu v Hv x.
    split.
    + intros [Gu Gv].
      destruct (proj1 (Hu x) Gu) as [u' [? [? ?]]].
      destruct (proj1 (Hv x) Gv) as [v' [? [? ?]]].
      exists (u' * v') ; firstorder.
    + intros [w [? [? ?]]].
      split ; now apply H2.
  - intros S K x.
    split.
    + intros [u [H1 H2]].
      destruct (K u H1 x) as [L1 _].
      destruct (L1 H2) as [v ?].
      exists v; firstorder.
    + firstorder.
Defined.

Require Import List.

(* The intersection of a finite list of subsets. *)
Definition inters {A : Type} (us : list (P A)) : P A :=
  {x : A | Forall (fun u => u x) us }.

(* The closure of a family of sets by finite intersections. *)
Definition inter_close {A : Type} (S : P (P A)) :=
  { v : P A | some us : Forall S, (forall x, v x <-> inters us x) }.

Lemma Forall_app {A : Type} (l1 l2 : list A) (P : A -> Prop):
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1 ; simpl ; auto.
  intro H.
  inversion H; auto.
Qed.

Lemma Forall_app1 {A : Type} (l1 l2 : list A) (P : A -> Prop) :
  Forall P (l1 ++ l2) -> Forall P l1.
Proof.
  induction l1; simpl ; auto.
  intro H.
  inversion H; auto.
Qed.

Lemma Forall_app2 {A : Type} (l1 l2 : list A) (P : A -> Prop):
  Forall P (l1 ++ l2) -> Forall P l2.
Proof.
  induction l1; simpl ; auto.
  intros H.
  inversion H; auto.
Qed.

(* The topology generated by a subbase S. *)
Definition subbase {A : Type} (S : P (P A)) : topology A.
Proof.
  apply (base (inter_close S)).
  - exists nil ; firstorder using Forall_nil.
  - intros u [us [Hu Gu]] v [vs [Hv Gv]].
    exists (us ++ vs).
    split ; [ (now apply Forall_app) | idtac ].
    split.
    + intros [? ?].
      apply Forall_app ; firstorder.
    + intro K; split.
      * apply Gu.
        apply (Forall_app1 _ _ _ K).
      * apply Gv.
        apply (Forall_app2 _ _ _ K).
Defined.

Lemma subbase_open {A : Type} (S : P (P A)) (u : P A) :
  S u -> (subbase S) u.
Proof.
  intros H x.
  split.
  - intro G.
    exists u ; split ; [ idtac | firstorder ].
    exists (u :: nil).
    split ; [now constructor | idtac].
    intro y; split.
    + intro ; now constructor.
    + intro K.
      inversion K; auto.
  - firstorder.
Qed.

Definition cofinite (A: Type) : topology A :=
  subbase { u : P A | exists x, forall y, (u y <-> y <> x) }.

Lemma cofinite_T1 (A : Type) : T1 (cofinite A).
Proof.
  intros x y N.
  exists {z : A | z<>y}.
  split ; auto.
  apply subbase_open.
  exists y; firstorder.
Qed.


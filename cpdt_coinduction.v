(*Require Import Arith.*)
Require Import List.
(*Require Import Streams.*)

Add LoadPath "Cpdt".

Require Import List.

Require Import CpdtTactics.

Definition bad : unit := tt.

Set Implicit Arguments.


Set Asymmetric Patterns.

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx t n'
      end
  end.

Eval simpl in approx zeroes 10.

Eval simpl in approx trues_falses 10.

Section map.
  Variables A B : Type.
  Variables f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
    | Cons h t => Cons (f h) (map t)
    end.
End map.

Section interleave.
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
    | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.
(*
Section map'.
  Variables A B : Type.
  Variable f : A -> B.
  CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
End map'.
 *)

Definition tl A (s : stream A) : stream A :=
  match s with
  | Cons _ s' => s'
  end.

(*CoFixpoint bad : stream nat := bad.
 *)

CoFixpoint ones : stream nat := Cons 1 ones.

Definition ones' := map S zeroes.

Theorem ones_eq : ones = ones'.
Abort.

Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
      stream_eq t1 t2
      -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Theorem ones_eq : stream_eq ones ones'.
Proof.
  cofix ones_eq.
  assumption.
  Undo.
  simpl.
Abort.

Definition frob A (s : stream A) : stream A :=
  match s with
  | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s; reflexivity.
Qed.

Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  simpl.
  constructor.

    
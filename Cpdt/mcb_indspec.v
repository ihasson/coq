From mathcomp.ssreflect Require Import all_ssreflect.
(*From mathcomp.ssreflect Require Import ssrnotation.*)
(*From mathcomp Require Import all_ssreflect.*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint has T (a : T -> bool) (s : seq T) : bool :=
  if s is x :: s' then a x || has a s' else false.
(*
Definition has_prop T (a : T -> bool) (x0 : T) (s : seq T)
  :=
    exists i, i < size s /\ a (nth x0 s i)
                           .*)


Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.

Definition bool_Prop_equiv (P : Prop) (b : bool) := b = true <-> P.

Lemma test_bool_Prop_equiv b P : bool_Prop_equiv P b -> P \/ ~P.
Proof.
  case: b; case => hlr hrl.
    by left; apply: hlr.
      by right => hP; move: (hrl hP).
Qed.

Inductive reflect (P : Prop) (b : bool) : Prop :=
| ReflectT (p : P) (e : b = true)
| ReflectF (np : ~P) (e : b = false).

                                    
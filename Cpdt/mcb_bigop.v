From mathcomp.ssreflect Require Import all_ssreflect.
(*From mathcomp.ssreflect Require Import ssrnotation.*)
(*From mathcomp Require Import all_ssreflect.*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition index_iota m n := iota m (n - m).

Lemma sum_odd n : \sum_(0 <= i < n.*2 | odd i) i = n^2.
Proof.
 
From mathcomp.ssreflect Require Import all_ssreflect.
(*From mathcomp.ssreflect Require Import ssrnotation.*)
(*From mathcomp Require Import all_ssreflect.*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition f (n:nat) : nat := n + 1.
Compute f 3.

Definition g (n m : nat) : nat := n+ m*2.

Definition repeat_twice (g : nat -> nat) : nat -> nat :=
  fun x => g (g x).

Compute repeat_twice f 2.

Check (repeat_twice f).

Compute
  let n := 33 : nat in
  let e := n + n + n in
  e + e + e.

(*Inductive bool := true | false.
Check true.*)

Definition twoVthree (b : bool) := if b then 3 else 2.
(*Compute if true then 3 else 2.*)

Compute twoVthree true.
Compute twoVthree false.
Check fun n => f n.+1.

Definition non_zero n := if n is p.+1 then true else false.

(*Compute non_zero 5.*)

Definition pred' n := if n is p.+1 then p else 0.

Definition larger_than_4 n :=
  if n is n.+1.+1.+1.+1 then true else false.

Definition three_patterns n :=
  match n with
    u.+1.+1.+1.+1 => u
  | v.+1 => v
  | O => n
  end.

Definition same_bool b1 b2 :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

Fixpoint addn n m :=
  if n is p.+1 then (addn p m).+1 else m.

Fixpoint subn m n : nat :=
  match m, n with
  | p.+1, q.+1 => subn p q
  | _ , _ => m
  end.

Inductive listn := niln | consn (hd : nat) (tl : listn).

Check consn 1 (consn 2 niln).

Inductive listb := nilb | consb (hd : bool) (tl : listb).

(*Inductive seq' (A : Type) := nil | cons (hd : A) (tl : seq A).
*)
Check cons 2 nil.

Check 1 :: 2 :: 3 :: nil.
Check fun l => 1 :: 2 :: 3 :: l.
(*
Definition head T (x0 : T) (s : seq T) := if s is x :: _ then x else x0.

Fixpoint size A (s : seq A) :=
  if s is _ :: tl then (size tl).+1 else O.

Fixpoint map A B (f : A -> B) s :=
  if s is e :: tl then f e :: map f tl else nil.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s).
Compute [seq i.+1 | i <- [:: 2; 3]].
 *)
(*
Inductive option A :=
  None
| Some (a : A).

Definition only_odd (n : nat) : option nat :=
  if odd n then Some n else None.

Definition ohead (A : Type) (s : seq A) :=
  if s is x :: _ then Some x else None.

Inductive pair (A B : Type) : Type := mk_pair (a : A) (b : B).

Notation "( a , b )" := (pair a b).
Notation "A * B" := (pair A B).

Definition fst A B (p : pair A B) :=
  match p with mk_pair x _ => x end.

Check (3, false).

Record point : Type := Point { x : nat; y : nat; z : nat }.

Inductive point : Type := Point (x : nat)  (y : nat) (z : nat).
 

Compute x (Point 3 0 2).
Compute y (Point 3 0 2).
 *)
(*
Definition x (p : point) := match p with Point a _ _ => a end.


Definition x (p : point) := let : Point a _ _ := p in a.
 *)
(*
Section iterators.

  Variables (T : Type) (A: Type).
  Variables (f : T -> A -> A).

  Implicit Type x : T.

  Fixpoint iter n op x :=
    if n is p.+1 then op (iter p op x) else x.

  Fixpoint foldr a s :=
    if s is y :: ys then f y (foldr a ys) else a.

End iterators.

About foldr.

Compute iter 5 predn 7.

Compute foldr addn 0 [:: 1; 2].
 *)
(* Symbolic computation. *)
(*
Section iterators.
  Variables (T : Type) (A : Type).
  Variables (f : T -> A -> A).

  Fixpoint foldr a s :=
    if s is x :: xs then f x (foldr a xs) else a.

  About foldr.
  
  Variable init : A.

  Variables x1 x2 : T.
  Compute foldr init [:: x1 ; x2].
  Compute addn 1 (addn 2 0).

  Fixpoint add n m := if n is p.+1 then add p m.+1 else m.
  
  About add.

  Variable n : nat.

  Eval simpl in predn (add n .+1 7).
  (*      = (add n 8).-1 *)
     (* : nat *)

  Eval simpl in predn (addn n .+1 7).
  (*      = addn n 7 *)
     (* : nat *)
 *)

Fixpoint iota m n := if n is u.+1 then m :: iota m.+1 u else [::].
Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n-m))).


Compute \sum_ (1 <= i < 5) (i * 2 - 1).

Compute \sum_ (1 <= i < 5) i.

Locate "=".
About eq.

Definition negb (b : bool) : bool := if b then false else
                                       true.
Lemma negbK b : ~~ (~~ b) = b.
Proof.
  case: b.
    by [].
      by [].
Qed.

Lemma negbK' b: ~~ (~~ b) = b.
Proof.
    by case: b. Qed.

Lemma leqn0 n: (n<= 0) = (n == 0).
Proof.
  by case: n => [| k].
Qed.


Section Chinese.
  Variables m1 m2 : nat.
  Hypothesis co_m12: coprime m1 m2.

  Lemma chinese_remainder x y :
    (x == y %[mod m1 * m2]) =
    (x == y %[mod m1]) && (x == y %[mod m2]).
  Proof.
    Admitted.
    (* End. *)
End Chinese.

About factorial.

Lemma example m p : prime p -> p %| m`! + 1 -> m < p.
Proof.
  move => prime_p.
  apply: contraLR.
  rewrite -leqNgt.
  move=> leq_p_m.
Abort.

Fail Check n+n : bool.

(*Variable n : nat.*)
Check muln0 n : n*0 = 0.

Check Prop.

Section SeqTheory.
  Variable T : eqType.
  Implicit Type s : seq T.

  Fixpoint mem_seq s x :=
    if s is y :: s' then (y==x) || mem_seq s' x else false.

  Fixpoint uniq s :=
    if s is x :: s' then (x \notin s') && uniq s' else true.
  Fixpoint undpu s :=
    if s is x :: s' then
      if x \in s' then undup s' else x :: undup s'
    else [::].

  Lemma in_cons y s x : (x \in y :: s) = (x == y) || (x \in s).
  Proof.
      by []. Qed.

  Lemma mem_undup s : undup s =i s.
  Proof.
    move=> x; elim: s=> //= y s IHs.
    case Hy: (y \in  s); last by rewrite in_cons IHs.
      by rewrite in_cons IHs; case: eqP => // ->.
  Qed.

  Lemma undup_uniq s : uniq (undup s).
  Proof.
      by elim : s => //= x s IHs; case sx: (x \in s); rewrite //=
                                                              mem_undup sx.
  Qed.

  Fixpoint eqseq s1 s2 {struct s2} :=
    match s1, s2 with
    | [::], [::] => true
    | x1 :: s1', x2 :: s2' => (x1 == x2) && eqseq s1' s2'
    | _, _ => false
    end.

  Lemma eqseqP : Equality.axiom eqseq.
  Proof.
    elim=> [|x1 s1 IHs] [|x2 s2] /=; do? [exact: ReflectT | exact : ReflectF].
    case: (x1 =P x2) => [<-|neqx]; last by apply: ReflectF => -[ eqx _].
      by apply: (iffP (IHs s2)) => [<-|[]].
  Qed.

  Definition seq_eqMixin := Equality.Mixin eqseqP.
(*
  Canonical seq_eqType := @Equality.Pack (seq T) seq_eqMixin.
 *)
End SeqTheory.



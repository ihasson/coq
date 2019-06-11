(*Require Import Arith.*)
Require Import List.
(*Require Import Streams.*)

Add LoadPath "Cpdt".

Require Import List.

Require Import CpdtTactics.

Definition bad : unit := tt.

Set Implicit Arguments.

(*
Set Asymmetric Patterns.

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.
*)
(*
CoFixpoint zeroes : stream nat := Cons nat 0 zeroes.
Check zeroes.
 *)
(*
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
Compute Nat.pow 2 3 .
*)

(*
CoFixpoint geoseries a b :  := Cons (Nat.pow a b) geoseries(a (b+1)).
*)
Inductive list (A:Set) : Set :=
  nil : list A
| cons : A -> list A -> list A.

CoInductive Llist (A:Set) :  Set :=
  Lnil :  Llist A
| Lcons :  A -> Llist A -> Llist A.
(*Implicit Arguments Lcons.*)

Definition ll123 := Lcons 1 (Lcons 2 (Lcons 3 (Lnil nat))).

Fixpoint list_to_llist (A:Set) (l:list A)
         {struct l} : Llist A :=
  match l with
    nil => (Lnil A)
  | a :: tl => Lcons a (list_to_llist A tl)
  end.



CoFixpoint lones : Llist nat := Lcons 1 lones.

Definition f : unit -> unit+(nat*unit):= fun _ => inr unit (1,tt).

CoFixpoint stream_finality (A:Set) (B:Set) (f: B-> unit+(A*B)):B-> Llist A:=
  fun b : B=> match f b with
             inl tt => Lnil A
           | inr (a,b2) => Lcons a (stream_finality A B f b2)
           end.
 
CoFixpoint nums (n:nat) : stream nat :=
  Cons n (nums (n+1)).

CoInductive stream : Set :=
  | Cons : nat -> stream -> stream.

CoFixpoint zipWith (f : nat -> nat -> nat) (a : stream)
           (b:stream) : stream :=
  match a , b with
  | Cons x xs, Cons y ys => Cons (f x y) (zipWith f xs ys)
  end.


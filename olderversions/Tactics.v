Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.

Theorem silly2: forall (n m o p :nat),
    n=m->
    (forall (q r: nat), q=r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly2a: forall (n m : nat),
    (n,n) = (m,m) ->
    (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true -> oddb 4 = true.
Proof.
  intros n eq1.
  apply eq1. Qed.

Theorem silly3_firsttry: forall (n : nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  symmetry.
  simpl.
  apply H. Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
(*Proof.
  intros l l' H.
  rewrite H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.
 *)
Proof.
  intros l l' H.
  symmetry.
  rewrite H.
  apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite eq2. reflexivity.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f: nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with(m:=m).
  apply eq2.
  apply eq1.
Qed.

Theorem S_injective : forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
    [n; m] = [o; o] ->
    [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity.
Qed.

Theorem inversion_ex2 : forall (n m : nat),
    [n] = [m] ->
    n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity.
Qed.

Example inversion_ex3 : forall (X:Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1 as [eq1']. 
  inversion eq2 as [eq2'].
  symmetry.
  rewrite eq1'. reflexivity.
Qed.

Theorem  beq_nat_0_l : forall n,
    beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl.
    intros H. inversion H.
Qed.

Theorem inversion_ex4 : forall(n : nat),
    S n = O ->
    2+2 = 5.
Proof.
  intros n contra. inversion contra.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
    false = true ->
    [n] = [m].
Proof.
  intros n m contra. inversion contra.
Qed.

Example inversion_ex6 : forall (X : Type)
                               (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros X x y z l j contra.
  inversion contra.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
                  x = y -> f x = f y.
Proof.
  intros A B f x y eq. rewrite eq. reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b ->
    beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.


Theorem silly3' : forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
    n+n = m+m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - (* case n = 0 *)
    intros m H. destruct m as [| m'].
    reflexivity.
    inversion H.
  - (*case n = S n' *)
    intros m. destruct m as [| m'].
    + intros eq. inversion eq.
    + intros H.
      rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H.
      inversion H. apply IHn' in H1. rewrite -> H1.
      reflexivity.
Qed.

Theorem double_injective : forall n m,
    double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = 0 *) simpl. intros m eq. destruct m as [| m'].
    + (* m = 0 *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) simpl.
    intros m eq. destruct m as [| m'].
    + (* m = 0 *) simpl. inversion eq.
    + apply f_equal.
      apply IHn'. inversion eq. reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = 0 *) simpl. intros m eq. destruct m as [| m'].
    + (* m = 0 *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) simpl.
    intros m eq. destruct m as [| m'].
    + (* m = 0 *) simpl. inversion eq.
    + (* m = S m' *) apply f_equal.
      apply IHn'. inversion eq. reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on m 
     and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = 0 *) simpl. intros n eq. destruct n as [| n'].
    + (* n = 0 *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *)  intros n eq. destruct n as [| n'].
    + (* n = 0 *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity.
Qed.

Theorem beq_id_true : forall x y,
    beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
                       rewrite H'. reflexivity.
Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    nth_error l n = None.
  intros n X l.
  generalize dependent n.
  induction l as [| l'].
  - (* l = [] *) simpl. reflexivity.
  - (* l = x :: l' *) intros n eq. destruct n as [| n'].
    + inversion eq.
    + apply IHl. inversion eq. reflexivity.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n*m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false: forall (n : nat),
    sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
  - (* beq_nat n 3 = true *) reflexivity.
  - (* beq_nat n 3 = false *) destruct (beq_nat n 5).
    + (* beq_nat n 5 = true *) reflexivity.
    + (* beq_nat n 5 = false *) reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list(X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  intros.
Abort.

Definition sillyfun1 (n: nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  - (* e3 = true *) apply beq_nat_true in Heqe3.
Abort.

Theorem bool_fn_applied_thrice :
  forall (f: bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b. destruct (f b) eqn:Hbool.
  - destruct b as [| b'].
    + rewrite Hbool. apply Hbool.
    + destruct (f true) eqn:Htrue.
      { rewrite Htrue. reflexivity. }
      { apply Hbool. }
  - destruct b as [| b'].
    + destruct (f false) eqn:Hfalse.
      { rewrite Hbool. reflexivity. }
      { apply Hfalse. }
    + rewrite Hbool. rewrite Hbool. reflexivity.
Qed.

      
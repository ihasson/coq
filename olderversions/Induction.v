Require Export Basics.

Theorem plus_n_O_firsttry : forall n:nat,
    n = n+0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem plus_n_O : forall n:nat, n=n+0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n :nat,
    n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.
  
Theorem plus_n_Sm : forall n m :nat ,
    S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
(* it seems the trick to this proof was to only do induction on n *)

Theorem plus_comm : forall n m:nat,
    n + m = m + n.
Proof.
  intros m. induction m as [| m' IHm'].
  - { intros n. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite  <- IHn'. reflexivity.
   }
  - { intros n. induction n as [| n' IHn'].
      - simpl. rewrite -> IHm'. reflexivity.
      - simpl. rewrite -> IHm'.
        simpl. rewrite <- IHn'.
        rewrite <- IHm'.
        reflexivity.
    }
Qed.

Theorem plus_comm2 : forall n m:nat,
    n+m=m+n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.


Theorem plus_assoc : forall n m p :nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'.  reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n+n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - (*really need to show S(S (double n')) = S n' + S n' *)
    simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. rewrite -> negb_involutive. reflexivity.
Qed.

(* proofs within proofs *)
Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_rearrange_firsttry : forall m n p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange : forall m n p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  {rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem plus_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc'' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat ,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p. (*induction n as [| n' IHn'].*)
  rewrite -> plus_assoc.
  assert (H : n + m = m + n).
  { rewrite plus_comm. reflexivity. }
  rewrite  H.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Lemma mult_comm_lemma : forall m n : nat,
    m * S n = m + m*n.
Proof.
  intros m n. induction m as [| m' IHm'].
  - (* m = 0 *) simpl. reflexivity.
  - (* m = S m' *)
    simpl. rewrite -> plus_swap. rewrite -> IHm'. reflexivity.
Qed.
    
Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
  intros n m.
 (* assert (H0 : 0 = m * 0). { reflexivity. }*)
  induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite -> mult_0_r. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. rewrite -> mult_comm_lemma. reflexivity.
Qed.


Theorem leb_refl : forall n : nat,
    true = leb n n.
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
    beq_nat 0 (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
    andb b false = false.
Proof.
  intros b. destruct b as [| b'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
    leb n m = true -> leb (p+n) (p+m) = true.
Proof.
  intros n m p eq1. induction p as [| p'].
  - simpl. rewrite eq1. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n: nat,
    beq_nat (S n) 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite plus_n_O. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
            (negb c))
    = true.
Proof.
  intros b c. destruct b as [| b'].
  - simpl. destruct c as [| c'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p: nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction p as [| p' IHp'].
  - rewrite mult_0_r. rewrite mult_0_r. rewrite mult_0_r.
    simpl. reflexivity.
  - rewrite <- mult_comm. simpl. rewrite -> mult_comm. rewrite -> IHp'.
    symmetry.
    rewrite mult_comm. simpl.
    rewrite plus_comm. rewrite mult_comm. simpl.
    rewrite plus_swap.
    assert(H: m + p' *m + p' * n = m + (p' * m + p' * n)). {
      rewrite -> plus_assoc. simpl. reflexivity. }
    rewrite H. rewrite plus_assoc.
    assert(H1: p' * m + p' * n = p' * n + p' * m). {
      rewrite plus_comm. reflexivity. }
    rewrite H1.
    assert(H2: p' * n =  n * p'). {
      rewrite mult_comm. reflexivity. }
    assert(H3: p' * m =  m * p'). {
      rewrite mult_comm. reflexivity. }
    rewrite H2. rewrite H3.
    simpl. reflexivity.
Qed.

Theorem mult_assoc : forall n m p: nat,
    n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> mult_plus_distr_r. rewrite IHn'.
    reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
    true = beq_nat n n.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'.
    reflexivity.
Qed.

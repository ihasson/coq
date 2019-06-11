Set Warnings "-notation-overridden,-parsing".
Add LoadPath "~/Documents/lf" as LF.
From Coq Require Import omega.Omega.
From LF Require Import Maps.
From LF Require Import Imp.

Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
    generalize dependent st2;
    induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; apply H1. }
    subst st'0.
    apply IHE1_2. assumption.
    (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. inversion H5.
    (* E_IfFalse *)
    - (* b evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption. Qed.

Example auto_example_1 : forall (P Q R: Prop),
    (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_exmple_1': forall (P Q R: Prop),
    (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

Example auto_example_3 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  auto.
  auto 6.
Qed.

Example auto_example_4 : forall P Q R : Prop,
    Q ->
    (Q -> R) ->
    P \/ (Q /\ R).
Proof. auto. Qed.

Lemma le_antisym : forall n m : nat, ( n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
    (n <= p -> (n <= m /\ m <= n)) ->
     n <= p ->
     n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.
Example auto_example_6' : forall n m p : nat,
    (n <= p -> (n <= m /\ m <= n)) ->
    n <= p ->
    n = m.
Proof.
  intros.
  auto.
Qed.

Definition is_fortytwo x := (x = 42).

Hint Unfold is_fortytwo.
Example auto_example_7: forall x,
    (x<= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto. Qed.

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.

Theorem ceval_deterministic'_alt: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
                st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
    generalize dependent st2;
    induction E1;
    intros st2 E2; inv E2...
  - assert (st' = st'0) as EQ1...
    subst st'0...
  -
    + rewrite H in H5. inversion H5.
  -
    + rewrite H in H5. inversion H5.
  -
    + rewrite H in H2. inversion H2.
  - rewrite H in H4. inversion H4.
  - assert (st' = st'0) as EQ1...
    subst st'0...
Qed.

Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Theorem ceval_deterministic'': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; auto.
  -
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  -
    + rwinv H H5.
  -
    + rwinv H H5.
  -
    +
      rwinv H H2.
  -
    rwinv H H4.
  -
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.

Ltac find_rwinv :=
  match goal with
    H1 : ?E = true,
         H2 : ?E = false
    |- _ => rwinv H1 H2
  end.


Theorem ceval_deterministic''': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; try find_rwinv;
      auto.
  -  assert (st' = st'0) as EQ1 by auto.
     subst st'0.
     auto.
  -
    + assert (st' = st'0) as EQ1 by auto.
      subst st'0.
      auto. Qed.

Theorem ceval_deterministic'''': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2;
      inv E2; try find_rwinv;
        auto.
  - rewrite (IHE1_1 st'0 H1) in *. auto.
  -
    + rewrite (IHE1_1 st'0 H3) in *. auto.
Qed.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
end.

Theorem ceval_deterministic''''': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; try find_rwinv;
      repeat find_eqn; auto.
Qed.

Module Repeat.
  
  Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

  Notation "'SKIP'" :=
    CSkip.

  Notation "c1 ; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "X '::=' a" :=
    (CAsgn X a) (at level 60).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity).
  Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
    (CRepeat e1 b2) (at level 80, right associativity).

  Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (TEST b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (TEST b1 THEN c1 ELSE c2 FI) st'
  | E_WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileTrue : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall st st' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = true ->
      ceval st (CRepeat c1 b1) st'
  | E_RepeatLoop : forall st st' st'' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = false ->
      ceval st' (CRepeat c1 b1) st'' ->
      ceval st (CRepeat c1 b1) st''.

  Notation "st '=[' c ']=>' st'" := (ceval st c st')
                                      (at level 40).

  Theorem ceval_deterministic: forall c st st1 st2,
      st =[ c ]=> st1 ->
      st =[ c ]=> st2 ->
      st1 = st2.
  Proof.
    intros c st st1 st2 E1 E2.
    generalize dependent st2;
      induction E1;
      intros st2 E2; inv E2; try find_rwinv; repeat find_eqn;
        auto.
    - (* E_RepeatEnd *)
      + find_rwinv.
    -
      + find_rwinv.
  Qed.
  

  Theorem ceval_deterministic': forall c st st1 st2,
      st =[ c ]=> st1 ->
      st =[ c ]=> st2 ->
      st1 = st2.
  Proof.
    intros c st st1 st2 E1 E2.
    generalize dependent st2;
      induction E1;
      intros st2 E2; inv E2; repeat find_eqn; try find_rwinv;
        auto.
  Qed.

End Repeat.


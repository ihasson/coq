Require Export Tactics.

Theorem plus_2_2_is_4 :
  2+2=4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.

Definition  is_three (n : nat) : Prop := n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Example and_example : 3 + 4 = 7 /\ 2*2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.
    
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  apply and_intro.
  - (* n = 0 *) induction n as [| n'].
    + reflexivity.
    + inversion H.
  - (* m = 0 *) induction m as [| m'].
    + reflexivity.
    + rewrite plus_comm in H. inversion H.
Qed.

Lemma and_example2 :
  forall n m : nat , n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
 
Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - (* left *) apply HQ.
  - (* right *) apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - (* n = 0 *)
    rewrite Hn. reflexivity.
  - (* m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [| n].
  - intros m H. rewrite mult_0_l in H. left. apply H.
  - intros [| m].
    + right. reflexivity.
    + intros H. inversion H.
Qed.

Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

Module MyNot.

Definition not (P:Prop) := P -> False.

(*Notation "¬ x" := (not x) : type_scope.*)

Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not : forall (P:Prop),
  (not P) -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  apply ex_falso_quodlibet. apply H. assumption.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H H0.
  unfold not in H0.
  unfold not.
  intros P'.
  apply H0.
  apply H.
  apply P'.
Qed.

Theorem not_both_true_and_false : forall P : Prop, ~ (P /\ ~P).
Proof.
  intros.
  unfold not. intros H. destruct H.
  apply H0. assumption.
Qed.

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Module MyIff.

  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity)
                        : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.  
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

Theorem iff_refl : forall P : Prop,
    P <-> P.
Proof.
  intros P.
  split.
  - (* P -> P *)
    intros H. apply H.
  - intros H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  split.
  - (* P -> R *)
    intros H1.
    apply H0.
    apply H.
    assumption.
  - (* R -> P *)
    intros H1.
    apply H.
    apply H0.
    assumption.
Qed.

    
Theorem or_distributes_over_and : forall P Q R: Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split.
  - (* -> *)
    intros H. inversion H.
    + split.
      { left. apply H0. }
      { left. apply H0. }
    + split.
      { right. apply H0. }
      { right. apply H0. }
  - (* <- *)
    intros H. inversion H.
    + destruct H1.
      { left. apply H1. }
      { destruct H0.
        - left. apply H0.
        - right. split.
          + apply H0.
          + apply H1. }
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n=0 \/ m=0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n*m*p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m: nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even: exists n :nat , 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2+m).
  apply Hm.
Qed.

Theorem dist_not_exists: forall (X:Type) (P : X-> Prop),
    (forall x, P x) -> ~(exists x, ~ P x).
Proof.
  intros.
  intros x.
  destruct x.
  apply H0.
  apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - (*->*) intros H. destruct H as [X' H]. destruct H as [HP | HQ].
    + left. exists X'. apply HP.
    + right. exists X'. apply HQ.
  - (*<-*) intros H. destruct H as [HP | HQ].
    + destruct HP as [X' HP]. exists X'. left. apply HP.
    + destruct HQ as [X' HQ]. exists X'. right. apply HQ.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 : forall n,
    In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| x' l' IHl' ].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - (* -> *) intros H. induction l as [|x' l' IHl'].
    + (* l = nil, contradiction *)
      simpl in H. contradiction.
    + (* l = x' :: l' *)
      simpl in H. destruct H as [H1 | H2].
      { exists x'. split.
        - apply H1.
        - simpl. left. reflexivity. }
      { apply IHl' in H2. destruct H2 as [x2 H2]. exists x2. split.
        - apply proj1 in H2. apply H2.
        - simpl. right. apply proj2 in H2. apply H2. }
  - (* <- *) intros H. induction l as [| x' l' IHl'].
    + (* l = [] *)
      simpl in H. destruct H as [x' H]. apply proj2 in H. contradiction.
    + (* l = x' :: l' *)
      simpl. simpl in H. destruct H as [x'' H].
      inversion H. destruct H1 as [H2 | H3].
      { left. rewrite H2. apply H0. }
      { right. apply IHl'. exists x''. split.
        - apply H0.
        - apply H3. }
Qed.

Lemma in_app_iff : forall A l l' (a:A),
    In  a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l'. split.
  - (* -> *)
    intros H. induction l.
    + simpl. simpl in H. right. apply H.
    + simpl. simpl in H. destruct H.
      { left. left. apply H. }
      { apply IHl in H. apply or_assoc. right. apply H. }
  - (* <- *)
    intros H. induction l.
    + simpl. simpl in H. destruct H.
      { contradiction. }
      { apply H. }
    + simpl. simpl in H. apply or_assoc in H. destruct H as [H1 | [H2 | H3]].
      { left. apply H1. }
      { right. apply IHl. left.  apply H2.
      } { right. apply IHl. right. apply H3. }
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l. split.
  - (* -> *) intros H. induction l.
    + simpl. reflexivity.
    + simpl. split.
      { apply H. simpl. left. reflexivity. }
      { apply IHl. intros x0 H0. apply H. simpl. right. apply H0. }
  - (* <- *) intros H. induction l.
    + simpl. intros x0 H0. contradiction.
    + simpl. intros x0 H0. destruct H0 as [|H1 H2].
      { simpl in H. apply proj1 in H. rewrite H0 in H. apply H. }
      { simpl in H. apply proj2 in H.
        apply IHl with x0 in H. apply H. apply H1. }
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (n : nat) =>  if oddb n then Podd n else Peven n.


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n Hodd Heven.
  unfold combine_odd_even. destruct (oddb n) eqn: H.
  - apply Hodd. reflexivity.
  - apply Heven. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n Hcomb Hodd.
  unfold combine_odd_even in Hcomb.
  rewrite Hodd in Hcomb. assumption.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n Hcomb Heven.
  unfold combine_odd_even in Hcomb.
  rewrite Heven in Hcomb. assumption.
Qed.

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ ( In_map_iff _ _ _ _ _) H)
    as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Axiom functional_extensionality :
  forall {X Y : Type}
         {f g : X -> Y},
    (forall (x:X) , f x = g x) -> f = g.

Example funtion_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Theorem app_nil_l : forall(X:Type), forall l:list X,
      [] ++ l = l.
Proof.
  reflexivity.
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X. apply functional_extensionality.
  intros x. induction x as [|x' lx].
  - simpl. unfold tr_rev. simpl. reflexivity.
  - simpl.
    rewrite <- IHlx. simpl tr_rev.
    unfold tr_rev. simpl rev_append.
Abort.
 (* rev_append lx [ ] = rev lx 
          I think this is the problem. *)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [| k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
    exists k , n = if evenb n then double k
                   else S (double k).
(* for any n in N there exists k s.t. k = 2n or k = 2n+1. *)
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. exists 0. simpl. reflexivity.
  - destruct (evenb n') eqn: Heq.
    + rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
      exists n''. rewrite IHn'. reflexivity.
    + rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
      exists (n'' + 1). rewrite IHn'. rewrite double_plus. rewrite double_plus.
      rewrite plus_n_Sm. rewrite <- plus_1_l. rewrite <- plus_n_Sm.
      rewrite <- (plus_1_l (n'' + n'')). rewrite plus_comm.
      rewrite plus_assoc. rewrite (plus_comm 1).
      rewrite plus_assoc. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
    evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
    beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Lemma andb_true_iff : forall b1 b2 : bool,
    b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - (* -> *) intros H. split.
    + rewrite andb_commutative in H. apply andb_true_elim2 in H. apply H.
    + apply andb_true_elim2 in H. apply H.
  - (* <- *) intros H. inversion H. rewrite H0. rewrite H1. reflexivity.
Qed.



Lemma orb_true_iff : forall b1 b2,
    b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - (* -> *) intros H.
    destruct b1.
    + simpl. left. reflexivity.
    + simpl. right. assumption.
  - (* <- *) intros H.
    destruct H as [H1 | H2].
    + rewrite H1. simpl. reflexivity.
    + rewrite H2. destruct b1.
      { reflexivity. }
      { reflexivity. }
Qed.

Theorem beq_nat_false_iff : forall x y : nat,
    beq_nat x y = false <-> x <> y.
Proof.
  intros x y. unfold not. split.
  - (* -> *) intros H0 H1. apply beq_nat_true_iff in H1.
    rewrite H1 in H0. inversion H0.
  - (* <- *) intros H.
    induction x as [| x'].
    + induction y as [| y'].
      { simpl. exfalso. apply H. reflexivity. }
      { generalize dependent y'. reflexivity. }
    + induction y as [| y'].
      { simpl. reflexivity. }
      { simpl. destruct (beq_nat x' y') eqn:Heq.
        - exfalso. apply H. apply f_equal. apply beq_nat_true_iff. apply Heq.
        - reflexivity. }
Qed.
      
Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match l1,l2 with
  | [] , [] => true
  | [] , _ => false
  | _ , [] => false
  | h1 :: t1, h2 :: t2 => (andb (beq h1 h2) (beq_list beq t1 t2))
  end.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H l1 l2. split.
  - (* -> *) generalize dependent l2.
    induction l1 as [| h1 l1' IHl1].
    + induction l2 as [| h2 l2' IHl2].
      { simpl. reflexivity. }
      { simpl. intros H1. inversion H1. }
    + induction l2 as [| h2 l2' IHl2].
      { simpl. intros H1. inversion H1. }
      { simpl. intros H1. destruct (beq h1 h2) eqn:Heq.
        + apply H in Heq. rewrite <- Heq.
          assert (l1' = l2' -> h1 :: l1' = h1 :: l2') as H2.
          { intros H3. rewrite H3. reflexivity. }
          apply H2. apply IHl1. apply H1.
        + inversion H1. }
  - (* <- *) generalize dependent l2.
    induction l1 as [| h1 l1' IHl1'].
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. reflexivity. }
      { simpl. intros H1. inversion H1. }
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. intros H1. inversion H1. }
      { simpl. intros H1. destruct (beq h1 h2) eqn:Heq.
        + apply IHl1'. apply H in Heq. rewrite Heq in H1.
          assert (h1 :: l1' = h1 :: l2' -> l1' = l2') as H2.
          { intros H3. inversion H1. reflexivity. }
          apply H2. rewrite Heq. apply H1.
        + inversion H1. apply H in H2. rewrite H2 in Heq. symmetry. apply Heq. }
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
Abort.

Definition excluded_middle := forall P : Prop,
    P \/ ~P.

Theorem restricted_excluded_middle : forall P b,
    (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
    n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n=m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

Theorem excluded_middle_irrefutable: forall (P : Prop),
    ~~(P \/ ~P).
Proof.
  unfold not. intros P H. apply H.
  right. intros. apply H. left. apply H0.
Qed.


Structure group :=
  {
    G:> Set;
    id : G;
    op : G -> G -> G;
    inv : G -> G;

    op_assoc : forall (x y z : G) , op x (op y z) = op (op x y) z;
    op_inv_l : forall (x : G), id = op (inv x) x;
    op_id_l : forall (x : G), x = op id x;
    op_inv_r: forall (x : G), id = op x (inv x);
    op_id_r : forall (x : G), x = op x id
  }.

Arguments id {g}.
Arguments op {g} _ _.
Arguments inv {g} _.

Notation "x <.> y" := (op x y) (at level 50, left associativity).
  
Theorem square_is_unique (G : group) :
  forall (f : G), f <.> f = f -> f = id.
Proof.
  intros f H.
  assert (H0 : (inv f) <.> (f <.> f) = (inv f) <.> f).
  { simpl. f_equal. assumption. }
  assert (H1 : (inv f) <.> f = id). { rewrite <- op_inv_l. reflexivity. }
  
  rewrite op_id_l in H1.
  rewrite H1 in H0.
  rewrite op_assoc in H0.
  rewrite <- op_inv_l in H0.
  rewrite <- op_id_l in H0.
  rewrite <- op_inv_l in H1.
  rewrite <- H1 in H0.
  assumption.
Qed.

(*
Theorem square_is_unique (G : group) :
  forall (f : G), f <.> f = f -> f = id.
Proof.
  intros f H1.
  assert ((inv f) <.> (f <.> f) = (inv f) <.> f) as H2.
  - f_equal. assumption.
  - rewrite op_assoc, <- op_inv_l, <- op_id_l in H2.
    assumption.
Qed.*)


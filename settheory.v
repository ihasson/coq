Require Import Classical_sets.

(* want to show E-F = E ∩ Fᶜ *)
Variable U : Type.
Theorem attempt1 :
  forall X Y: Ensemble U , (Setminus U X Y) = Intersection U X (Complement U Y).
Proof.
  
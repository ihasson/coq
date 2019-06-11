Require Export Lists.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

(*
Check (cons nat 2 (cons nat 1 (nil nat))).
 *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1:
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.

  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

  Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  Check d mumble (b a 5).
  Check d bool (b a 5).
  Check e bool true.
  Check e mumble (b c 0).
  Check c.
End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
Check repeat.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
| nil' : list'
| cons' : X-> list' -> list'.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
      l ++ [] = l.
Proof.
  intros X l. induction l as [|n l' IHl'].
  - simpl. reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n: list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n . induction l as [| h  l'  IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons h l' *)
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
      rev (rev l) = l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'.
    simpl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x::tx, y:: ty => (x,y) :: (combine tx ty)
  end.

Check @combine.
Compute (combine [1;2] [false;false;true;true]).

(* two approaches , use left split and right split or
 * do both splits together.
 *)
Fixpoint lsplit {X Y : Type} (l : list (X*Y)) : (list X) :=
  match l with
  | [] => []
  | p::tp => (fst p)::(lsplit tp)
  end.
Fixpoint rsplit {X Y : Type} (l : list (X*Y)) : (list Y) :=
  match l with
  | [] => []
  | p::tp => (snd p)::(rsplit tp)
  end.
Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([],[])
  | (x,y)::txy => (x::(lsplit txy),y::(rsplit txy))
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n 0 then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => Some a
  end.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error ([] : (list (option nat)))  = None.
Proof. reflexivity. Qed.


Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test : X -> bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
              else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1
         [ [1;2];[3];[4]; [5;6;7]; []; [8]] = [[3];[4];[8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n*n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l =>  beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun a =>  (andb (evenb a) (blt_nat  7 a) ))  l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type}
           (test : X -> bool)
           (l : list X)
  : list X * list X :=
  ((filter test l), (filter (fun n => negb (test n)) l)).
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f: X-> Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
           map oddb [2;1;2;5] = [false; true; false; true].
Proof. reflexivity. Qed.

Example test_map3:
  map (fun n => [evenb n; oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_app_distr : forall (X Y : Type) (f : X-> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.
    
Theorem map_rev : forall (X Y :Type) (f :X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros X Y f l . induction l as [| n l' IHl'].
  - reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite <- IHl'. rewrite -> map_app_distr. simpl. reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | n::l' => (f n) ++ (flat_map f l')
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.
(* should do this exercise just above the start of the Fold section*)

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb).

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Compute (fold (fun l n => length(l) + n) [[1;2];[];[3]] 0).

Definition constfun {X: Type} (x:X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.


Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

  Definition fold_length {X : Type} (l : list X) : nat :=
    fold (fun _ n => S n) l 0.

  Example test_fold_length1 : fold_length [4;7;0] = 3.
  Proof. reflexivity. Qed.

  Theorem fold_length_correct : forall X (l: list X),
      fold_length l = length l.
  Proof.
    intros X l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite <- IHl'. reflexivity.
  Qed.

  Definition fold_map {X Y:Type} (f : X -> Y) (l: list X) : list Y :=
    (fold (fun n b => (f n)::b) l [] ).
 
  Compute fold_map (fun n => n+1) [1;2;3].
  Theorem fold_map_correct : forall {X Y: Type} (f : X -> Y) (l: list X),
      fold_map f l = map f l.
  Proof.
    intros X Y f l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite <- IHl'. reflexivity.
  Qed.

  Definition prod_curry {X Y Z : Type}
             (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
  
(*  Definition prod_uncurry {X Y Z : Type}
             (f : X -> Y -> Z) (p : X * Y) : Z :=
  *)  
End Exercises.               


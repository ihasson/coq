
(*Require Import Coq.Numbers.Integer.NatPairs.ZNatPairs.*)
Require Export Int ZArith.
Import Z_as_Int.

Compute Z.eq (-1) 1.
Check (-1)%Z.
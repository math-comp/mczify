From Coq Require Import BinInt Zify.
From mathcomp Require Import all_ssreflect all_algebra zify ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Delimit Scope Z_scope with Z.

Fact test_unit_int m :
  m \is a GRing.unit = (Z_of_int m =? 1)%Z || (Z_of_int m =? - 1)%Z.
Proof. zify_pre_hook; zify_op; reflexivity. Qed.

From Coq Require Import BinInt Zify.
From mathcomp Require Import all_ssreflect all_algebra zify ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Delimit Scope Z_scope with Z.

Fact test_zero_nat : Z.of_nat 0%R = 0%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_add_nat n m : Z.of_nat (n + m)%R = (Z.of_nat n + Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_one_nat : Z.of_nat 1%R = 1%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_mul_nat n m : Z.of_nat (n * m)%R = (Z.of_nat n * Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_natmul_nat n m : Z.of_nat (n *+ m)%R = (Z.of_nat n * Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_exp_nat n m : Z.of_nat (n ^+ m)%R = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_zero_N : Z.of_N 0%R = 0%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_add_N n m : Z.of_N (n + m)%R = (Z.of_N n + Z.of_N m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_one_N : Z.of_N 1%R = 1%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_mul_N n m : Z.of_N (n * m)%R = (Z.of_N n * Z.of_N m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_natmul_N n m : Z.of_N (n *+ m)%R = (Z.of_N n * Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_exp_N n m : Z.of_N (n ^+ m)%R = (Z.of_N n ^ Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_unit_int m :
  m \is a GRing.unit = (Z_of_int m =? 1)%Z || (Z_of_int m =? - 1)%Z.
Proof. zify_pre_hook; zify_op; reflexivity. Qed.

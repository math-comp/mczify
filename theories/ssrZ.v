From Coq Require Import ZArith.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import order binomial ssralg countalg ssrnum ssrint.
From mathcomp Require Import zify_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Definition int_of_Z (n : Z) : int :=
  match n with
  | Z0 => Posz 0
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => Negz (Pos.to_nat p).-1
  end.

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

Lemma int_of_ZK : cancel int_of_Z Z_of_int.
Proof. by case=> //= p; lia. Qed.

Lemma Z_of_intK : cancel Z_of_int int_of_Z.
Proof.
case=> [[|n]|n] //=.
  congr Posz; lia.
rewrite addnC /=; congr Negz; lia.
Qed.

Module ZInstances.

Implicit Types (m n : Z).

Fact eqZP : Equality.axiom Z.eqb.
Proof. by move=> x y; apply: (iffP idP); lia. Qed.

#[export]
HB.instance Definition _ := hasDecEq.Build Z eqZP.

#[export]
HB.instance Definition _ := Countable.copy Z (can_type int_of_ZK).

#[export]
HB.instance Definition _ := GRing.isZmodule.Build Z
  Zplus_assoc Zplus_comm Zplus_0_l Zplus_opp_l.

#[export]
HB.instance Definition _ := GRing.Zmodule_isComRing.Build Z
  Zmult_assoc Zmult_comm Zmult_1_l Zmult_plus_distr_l isT.

Definition unitZ := [qualify a n : Z | (n == Z.pos xH) || (n == Z.neg xH)].
Definition invZ n := n.

Fact mulVZ : {in unitZ, left_inverse 1%R invZ *%R}.
Proof. by move=> n /pred2P[] ->. Qed.

Fact unitZPl m n : (n * m = 1)%R -> m \is a unitZ.
Proof. case: m n => [|[m|m|]|[m|m|]] [|n|n] //= []; lia. Qed.

Fact invZ_out : {in [predC unitZ], invZ =1 id}.
Proof. exact. Qed.

#[export]
HB.instance Definition _ := GRing.ComRing_hasMulInverse.Build Z
  mulVZ unitZPl invZ_out.

Fact idomain_axiomZ m n : (m * n = 0)%R -> (m == 0%R) || (n == 0%R).
Proof. by case: m n => [|m|m] []. Qed.

#[export]
HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build Z idomain_axiomZ.

Fact leZ_add m n : Z.leb 0 m -> Z.leb 0 n -> Z.leb 0 (m + n). Proof. lia. Qed.
Fact leZ_mul m n : Z.leb 0 m -> Z.leb 0 n -> Z.leb 0 (m * n). Proof. lia. Qed.
Fact leZ_anti m : Z.leb 0 m -> Z.leb m 0 -> m = Z0. Proof. lia. Qed.

Fact subZ_ge0 m n : Z.leb 0 (n - m)%R = Z.leb m n.
Proof. by rewrite /GRing.add /GRing.opp /=; lia. Qed.

Fact leZ_total m n : Z.leb m n || Z.leb n m. Proof. lia. Qed.

Fact normZN m : Z.abs (- m) = Z.abs m. Proof. lia. Qed.

Fact geZ0_norm m : Z.leb 0 m -> Z.abs m = m. Proof. lia. Qed.

Fact ltZ_def m n : (Z.ltb m n) = (n != m) && (Z.leb m n).
Proof. by rewrite eqE /=; lia. Qed.

#[export]
HB.instance Definition _ := Num.IntegralDomain_isLeReal.Build Z
  leZ_add leZ_mul leZ_anti subZ_ge0 (leZ_total 0) normZN geZ0_norm ltZ_def.

Fact Z_of_intE (n : int) : Z_of_int n = (n%:~R)%R.
Proof.
have Hnat (m : nat) : Z.of_nat m = (m%:R)%R.
  by elim: m => // m; rewrite Nat2Z.inj_succ -Z.add_1_l mulrS => ->.
case: n => n; rewrite /intmul /=; first exact: Hnat.
by congr Z.opp; rewrite Nat2Z.inj_add /= mulrSr Hnat.
Qed.

Fact Z_of_int_is_additive : additive Z_of_int.
Proof. by move=> m n; rewrite !Z_of_intE raddfB. Qed.

#[export]
HB.instance Definition _ := GRing.isAdditive.Build int Z Z_of_int
  Z_of_int_is_additive.

Fact int_of_Z_is_additive : additive int_of_Z.
Proof. exact: can2_additive Z_of_intK int_of_ZK. Qed.

#[export]
HB.instance Definition _ := GRing.isAdditive.Build Z int int_of_Z
  int_of_Z_is_additive.

Fact Z_of_int_is_multiplicative : multiplicative Z_of_int.
Proof. by split => // n m; rewrite !Z_of_intE rmorphM. Qed.

#[export]
HB.instance Definition _ := GRing.isMultiplicative.Build int Z Z_of_int
  Z_of_int_is_multiplicative.

Fact int_of_Z_is_multiplicative : multiplicative int_of_Z.
Proof. exact: can2_rmorphism Z_of_intK int_of_ZK. Qed.

#[export]
HB.instance Definition _ := GRing.isMultiplicative.Build Z int int_of_Z
  int_of_Z_is_multiplicative.

Module Exports. HB.reexport. End Exports.

End ZInstances.

Export ZInstances.Exports.

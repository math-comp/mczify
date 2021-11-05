From Coq Require Import ZArith.

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

Canonical Z_eqType := EqType Z (EqMixin eqZP).
Canonical Z_choiceType := ChoiceType Z (CanChoiceMixin int_of_ZK).
Canonical Z_countType := CountType Z (CanCountMixin int_of_ZK).

Definition Z_zmodMixin :=
  ZmodMixin Zplus_assoc Zplus_comm Zplus_0_l Zplus_opp_l.
Canonical Z_zmodType := ZmodType Z Z_zmodMixin.

Definition Z_ringMixin :=
  RingMixin
    Zmult_assoc Zmult_1_l Zmult_1_r Zmult_plus_distr_l Zmult_plus_distr_r isT.
Canonical Z_ringType := RingType Z Z_ringMixin.
Canonical Z_comRingType := ComRingType Z Zmult_comm.

Definition unitZ := [qualify a n : Z | (n == Z.pos xH) || (n == Z.neg xH)].
Definition invZ n := n.

Fact mulVZ : {in unitZ, left_inverse 1%R invZ *%R}.
Proof. by move=> n /pred2P[] ->. Qed.

Fact unitZPl m n : (n * m = 1)%R -> m \is a unitZ.
Proof. case: m n => [|[m|m|]|[m|m|]] [|n|n] //= []; lia. Qed.

Fact invZ_out : {in [predC unitZ], invZ =1 id}.
Proof. exact. Qed.

Fact idomain_axiomZ m n : (m * n = 0)%R -> (m == 0%R) || (n == 0%R).
Proof. by case: m n => [|m|m] []. Qed.

Canonical Z_unitRingType :=
  UnitRingType Z (ComUnitRingMixin mulVZ unitZPl invZ_out).
Canonical Z_comUnitRing := [comUnitRingType of Z].
Canonical Z_idomainType := IdomainType Z idomain_axiomZ.

Canonical Z_countZmodType := [countZmodType of Z].
Canonical Z_countRingType := [countRingType of Z].
Canonical Z_countComRingType := [countComRingType of Z].
Canonical Z_countUnitRingType := [countUnitRingType of Z].
Canonical Z_countComUnitRingType := [countComUnitRingType of Z].
Canonical Z_countIdomainType := [countIdomainType of Z].

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

Definition Mixin : realLeMixin [idomainType of Z] :=
  RealLeMixin
    leZ_add leZ_mul leZ_anti subZ_ge0 (leZ_total 0) normZN geZ0_norm ltZ_def.

Canonical Z_porderType := POrderType ring_display Z Mixin.
Canonical Z_latticeType := LatticeType Z Mixin.
Canonical Z_distrLatticeType := DistrLatticeType Z Mixin.
Canonical Z_orderType := OrderType Z leZ_total.
Canonical Z_numDomainType := NumDomainType Z Mixin.
Canonical Z_normedZmodType := NormedZmodType Z Z Mixin.
Canonical Z_realDomainType := [realDomainType of Z].

Fact Z_of_intE (n : int) : Z_of_int n = (n%:~R)%R.
Proof.
have Hnat (m : nat) : Z.of_nat m = (m%:R)%R.
  by elim: m => // m; rewrite Nat2Z.inj_succ -Z.add_1_l mulrS => ->.
case: n => n; rewrite /intmul /=; first exact: Hnat.
by congr Z.opp; rewrite Nat2Z.inj_add /= mulrSr Hnat.
Qed.

Fact Z_of_int_is_additive : additive Z_of_int.
Proof. by move=> m n; rewrite !Z_of_intE raddfB. Qed.

Canonical Z_of_int_additive := Additive Z_of_int_is_additive.

Fact int_of_Z_is_additive : additive int_of_Z.
Proof. exact: can2_additive Z_of_intK int_of_ZK. Qed.

Canonical int_of_Z_additive := Additive int_of_Z_is_additive.

Fact Z_of_int_is_multiplicative : multiplicative Z_of_int.
Proof. by split => // n m; rewrite !Z_of_intE rmorphM. Qed.

Canonical Z_of_int_rmorphism := AddRMorphism Z_of_int_is_multiplicative.

Fact int_of_Z_is_multiplicative : multiplicative int_of_Z.
Proof. exact: can2_rmorphism Z_of_intK int_of_ZK. Qed.

Canonical int_of_Z_rmorphism := AddRMorphism int_of_Z_is_multiplicative.

End ZInstances.

Canonical ZInstances.Z_eqType.
Canonical ZInstances.Z_choiceType.
Canonical ZInstances.Z_countType.
Canonical ZInstances.Z_zmodType.
Canonical ZInstances.Z_ringType.
Canonical ZInstances.Z_comRingType.
Canonical ZInstances.Z_unitRingType.
Canonical ZInstances.Z_comUnitRing.
Canonical ZInstances.Z_idomainType.
Canonical ZInstances.Z_countZmodType.
Canonical ZInstances.Z_countRingType.
Canonical ZInstances.Z_countComRingType.
Canonical ZInstances.Z_countUnitRingType.
Canonical ZInstances.Z_countComUnitRingType.
Canonical ZInstances.Z_countIdomainType.
Canonical ZInstances.Z_porderType.
Canonical ZInstances.Z_latticeType.
Canonical ZInstances.Z_distrLatticeType.
Canonical ZInstances.Z_orderType.
Canonical ZInstances.Z_numDomainType.
Canonical ZInstances.Z_normedZmodType.
Canonical ZInstances.Z_realDomainType.
Canonical ZInstances.Z_of_int_additive.
Canonical ZInstances.int_of_Z_additive.
Canonical ZInstances.Z_of_int_rmorphism.
Canonical ZInstances.int_of_Z_rmorphism.

From Coq Require Import ZArith ZifyClasses ZifyBool.
From Coq Require Export Lia.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import order binomial ssralg countalg ssrnum ssrint rat.
From mathcomp Require Import intdiv.
From mathcomp Require Import zify_ssreflect ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module AlgebraZifyInstances.

Local Delimit Scope Z_scope with Z.

Import Order.Theory GRing.Theory Num.Theory SsreflectZifyInstances.

(* TODO: remove natn below when we drop support for MathComp 2.0 *)
Local Lemma natn n : n%:R%R = n :> nat.
Proof. by elim: n => // n; rewrite mulrS => ->. Qed.

(******************************************************************************)
(* nat                                                                        *)
(******************************************************************************)

#[global]
Instance Op_nat_0 : CstOp (0%R : nat) := ZifyInst.Op_O.
Add Zify CstOp Op_nat_0.

#[global]
Instance Op_nat_add : BinOp (+%R : nat -> nat -> nat) := Op_addn.
Add Zify BinOp Op_nat_add.

#[global]
Instance Op_nat_1 : CstOp (1%R : nat) := { TCst := 1%Z; TCstInj := erefl }.
Add Zify CstOp Op_nat_1.

#[global]
Instance Op_nat_mul : BinOp ( *%R : nat -> nat -> nat) := Op_muln.
Add Zify BinOp Op_nat_mul.

Fact Op_nat_natmul_subproof (n m : nat) :
  Z.of_nat (n *+ m)%R = (Z.of_nat n * Z.of_nat m)%Z.
Proof. by rewrite raddfMn -mulr_natr -[m in RHS]natn rmorph_nat. Qed.

#[global]
Instance Op_nat_natmul : BinOp (@GRing.natmul _ : nat -> nat -> nat) :=
  { TBOp := Z.mul; TBOpInj := Op_nat_natmul_subproof }.
Add Zify BinOp Op_nat_natmul.

Fact Op_nat_exp_subproof (n : nat) (m : nat) :
  Z_of_nat (n ^+ m)%R = (Z_of_int n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia. Qed.

#[global]
Instance Op_nat_exp : BinOp (@GRing.exp _ : nat -> nat -> nat) :=
  { TBOp := Z.pow; TBOpInj := Op_nat_exp_subproof }.
Add Zify BinOp Op_nat_exp.

(******************************************************************************)
(* N                                                                          *)
(******************************************************************************)

#[global]
Instance Op_N_0 : CstOp (0%R : N) := ZifyInst.Op_N_N0.
Add Zify CstOp Op_N_0.

#[global]
Instance Op_N_add : BinOp (+%R : N -> N -> N) := ZifyInst.Op_N_add.
Add Zify BinOp Op_N_add.

#[global]
Instance Op_N_1 : CstOp (1%R : N) := { TCst := 1%Z; TCstInj := erefl }.
Add Zify CstOp Op_N_1.

#[global]
Instance Op_N_mul : BinOp ( *%R : N -> N -> N) := ZifyInst.Op_N_mul.
Add Zify BinOp Op_N_mul.

Fact Op_N_natmul_subproof (n : N) (m : nat) :
  Z.of_N (n *+ m)%R = (Z.of_N n * Z.of_nat m)%Z.
Proof. by rewrite raddfMn -mulr_natr -[m in RHS]natn rmorph_nat. Qed.

#[global]
Instance Op_N_natmul : BinOp (@GRing.natmul _ : N -> nat -> N) :=
  { TBOp := Z.mul; TBOpInj := Op_N_natmul_subproof }.
Add Zify BinOp Op_N_natmul.

Fact Op_N_exp_subproof (n : N) (m : nat) :
  Z_of_N (n ^+ m)%R = (Z_of_N n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia. Qed.

#[global]
Instance Op_N_exp : BinOp (@GRing.exp _ : N -> nat -> N) :=
  { TBOp := Z.pow; TBOpInj := Op_N_exp_subproof }.
Add Zify BinOp Op_N_exp.

(******************************************************************************)
(* ssrint                                                                     *)
(******************************************************************************)

#[global]
Instance Inj_int_Z : InjTyp int Z :=
  { inj := Z_of_int; pred _ := True; cstr _ := I }.
Add Zify InjTyp Inj_int_Z.

#[global]
Instance Op_Z_of_int : UnOp Z_of_int := { TUOp := id; TUOpInj _ := erefl }.
Add Zify UnOp Op_Z_of_int.

#[global]
Instance Op_int_of_Z : UnOp int_of_Z := { TUOp := id; TUOpInj := int_of_ZK }.
Add Zify UnOp Op_int_of_Z.

#[global]
Instance Op_Posz : UnOp Posz := { TUOp := id; TUOpInj _ := erefl }.
Add Zify UnOp Op_Posz.

#[global]
Instance Op_Negz : UnOp Negz :=
  { TUOp x := (- (x + 1))%Z; TUOpInj := ltac:(simpl; lia) }.
Add Zify UnOp Op_Negz.

#[global]
Instance Op_int_eq : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := ltac:(by split=> [->|/(can_inj Z_of_intK)]) }.
Add Zify BinRel Op_int_eq.

#[global]
Instance Op_int_eq_op : BinOp (@eq_op int : int -> int -> bool) :=
  { TBOp := Z.eqb;
    TBOpInj := ltac:(move=> [] ? [] ?; do 2 rewrite eqE /=; lia) }.
Add Zify BinOp Op_int_eq_op.

#[global]
Instance Op_int_0 : CstOp (0%R : int) := { TCst := 0%Z; TCstInj := erefl }.
Add Zify CstOp Op_int_0.

#[global]
Instance Op_addz : BinOp intZmod.addz := { TBOp := Z.add; TBOpInj := raddfD _ }.
Add Zify BinOp Op_addz.

#[global]
Instance Op_int_add : BinOp +%R := Op_addz.
Add Zify BinOp Op_int_add.

#[global]
Instance Op_oppz : UnOp intZmod.oppz := { TUOp := Z.opp; TUOpInj := raddfN _ }.
Add Zify UnOp Op_oppz.

#[global]
Instance Op_int_opp : UnOp (@GRing.opp _) := Op_oppz.
Add Zify UnOp Op_int_opp.

#[global]
Instance Op_int_1 : CstOp (1%R : int) := { TCst := 1%Z; TCstInj := erefl }.
Add Zify CstOp Op_int_1.

#[global]
Instance Op_mulz : BinOp intRing.mulz :=
  { TBOp := Z.mul; TBOpInj := rmorphM _ }.
Add Zify BinOp Op_mulz.

#[global]
Instance Op_int_mulr : BinOp *%R := Op_mulz.
Add Zify BinOp Op_int_mulr.

#[global]
Instance Op_int_natmul : BinOp (@GRing.natmul _ : int -> nat -> int) :=
  { TBOp := Z.mul; TBOpInj _ _ := ltac:(rewrite /= pmulrn mulrzz; lia) }.
Add Zify BinOp Op_int_natmul.

#[global]
Instance Op_int_intmul : BinOp ( *~%R%R : int -> int -> int) :=
  { TBOp := Z.mul; TBOpInj _ _ := ltac:(rewrite /= mulrzz; lia) }.
Add Zify BinOp Op_int_intmul.

#[global]
Instance Op_int_scale : BinOp (@GRing.scale _ int^o) :=
  Op_mulz.
Add Zify BinOp Op_int_scale.

Fact Op_int_exp_subproof n m : Z_of_int (n ^+ m) = (Z_of_int n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia. Qed.

#[global]
Instance Op_int_exp : BinOp (@GRing.exp _ : int -> nat -> int) :=
  { TBOp := Z.pow; TBOpInj := Op_int_exp_subproof }.
Add Zify BinOp Op_int_exp.

#[global]
Instance Op_unitz : UnOp (has_quality 1 intUnitRing.unitz : int -> bool) :=
  { TUOp x := (x =? 1)%Z || (x =? - 1)%Z; TUOpInj := ltac:(simpl; lia) }.
Add Zify UnOp Op_unitz.

#[global]
Instance Op_int_unit : UnOp (has_quality 1 GRing.unit) := Op_unitz.
Add Zify UnOp Op_int_unit.

#[global]
Instance Op_invz : UnOp intUnitRing.invz :=
  { TUOp := id; TUOpInj _ := erefl }.
Add Zify UnOp Op_invz.

#[global]
Instance Op_int_inv : UnOp GRing.inv := Op_invz.
Add Zify UnOp Op_int_inv.

#[global]
Instance Op_absz : UnOp absz :=
  { TUOp := Z.abs; TUOpInj := ltac:(case=> ? /=; lia) }.
Add Zify UnOp Op_absz.

#[global]
Instance Op_int_normr : UnOp (Num.norm : int -> int) :=
  { TUOp := Z.abs; TUOpInj := ltac:(rewrite /Num.norm /=; lia) }.
Add Zify UnOp Op_int_normr.

#[global]
Instance Op_lez : BinOp intOrdered.lez :=
  { TBOp := Z.leb; TBOpInj := ltac:(case=> ? [] ? /=; lia) }.
Add Zify BinOp Op_lez.

#[global]
Instance Op_ltz : BinOp intOrdered.ltz :=
  { TBOp := Z.ltb; TBOpInj := ltac:(case=> ? [] ? /=; lia) }.
Add Zify BinOp Op_ltz.

#[global]
Instance Op_int_sgr : UnOp (Num.sg : int -> int) :=
  { TUOp := Z.sgn; TUOpInj := ltac:(case=> [[]|] //=; lia) }.
Add Zify UnOp Op_int_sgr.

#[global]
Instance Op_int_sgz : UnOp (@sgz _) := Op_int_sgr.
Add Zify UnOp Op_int_sgz.

#[global]
Instance Op_int_le : BinOp <=%O := Op_lez.
Add Zify BinOp Op_int_le.

#[global]
Instance Op_int_le' : BinOp (>=^d%O : rel int^d) := Op_lez.
Add Zify BinOp Op_int_le'.

#[global]
Instance Op_int_ge : BinOp (>=%O : int -> int -> bool) :=
  { TBOp := Z.geb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_int_ge.

#[global]
Instance Op_int_ge' : BinOp (<=^d%O : rel int^d) := Op_int_ge.
Add Zify BinOp Op_int_ge'.

#[global]
Instance Op_int_lt : BinOp <%O := Op_ltz.
Add Zify BinOp Op_int_lt.

#[global]
Instance Op_int_lt' : BinOp (>^d%O : rel int^d) := Op_ltz.
Add Zify BinOp Op_int_lt'.

#[global]
Instance Op_int_gt : BinOp (>%O : int -> int -> bool) :=
  { TBOp := Z.gtb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_int_gt.

#[global]
Instance Op_int_gt' : BinOp (<^d%O : rel int^d) := Op_int_gt.
Add Zify BinOp Op_int_gt'.

#[global]
Instance Op_int_min : BinOp (Order.min : int -> int -> int) :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_int_min.

#[global]
Instance Op_int_min' : BinOp ((Order.max : int^d -> _) : int -> int -> int) :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_int_min'.

#[global]
Instance Op_int_max : BinOp (Order.max : int -> int -> int) :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_int_max.

#[global]
Instance Op_int_max' : BinOp ((Order.min : int^d -> _) : int -> int -> int) :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_int_max'.

#[global]
Instance Op_int_meet : BinOp (Order.meet : int -> int -> int) :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_int_meet.

#[global]
Instance Op_int_meet' : BinOp (Order.join : int^d -> _) := Op_int_min.
Add Zify BinOp Op_int_meet'.

#[global]
Instance Op_int_join : BinOp (Order.join : int -> int -> int) :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_int_join.

#[global]
Instance Op_int_join' : BinOp (Order.meet : int^d -> _) := Op_int_max.
Add Zify BinOp Op_int_join'.

(******************************************************************************)
(* ssrZ                                                                       *)
(******************************************************************************)

#[global]
Instance Op_Z_eq_op : BinOp (eq_op : Z -> Z -> bool) := Op_Zeqb.
Add Zify BinOp Op_Z_eq_op.

#[global]
Instance Op_Z_0 : CstOp (0%R : Z) := { TCst := 0%Z; TCstInj := erefl }.
Add Zify CstOp Op_Z_0.

#[global]
Instance Op_Z_add : BinOp (+%R : Z -> Z -> Z) :=
  { TBOp := Z.add; TBOpInj _ _ := erefl }.
Add Zify BinOp Op_Z_add.

#[global]
Instance Op_Z_opp : UnOp (@GRing.opp _ : Z -> Z) :=
  { TUOp := Z.opp; TUOpInj _ := erefl }.
Add Zify UnOp Op_Z_opp.

#[global]
Instance Op_Z_1 : CstOp (1%R : Z) := { TCst := 1%Z; TCstInj := erefl }.
Add Zify CstOp Op_Z_1.

#[global]
Instance Op_Z_mulr : BinOp ( *%R : Z -> Z -> Z) :=
  { TBOp := Z.mul; TBOpInj _ _ := erefl }.
Add Zify BinOp Op_Z_mulr.

Fact Op_Z_natmul_subproof (n : Z) (m : nat) : (n *+ m)%R = (n * Z.of_nat m)%Z.
Proof.
elim: m => [|m]; rewrite (mulr0n, mulrS); first by lia.
by move=> ->; lia.
Qed.

#[global]
Instance Op_Z_natmul : BinOp (@GRing.natmul _ : Z -> nat -> Z) :=
  { TBOp := Z.mul; TBOpInj := Op_Z_natmul_subproof }.
Add Zify BinOp Op_Z_natmul.

#[global]
Instance Op_Z_intmul : BinOp ( *~%R%R : Z -> int -> Z) :=
  { TBOp := Z.mul; TBOpInj := ltac:(move=> n [] m; rewrite /intmul /=; lia) }.
Add Zify BinOp Op_Z_intmul.

#[global]
Instance Op_Z_scale : BinOp (@GRing.scale _ Z^o) :=
  Op_Z_mulr.
Add Zify BinOp Op_Z_scale.

Fact Op_Z_exp_subproof n m : (n ^+ m)%R = (n ^ Z.of_nat m)%Z.
Proof. by rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS. Qed.

#[global]
Instance Op_Z_exp : BinOp (@GRing.exp _ : Z -> nat -> Z) :=
  { TBOp := Z.pow; TBOpInj := Op_Z_exp_subproof }.
Add Zify BinOp Op_Z_exp.

#[global]
Instance Op_unitZ : UnOp (has_quality 1 Instances.unitZ : Z -> bool) :=
  { TUOp x := (x =? 1)%Z || (x =? - 1)%Z; TUOpInj _ := erefl }.
Add Zify UnOp Op_unitZ.

#[global]
Instance Op_Z_unit : UnOp (has_quality 1 GRing.unit : Z -> bool) := Op_unitZ.
Add Zify UnOp Op_Z_unit.

#[global]
Instance Op_invZ : UnOp Instances.invZ := { TUOp := id; TUOpInj _ := erefl }.
Add Zify UnOp Op_invZ.

#[global]
Instance Op_Z_inv : UnOp (GRing.inv : Z -> Z) :=
  { TUOp := id; TUOpInj _ := erefl }.
Add Zify UnOp Op_Z_inv.

#[global]
Instance Op_Z_normr : UnOp (Num.norm : Z -> Z) :=
  { TUOp := Z.abs; TUOpInj _ := erefl }.
Add Zify UnOp Op_Z_normr.

#[global]
Instance Op_Z_sgr : UnOp (Num.sg : Z -> Z) :=
  { TUOp := Z.sgn; TUOpInj := ltac:(case=> //=; lia) }.
Add Zify UnOp Op_Z_sgr.

#[global]
Instance Op_Z_le : BinOp (<=%O : Z -> Z -> bool) :=
  { TBOp := Z.leb; TBOpInj _ _ := erefl }.
Add Zify BinOp Op_Z_le.

#[global]
Instance Op_Z_le' : BinOp (>=^d%O : rel Z^d) := Op_Z_le.
Add Zify BinOp Op_Z_le'.

#[global]
Instance Op_Z_ge : BinOp (>=%O : Z -> Z -> bool) :=
  { TBOp := Z.geb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_Z_ge.

#[global]
Instance Op_Z_ge' : BinOp (<=^d%O : rel Z^d) := Op_Z_ge.
Add Zify BinOp Op_Z_ge'.

#[global]
Instance Op_Z_lt : BinOp (<%O : Z -> Z -> bool) :=
  { TBOp := Z.ltb; TBOpInj _ _ := erefl }.
Add Zify BinOp Op_Z_lt.

#[global]
Instance Op_Z_lt' : BinOp (>^d%O : rel Z^d) := Op_Z_lt.
Add Zify BinOp Op_Z_lt'.

#[global]
Instance Op_Z_gt : BinOp (>%O : Z -> Z -> bool) :=
  { TBOp := Z.gtb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_Z_gt.

#[global]
Instance Op_Z_gt' : BinOp (<^d%O : rel Z^d) := Op_Z_gt.
Add Zify BinOp Op_Z_gt'.

#[global]
Instance Op_Z_min : BinOp (Order.min : Z -> Z -> Z) :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_Z_min.

#[global]
Instance Op_Z_min' : BinOp ((Order.max : Z^d -> _) : Z -> Z -> Z) :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_Z_min'.

#[global]
Instance Op_Z_max : BinOp (Order.max : Z -> Z -> Z) :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_Z_max.

#[global]
Instance Op_Z_max' : BinOp ((Order.min : Z^d -> _) : Z -> Z -> Z) :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_Z_max'.

#[global]
Instance Op_Z_meet : BinOp (Order.meet : Z -> Z -> Z) :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_Z_meet.

#[global]
Instance Op_Z_meet' : BinOp (Order.join : Z^d -> _) := Op_Z_min.
Add Zify BinOp Op_Z_meet'.

#[global]
Instance Op_Z_join : BinOp (Order.join : Z -> Z -> Z) :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leP => /=; lia) }.
Add Zify BinOp Op_Z_join.

#[global]
Instance Op_Z_join' : BinOp (Order.meet : Z^d -> _) := Op_Z_max.
Add Zify BinOp Op_Z_join'.

(******************************************************************************)
(* intdiv                                                                     *)
(******************************************************************************)

Fact Op_divz_subproof n m :
  Z_of_int (divz n m) = divZ (Z_of_int n) (Z_of_int m).
Proof. case: n => [[|n]|n]; rewrite /divz /divZ /= ?addn1 /=; nia. Qed.

#[global]
Instance Op_divz : BinOp (divz : int -> int -> int) :=
  { TBOp := divZ; TBOpInj := Op_divz_subproof }.
Add Zify BinOp Op_divz.

#[global]
Instance Op_modz : BinOp modz :=
  { TBOp := modZ; TBOpInj := ltac:(rewrite /= /modz; lia) }.
Add Zify BinOp Op_modz.

#[global]
Instance Op_dvdz : BinOp dvdz :=
  { TBOp n m := (modZ m n =? 0)%Z;
    TBOpInj _ _ := ltac:(apply/dvdz_mod0P/idP; lia) }.
Add Zify BinOp Op_dvdz.

Fact Op_gcdz_subproof n m :
  Z_of_int (gcdz n m) = Z.gcd (Z_of_int n) (Z_of_int m).
Proof. rewrite /gcdz -Z.gcd_abs_l -Z.gcd_abs_r; lia. Qed.

#[global]
Instance Op_gcdz : BinOp gcdz := { TBOp := Z.gcd; TBOpInj := Op_gcdz_subproof }.
Add Zify BinOp Op_gcdz.

#[global]
Instance Op_coprimez : BinOp coprimez :=
  { TBOp x y := (Z.gcd x y =? 1)%Z;
    TBOpInj := ltac:(rewrite /= /coprimez; lia) }.
Add Zify BinOp Op_coprimez.

Module Exports.
Add Zify CstOp Op_nat_0.
Add Zify BinOp Op_nat_add.
Add Zify CstOp Op_nat_1.
Add Zify BinOp Op_nat_mul.
Add Zify BinOp Op_nat_natmul.
Add Zify BinOp Op_nat_exp.
Add Zify CstOp Op_N_0.
Add Zify BinOp Op_N_add.
Add Zify CstOp Op_N_1.
Add Zify BinOp Op_N_mul.
Add Zify BinOp Op_N_natmul.
Add Zify BinOp Op_N_exp.
Add Zify InjTyp Inj_int_Z.
Add Zify UnOp Op_Z_of_int.
Add Zify UnOp Op_Posz.
Add Zify UnOp Op_Negz.
Add Zify BinRel Op_int_eq.
Add Zify BinOp Op_int_eq_op.
Add Zify CstOp Op_int_0.
Add Zify BinOp Op_addz.
Add Zify BinOp Op_int_add.
Add Zify UnOp Op_oppz.
Add Zify UnOp Op_int_opp.
Add Zify CstOp Op_int_1.
Add Zify BinOp Op_mulz.
Add Zify BinOp Op_int_mulr.
Add Zify BinOp Op_int_natmul.
Add Zify BinOp Op_int_intmul.
Add Zify BinOp Op_int_scale.
Add Zify BinOp Op_int_exp.
Add Zify UnOp Op_unitz.
Add Zify UnOp Op_int_unit.
Add Zify UnOp Op_invz.
Add Zify UnOp Op_int_inv.
Add Zify UnOp Op_absz.
Add Zify UnOp Op_int_normr.
Add Zify BinOp Op_lez.
Add Zify BinOp Op_ltz.
Add Zify UnOp Op_int_sgr.
Add Zify UnOp Op_int_sgz.
Add Zify BinOp Op_int_le.
Add Zify BinOp Op_int_le'.
Add Zify BinOp Op_int_ge.
Add Zify BinOp Op_int_ge'.
Add Zify BinOp Op_int_lt.
Add Zify BinOp Op_int_lt'.
Add Zify BinOp Op_int_gt.
Add Zify BinOp Op_int_gt'.
Add Zify BinOp Op_int_min.
Add Zify BinOp Op_int_min'.
Add Zify BinOp Op_int_max.
Add Zify BinOp Op_int_max'.
Add Zify BinOp Op_int_meet.
Add Zify BinOp Op_int_meet'.
Add Zify BinOp Op_int_join.
Add Zify BinOp Op_int_join'.
Add Zify BinOp Op_Z_eq_op.
Add Zify CstOp Op_Z_0.
Add Zify BinOp Op_Z_add.
Add Zify UnOp Op_Z_opp.
Add Zify CstOp Op_Z_1.
Add Zify BinOp Op_Z_mulr.
Add Zify BinOp Op_Z_natmul.
Add Zify BinOp Op_Z_intmul.
Add Zify BinOp Op_Z_scale.
Add Zify BinOp Op_Z_exp.
Add Zify UnOp Op_unitZ.
Add Zify UnOp Op_Z_unit.
Add Zify UnOp Op_invZ.
Add Zify UnOp Op_Z_inv.
Add Zify UnOp Op_Z_normr.
Add Zify UnOp Op_Z_sgr.
Add Zify BinOp Op_Z_le.
Add Zify BinOp Op_Z_le'.
Add Zify BinOp Op_Z_ge.
Add Zify BinOp Op_Z_ge'.
Add Zify BinOp Op_Z_lt.
Add Zify BinOp Op_Z_lt'.
Add Zify BinOp Op_Z_gt.
Add Zify BinOp Op_Z_gt'.
Add Zify BinOp Op_Z_min.
Add Zify BinOp Op_Z_min'.
Add Zify BinOp Op_Z_max.
Add Zify BinOp Op_Z_max'.
Add Zify BinOp Op_Z_meet.
Add Zify BinOp Op_Z_meet'.
Add Zify BinOp Op_Z_join.
Add Zify BinOp Op_Z_join'.
Add Zify BinOp Op_divz.
Add Zify BinOp Op_modz.
Add Zify BinOp Op_dvdz.
Add Zify BinOp Op_gcdz.
Add Zify BinOp Op_coprimez.
End Exports.

End AlgebraZifyInstances.
Export SsreflectZifyInstances.Exports.
Export AlgebraZifyInstances.Exports.

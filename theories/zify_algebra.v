From Coq Require Import ZArith ZifyClasses Zify ZifyInst ZifyBool.
From Coq Require Export Lia.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import order binomial ssralg countalg ssrnum ssrint rat.
From mathcomp Require Import intdiv.
From mathcomp Require Import zify_ssreflect.

Module AlgebraZifyInstances.

Local Delimit Scope Z_scope with Z.

Import Order.Theory GRing.Theory Num.Theory SsreflectZifyInstances.

(******************************************************************************)
(* ssrint                                                                     *)
(******************************************************************************)

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

Instance Inj_int_Z : InjTyp int Z :=
  { inj := Z_of_int; pred := fun => True; cstr := fun => I }.
Add Zify InjTyp Inj_int_Z.

Instance Op_Z_of_int : UnOp Z_of_int := { TUOp := id; TUOpInj := fun => erefl }.
Add Zify UnOp Op_Z_of_int.

Instance Op_Posz : UnOp Posz := { TUOp := id; TUOpInj := fun => erefl }.
Add Zify UnOp Op_Posz.

Instance Op_Negz : UnOp Negz :=
  { TUOp := fun x => (- (x + 1))%Z; TUOpInj := ltac:(simpl; lia) }.
Add Zify UnOp Op_Negz.

Lemma Op_int_eq_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. split=> [->|] //; case: n m => ? [] ? ?; f_equal; lia. Qed.

Instance Op_int_eq : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_int_eq_subproof }.
Add Zify BinRel Op_int_eq.

Instance Op_int_eq_op : BinOp (@eq_op int_eqType : int -> int -> bool) :=
  { TBOp := Z.eqb;
    TBOpInj := ltac:(move=> [] ? [] ?; do 2 rewrite /eq_op /=; lia) }.
Add Zify BinOp Op_int_eq_op.

Instance Op_int_0 : CstOp (0%R : int) := { TCst := 0%Z; TCstInj := erefl }.
Add Zify CstOp Op_int_0.

Instance Op_addz : BinOp intZmod.addz :=
  { TBOp := Z.add; TBOpInj := ltac:(case=> ? [] ? /=; try case: leqP; lia) }.
Add Zify BinOp Op_addz.

Instance Op_int_add : BinOp +%R := Op_addz.
Add Zify BinOp Op_int_add.

Instance Op_oppz : UnOp intZmod.oppz :=
  { TUOp := Z.opp; TUOpInj := ltac:(case=> [[|?]|?] /=; lia) }.
Add Zify UnOp Op_oppz.

Instance Op_int_opp : UnOp (@GRing.opp _) := Op_oppz.
Add Zify UnOp Op_int_opp.

Instance Op_int_1 : CstOp (1%R : int) := { TCst := 1%Z; TCstInj := erefl }.
Add Zify CstOp Op_int_1.

Instance Op_mulz : BinOp intRing.mulz :=
  { TBOp := Z.mul; TBOpInj := ltac:(case=> ? [] ? /=; lia) }.
Add Zify BinOp Op_mulz.

Instance Op_int_mulr : BinOp *%R := Op_mulz.
Add Zify BinOp Op_int_mulr.

Instance Op_int_intmul : BinOp ( *~%R%R : int -> int -> int) :=
  { TBOp := Z.mul; TBOpInj := ltac:(move=> ? ?; rewrite /= mulrzz; lia) }.
Add Zify BinOp Op_int_intmul.

Instance Op_int_natmul : BinOp (@GRing.natmul _ : int -> nat -> int) :=
  { TBOp := Z.mul;
    TBOpInj := ltac:(move=> ? ?; rewrite /= pmulrn mulrzz; lia) }.
Add Zify BinOp Op_int_natmul.

Instance Op_int_scale : BinOp (@GRing.scale _ [lmodType int of int^o]) :=
  Op_mulz.
Add Zify BinOp Op_int_scale.

Lemma Op_int_exp_subproof n m :
  Z_of_int (n ^+ m) = (Z_of_int n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia. Qed.

Instance Op_int_exp : BinOp (@GRing.exp _ : int -> nat -> int) :=
  { TBOp := Z.pow; TBOpInj := Op_int_exp_subproof }.
Add Zify BinOp Op_int_exp.

Instance Op_invz : UnOp intUnitRing.invz :=
  { TUOp := id; TUOpInj := fun => erefl }.
Add Zify UnOp Op_invz.

Instance Op_int_inv : UnOp GRing.inv := Op_invz.
Add Zify UnOp Op_int_inv.

Instance Op_absz : UnOp absz :=
  { TUOp := Z.abs; TUOpInj := ltac:(case=> ? /=; lia) }.
Add Zify UnOp Op_absz.

Instance Op_int_normr : UnOp (Num.norm : int -> int) :=
  { TUOp := Z.abs; TUOpInj := ltac:(rewrite /Num.norm /=; lia) }.
Add Zify UnOp Op_int_normr.

Instance Op_lez : BinOp intOrdered.lez :=
  { TBOp := Z.leb; TBOpInj := ltac:(case=> ? [] ? /=; lia) }.
Add Zify BinOp Op_lez.

Instance Op_ltz : BinOp intOrdered.ltz :=
  { TBOp := Z.ltb; TBOpInj := ltac:(case=> ? [] ? /=; lia) }.
Add Zify BinOp Op_ltz.

Instance Op_int_sgr : UnOp (Num.sg : int -> int) :=
  { TUOp := Z.sgn; TUOpInj := ltac:(case=> [[]|] //=; lia) }.
Add Zify UnOp Op_int_sgr.

Instance Op_int_sgz : UnOp (@sgz _) := Op_int_sgr.
Add Zify UnOp Op_int_sgz.

Instance Op_int_le : BinOp <=%O := Op_lez.
Add Zify BinOp Op_int_le.

Instance Op_int_le' : BinOp (>=^d%O : rel int^d) := Op_lez.
Add Zify BinOp Op_int_le'.

Instance Op_int_ge : BinOp (>=%O : int -> int -> bool) :=
  { TBOp := Z.geb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_int_ge.

Instance Op_int_ge' : BinOp (<=^d%O : rel int^d) := Op_int_ge.
Add Zify BinOp Op_int_ge'.

Instance Op_int_lt : BinOp <%O := Op_ltz.
Add Zify BinOp Op_int_lt.

Instance Op_int_lt' : BinOp (>^d%O : rel int^d) := Op_ltz.
Add Zify BinOp Op_int_lt'.

Instance Op_int_gt : BinOp (>%O : int -> int -> bool) :=
  { TBOp := Z.gtb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_int_gt.

Instance Op_int_gt' : BinOp (<^d%O : rel int^d) := Op_int_gt.
Add Zify BinOp Op_int_gt'.

Instance Op_int_min : BinOp (Order.min : int -> int -> int) :=
  { TBOp := Z.min; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_int_min.

Instance Op_int_min' : BinOp ((Order.max : int^d -> _) : int -> int -> int) :=
  { TBOp := Z.min; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_int_min'.

Instance Op_int_max : BinOp (Order.max : int -> int -> int) :=
  { TBOp := Z.max; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_int_max.

Instance Op_int_max' : BinOp ((Order.min : int^d -> _) : int -> int -> int) :=
  { TBOp := Z.max; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_int_max'.

Instance Op_int_meet : BinOp (Order.meet : int -> int -> int) :=
  { TBOp := Z.min; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_int_meet.

Instance Op_int_meet' : BinOp (Order.join : int^d -> _) := Op_int_min.
Add Zify BinOp Op_int_meet'.

Instance Op_int_join : BinOp (Order.join : int -> int -> int) :=
  { TBOp := Z.max; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_int_join.

Instance Op_int_join' : BinOp (Order.meet : int^d -> _) := Op_int_max.
Add Zify BinOp Op_int_join'.

(******************************************************************************)
(* intdiv                                                                     *)
(******************************************************************************)

Lemma Op_divz_subproof n m :
  Z_of_int (divz n m) = divZ (Z_of_int n) (Z_of_int m).
Proof. case: n => [[|n]|n]; rewrite /divz /divZ /= ?addn1 /=; nia. Qed.

Instance Op_divz : BinOp (divz : int -> int -> int) :=
  { TBOp := divZ; TBOpInj := Op_divz_subproof }.
Add Zify BinOp Op_divz.

Instance Op_modz : BinOp modz :=
  { TBOp := modZ; TBOpInj := ltac:(rewrite /= /modz; lia) }.
Add Zify BinOp Op_modz.

Instance Op_dvdz : BinOp dvdz :=
  { TBOp := fun n m => Z.eqb (modZ m n) 0%Z;
    TBOpInj := ltac:(move=> ? ? /=; apply/dvdz_mod0P/idP; lia) }.
Add Zify BinOp Op_dvdz.

Lemma Op_gcdz_subproof n m :
  Z_of_int (gcdz n m) = Z.gcd (Z_of_int n) (Z_of_int m).
Proof. rewrite /gcdz -Z.gcd_abs_l -Z.gcd_abs_r; lia. Qed.

Instance Op_gcdz : BinOp gcdz := { TBOp := Z.gcd; TBOpInj := Op_gcdz_subproof }.
Add Zify BinOp Op_gcdz.

Instance Op_coprimez : BinOp coprimez :=
  { TBOp := fun x y => Z.eqb (Z.gcd x y) 1%Z;
    TBOpInj := ltac:(rewrite /= /coprimez; lia) }.
Add Zify BinOp Op_coprimez.

Module Exports.
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
Add Zify BinOp Op_int_intmul.
Add Zify BinOp Op_int_natmul.
Add Zify BinOp Op_int_scale.
Add Zify BinOp Op_int_exp.
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
Add Zify BinOp Op_divz.
Add Zify BinOp Op_modz.
Add Zify BinOp Op_dvdz.
Add Zify BinOp Op_gcdz.
Add Zify BinOp Op_coprimez.
End Exports.

End AlgebraZifyInstances.
Export SsreflectZifyInstances.Exports.
Export AlgebraZifyInstances.Exports.

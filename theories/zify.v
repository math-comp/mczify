From Coq Require Import ZArith ZifyClasses Zify ZifyInst ZifyBool.
From Coq Require Export Lia.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import order binomial ssralg countalg ssrnum ssrint rat.
From mathcomp Require Import intdiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac zify ::=
  intros;
  unfold is_true in *; do ?rewrite -> unfold_in in *;
  zify_elim_let;
  zify_op;
  zify_iter_specs;
  zify_saturate; zify_post_hook.

Module MathcompZifyInstances.

Import Order.Theory GRing.Theory Num.Theory.

Local Delimit Scope Z_scope with Z.

Instance Op_bool_inj : UnOp (inj : bool -> bool) :=
  { TUOp := id; TUOpInj := fun => erefl }.
Add Zify UnOp Op_bool_inj.

Instance Op_nat_inj : UnOp (inj : nat -> Z) := Op_Z_of_nat.
Add Zify UnOp Op_nat_inj.

(******************************************************************************)
(* bool                                                                       *)
(******************************************************************************)

Instance Op_addb : BinOp addb :=
  { TBOp := fun x y => Bool.eqb x (negb y); TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_addb.

Instance Op_eqb : BinOp eqb :=
  { TBOp := Bool.eqb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_eqb.

Instance Op_eq_op_bool : BinOp (@eq_op bool_eqType) := Op_eqb.
Add Zify BinOp Op_eq_op_bool.

Instance Op_bool_le : BinOp (<=%O : bool -> bool -> bool) :=
  { TBOp := implb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_le.

Instance Op_bool_le' : BinOp (>=^d%O : rel bool^d) := Op_bool_le.
Add Zify BinOp Op_bool_le'.

Instance Op_bool_ge : BinOp (>=%O : bool -> bool -> bool) :=
  { TBOp := fun x y => implb y x; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_ge.

Instance Op_bool_ge' : BinOp (<=^d%O : rel bool^d) := Op_bool_ge.
Add Zify BinOp Op_bool_ge'.

Instance Op_bool_lt : BinOp (<%O : bool -> bool -> bool) :=
  { TBOp := fun x y => ~~ x && y; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_lt.

Instance Op_bool_lt' : BinOp (>^d%O : rel bool^d) := Op_bool_lt.
Add Zify BinOp Op_bool_lt'.

Instance Op_bool_gt : BinOp (>%O : bool -> bool -> bool) :=
  { TBOp := fun x y => x && ~~ y; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_gt.

Instance Op_bool_gt' : BinOp (<^d%O : rel bool^d) := Op_bool_gt.
Add Zify BinOp Op_bool_gt'.

Instance Op_bool_min : BinOp (Order.min : bool -> bool -> bool) :=
  { TBOp := andb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_min.

Instance Op_bool_min' :
  BinOp ((Order.max : bool^d -> _) : bool -> bool -> bool) :=
  { TBOp := andb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_min'.

Instance Op_bool_max : BinOp (Order.max : bool -> bool -> bool) :=
  { TBOp := orb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_max.

Instance Op_bool_max' :
  BinOp ((Order.min : bool^d -> _) : bool -> bool -> bool) :=
  { TBOp := orb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_max'.

Instance Op_bool_meet : BinOp (Order.meet : bool -> bool -> bool) := Op_andb.
Add Zify BinOp Op_bool_meet.

Instance Op_bool_meet' : BinOp (Order.join : bool^d -> _) := Op_andb.
Add Zify BinOp Op_bool_meet'.

Instance Op_bool_join : BinOp (Order.join : bool -> bool -> bool) := Op_orb.
Add Zify BinOp Op_bool_join.

Instance Op_bool_join' : BinOp (Order.meet : bool^d -> _) := Op_orb.
Add Zify BinOp Op_bool_join'.

Instance Op_bool_bottom : CstOp (0%O : bool) := Op_false.
Add Zify CstOp Op_bool_bottom.

Instance Op_bool_bottom' : CstOp (1%O : bool^d) := Op_false.
Add Zify CstOp Op_bool_bottom'.

Instance Op_bool_top : CstOp (1%O : bool) := Op_true.
Add Zify CstOp Op_bool_top.

Instance Op_bool_top' : CstOp (0%O : bool^d) := Op_true.
Add Zify CstOp Op_bool_top'.

Instance Op_bool_sub : BinOp (Order.sub : bool -> bool -> bool) :=
  { TBOp := fun x y => x && ~~ y; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_sub.

Instance Op_bool_compl : UnOp (Order.compl : bool -> bool) := Op_negb.
Add Zify UnOp Op_bool_compl.

(******************************************************************************)
(* nat                                                                        *)
(******************************************************************************)

Instance Op_eqn : BinOp eqn := Op_nat_eqb.
Add Zify BinOp Op_eqn.

Instance Op_eq_op_nat : BinOp (@eq_op nat_eqType) := Op_eqn.
Add Zify BinOp Op_eq_op_nat.

Instance Op_addn_rec : BinOp addn_rec := Op_plus.
Add Zify BinOp Op_addn_rec.

Instance Op_addn : BinOp addn := Op_plus.
Add Zify BinOp Op_addn.

Instance Op_subn_rec : BinOp subn_rec := Op_sub.
Add Zify BinOp Op_subn_rec.

Instance Op_subn : BinOp subn := Op_sub.
Add Zify BinOp Op_subn.

Instance Op_muln_rec : BinOp muln_rec := Op_mul.
Add Zify BinOp Op_muln_rec.

Instance Op_muln : BinOp muln := Op_mul.
Add Zify BinOp Op_muln.

Lemma nat_lebE n m : (n <= m) = Nat.leb n m.
Proof. by elim: n m => [|n ih []]. Qed.

Instance Op_leq : BinOp leq :=
  { TBOp := Z.leb; TBOpInj := ltac:(move=> ? ?; rewrite nat_lebE; lia) }.
Add Zify BinOp Op_leq.

Instance Op_geq : BinOp (geq : nat -> nat -> bool) :=
  { TBOp := Z.geb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_geq.

Instance Op_ltn : BinOp (ltn : nat -> nat -> bool) :=
  { TBOp := Z.ltb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_ltn.

Instance Op_gtn : BinOp (gtn : nat -> nat -> bool) :=
  { TBOp := Z.gtb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_gtn.

Instance Op_minn : BinOp minn :=
  { TBOp := Z.min; TBOpInj := ltac:(move=> ? ?; case: leqP; lia) }.
Add Zify BinOp Op_minn.

Instance Op_maxn : BinOp maxn :=
  { TBOp := Z.max; TBOpInj := ltac:(move=> ? ?; case: leqP; lia) }.
Add Zify BinOp Op_maxn.

Instance Op_nat_of_bool : UnOp nat_of_bool :=
  { TUOp := Z.b2z; TUOpInj := ltac:(by case) }.
Add Zify UnOp Op_nat_of_bool.

Instance Op_double : UnOp double :=
  { TUOp := Z.mul 2; TUOpInj := ltac:(move=> ?; rewrite -muln2; lia) }.
Add Zify UnOp Op_double.

Lemma Op_expn_subproof n m : Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite expnS; lia. Qed.

Instance Op_expn_rec : BinOp expn_rec :=
  { TBOp := Z.pow; TBOpInj := Op_expn_subproof }.
Add Zify BinOp Op_expn_rec.

Instance Op_expn : BinOp expn := Op_expn_rec.
Add Zify BinOp Op_expn.

(* missing: *)
(* Print fact_rec. *)
(* Print factorial. *)

Instance Op_nat_le : BinOp (<=%O : rel nat) := Op_leq.
Add Zify BinOp Op_nat_le.

Instance Op_nat_le' : BinOp (>=^d%O : rel nat^d) := Op_leq.
Add Zify BinOp Op_nat_le'.

Instance Op_nat_ge : BinOp (>=%O : rel nat) := Op_geq.
Add Zify BinOp Op_nat_ge.

Instance Op_nat_ge' : BinOp (<=^d%O : rel nat^d) := Op_geq.
Add Zify BinOp Op_nat_ge'.

Instance Op_nat_lt : BinOp (<%O : rel nat) := Op_ltn.
Add Zify BinOp Op_nat_lt.

Instance Op_nat_lt' : BinOp (>^d%O : rel nat^d) := Op_ltn.
Add Zify BinOp Op_nat_lt'.

Instance Op_nat_gt : BinOp (>%O : rel nat) := Op_gtn.
Add Zify BinOp Op_nat_gt.

Instance Op_nat_gt' : BinOp (<^d%O : rel nat^d) := Op_gtn.
Add Zify BinOp Op_nat_gt'.

Instance Op_nat_min : BinOp (Order.min : nat -> _) := Op_minn.
Add Zify BinOp Op_nat_min.

Instance Op_nat_min' : BinOp ((Order.max : nat^d -> _) : nat -> nat -> nat) :=
  { TBOp := Z.min; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_nat_min'.

Instance Op_nat_max : BinOp (Order.max : nat -> _) := Op_maxn.
Add Zify BinOp Op_nat_max.

Instance Op_nat_max' : BinOp ((Order.min : nat^d -> _) : nat -> nat -> nat) :=
  { TBOp := Z.max; TBOpInj := ltac:(move=> ? ? /=; case: leP; lia) }.
Add Zify BinOp Op_nat_max'.

Instance Op_nat_meet : BinOp (Order.meet : nat -> _) := Op_minn.
Add Zify BinOp Op_nat_meet.

Instance Op_nat_meet' : BinOp (Order.join : nat^d -> _) := Op_minn.
Add Zify BinOp Op_nat_meet'.

Instance Op_nat_join : BinOp (Order.join : nat -> _) := Op_maxn.
Add Zify BinOp Op_nat_join.

Instance Op_nat_join' : BinOp (Order.meet : nat^d -> _) := Op_maxn.
Add Zify BinOp Op_nat_join'.

Instance Op_nat_bottom : CstOp (0%O : nat) := Op_O.
Add Zify CstOp Op_nat_bottom.

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

Lemma Op_int_eq_op_subproof (n m : int) :
  (n == m) = Z.eqb (Z_of_int n) (Z_of_int m).
Proof. case: n m => ? [] ?; do 2 rewrite /eq_op /=; lia. Qed.

Instance Op_int_eq_op : BinOp (@eq_op int_eqType : int -> int -> bool) :=
  { TBOp := Z.eqb; TBOpInj := Op_int_eq_op_subproof }.
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

(* missing: *)
(* Print Num.Def.lerif. *)

Lemma Op_int_sgr_subproof n : Z_of_int (Num.sg n) = Z.sgn (Z_of_int n).
Proof. by case: n => [[]|n] //=; rewrite addn1. Qed.

Instance Op_int_sgr : UnOp (Num.sg : int -> int) :=
  { TUOp := Z.sgn; TUOpInj := Op_int_sgr_subproof }.
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
(* int <-> Z                                                                  *)
(******************************************************************************)

Definition int_of_Z (n : Z) :=
  match n with
  | Z0 => Posz 0
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => Negz (Pos.to_nat p).-1
  end.

Lemma int_of_ZK : cancel int_of_Z Z_of_int. Proof. case=> //= p; lia. Qed.

Instance Op_int_of_Z : UnOp int_of_Z :=
  { TUOp := id : Z -> Z; TUOpInj := int_of_ZK }.
Add Zify UnOp Op_int_of_Z.

Lemma Z_of_intK : cancel Z_of_int int_of_Z. Proof. move=> ?; lia. Qed.

(******************************************************************************)
(* intdiv                                                                     *)
(******************************************************************************)

Definition divZ (n m : Z) : Z := Z_of_int (divz (int_of_Z n) (int_of_Z m)).
Definition modZ (n m : Z) : Z := Z_of_int (modz (int_of_Z n) (int_of_Z m)).

Instance Op_divZ : BinOp divZ := { TBOp := divZ; TBOpInj := fun _ _ => erefl }.
Add Zify BinOp Op_divZ.

Instance Op_modZ : BinOp modZ := { TBOp := modZ; TBOpInj := fun _ _ => erefl }.
Add Zify BinOp Op_modZ.

Instance Op_divz : BinOp (divz : int -> int -> int) :=
  { TBOp := divZ; TBOpInj := ltac:(by move=> ? ?; rewrite /divZ !Z_of_intK) }.
Add Zify BinOp Op_divz.

Instance Op_modz : BinOp modz :=
  { TBOp := modZ; TBOpInj := ltac:(by move=> ? ?; rewrite /modZ !Z_of_intK) }.
Add Zify BinOp Op_modz.

Lemma Op_dvdz_subproof (n m : int) :
  dvdz n m = Z.eqb (modZ (Z_of_int m) (Z_of_int n)) 0%Z.
Proof. apply/dvdz_mod0P/idP; lia. Qed.

Instance Op_dvdz : BinOp dvdz :=
  { TBOp := fun n m => Z.eqb (modZ m n) 0%Z; TBOpInj := Op_dvdz_subproof }.
Add Zify BinOp Op_dvdz.

(* Reimplementation of Z.div_mod_to_equations (PreOmega.v) for divZ and modZ: *)

Lemma divZ_eq m d : m = (divZ m d * d + modZ m d)%Z.
Proof. by move: (divz_eq (int_of_Z m) (int_of_Z d)); lia. Qed.

Lemma modZ_ge0 m d : d <> 0%Z -> (0 <= modZ m d)%Z.
Proof. by move: (@modz_ge0 (int_of_Z m) (int_of_Z d)); lia. Qed.

Lemma ltz_pmodZ m d : (0 < d)%Z -> (modZ m d < d)%Z.
Proof. by move: (@ltz_mod (int_of_Z m) (int_of_Z d)); lia. Qed.

Lemma ltz_nmodZ m d : (d < 0)%Z -> (modZ m d < - d)%Z.
Proof. by move: (@ltz_mod (int_of_Z m) (int_of_Z d)); lia. Qed.

Lemma divZ0 m d : d = 0%Z -> divZ m d = 0%Z.
Proof. by move: (divz0 (int_of_Z m)) => ? ->; lia. Qed.

Ltac divZ_modZ_to_equations :=
  let divZ_modZ_to_equations' m d :=
    pose proof (@divZ_eq m d);
    pose proof (@modZ_ge0 m d);
    pose proof (@ltz_pmodZ m d);
    pose proof (@ltz_nmodZ m d);
    pose proof (@divZ0 m d);
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := divZ m d) in *;
    set (r := modZ m d) in *;
    (* Find [divZ ?m' ?d'] and [modZ ?m' ?d'] that are convertible with       *)
    (* [divZ m d] and [modZ m d] respectively.                                *)
    repeat
      match goal with
        | |- context [divZ ?m' ?d'] => change (divZ m' d') with q
        | |- context [modZ ?m' ?d'] => change (modZ m' d') with r
        | H : context [divZ ?m' ?d'] |- _ => change (divZ m' d') with q in H
        | H : context [modZ ?m' ?d'] |- _ => change (modZ m' d') with r in H
      end;
    clearbody q r
  in
  repeat
    match goal with
      | [ |- context [divZ ?m ?d] ] => divZ_modZ_to_equations' m d
      | [ |- context [modZ ?m ?d] ] => divZ_modZ_to_equations' m d
      | [ H : context [divZ ?m ?d] |- _] => divZ_modZ_to_equations' m d
      | [ H : context [modZ ?m ?d] |- _] => divZ_modZ_to_equations' m d
    end.

Ltac Zify.zify_post_hook ::= elim_bool_cstr; divZ_modZ_to_equations.

(******************************************************************************)
(* natdiv                                                                     *)
(******************************************************************************)

Lemma Op_divn_subproof n m : Z.of_nat (n %/ m) = divZ (Z.of_nat n) (Z.of_nat m).
Proof.
by rewrite /divZ !(Z_of_intK (Posz _)) /divz; case: m => //= m; rewrite mul1n.
Qed.

Instance Op_divn : BinOp divn := { TBOp := divZ; TBOpInj := Op_divn_subproof }.
Add Zify BinOp Op_divn.

Lemma Op_modn_subproof n m : Z.of_nat (n %% m) = modZ (Z_of_int n) (Z_of_int m).
Proof. by rewrite /modZ !Z_of_intK modz_nat. Qed.

Instance Op_modn : BinOp modn := { TBOp := modZ; TBOpInj := Op_modn_subproof }.
Add Zify BinOp Op_modn.

Instance Op_dvdn : BinOp dvdn :=
  { TBOp := fun x y => Z.eqb (modZ y x) 0%Z;
    TBOpInj := ltac:(rewrite /dvdn; lia) }.
Add Zify BinOp Op_dvdn.

Instance Op_odd : UnOp odd :=
  { TUOp := fun x => Z.eqb (modZ x 2) 1%Z;
    TUOpInj := ltac:(move=> n; case: odd (modn2 n); lia) }.
Add Zify UnOp Op_odd.

Instance Op_half : UnOp half :=
  { TUOp := fun x => divZ x 2;
    TUOpInj := ltac:(move=> ?; rewrite -divn2; lia) }.
Add Zify UnOp Op_half.

Instance Op_uphalf : UnOp uphalf :=
  { TUOp := fun x => divZ (x + 1)%Z 2;
    TUOpInj := ltac:(move=> ?; rewrite uphalf_half; lia) }.
Add Zify UnOp Op_uphalf.

(******************************************************************************)
(* gcd, lcm, and coprime                                                      *)
(******************************************************************************)

Lemma Op_gcdn_subproof n m :
  Z.of_nat (gcdn n m) = Z.gcd (Z.of_nat n) (Z.of_nat m).
Proof.
apply/esym/Z.gcd_unique; first by case: gcdn.
- case/dvdnP: (dvdn_gcdl n m) => k {2}->; exists (Z.of_nat k); lia.
- case/dvdnP: (dvdn_gcdr n m) => k {2}->; exists (Z.of_nat k); lia.
- move=> k [n' Hkn] [m' Hkm].
  suff/dvdnP [k' ->]: Z.abs_nat k %| gcdn n m
    by apply/Znumtheory.Zdivide_Zabs_l; exists (Z.of_nat k'); lia.
  rewrite dvdn_gcd; apply/andP; split; apply/dvdnP;
    [exists (Z.abs_nat n') | exists (Z.abs_nat m')]; nia.
Qed.

Instance Op_gcdn : BinOp gcdn := { TBOp := Z.gcd; TBOpInj := Op_gcdn_subproof }.
Add Zify BinOp Op_gcdn.

Lemma Op_lcmn_subproof n m :
  Z.of_nat (lcmn n m) = Z.lcm (Z.of_nat n) (Z.of_nat m).
Proof.
case: n m => [|n][|m]; rewrite ?lcmn0 // /lcmn /Z.lcm -Op_gcdn_subproof.
case/dvdnP: (dvdn_gcdr n.+1 m.+1) => k {1 3}->.
rewrite mulnA mulnK ?gcdn_gt0 // !Nat2Z.inj_mul Z_div_mult_full //; first nia.
by case: (gcdn _ _) (gcdn_gt0 n.+1 m.+1).
Qed.

Instance Op_lcmn : BinOp lcmn := { TBOp := Z.lcm; TBOpInj := Op_lcmn_subproof }.
Add Zify BinOp Op_lcmn.

Instance Op_coprime : BinOp coprime :=
  { TBOp := fun x y => Z.eqb (Z.gcd x y) 1%Z;
    TBOpInj := ltac:(rewrite /= /coprime; lia) }.
Add Zify BinOp Op_coprime.

Lemma Op_gcdz_subproof n m :
  Z_of_int (gcdz n m) = Z.gcd (Z_of_int n) (Z_of_int m).
Proof.
by rewrite /gcdz /= Op_gcdn_subproof; case: n m => n[]m;
  rewrite ![absz _]/= -?(addn1 n) -?(addn1 m) /= ?Z.gcd_opp_l ?Z.gcd_opp_r.
Qed.

Instance Op_gcdz : BinOp gcdz := { TBOp := Z.gcd; TBOpInj := Op_gcdz_subproof }.
Add Zify BinOp Op_gcdz.

Instance Op_coprimez : BinOp coprimez :=
  { TBOp := fun x y => Z.eqb (Z.gcd x y) 1%Z;
    TBOpInj := ltac:(rewrite /= /coprimez; lia) }.
Add Zify BinOp Op_coprimez.

(******************************************************************************)
(* natdvd                                                                     *)
(******************************************************************************)

Instance Op_natdvd_le : BinOp (<=%O : rel natdvd) := Op_dvdn.
Add Zify BinOp Op_natdvd_le.

Instance Op_natdvd_le' : BinOp (>=^d%O : rel natdvd^d) := Op_dvdn.
Add Zify BinOp Op_natdvd_le'.

Instance Op_natdvd_ge : BinOp ((>=%O : rel natdvd) : nat -> nat -> bool) :=
  { TBOp := fun x y => Z.eqb (modZ x y) 0%Z;
    TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_natdvd_ge.

Instance Op_natdvd_ge' : BinOp (<=^d%O : rel natdvd^d) := Op_natdvd_ge.
Add Zify BinOp Op_natdvd_ge'.

Instance Op_natdvd_lt : BinOp ((<%O : rel natdvd) : nat -> nat -> bool) :=
  { TBOp := fun x y => negb (Z.eqb y x) && Z.eqb (modZ y x) 0%Z;
    TBOpInj := ltac:(move=> ? ? /=; rewrite sdvdEnat; lia) }.
Add Zify BinOp Op_natdvd_lt.

Instance Op_natdvd_lt' : BinOp (>^d%O : rel natdvd^d) := Op_natdvd_lt.
Add Zify BinOp Op_natdvd_lt'.

Instance Op_natdvd_gt : BinOp ((>%O : rel natdvd) : nat -> nat -> bool) :=
  { TBOp := fun x y => negb (Z.eqb x y) && Z.eqb (modZ x y) 0%Z;
    TBOpInj := ltac:(move=> ? ? /=; rewrite sdvdEnat; lia) }.
Add Zify BinOp Op_natdvd_gt.

Instance Op_natdvd_gt' : BinOp (<^d%O : rel natdvd^d) := Op_natdvd_gt.
Add Zify BinOp Op_natdvd_gt'.

(* missing: min and max for natdvd *)

Instance Op_natdvd_meet : BinOp (Order.meet : natdvd -> _) := Op_gcdn.
Add Zify BinOp Op_natdvd_meet.

Instance Op_natdvd_meet' : BinOp (Order.join : natdvd^d -> _) := Op_gcdn.
Add Zify BinOp Op_natdvd_meet'.

Instance Op_natdvd_join : BinOp (Order.join : natdvd -> _) := Op_lcmn.
Add Zify BinOp Op_natdvd_join.

Instance Op_natdvd_join' : BinOp (Order.meet : natdvd^d -> _) := Op_lcmn.
Add Zify BinOp Op_natdvd_join'.

Instance Op_natdvd_bottom : CstOp (0%O : natdvd) :=
  { TCst := 1%Z; TCstInj := erefl }.
Add Zify CstOp Op_natdvd_bottom.

(* missing: definitions in prime and binomial *)

End MathcompZifyInstances.

Module Export Exports.
Import MathcompZifyInstances.
(* Add Zify UnOp Op_bool_inj. *)
(* Add Zify UnOp Op_nat_inj. *)
Add Zify BinOp Op_addb.
Add Zify BinOp Op_eqb.
Add Zify BinOp Op_eq_op_bool.
Add Zify BinOp Op_bool_le.
Add Zify BinOp Op_bool_le'.
Add Zify BinOp Op_bool_ge.
Add Zify BinOp Op_bool_ge'.
Add Zify BinOp Op_bool_lt.
Add Zify BinOp Op_bool_lt'.
Add Zify BinOp Op_bool_gt.
Add Zify BinOp Op_bool_gt'.
Add Zify BinOp Op_bool_min.
Add Zify BinOp Op_bool_min'.
Add Zify BinOp Op_bool_max.
Add Zify BinOp Op_bool_max'.
Add Zify BinOp Op_bool_meet.
Add Zify BinOp Op_bool_meet'.
Add Zify BinOp Op_bool_join.
Add Zify BinOp Op_bool_join'.
Add Zify CstOp Op_bool_bottom.
Add Zify CstOp Op_bool_bottom'.
Add Zify CstOp Op_bool_top.
Add Zify CstOp Op_bool_top'.
Add Zify BinOp Op_bool_sub.
Add Zify UnOp Op_bool_compl.
Add Zify BinOp Op_eqn.
Add Zify BinOp Op_eq_op_nat.
Add Zify BinOp Op_addn_rec.
Add Zify BinOp Op_addn.
Add Zify BinOp Op_subn_rec.
Add Zify BinOp Op_subn.
Add Zify BinOp Op_muln_rec.
Add Zify BinOp Op_muln.
Add Zify BinOp Op_leq.
Add Zify BinOp Op_geq.
Add Zify BinOp Op_ltn.
Add Zify BinOp Op_gtn.
Add Zify BinOp Op_minn.
Add Zify BinOp Op_maxn.
Add Zify UnOp Op_nat_of_bool.
Add Zify UnOp Op_double.
Add Zify BinOp Op_expn_rec.
Add Zify BinOp Op_expn.
Add Zify BinOp Op_nat_le.
Add Zify BinOp Op_nat_le'.
Add Zify BinOp Op_nat_ge.
Add Zify BinOp Op_nat_ge'.
Add Zify BinOp Op_nat_lt.
Add Zify BinOp Op_nat_lt'.
Add Zify BinOp Op_nat_gt.
Add Zify BinOp Op_nat_gt'.
Add Zify BinOp Op_nat_min.
Add Zify BinOp Op_nat_min'.
Add Zify BinOp Op_nat_max.
Add Zify BinOp Op_nat_max'.
Add Zify BinOp Op_nat_meet.
Add Zify BinOp Op_nat_meet'.
Add Zify BinOp Op_nat_join.
Add Zify BinOp Op_nat_join'.
Add Zify CstOp Op_nat_bottom.
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
Add Zify UnOp Op_int_of_Z.
Add Zify BinOp Op_divZ.
Add Zify BinOp Op_modZ.
Add Zify BinOp Op_divz.
Add Zify BinOp Op_modz.
Add Zify BinOp Op_dvdz.
Add Zify BinOp Op_divn.
Add Zify BinOp Op_modn.
Add Zify BinOp Op_dvdn.
Add Zify UnOp Op_odd.
Add Zify UnOp Op_half.
Add Zify UnOp Op_uphalf.
Add Zify BinOp Op_gcdn.
Add Zify BinOp Op_lcmn.
Add Zify BinOp Op_coprime.
Add Zify BinOp Op_gcdz.
Add Zify BinOp Op_coprimez.
Add Zify BinOp Op_natdvd_le.
Add Zify BinOp Op_natdvd_le'.
Add Zify BinOp Op_natdvd_ge.
Add Zify BinOp Op_natdvd_ge'.
Add Zify BinOp Op_natdvd_lt.
Add Zify BinOp Op_natdvd_lt'.
Add Zify BinOp Op_natdvd_gt.
Add Zify BinOp Op_natdvd_gt'.
Add Zify BinOp Op_natdvd_meet.
Add Zify BinOp Op_natdvd_meet'.
Add Zify BinOp Op_natdvd_join.
Add Zify BinOp Op_natdvd_join'.
Add Zify CstOp Op_natdvd_bottom.
End Exports.

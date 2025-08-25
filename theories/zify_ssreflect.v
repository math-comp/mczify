From mathcomp Require all_algebra. (* remove this line when requiring Rocq > 9.1 *)
From Coq Require Import ZArith ZifyClasses ZifyInst ZifyBool.
From Coq Require Export Lia.
From Coq Require Znumtheory.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import order binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac Zify.zify_pre_hook ::= unfold is_true in *; do ?rewrite -> unfold_in in *.

Module SsreflectZifyInstances.

Import Order.Theory.

#[global]
Instance Op_bool_inj : UnOp (inj : bool -> bool) :=
  { TUOp := id; TUOpInj _ := erefl }.
Add Zify UnOp Op_bool_inj.

#[global]
Instance Op_nat_inj : UnOp (inj : nat -> Z) := Op_Z_of_nat.
Add Zify UnOp Op_nat_inj.

(******************************************************************************)
(* ssrbool                                                                    *)
(******************************************************************************)

#[global]
Instance Op_addb : BinOp addb :=
  { TBOp x y := Bool.eqb x (~~ y); TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_addb.

#[global]
Instance Op_eqb : BinOp eqb :=
  { TBOp := Bool.eqb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_eqb.

#[global]
Instance Op_eq_op_bool : BinOp (eq_op : rel bool) := Op_eqb.
Add Zify BinOp Op_eq_op_bool.

#[global]
Instance Op_bool_le : BinOp (<=%O : bool -> bool -> bool) :=
  { TBOp := implb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_le.

#[global]
Instance Op_bool_le' : BinOp (>=^d%O : rel bool^d) := Op_bool_le.
Add Zify BinOp Op_bool_le'.

#[global]
Instance Op_bool_ge : BinOp (>=%O : bool -> bool -> bool) :=
  { TBOp x y := implb y x; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_ge.

#[global]
Instance Op_bool_ge' : BinOp (<=^d%O : rel bool^d) := Op_bool_ge.
Add Zify BinOp Op_bool_ge'.

#[global]
Instance Op_bool_lt : BinOp (<%O : bool -> bool -> bool) :=
  { TBOp x y := ~~ x && y; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_lt.

#[global]
Instance Op_bool_lt' : BinOp (>^d%O : rel bool^d) := Op_bool_lt.
Add Zify BinOp Op_bool_lt'.

#[global]
Instance Op_bool_gt : BinOp (>%O : bool -> bool -> bool) :=
  { TBOp x y := x && ~~ y; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_gt.

#[global]
Instance Op_bool_gt' : BinOp (<^d%O : rel bool^d) := Op_bool_gt.
Add Zify BinOp Op_bool_gt'.

#[global]
Instance Op_bool_min : BinOp (Order.min : bool -> bool -> bool) :=
  { TBOp := andb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_min.

#[global]
Instance Op_bool_min' :
  BinOp ((Order.max : bool^d -> _) : bool -> bool -> bool) :=
  { TBOp := andb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_min'.

#[global]
Instance Op_bool_max : BinOp (Order.max : bool -> bool -> bool) :=
  { TBOp := orb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_max.

#[global]
Instance Op_bool_max' :
  BinOp ((Order.min : bool^d -> _) : bool -> bool -> bool) :=
  { TBOp := orb; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_max'.

#[global]
Instance Op_bool_meet : BinOp (Order.meet : bool -> bool -> bool) := Op_andb.
Add Zify BinOp Op_bool_meet.

#[global]
Instance Op_bool_meet' : BinOp (Order.join : bool^d -> _) := Op_andb.
Add Zify BinOp Op_bool_meet'.

#[global]
Instance Op_bool_join : BinOp (Order.join : bool -> bool -> bool) := Op_orb.
Add Zify BinOp Op_bool_join.

#[global]
Instance Op_bool_join' : BinOp (Order.meet : bool^d -> _) := Op_orb.
Add Zify BinOp Op_bool_join'.

#[global]
Instance Op_bool_bottom : CstOp (\bot : bool)%O := Op_false.
Add Zify CstOp Op_bool_bottom.

#[global]
Instance Op_bool_bottom' : CstOp (\top : bool^d)%O := Op_false.
Add Zify CstOp Op_bool_bottom'.

#[global]
Instance Op_bool_top : CstOp (\top : bool)%O := Op_true.
Add Zify CstOp Op_bool_top.

#[global]
Instance Op_bool_top' : CstOp (\bot : bool^d)%O := Op_true.
Add Zify CstOp Op_bool_top'.

#[global]
Instance Op_bool_sub : BinOp (Order.diff : bool -> bool -> bool) :=
  { TBOp x y := x && ~~ y; TBOpInj := ltac:(by case=> [][]) }.
Add Zify BinOp Op_bool_sub.

#[global]
Instance Op_bool_compl : UnOp (Order.compl : bool -> bool) := Op_negb.
Add Zify UnOp Op_bool_compl.

(******************************************************************************)
(* ssrnat                                                                     *)
(******************************************************************************)

#[global]
Instance Op_eqn : BinOp eqn := Op_nat_eqb.
Add Zify BinOp Op_eqn.

#[global]
Instance Op_eq_op_nat : BinOp (eq_op : rel nat) := Op_eqn.
Add Zify BinOp Op_eq_op_nat.

#[global]
Instance Op_addn_rec : BinOp addn_rec := Op_plus.
Add Zify BinOp Op_addn_rec.

#[global]
Instance Op_addn : BinOp addn := Op_plus.
Add Zify BinOp Op_addn.

#[global]
Instance Op_addn_trec : BinOp NatTrec.add :=
  { TBOp := Z.add; TBOpInj n m := ltac:(rewrite NatTrec.addE; lia) }.
Add Zify BinOp Op_addn_trec.

#[global]
Instance Op_subn_rec : BinOp subn_rec := Op_sub.
Add Zify BinOp Op_subn_rec.

#[global]
Instance Op_subn : BinOp subn := Op_sub.
Add Zify BinOp Op_subn.

#[global]
Instance Op_muln_rec : BinOp muln_rec := Op_mul.
Add Zify BinOp Op_muln_rec.

#[global]
Instance Op_muln : BinOp muln := Op_mul.
Add Zify BinOp Op_muln.

#[global]
Instance Op_muln_trec : BinOp NatTrec.mul :=
  { TBOp := Z.mul; TBOpInj n m := ltac:(rewrite NatTrec.mulE; lia) }.
Add Zify BinOp Op_muln_trec.

#[global]
Instance Op_leq : BinOp leq :=
  { TBOp := Z.leb; TBOpInj := ltac:(rewrite /leq; lia) }.
Add Zify BinOp Op_leq.

#[global]
Instance Op_geq : BinOp (geq : nat -> nat -> bool) :=
  { TBOp := Z.geb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_geq.

#[global]
Instance Op_ltn : BinOp (ltn : nat -> nat -> bool) :=
  { TBOp := Z.ltb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_ltn.

#[global]
Instance Op_gtn : BinOp (gtn : nat -> nat -> bool) :=
  { TBOp := Z.gtb; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_gtn.

#[global]
Instance Op_minn : BinOp minn :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leqP; lia) }.
Add Zify BinOp Op_minn.

#[global]
Instance Op_maxn : BinOp maxn :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leqP; lia) }.
Add Zify BinOp Op_maxn.

#[global]
Instance Op_nat_of_bool : UnOp nat_of_bool :=
  { TUOp := Z.b2z; TUOpInj := ltac:(by case) }.
Add Zify UnOp Op_nat_of_bool.

#[global]
Instance Op_double : UnOp double :=
  { TUOp := Z.mul 2; TUOpInj _ := ltac:(rewrite -muln2; lia) }.
Add Zify UnOp Op_double.

#[global]
Instance Op_double_trec : UnOp NatTrec.double :=
  { TUOp := Z.mul 2; TUOpInj _ := ltac:(rewrite NatTrec.doubleE; lia) }.
Add Zify UnOp Op_double_trec.

Fact Op_expn_subproof n m : Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite expnS; lia. Qed.

#[global]
Instance Op_expn_rec : BinOp expn_rec :=
  { TBOp := Z.pow; TBOpInj := Op_expn_subproof }.
Add Zify BinOp Op_expn_rec.

#[global]
Instance Op_expn : BinOp expn := Op_expn_rec.
Add Zify BinOp Op_expn.

#[global]
Instance Op_expn_trec : BinOp NatTrec.exp :=
  { TBOp := Z.pow; TBOpInj n m := ltac:(rewrite NatTrec.expE; lia) }.
Add Zify BinOp Op_expn_trec.

#[global]
Instance Op_eq_op_N : BinOp (eq_op : N -> N -> bool) :=
  { TBOp := Z.eqb; TBOpInj := ltac:(by case => [|n] []) }.
Add Zify BinOp Op_eq_op_N.

Fact nat_of_posE : nat_of_pos =1 Pos.to_nat.
Proof.
move=> p; rewrite /Pos.to_nat -[LHS]muln1.
elim: p 1 => /= [p IHp | p IHp |] n; rewrite -?IHp; lia.
Qed.

#[global]
Instance Op_nat_of_pos : UnOp nat_of_pos :=
  { TUOp := id; TUOpInj n := ltac:(rewrite /= nat_of_posE; lia) }.
Add Zify UnOp Op_nat_of_pos.

#[global]
Instance Op_nat_of_bin : UnOp nat_of_bin :=
  { TUOp := id; TUOpInj := ltac:(case => //=; lia) }.
Add Zify UnOp Op_nat_of_bin.

Fact pos_of_natE n m : pos_of_nat n m = Pos.of_succ_nat (n * 2 - m).
Proof. elim: n m => // n IHn [|[|m]] /=; rewrite IHn; lia. Qed.

#[global]
Instance Op_pos_of_nat : BinOp pos_of_nat :=
  { TBOp n m := Z.max 1 (n * 2 - m + 1);
    TBOpInj n m := ltac:(rewrite /= pos_of_natE; lia) }.
Add Zify BinOp Op_pos_of_nat.

#[global]
Instance Op_bin_of_nat : UnOp bin_of_nat :=
  { TUOp := id; TUOpInj n := ltac:(rewrite /= -[n in RHS]bin_of_natK; lia) }.
Add Zify UnOp Op_bin_of_nat.

#[global]
Instance Op_nat_le : BinOp (<=%O : rel nat) := Op_leq.
Add Zify BinOp Op_nat_le.

#[global]
Instance Op_nat_le' : BinOp (>=^d%O : rel nat^d) := Op_leq.
Add Zify BinOp Op_nat_le'.

#[global]
Instance Op_nat_ge : BinOp (>=%O : rel nat) := Op_geq.
Add Zify BinOp Op_nat_ge.

#[global]
Instance Op_nat_ge' : BinOp (<=^d%O : rel nat^d) := Op_geq.
Add Zify BinOp Op_nat_ge'.

#[global]
Instance Op_nat_lt : BinOp (<%O : rel nat) := Op_ltn.
Add Zify BinOp Op_nat_lt.

#[global]
Instance Op_nat_lt' : BinOp (>^d%O : rel nat^d) := Op_ltn.
Add Zify BinOp Op_nat_lt'.

#[global]
Instance Op_nat_gt : BinOp (>%O : rel nat) := Op_gtn.
Add Zify BinOp Op_nat_gt.

#[global]
Instance Op_nat_gt' : BinOp (<^d%O : rel nat^d) := Op_gtn.
Add Zify BinOp Op_nat_gt'.

#[global]
Instance Op_nat_min : BinOp (Order.min : nat -> _) := Op_minn.
Add Zify BinOp Op_nat_min.

#[global]
Instance Op_nat_min' : BinOp ((Order.max : nat^d -> _) : nat -> nat -> nat) :=
  { TBOp := Z.min; TBOpInj _ _ := ltac:(case: leP; lia) }.
Add Zify BinOp Op_nat_min'.

#[global]
Instance Op_nat_max : BinOp (Order.max : nat -> _) := Op_maxn.
Add Zify BinOp Op_nat_max.

#[global]
Instance Op_nat_max' : BinOp ((Order.min : nat^d -> _) : nat -> nat -> nat) :=
  { TBOp := Z.max; TBOpInj _ _ := ltac:(case: leP; lia) }.
Add Zify BinOp Op_nat_max'.

#[global]
Instance Op_nat_meet : BinOp (Order.meet : nat -> _) := Op_minn.
Add Zify BinOp Op_nat_meet.

#[global]
Instance Op_nat_meet' : BinOp (Order.join : nat^d -> _) := Op_minn.
Add Zify BinOp Op_nat_meet'.

#[global]
Instance Op_nat_join : BinOp (Order.join : nat -> _) := Op_maxn.
Add Zify BinOp Op_nat_join.

#[global]
Instance Op_nat_join' : BinOp (Order.meet : nat^d -> _) := Op_maxn.
Add Zify BinOp Op_nat_join'.

#[global]
Instance Op_nat_bottom : CstOp (\bot : nat)%O := Op_O.
Add Zify CstOp Op_nat_bottom.

(******************************************************************************)
(* division / modulo: Since `divz` and `modz` of MathComp (defined in         *)
(* `intdiv.v`) are incompatible with the division and modulo functions for    *)
(* `Z` in the Coq standard library, here we have to define ones for `Z` which *)
(* behave the same as `divz` and `modz`.                                      *)
(******************************************************************************)

Definition divZ (m d : Z) : Z :=
  Z.sgn d *
  match m with
  | Z0 => 0
  | Z.pos p => Z.of_nat (Pos.to_nat p %/ Z.abs_nat d)%N
  | Z.neg p => - Z.succ (Z.of_nat ((Pos.to_nat p).-1 %/ Z.abs_nat d)%N)
  end%Z.

Definition modZ (m d : Z) : Z := (m - divZ m d * d)%Z.

#[global]
Instance Op_divZ : BinOp divZ := { TBOp := divZ; TBOpInj _ _ := erefl }.
Add Zify BinOp Op_divZ.

#[global]
Instance Op_modZ : BinOp modZ := { TBOp := modZ; TBOpInj _ _ := erefl }.
Add Zify BinOp Op_modZ.

(* Reimplementation of Z.div_mod_to_equations (PreOmega.v) for divZ and modZ: *)

Fact divZ_eq m d : m = (divZ m d * d + modZ m d)%Z.
Proof. rewrite /modZ; lia. Qed.

Fact modZ_ge0 m d : d <> 0%Z -> (0 <= modZ m d)%Z.
Proof.
by move: d m => [] // d [] // m _; rewrite /modZ /divZ [Z.abs_nat _]/=;
  move: (leq_trunc_div (Pos.to_nat m) (Pos.to_nat d));
  move: (@ltn_ceil (Pos.to_nat m).-1 (Pos.to_nat d)); lia.
Qed.

Fact ltz_pmodZ m d : (0 < d)%Z -> (modZ m d < d)%Z.
Proof.
by move: d m => [] // d [] // m _; rewrite /modZ /divZ [Z.abs_nat _]/=;
  move: (leq_trunc_div (Pos.to_nat m).-1 (Pos.to_nat d));
  move: (@ltn_ceil (Pos.to_nat m) (Pos.to_nat d)); lia.
Qed.

Fact ltz_nmodZ m d : (d < 0)%Z -> (modZ m d < - d)%Z.
Proof.
move: d m => [] // d [] // m _; rewrite /modZ /divZ [Z.abs_nat _]/=;
  move: (leq_trunc_div (Pos.to_nat m).-1 (Pos.to_nat d));
  move: (@ltn_ceil (Pos.to_nat m) (Pos.to_nat d)); lia.
Qed.

Fact divZ0 m d : d = 0%Z -> divZ m d = 0%Z.
Proof. by move=> ->. Qed.

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
(* div (divn, modn, dvdn, gcdn, lcmn, and coprime)                            *)
(******************************************************************************)

Fact Op_divn_subproof n m : Z.of_nat (n %/ m) = divZ (Z.of_nat n) (Z.of_nat m).
Proof.
by case: n m => [|n] [|m]; rewrite /divZ //= ?SuccNat2Pos.id_succ; case: divn.
Qed.

#[global]
Instance Op_divn : BinOp divn := { TBOp := divZ; TBOpInj := Op_divn_subproof }.
Add Zify BinOp Op_divn.

#[global]
Instance Op_modn : BinOp modn :=
  { TBOp := modZ; TBOpInj n m := ltac:(move: (divn_eq n m); lia) }.
Add Zify BinOp Op_modn.

#[global]
Instance Op_dvdn : BinOp dvdn :=
  { TBOp x y := (modZ y x =? 0)%Z; TBOpInj := ltac:(rewrite /dvdn; lia) }.
Add Zify BinOp Op_dvdn.

#[global]
Instance Op_odd : UnOp odd :=
  { TUOp x := (modZ x 2 =? 1)%Z; TUOpInj n := ltac:(case: odd (modn2 n); lia) }.
Add Zify UnOp Op_odd.

#[global]
Instance Op_odd_trec : UnOp NatTrec.odd :=
  { TUOp x := (modZ x 2 =? 1)%Z;
    TUOpInj n := ltac:(rewrite NatTrec.oddE; lia) }.
Add Zify UnOp Op_odd_trec.

#[global]
Instance Op_half : UnOp half :=
  { TUOp x := divZ x 2; TUOpInj _ := ltac:(rewrite -divn2; lia) }.
Add Zify UnOp Op_half.

#[global]
Instance Op_uphalf : UnOp uphalf :=
  { TUOp x := divZ (x + 1)%Z 2; TUOpInj _ := ltac:(rewrite uphalf_half; lia) }.
Add Zify UnOp Op_uphalf.

Fact Op_gcdn_subproof n m :
  Z.of_nat (gcdn n m) = Z.gcd (Z.of_nat n) (Z.of_nat m).
Proof.
apply/esym/Z.gcd_unique; first by case: gcdn.
- case/dvdnP: (dvdn_gcdl n m) => k {2}->; exists (Z.of_nat k); lia.
- case/dvdnP: (dvdn_gcdr n m) => k {2}->; exists (Z.of_nat k); lia.
- move=> k [n' Hkn] [m' Hkm].
  suff/dvdnP [k' ->]: Z.abs_nat k %| gcdn n m.
    by apply/Znumtheory.Zdivide_Zabs_l; exists (Z.of_nat k'); lia.
  rewrite dvdn_gcd; apply/andP; split; apply/dvdnP;
    [exists (Z.abs_nat n') | exists (Z.abs_nat m')]; nia.
Qed.

#[global]
Instance Op_gcdn : BinOp gcdn := { TBOp := Z.gcd; TBOpInj := Op_gcdn_subproof }.
Add Zify BinOp Op_gcdn.

Fact Op_lcmn_subproof n m :
  Z.of_nat (lcmn n m) = Z.lcm (Z.of_nat n) (Z.of_nat m).
Proof.
case: n m => [|n][|m]; rewrite ?lcmn0 // /lcmn /Z.lcm -Op_gcdn_subproof.
case/dvdnP: (dvdn_gcdr n.+1 m.+1) => k {1 3}->.
rewrite mulnA mulnK ?gcdn_gt0 // !Nat2Z.inj_mul Z_div_mult_full //; first nia.
by case: (gcdn _ _) (gcdn_gt0 n.+1 m.+1).
Qed.

#[global]
Instance Op_lcmn : BinOp lcmn := { TBOp := Z.lcm; TBOpInj := Op_lcmn_subproof }.
Add Zify BinOp Op_lcmn.

#[global]
Instance Op_coprime : BinOp coprime :=
  { TBOp x y := (Z.gcd x y =? 1)%Z;
    TBOpInj := ltac:(rewrite /= /coprime; lia) }.
Add Zify BinOp Op_coprime.

(******************************************************************************)
(* natdvd in order.v                                                          *)
(******************************************************************************)

#[global]
Instance Op_natdvd_le : BinOp (<=%O : rel natdvd) := Op_dvdn.
Add Zify BinOp Op_natdvd_le.

#[global]
Instance Op_natdvd_le' : BinOp (>=^d%O : rel natdvd^d) := Op_dvdn.
Add Zify BinOp Op_natdvd_le'.

#[global]
Instance Op_natdvd_ge : BinOp ((>=%O : rel natdvd) : nat -> nat -> bool) :=
  { TBOp x y := (modZ x y =? 0)%Z; TBOpInj := ltac:(simpl; lia) }.
Add Zify BinOp Op_natdvd_ge.

#[global]
Instance Op_natdvd_ge' : BinOp (<=^d%O : rel natdvd^d) := Op_natdvd_ge.
Add Zify BinOp Op_natdvd_ge'.

#[global]
Instance Op_natdvd_lt : BinOp ((<%O : rel natdvd) : nat -> nat -> bool) :=
  { TBOp x y := ~~ (y =? x)%Z && (modZ y x =? 0)%Z;
    TBOpInj _ _ := ltac:(rewrite /= sdvdEnat; lia) }.
Add Zify BinOp Op_natdvd_lt.

#[global]
Instance Op_natdvd_lt' : BinOp (>^d%O : rel natdvd^d) := Op_natdvd_lt.
Add Zify BinOp Op_natdvd_lt'.

#[global]
Instance Op_natdvd_gt : BinOp ((>%O : rel natdvd) : nat -> nat -> bool) :=
  { TBOp x y := ~~ (x =? y)%Z && (modZ x y =? 0)%Z;
    TBOpInj _ _ := ltac:(rewrite /= sdvdEnat; lia) }.
Add Zify BinOp Op_natdvd_gt.

#[global]
Instance Op_natdvd_gt' : BinOp (<^d%O : rel natdvd^d) := Op_natdvd_gt.
Add Zify BinOp Op_natdvd_gt'.

#[global]
Instance Op_natdvd_meet : BinOp (Order.meet : natdvd -> _) := Op_gcdn.
Add Zify BinOp Op_natdvd_meet.

#[global]
Instance Op_natdvd_meet' : BinOp (Order.join : natdvd^d -> _) := Op_gcdn.
Add Zify BinOp Op_natdvd_meet'.

#[global]
Instance Op_natdvd_join : BinOp (Order.join : natdvd -> _) := Op_lcmn.
Add Zify BinOp Op_natdvd_join.

#[global]
Instance Op_natdvd_join' : BinOp (Order.meet : natdvd^d -> _) := Op_lcmn.
Add Zify BinOp Op_natdvd_join'.

#[global]
Instance Op_natdvd_bottom : CstOp (\bot : natdvd)%O :=
  { TCst := 1%Z; TCstInj := erefl }.
Add Zify CstOp Op_natdvd_bottom.

#[global]
Instance Op_natdvd_bottom' : CstOp (\top : natdvd^d)%O := Op_natdvd_bottom.
Add Zify CstOp Op_natdvd_bottom'.

#[global]
Instance Op_natdvd_top : CstOp (\top : natdvd)%O := Op_O.
Add Zify CstOp Op_natdvd_top.

#[global]
Instance Op_natdvd_top' : CstOp (\bot : natdvd^d)%O := Op_O.
Add Zify CstOp Op_natdvd_top'.

Module Exports.
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
Add Zify BinOp Op_addn_trec.
Add Zify BinOp Op_subn_rec.
Add Zify BinOp Op_subn.
Add Zify BinOp Op_muln_rec.
Add Zify BinOp Op_muln.
Add Zify BinOp Op_muln_trec.
Add Zify BinOp Op_leq.
Add Zify BinOp Op_geq.
Add Zify BinOp Op_ltn.
Add Zify BinOp Op_gtn.
Add Zify BinOp Op_minn.
Add Zify BinOp Op_maxn.
Add Zify UnOp Op_nat_of_bool.
Add Zify UnOp Op_double.
Add Zify UnOp Op_double_trec.
Add Zify BinOp Op_expn_rec.
Add Zify BinOp Op_expn.
Add Zify BinOp Op_expn_trec.
Add Zify BinOp Op_eq_op_N.
Add Zify UnOp Op_nat_of_pos.
Add Zify UnOp Op_nat_of_bin.
Add Zify BinOp Op_pos_of_nat.
Add Zify UnOp Op_bin_of_nat.
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
Add Zify BinOp Op_divZ.
Add Zify BinOp Op_modZ.
Add Zify BinOp Op_divn.
Add Zify BinOp Op_modn.
Add Zify BinOp Op_dvdn.
Add Zify UnOp Op_odd.
Add Zify UnOp Op_odd_trec.
Add Zify UnOp Op_half.
Add Zify UnOp Op_uphalf.
Add Zify BinOp Op_gcdn.
Add Zify BinOp Op_lcmn.
Add Zify BinOp Op_coprime.
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
Add Zify CstOp Op_natdvd_bottom'.
Add Zify CstOp Op_natdvd_top.
Add Zify CstOp Op_natdvd_top'.
End Exports.

End SsreflectZifyInstances.
Export SsreflectZifyInstances.Exports.

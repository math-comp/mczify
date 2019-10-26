From Coq Require Import ZArith ZifyClasses Zify ZifyBool Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import binomial ssralg countalg ssrnum ssrint rat intdiv.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
Ltac zify ::=
  unfold is_true in *; zify_op; (iter_specs applySpec); zify_post_hook.

(* missing instances *)
Instance Op_isZero : UnOp isZero :=
  { TUOp := isZero; TUOpInj := fun _ => erefl }.
Add UnOp Op_isZero.

Instance Op_isLeZero : UnOp isLeZero :=
  { TUOp := isLeZero; TUOpInj := fun _ => erefl }.
Add UnOp Op_isLeZero.

Module zify.

Local Delimit Scope Z_scope with Z.

Canonical Inj_nat_Z. (* Z_of_bool =? inj _ *)
Canonical Inj_bool_Z. (* Z.of_nat =? inj _ *)

Lemma pos_eqP : Equality.axiom Pos.eqb.
Proof.
by elim=> [? ih|? ih|] [?|?|]; apply/(iffP idP) => //=;
  move/ih => -> || case=> /ih.
Qed.

Definition pos_eqMixin := Equality.Mixin pos_eqP.
Canonical pos_eqType := Equality.Pack pos_eqMixin.

Lemma Z_eqP : Equality.axiom Z.eqb.
Proof.
by case=> [|p|p] [|p'|p']; apply/(iffP idP) => //=;
  move/(@eqP pos_eqType) => -> || case => /eqP.
Qed.

Definition Z_eqMixin := Equality.Mixin Z_eqP.
Canonical Z_eqType := Equality.Pack Z_eqMixin.

(******************************************************************************)
(* bool                                                                       *)
(******************************************************************************)

Instance Op_addb : BinOp addb :=
  { TBOp := fun x y => (Z.max (x - y) (y - x))%Z;
    TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_addb.

Instance Op_eqb : BinOp eqb :=
  { TBOp := fun x y => isZero (x - y)%Z;
    TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_eqb.

Instance Op_eq_op_bool : BinOp (@eq_op bool_eqType) := Op_eqb.
Add BinOp Op_eq_op_bool.

Instance Op_Z_of_bool : UnOp Z_of_bool :=
  { TUOp := id; TUOpInj := fun _ => erefl }.
Add UnOp Op_Z_of_bool.

(******************************************************************************)
(* nat                                                                        *)
(******************************************************************************)

Instance Op_eqn : BinOp eqn := Op_nat_eqb.
Add BinOp Op_eqn.

Instance Op_eq_op_nat : BinOp (@eq_op nat_eqType) := Op_eqn.
Add BinOp Op_eq_op_nat.

Instance Op_addn_rec : BinOp addn_rec := Op_plus.
Add BinOp Op_addn_rec.

Instance Op_addn : BinOp addn := Op_plus.
Add BinOp Op_addn.

Instance Op_subn_rec : BinOp subn_rec := Op_sub.
Add BinOp Op_subn_rec.

Instance Op_subn : BinOp subn := Op_sub.
Add BinOp Op_subn.

Instance Op_muln_rec : BinOp muln_rec := Op_mul.
Add BinOp Op_muln_rec.

Instance Op_muln : BinOp muln := Op_mul.
Add BinOp Op_muln.

Lemma nat_lebE n m : (n <= m) = Nat.leb n m.
Proof. by elim: n m => // n ih [|m] //=; rewrite -ih. Qed.

Instance Op_leq : BinOp leq :=
  { TBOp := fun x y => isLeZero (x - y)%Z;
    TBOpInj := ltac:(move=> *; rewrite nat_lebE /=; lia) }.
Add BinOp Op_leq.

Instance Op_geq : BinOp geq :=
  { TBOp := fun x y => isLeZero (y - x)%Z;
    TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_geq.

Instance Op_ltn : BinOp ltn :=
  { TBOp := fun x y => isLeZero (x + 1 - y)%Z; TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_ltn.

Instance Op_gtn : BinOp gtn :=
  { TBOp := fun x y => isLeZero (y + 1 - x); TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_gtn.

Lemma Op_minn_subproof n m :
  Z.of_nat (minn n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. rewrite /minn /=; case: leqP; lia. Qed.

Instance Op_minn : BinOp minn :=
  {| TBOp := Z.min; TBOpInj := Op_minn_subproof |}.
Add BinOp Op_minn.

Lemma Op_maxn_subproof n m :
  Z.of_nat (maxn n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. rewrite /maxn /=; case: leqP; lia. Qed.

Instance Op_maxn : BinOp maxn :=
  {| TBOp := Z.max; TBOpInj := Op_maxn_subproof |}.
Add BinOp Op_maxn.

Lemma Z_of_nat_of_boolE (b : bool) : Z.of_nat b = Z_of_bool b.
Proof. by case: b. Qed.

Instance Op_nat_of_bool : UnOp nat_of_bool :=
  {| TUOp := id; TUOpInj := Z_of_nat_of_boolE |}.
Add UnOp Op_nat_of_bool.

Lemma Op_double_subproof n : Z.of_nat n.*2 = (2 * (Z.of_nat n))%Z.
Proof. rewrite -muln2; lia. Qed.

Instance Op_double : UnOp double :=
  {| TUOp := Z.mul 2; TUOpInj := Op_double_subproof |}.
Add UnOp Op_double.

Lemma Op_expn_subproof n m : Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite expnS; nia. Qed.

Instance Op_expn_rec : BinOp expn_rec :=
  {| TBOp := Z.pow; TBOpInj := Op_expn_subproof |}.
Add BinOp Op_expn_rec.

Instance Op_expn : BinOp expn := Op_expn_rec.
Add BinOp Op_expn.

(* missing (but cannot be handled by Micromega): *)
(* Print fact_rec. *)
(* Print factorial. *)

(******************************************************************************)
(* natdiv                                                                     *)
(******************************************************************************)

Lemma Op_divn_subproof n m : Z.of_nat (n %/ m) = (Z.of_nat n / Z.of_nat m)%Z.
Proof.
case: m=> [|m]; first by case: n.
rewrite /divn; case: edivnP => q r -> {n}.
rewrite -div_Zdiv // Nat.div_add_l // => le_r_m.
by rewrite Nat.div_small 1?Nat.add_comm //; apply/ltP.
Qed.

Instance Op_divn : BinOp divn :=
  {| TBOp := Z.div; TBOpInj := Op_divn_subproof |}.
Add BinOp Op_divn.

Lemma Op_modn_subproof n m :
  Z.of_nat (n %% m) = Z.rem (Z.of_nat n) (Z.of_nat m).
Proof.
case: m=> [|m]; first by case: n.
rewrite modn_def Z.rem_mod_nonneg -?mod_Zmod //; last exact: Zle_0_nat.
case: edivnP => q r -> {n} //; rewrite addnC Nat.mod_add // => le_r_m.
by rewrite Nat.mod_small //; apply/ltP.
Qed.

Instance Op_modn : BinOp modn :=
  {| TBOp := Z.rem; TBOpInj := Op_modn_subproof |}.
Add BinOp Op_modn.

Lemma Op_dvdn_subproof n m :
  Z_of_bool (n %| m) = isZero (Z.rem (Z.of_nat m) (Z.of_nat n)).
Proof. rewrite /dvdn; lia. Qed.

Instance Op_dvdn : BinOp dvdn :=
  {| TBOp := fun x y => isZero (Z.rem y x); TBOpInj := Op_dvdn_subproof |}.
Add BinOp Op_dvdn.

Lemma Op_odd_subproof n : Z_of_bool (odd n) = (Z.of_nat n mod 2)%Z.
Proof. rewrite -Z_of_nat_of_boolE -modn2; lia. Qed.

Instance Op_odd : UnOp odd :=
  {| TUOp := fun x => (x mod 2)%Z; TUOpInj := Op_odd_subproof |}.
Add UnOp Op_odd.

Lemma Op_half_subproof n : Z.of_nat n./2 = (Z.of_nat n / 2)%Z.
Proof. rewrite -divn2; lia. Qed.

Instance Op_half : UnOp half :=
  {| TUOp := fun x => (x / 2)%Z; TUOpInj := Op_half_subproof |}.
Add UnOp Op_half.

(* Print gcdn. *)
(* Print lcmn. *)

(******************************************************************************)
(* ssrint                                                                     *)
(******************************************************************************)

Section ssrint.

Import GRing.Theory Num.Theory.

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Zneg (Pos.of_succ_nat n')
  end.

Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun _ => True) (fun _ => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

Instance Op_Z_of_int : UnOp Z_of_int :=
  { TUOp := id : Z -> Z; TUOpInj := ltac:(by []) }.
Add UnOp Op_Z_of_int.

Instance Op_Posz : UnOp Posz := mkuop _ _ _ Posz _ _ id (fun _ => erefl).
Add UnOp Op_Posz.

Lemma Op_Negz_subproof n : Z_of_int (Negz n) = (- (Z.of_nat n + 1))%Z.
Proof. simpl; lia. Qed.

Instance Op_Negz : UnOp Negz :=
  {| TUOp := fun x => (- (x + 1))%Z; TUOpInj := Op_Negz_subproof |}.
Add UnOp Op_Negz.

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. split=> [->|] //; case: n m => ?[]? /= ?; f_equal; lia. Qed.

Instance Op_eq_int : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_eq_int_subproof }.
Add BinRel Op_eq_int.

Lemma Op_eq_op_int_subproof (n m : int) :
  Z_of_bool (n == m) = isZero (Z_of_int n - Z_of_int m).
Proof. case: n m => ?[]? //; rewrite /eq_op [LHS]/= /eq_op [LHS]/=; lia. Qed.

Instance Op_eq_op_int : BinOp (@eq_op int_eqType) :=
  { TBOp := fun x y => isZero (x - y); TBOpInj := Op_eq_op_int_subproof }.
Add BinOp Op_eq_op_int.

Instance Op_0_int : CstOp 0%R :=
  {| TCst := 0%Z; TCstInj := (erefl _ : Z_of_int 0%R = 0%Z) |}.
Add CstOp Op_0_int.

Lemma Op_addz_subproof n m :
  Z_of_int (intZmod.addz n m) = (Z_of_int n + Z_of_int m)%Z.
Proof. case: n m => ?[]?; rewrite /intZmod.addz; try case: leqP; lia. Qed.

Instance Op_addz : BinOp intZmod.addz :=
  {| TBOp := Z.add; TBOpInj := Op_addz_subproof |}.
Add BinOp Op_addz.

Instance Op_add_int : BinOp +%R := Op_addz.
Add BinOp Op_add_int.

Lemma Op_oppz_subproof n : Z_of_int (intZmod.oppz n) = (- Z_of_int n)%Z.
Proof. case: n=> [[|?]|?]; rewrite /intZmod.oppz; lia. Qed.

Instance Op_oppz : UnOp intZmod.oppz :=
  {| TUOp := Z.opp; TUOpInj := Op_oppz_subproof |}.
Add UnOp Op_oppz.

Instance Op_opp_int : UnOp (@GRing.opp _) := Op_oppz.
Add UnOp Op_opp_int.

Instance Op_1_int : CstOp 1%R :=
  {| TCst := 1%Z; TCstInj := (erefl _ : Z_of_int 1%R = 1%Z) |}.
Add CstOp Op_1_int.

Lemma Op_mulz_subproof n m :
  Z_of_int (intRing.mulz n m) = (Z_of_int n * Z_of_int m)%Z.
Proof. case: n m => ?[]?; rewrite /intRing.mulz; nia. Qed.

Instance Op_mulz : BinOp intRing.mulz :=
  {| TBOp := Z.mul; TBOpInj := Op_mulz_subproof |}.
Add BinOp Op_mulz.

Instance Op_mulr_int : BinOp *%R := Op_mulz.
Add BinOp Op_mulr_int.

Lemma Op_int_intmul_subproof n m :
  Z_of_int (n *~ m) = (Z_of_int n * Z_of_int m)%Z.
Proof. rewrite mulrzz; lia. Qed.

Instance Op_int_intmul : BinOp *~%R%R :=
  {| TBOp := Z.mul; TBOpInj := Op_int_intmul_subproof |}.
Add BinOp Op_int_intmul.

Lemma Op_int_natmul_subproof n m :
  Z_of_int (n *+ m) = (Z_of_int n * Z_of_nat m)%Z.
Proof. rewrite pmulrn mulrzz; lia. Qed.

Instance Op_int_natmul : BinOp (@GRing.natmul _) :=
  {| TBOp := Z.mul; TBOpInj := Op_int_natmul_subproof |}.
Add BinOp Op_int_natmul.

Lemma Op_int_exp_subproof n m :
  Z_of_int (n ^+ m) = (Z_of_int n ^ Z.of_nat m)%Z.
Proof.
rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia.
Qed.

Instance Op_int_exp : BinOp (@GRing.exp _) :=
  {| TBOp := Z.pow; TBOpInj := Op_int_exp_subproof |}.
Add BinOp Op_int_exp.

Lemma Op_int_scale_subproof (n : int) (m : int^o) :
  Z_of_int (n *: m) = (Z_of_int n * Z_of_int m)%Z.
Proof. rewrite /GRing.scale /=; lia. Qed.

Instance Op_int_scale : BinOp (@GRing.scale _ [lmodType int of int^o]) :=
  {| TBOp := Z.mul; TBOpInj := Op_int_scale_subproof |}.
Add BinOp Op_int_scale.

Instance Op_invz : UnOp intUnitRing.invz :=
  {| TUOp := id; TUOpInj := fun _ => erefl |}.
Add UnOp Op_invz.

Instance Op_int_inv : UnOp GRing.inv := Op_invz.
Add UnOp Op_int_inv.

Lemma Op_absz_subproof n : Z.of_nat (absz n) = Z.abs (Z_of_int n).
Proof. case: n => ? /=; lia. Qed.

Instance Op_absz : UnOp absz :=
  { TUOp := Z.abs; TUOpInj := Op_absz_subproof }.
Add UnOp Op_absz.

Lemma Op_int_normr_subproof (n : int) : Z_of_int `|n|%R = Z.abs (Z_of_int n).
Proof. rewrite /Num.norm /=; lia. Qed.

Instance Op_int_normr : UnOp Num.norm :=
  { TUOp := Z.abs; TUOpInj := Op_int_normr_subproof }.
Add UnOp Op_int_normr.

Lemma Op_lez_subproof n m :
  Z_of_bool (intOrdered.lez n m) = isLeZero (Z_of_int n - Z_of_int m).
Proof. case: n m => ?[]?; rewrite [LHS]/=; lia. Qed.

Instance Op_lez : BinOp intOrdered.lez :=
  {| TBOp := fun x y => isLeZero (x - y)%Z; TBOpInj := Op_lez_subproof |}.
Add BinOp Op_lez.

Instance Op_int_ler : BinOp Num.le := Op_lez.
Add BinOp Op_int_ler.

Lemma Op_ltz_subproof n m :
  Z_of_bool (intOrdered.ltz n m) = isLeZero (Z_of_int n + 1 - Z_of_int m).
Proof. case: n m => ?[]?; rewrite [LHS]/=; lia. Qed.

Instance Op_ltz : BinOp intOrdered.ltz :=
  {| TBOp := fun x y => isLeZero (x + 1 - y)%Z; TBOpInj := Op_ltz_subproof |}.
Add BinOp Op_ltz.

Instance Op_int_ltr : BinOp Num.lt := Op_ltz.
Add BinOp Op_int_ltr.

(* Print Num.Def.lerif. *)

Lemma Op_int_sgr_subproof n : Z_of_int (Num.sg n) = Z.sgn (Z_of_int n).
Proof. by case: n => [[]|]. Qed.

Instance Op_int_sgr : UnOp Num.sg :=
  {| TUOp := Z.sgn; TUOpInj := Op_int_sgr_subproof |}.
Add UnOp Op_int_sgr.

Lemma Op_int_min_subproof n m :
  Z_of_int (Num.min n m) = Z.min (Z_of_int n) (Z_of_int m).
Proof. case: minrP; lia. Qed.

Instance Op_int_min : BinOp Num.min :=
  {| TBOp := Z.min; TBOpInj := Op_int_min_subproof |}.
Add BinOp Op_int_min.

Lemma Op_int_max_subproof n m :
  Z_of_int (Num.max n m) = Z.max (Z_of_int n) (Z_of_int m).
Proof. case: maxrP; lia. Qed.

Instance Op_int_max : BinOp Num.max :=
  {| TBOp := Z.max; TBOpInj := Op_int_max_subproof |}.
Add BinOp Op_int_max.

End ssrint.

(******************************************************************************)
(* intdiv                                                                     *)
(******************************************************************************)



End zify.

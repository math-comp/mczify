From Coq Require Import ZArith ZifyClasses Zify ZifyBool Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import binomial ssralg countalg ssrnum ssrint rat intdiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
Ltac zify ::=
  unfold is_true in *; zify_op; (iter_specs applySpec); zify_post_hook.

(* missing instances in ZifyBool.v *)
Instance Op_isZero : UnOp isZero :=
  { TUOp := isZero; TUOpInj := fun => erefl }.
Add UnOp Op_isZero.

Instance Op_isLeZero : UnOp isLeZero :=
  { TUOp := isLeZero; TUOpInj := fun => erefl }.
Add UnOp Op_isLeZero.

Module zify.

Local Delimit Scope Z_scope with Z.

Canonical Inj_nat_Z. (* Z_of_bool =? inj _ *)
Canonical Inj_bool_Z. (* Z.of_nat =? inj _ *)

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
  { TUOp := id; TUOpInj := fun => erefl }.
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
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite expnS; lia. Qed.

Instance Op_expn_rec : BinOp expn_rec :=
  {| TBOp := Z.pow; TBOpInj := Op_expn_subproof |}.
Add BinOp Op_expn_rec.

Instance Op_expn : BinOp expn := Op_expn_rec.
Add BinOp Op_expn.

(* missing: *)
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
by rewrite Nat.div_small -?plus_n_O //; apply/ltP.
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

Lemma Op_uphalf_subproof n : Z.of_nat (uphalf n) = ((Z.of_nat n + 1) / 2)%Z.
Proof. rewrite uphalf_half; lia. Qed.

Instance Op_uphalf : UnOp uphalf :=
  {| TUOp := fun x => ((x + 1) / 2)%Z; TUOpInj := Op_uphalf_subproof |}.
Add UnOp Op_uphalf.

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

Instance Op_gcdn : BinOp gcdn :=
  {| TBOp := Z.gcd; TBOpInj := Op_gcdn_subproof |}.
Add BinOp Op_gcdn.

Lemma Op_lcmn_subproof n m :
  Z.of_nat (lcmn n m) = Z.lcm (Z.of_nat n) (Z.of_nat m).
Proof.
case: n m => [|n][|m]; rewrite ?lcmn0 // /lcmn /Z.lcm -Op_gcdn_subproof.
case/dvdnP: (dvdn_gcdr n.+1 m.+1) => k {1 3}->.
rewrite mulnA mulnK ?gcdn_gt0 // !Nat2Z.inj_mul Z_div_mult_full //; first nia.
by case: (gcdn _ _) (gcdn_gt0 n.+1 m.+1).
Qed.

Instance Op_lcmn : BinOp lcmn :=
  {| TBOp := Z.lcm; TBOpInj := Op_lcmn_subproof |}.
Add BinOp Op_lcmn.

Lemma Op_coprime_subproof n m :
  Z_of_bool (coprime n m) = isZero (Z.gcd (Z.of_nat n) (Z.of_nat m) - 1)%Z.
Proof. rewrite /coprime; lia. Qed.

Instance Op_coprime : BinOp coprime :=
  {| TBOp := fun x y => isZero (Z.gcd x y - 1);
     TBOpInj := Op_coprime_subproof |}.
Add BinOp Op_coprime.

(* missing: definitions in prime and binomial *)

(******************************************************************************)
(* ssrint                                                                     *)
(******************************************************************************)

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun => True) (fun => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

Instance Op_Z_of_int : UnOp Z_of_int :=
  { TUOp := id : Z -> Z; TUOpInj := ltac:(by []) }.
Add UnOp Op_Z_of_int.

Instance Op_Posz : UnOp Posz := mkuop _ _ _ Posz _ _ id (fun => erefl).
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
  (* { TBOp := fun x y => isZero (x - y); TBOpInj := Op_eq_op_int_subproof }. *)
  mkbop int int bool Z (@eq_op _) Inj_int_Z Inj_int_Z Inj_bool_Z
        (fun x y : Z => isZero (Z.sub x y)) Op_eq_op_int_subproof.
Add BinOp Op_eq_op_int.

Instance Op_0_int : CstOp 0%R :=
  {| TCst := 0%Z; TCstInj := erefl (Z_of_int 0%R) |}.
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
Proof. case: n m => ?[]?; rewrite /intRing.mulz; lia. Qed.

Instance Op_mulz : BinOp intRing.mulz :=
  {| TBOp := Z.mul; TBOpInj := Op_mulz_subproof |}.
Add BinOp Op_mulz.

Instance Op_mulr_int : BinOp *%R := Op_mulz.
Add BinOp Op_mulr_int.

Lemma Op_int_intmul_subproof n m :
  Z_of_int (n *~ m) = (Z_of_int n * Z_of_int m)%Z.
Proof. rewrite mulrzz; lia. Qed.

Instance Op_int_intmul : BinOp *~%R%R :=
  (* {| TBOp := Z.mul; TBOpInj := Op_int_intmul_subproof |}. *)
  mkbop int int int Z (@intmul _) Inj_int_Z Inj_int_Z
        Inj_int_Z Z.mul Op_int_intmul_subproof.
Add BinOp Op_int_intmul.

Lemma Op_int_natmul_subproof n m :
  Z_of_int (n *+ m) = (Z_of_int n * Z_of_nat m)%Z.
Proof. rewrite pmulrn mulrzz; lia. Qed.

Instance Op_int_natmul : BinOp (@GRing.natmul _) :=
  (* {| TBOp := Z.mul; TBOpInj := Op_int_natmul_subproof |}. *)
  mkbop int nat int Z (@GRing.natmul _) Inj_int_Z Inj_nat_Z
        Inj_int_Z Z.mul Op_int_natmul_subproof.
Add BinOp Op_int_natmul.

Lemma Op_int_scale_subproof (n : int) (m : int^o) :
  Z_of_int (n *: m) = (Z_of_int n * Z_of_int m)%Z.
Proof. rewrite /GRing.scale /=; lia. Qed.

Instance Op_int_scale : BinOp (@GRing.scale _ [lmodType int of int^o]) :=
  (* {| TBOp := Z.mul; TBOpInj := Op_int_scale_subproof |}. *)
  mkbop int int int Z (@GRing.scale _ (GRing.regular_lmodType int_Ring))
        Inj_int_Z Inj_int_Z Inj_int_Z Z.mul Op_int_scale_subproof.
Add BinOp Op_int_scale.

Lemma Op_int_exp_subproof n m :
  Z_of_int (n ^+ m) = (Z_of_int n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia. Qed.

Instance Op_int_exp : BinOp (@GRing.exp _) :=
  {| TBOp := Z.pow; TBOpInj := Op_int_exp_subproof |}.
Add BinOp Op_int_exp.

Instance Op_invz : UnOp intUnitRing.invz :=
  {| TUOp := id; TUOpInj := fun => erefl |}.
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

(* missing: *)
(* Print Num.Def.lerif. *)

Lemma Op_int_sgr_subproof n : Z_of_int (Num.sg n) = Z.sgn (Z_of_int n).
Proof. by case: n => [[]|n] //=; rewrite addn1. Qed.

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

(******************************************************************************)
(* intdiv                                                                     *)
(******************************************************************************)

Lemma Op_divz_subproof n m :
  Z_of_int (divz n m) =
  (Z.sgn (Z_of_int m) * (Z_of_int n / Z.abs (Z_of_int m)))%Z.
Proof.
rewrite /divz /sgz; case: n m => n[[|m]|m];
  rewrite [X in Z_of_int X]/= [Z.sgn _]/= ?{1}addn1 ?[Z.sgn _]/= [Z.abs _]/=;
  rewrite ?mulN1r ?mul1r; nia.
Qed.

Instance Op_divz : BinOp divz :=
  {| TBOp := (fun n m => Z.sgn m * (n / Z.abs m))%Z;
     TBOpInj := Op_divz_subproof |}.
Add BinOp Op_divz.

(* missing: *)
(* Print modz. *)

Lemma Op_dvdz_subproof n m :
  Z_of_bool (dvdz n m) = isZero (Z.rem (Z_of_int m) (Z_of_int n)).
Proof.
case: n m => n[]m;
  rewrite /dvdz ![absz _]/= ![Z_of_int _]/= ?Z.rem_opp_l' ?Z.rem_opp_r'; lia.
Qed.

Instance Op_dvdz : BinOp dvdz :=
  {| TBOp := fun x y => isZero (Z.rem y x); TBOpInj := Op_dvdz_subproof |}.
Add BinOp Op_dvdz.

Lemma Op_gcdz_subproof n m :
  Z_of_int (gcdz n m) = Z.gcd (Z_of_int n) (Z_of_int m).
Proof.
by rewrite /gcdz /= Op_gcdn_subproof; case: n m => n[]m;
  rewrite ![absz _]/= -?(addn1 n) -?(addn1 m) /= ?Z.gcd_opp_l ?Z.gcd_opp_r.
Qed.

Instance Op_gcdz : BinOp gcdz :=
  {| TBOp := Z.gcd; TBOpInj := Op_gcdz_subproof |}.
Add BinOp Op_gcdz.

Lemma Op_coprimez_subproof n m :
  Z_of_bool (coprimez n m) = isZero (Z.gcd (Z_of_int n) (Z_of_int m) - 1)%Z.
Proof. rewrite /coprimez; lia. Qed.

Instance Op_coprimez : BinOp coprimez :=
  {| TBOp := fun x y => isZero (Z.gcd x y - 1);
     TBOpInj := Op_coprimez_subproof |}.
Add BinOp Op_coprimez.

End zify.

Add UnOp   zify.Op_isZero.
Add UnOp   zify.Op_isLeZero.
Add BinOp  zify.Op_addb.
Add BinOp  zify.Op_eqb.
Add BinOp  zify.Op_eq_op_bool.
Add UnOp   zify.Op_Z_of_bool.
Add BinOp  zify.Op_eqn.
Add BinOp  zify.Op_eq_op_nat.
Add BinOp  zify.Op_addn_rec.
Add BinOp  zify.Op_addn.
Add BinOp  zify.Op_subn_rec.
Add BinOp  zify.Op_subn.
Add BinOp  zify.Op_muln_rec.
Add BinOp  zify.Op_muln.
Add BinOp  zify.Op_leq.
Add BinOp  zify.Op_geq.
Add BinOp  zify.Op_ltn.
Add BinOp  zify.Op_gtn.
Add BinOp  zify.Op_minn.
Add BinOp  zify.Op_maxn.
Add UnOp   zify.Op_nat_of_bool.
Add UnOp   zify.Op_double.
Add BinOp  zify.Op_expn_rec.
Add BinOp  zify.Op_expn.
Add BinOp  zify.Op_divn.
Add BinOp  zify.Op_modn.
Add BinOp  zify.Op_dvdn.
Add UnOp   zify.Op_odd.
Add UnOp   zify.Op_half.
Add UnOp   zify.Op_uphalf.
Add BinOp  zify.Op_gcdn.
Add BinOp  zify.Op_lcmn.
Add BinOp  zify.Op_coprime.
Add InjTyp zify.Inj_int_Z.
Add UnOp   zify.Op_Z_of_int.
Add UnOp   zify.Op_Posz.
Add UnOp   zify.Op_Negz.
Add BinRel zify.Op_eq_int.
Add BinOp  zify.Op_eq_op_int.
Add CstOp  zify.Op_0_int.
Add BinOp  zify.Op_addz.
Add BinOp  zify.Op_add_int.
Add UnOp   zify.Op_oppz.
Add UnOp   zify.Op_opp_int.
Add CstOp  zify.Op_1_int.
Add BinOp  zify.Op_mulz.
Add BinOp  zify.Op_mulr_int.
Add BinOp  zify.Op_int_intmul.
Add BinOp  zify.Op_int_natmul.
Add BinOp  zify.Op_int_scale.
Add BinOp  zify.Op_int_exp.
Add UnOp   zify.Op_invz.
Add UnOp   zify.Op_int_inv.
Add UnOp   zify.Op_absz.
Add UnOp   zify.Op_int_normr.
Add BinOp  zify.Op_lez.
Add BinOp  zify.Op_int_ler.
Add BinOp  zify.Op_ltz.
Add BinOp  zify.Op_int_ltr.
Add UnOp   zify.Op_int_sgr.
Add BinOp  zify.Op_int_min.
Add BinOp  zify.Op_int_max.
Add BinOp  zify.Op_divz.
Add BinOp  zify.Op_dvdz.
Add BinOp  zify.Op_gcdz.
Add BinOp  zify.Op_coprimez.

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

Canonical Inj_nat_Z. (* Z_of_nat =? inj _ *)

(******************************************************************************)
(* bool                                                                       *)
(******************************************************************************)

Instance Op_addb : BinOp addb :=
  { TBOp := fun x y => Bool.eqb x (negb y); TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_addb.

Instance Op_eqb : BinOp eqb :=
  { TBOp := Bool.eqb; TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_eqb.

Instance Op_eq_op_bool : BinOp (@eq_op bool_eqType) := Op_eqb.
Add BinOp Op_eq_op_bool.

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
  { TBOp := Z.leb; TBOpInj := ltac:(move=> *; rewrite nat_lebE /=; lia) }.
Add BinOp Op_leq.

Instance Op_geq : BinOp (geq: nat -> nat -> bool) := { TBOp := Z.geb; TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_geq.

Instance Op_ltn : BinOp (ltn: nat -> nat -> bool) := { TBOp := Z.ltb; TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_ltn.

Instance Op_gtn : BinOp (gtn : nat -> nat -> bool) := { TBOp := Z.gtb; TBOpInj := ltac:(simpl; lia) }.
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

Lemma Op_nat_of_bool_subproof (b : bool) : Z.of_nat b = Z.b2z (inj b).
Proof. by case: b. Qed.

Instance Op_nat_of_bool : UnOp nat_of_bool :=
  {| TUOp := Z.b2z; TUOpInj := Op_nat_of_bool_subproof |}.
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
  { TUOp := fun n : Z => n; TUOpInj := fun _ => erefl }.
Add UnOp Op_Z_of_int.

Instance Op_Posz : UnOp Posz :=
  { TUOp := fun n : Z => n; TUOpInj := fun _ => erefl }.
Add UnOp Op_Posz.

Instance Op_Negz : UnOp Negz :=
  { TUOp := fun x => (- (x + 1))%Z; TUOpInj := ltac:(simpl; lia) }.
Add UnOp Op_Negz.

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. split=> [->|] //; case: n m => ?[]? /= ?; f_equal; lia. Qed.

Instance Op_eq_int : BinRel (@eq int) :=
  {| TR := @eq Z; TRInj := Op_eq_int_subproof |}.
Add BinRel Op_eq_int.

Lemma Op_eq_op_int_subproof (n m : int) :
  (n == m) = Z.eqb (Z_of_int n) (Z_of_int m).
Proof. case: n m => ? [] ? //; rewrite /eq_op [LHS]/= /eq_op [LHS]/=; lia. Qed.

Instance Op_eq_op_int : BinOp (@eq_op int_eqType : int -> int -> bool) :=
 { TBOp := Z.eqb; TBOpInj := Op_eq_op_int_subproof }.
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
  {| TCst := 1%Z; TCstInj := erefl (Z_of_int 1%R) |}.
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

Instance Op_int_intmul : BinOp ( *~%R%R : int -> int -> int) :=
 { TBOp := Z.mul; TBOpInj := Op_int_intmul_subproof }.
Add BinOp Op_int_intmul.

Lemma Op_int_natmul_subproof n m :
  Z_of_int (n *+ m) = (Z_of_int n * Z_of_nat m)%Z.
Proof. rewrite pmulrn mulrzz; lia. Qed.

Instance Op_int_natmul : BinOp (@GRing.natmul _ : int -> nat -> int) :=
   { TBOp := Z.mul; TBOpInj := Op_int_natmul_subproof }.
Add BinOp Op_int_natmul.

Lemma Op_int_scale_subproof (n : int) (m : int^o) :
  Z_of_int (n *: m) = (Z_of_int n * Z_of_int m)%Z.
Proof. rewrite /GRing.scale /=; lia. Qed.

Instance Op_int_scale : BinOp (@GRing.scale _ [lmodType int of int^o]) :=
  Op_mulz.
Add BinOp Op_int_scale.

Lemma Op_int_exp_subproof n m :
  Z_of_int (n ^+ m) = (Z_of_int n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia. Qed.

Instance Op_int_exp : BinOp (@GRing.exp _ : int -> nat -> int) :=
  { TBOp := Z.pow; TBOpInj := Op_int_exp_subproof }.
Add BinOp Op_int_exp.

Instance Op_invz : UnOp intUnitRing.invz :=
  {| TUOp := id; TUOpInj := fun => erefl |}.
Add UnOp Op_invz.

Instance Op_int_inv : UnOp GRing.inv := Op_invz.
Add UnOp Op_int_inv.

Instance Op_absz : UnOp absz :=
  { TUOp := Z.abs; TUOpInj := ltac:(case=> ? /=; lia) }.
Add UnOp Op_absz.

Instance Op_int_normr : UnOp (Num.norm: int -> int) :=
  { TUOp := Z.abs; TUOpInj := ltac:(rewrite /Num.norm /=; lia) }.
Add UnOp Op_int_normr.

Instance Op_lez : BinOp intOrdered.lez :=
  { TBOp := Z.leb; TBOpInj := ltac:(case=> ? [] ? /=; lia) }.
Add BinOp Op_lez.

Instance Op_int_ler : BinOp Num.le := Op_lez.
Add BinOp Op_int_ler.

Instance Op_ltz : BinOp intOrdered.ltz :=
  { TBOp := Z.ltb; TBOpInj := ltac:(case=> ? [] ? /=; lia) }.
Add BinOp Op_ltz.

Instance Op_int_ltr : BinOp Num.lt := Op_ltz.
Add BinOp Op_int_ltr.

(* missing: *)
(* Print Num.Def.lerif. *)

Lemma Op_int_sgr_subproof n : Z_of_int (Num.sg n) = Z.sgn (Z_of_int n).
Proof. by case: n => [[]|n] //=; rewrite addn1. Qed.

Instance Op_int_sgr : UnOp (Num.sg: int -> int) :=
  { TUOp := Z.sgn; TUOpInj := Op_int_sgr_subproof }.
Add UnOp Op_int_sgr.

Instance Op_int_sgz : UnOp (@sgz _) := Op_int_sgr.
Add UnOp Op_int_sgz.

Lemma Op_int_min_subproof n m :
  Z_of_int (Num.min n m) = Z.min (Z_of_int n) (Z_of_int m).
Proof. case: leP; lia. Qed.

Instance Op_int_min : BinOp (Num.min : int -> int -> int) :=
  { TBOp := Z.min; TBOpInj := Op_int_min_subproof }.
Add BinOp Op_int_min.

Lemma Op_int_max_subproof n m :
  Z_of_int (Num.max n m) = Z.max (Z_of_int n) (Z_of_int m).
Proof. case: leP; lia. Qed.

Instance Op_int_max : BinOp (Num.max: int -> int -> int) :=
  { TBOp := Z.max; TBOpInj := Op_int_max_subproof }.
Add BinOp Op_int_max.

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
Add UnOp Op_int_of_Z.

Lemma Z_of_intK : cancel Z_of_int int_of_Z. Proof. move=> ?; lia. Qed.

(******************************************************************************)
(* intdiv                                                                     *)
(******************************************************************************)

Definition divZ (n m : Z) : Z := Z_of_int (divz (int_of_Z n) (int_of_Z m)).
Definition modZ (n m : Z) : Z := Z_of_int (modz (int_of_Z n) (int_of_Z m)).

Instance Op_divZ : BinOp divZ := { TBOp := divZ; TBOpInj := fun _ _ => erefl }.
Add BinOp Op_divZ.

Instance Op_modZ : BinOp modZ := { TBOp := modZ; TBOpInj := fun _ _ => erefl }.
Add BinOp Op_modZ.

Lemma Op_divz_subproof n m :
  Z_of_int (divz n m) = divZ (Z_of_int n) (Z_of_int m).
Proof. by rewrite /divZ !Z_of_intK. Qed.

Instance Op_divz : BinOp (divz: int -> int -> int) :=
  { TBOp := divZ; TBOpInj := Op_divz_subproof }.
Add BinOp Op_divz.

Lemma Op_modz_subproof n m :
  Z_of_int (modz n m) = modZ (Z_of_int n) (Z_of_int m).
Proof. by rewrite /modZ !Z_of_intK. Qed.

Instance Op_modz : BinOp modz :=
  {| TBOp := modZ; TBOpInj := Op_modz_subproof |}.
Add BinOp Op_modz.

Lemma Op_dvdz_subproof (n m : int) :
  dvdz n m = Z.eqb (modZ (Z_of_int m) (Z_of_int n)) 0%Z.
Proof. apply/dvdz_mod0P/idP; lia. Qed.

Instance Op_dvdz : BinOp dvdz :=
  {| TBOp := fun n m => Z.eqb (modZ m n) 0%Z; TBOpInj := Op_dvdz_subproof |}.
Add BinOp Op_dvdz.

Lemma divZ_spec_subproof n m :
  (0 < m -> divZ n m * m <= n < (divZ n m + 1) * m)%Z /\
  (m < 0 -> divZ n m * m <= n < (divZ n m - 1) * m)%Z /\
  (m = 0 -> divZ n m = 0)%Z.
Proof.
suff: let n := int_of_Z n in
      let m := int_of_Z m in
      [/\ 0 < m -> divz n m * m <= n < (divz n m + 1) * m,
          m < 0 -> divz n m * m <= n < (divz n m - 1) * m
        & m = 0 -> divz n m = 0]%R
  by case=> hpos hneg h0; split => [{hneg h0}|{hpos}]; lia.
move: (int_of_Z n) (int_of_Z m) => {}n {}m /=; split => hm.
- rewrite -(addr0 (_ * m)%R) mulrDl mul1r {2 3}(divz_eq n m).
  rewrite ler_add2l ltr_add2l ltz_pmod // modz_ge0; lia.
- rewrite -(addr0 (divz _ _ * _)%R) mulrDl mulN1r {2 3}(divz_eq n m).
  rewrite ler_add2l ltr_add2l -modzN ltz_pmod ?modz_ge0; lia.
- by rewrite hm divz0.
Qed.

Instance divZ_spec : BinOpSpec divZ :=
  {| BPred := fun n m r => (0 < m -> r * m <= n < (r + 1) * m)%Z /\
                           (m < 0 -> r * m <= n < (r - 1) * m)%Z /\
                           (m = 0 -> r = 0)%Z;
     BSpec := divZ_spec_subproof |}.
Add BinOpSpec divZ_spec.

Lemma modZ_spec_subproof n m :
  (n = divZ n m * m + modZ n m /\
   (0 < m -> 0 <= modZ n m < m) /\
   (m < 0 -> 0 <= modZ n m < - m) /\
   (m = 0 -> modZ n m = n))%Z.
Proof.
have: let n := int_of_Z n in
      let m := int_of_Z m in
      [/\ n = divz n m * m + modz n m,
          0 < m -> 0 <= modz n m < m, m < 0 -> 0 <= modz n m < - m
        & m = 0 -> modz n m = n]%R
  by rewrite /= -divz_eq /modz; split; lia.
case=> hn hpos hneg h0;
  split => [{hpos hneg h0}|{hn}]; last split => [{hneg h0}|{hpos}]; lia.
Qed.

Instance modZ_spec : BinOpSpec modZ :=
  {| BPred := (fun n m r =>
                 n = divZ n m * m + r /\
                 (0 < m -> 0 <= r < m) /\
                 (m < 0 -> 0 <= r < - m) /\
                 (m = 0 -> r = n))%Z;
     BSpec := modZ_spec_subproof |}.
Add BinOpSpec modZ_spec.
Add BinOpSpec divZ_spec. (* workaround *)

(******************************************************************************)
(* natdiv                                                                     *)
(******************************************************************************)

Lemma Op_divn_subproof n m :
  Z.of_nat (n %/ m) = divZ (Z.of_nat n) (Z.of_nat m).
Proof.
rewrite /divZ -!/(Z_of_int (Posz _)) !Z_of_intK /divz /=.
by case: m => //= m; rewrite mul1n.
Qed.

Instance Op_divn : BinOp divn :=
  {| TBOp := divZ; TBOpInj := Op_divn_subproof |}.
Add BinOp Op_divn.

Lemma Op_modn_subproof n m :
  Z.of_nat (n %% m) = modZ (Z_of_int n) (Z_of_int m).
Proof. by rewrite /modZ !Z_of_intK modz_nat. Qed.

Instance Op_modn : BinOp modn :=
  {| TBOp := modZ; TBOpInj := Op_modn_subproof |}.
Add BinOp Op_modn.

Lemma Op_dvdn_subproof n m :
  inj (n %| m) = Z.eqb (modZ (Z_of_nat m) (Z_of_nat n)) 0%Z.
Proof. rewrite /= /dvdn; lia. Qed.

Instance Op_dvdn : BinOp dvdn :=
  {| TBOp := fun x y => Z.eqb (modZ y x) 0%Z; TBOpInj := Op_dvdn_subproof |}.
Add BinOp Op_dvdn.

Lemma Op_odd_subproof n : inj (odd n) = Z.eqb (modZ (Z_of_nat n) 2) 1%Z.
Proof. case: odd (modn2 n) => /=; lia. Qed.

Instance Op_odd : UnOp odd :=
  {| TUOp := fun x => Z.eqb (modZ x 2) 1%Z; TUOpInj := Op_odd_subproof |}.
Add UnOp Op_odd.

Lemma Op_half_subproof n : Z.of_nat n./2 = divZ (Z.of_nat n) 2.
Proof. rewrite -divn2; lia. Qed.

Instance Op_half : UnOp half :=
  {| TUOp := fun x => divZ x 2; TUOpInj := Op_half_subproof |}.
Add UnOp Op_half.

Lemma Op_uphalf_subproof n :
  Z.of_nat (uphalf n) = divZ (Z.of_nat n + 1)%Z 2.
Proof. rewrite uphalf_half; lia. Qed.

Instance Op_uphalf : UnOp uphalf :=
  {| TUOp := fun x => divZ (x + 1)%Z 2; TUOpInj := Op_uphalf_subproof |}.
Add UnOp Op_uphalf.

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
  inj (coprime n m) = Z.eqb (Z.gcd (Z.of_nat n) (Z.of_nat m)) 1%Z.
Proof. rewrite /= /coprime; lia. Qed.

Instance Op_coprime : BinOp coprime :=
  {| TBOp := fun x y => Z.eqb (Z.gcd x y) 1%Z;
     TBOpInj := Op_coprime_subproof |}.
Add BinOp Op_coprime.

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
  coprimez n m = Z.eqb (Z.gcd (Z_of_int n) (Z_of_int m)) 1%Z.
Proof. rewrite /= /coprimez; lia. Qed.

Instance Op_coprimez : BinOp coprimez :=
  {| TBOp := fun x y => Z.eqb (Z.gcd x y) 1%Z;
     TBOpInj := Op_coprimez_subproof |}.
Add BinOp Op_coprimez.

(* missing: definitions in prime and binomial *)

End MathcompZifyInstances.

Module Export Exports.
Import MathcompZifyInstances.
Add BinOp Op_addb.
Add BinOp Op_eqb.
Add BinOp Op_eq_op_bool.
Add BinOp Op_eqn.
Add BinOp Op_eq_op_nat.
Add BinOp Op_addn_rec.
Add BinOp Op_addn.
Add BinOp Op_subn_rec.
Add BinOp Op_subn.
Add BinOp Op_muln_rec.
Add BinOp Op_muln.
Add BinOp Op_leq.
Add BinOp Op_geq.
Add BinOp Op_ltn.
Add BinOp Op_gtn.
Add BinOp Op_minn.
Add BinOp Op_maxn.
Add UnOp Op_nat_of_bool.
Add UnOp Op_double.
Add BinOp Op_expn_rec.
Add BinOp Op_expn.
Add InjTyp Inj_int_Z.
Add UnOp Op_Z_of_int.
Add UnOp Op_Posz.
Add UnOp Op_Negz.
Add BinRel Op_eq_int.
Add BinOp Op_eq_op_int.
Add CstOp Op_0_int.
Add BinOp Op_addz.
Add BinOp Op_add_int.
Add UnOp Op_oppz.
Add UnOp Op_opp_int.
Add CstOp Op_1_int.
Add BinOp Op_mulz.
Add BinOp Op_mulr_int.
Add BinOp Op_int_intmul.
Add BinOp Op_int_natmul.
Add BinOp Op_int_scale.
Add BinOp Op_int_exp.
Add UnOp Op_invz.
Add UnOp Op_int_inv.
Add UnOp Op_absz.
Add UnOp Op_int_normr.
Add BinOp Op_lez.
Add BinOp Op_int_ler.
Add BinOp Op_ltz.
Add BinOp Op_int_ltr.
Add UnOp Op_int_sgr.
Add UnOp Op_int_sgz.
Add BinOp Op_int_min.
Add BinOp Op_int_max.
Add UnOp Op_int_of_Z.
Add BinOp Op_divZ.
Add BinOp Op_modZ.
Add BinOp Op_divz.
Add BinOp Op_modz.
Add BinOp Op_dvdz.
Add BinOpSpec modZ_spec.
Add BinOpSpec divZ_spec.
Add BinOp Op_divn.
Add BinOp Op_modn.
Add BinOp Op_dvdn.
Add UnOp Op_odd.
Add UnOp Op_half.
Add UnOp Op_uphalf.
Add BinOp Op_gcdn.
Add BinOp Op_lcmn.
Add BinOp Op_coprime.
Add BinOp Op_gcdz.
Add BinOp Op_coprimez.
End Exports.

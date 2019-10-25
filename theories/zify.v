From Coq Require Import ZArith ZifyClasses Zify ZifyBool Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import binomial ssralg countalg ssrnum ssrint rat.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Module zify.

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

Instance Op_implb : BinOp implb := (* missing in ZifyBool *)
  { TBOp := fun x y => Z.max (Z.sub (Zpos xH) x) y;
    TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_implb.

Instance Op_addb : BinOp addb :=
  { TBOp := fun x y => Z.max (Z.sub x y) (Z.sub y x);
    TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_addb.

Instance Op_eqb : BinOp eqb :=
  { TBOp := fun x y => isZero (Z.sub x y);
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

Instance Op_eqn : BinOp eqn := Op_nat_eqb.
Add BinOp Op_eqn.

Instance Op_eq_op_nat : BinOp (@eq_op nat_eqType) := Op_eqn.
Add BinOp Op_eq_op_nat.

Lemma nat_lebE n m : (n <= m) = Nat.leb n m.
Proof. by elim: n m => // n ih [|m] //=; rewrite -ih. Qed.

Instance Op_leq : BinOp leq :=
  { TBOp := fun x y => isLeZero (Z.sub x y);
    TBOpInj := ltac:(move=> *; rewrite nat_lebE /=; lia) }.
Add BinOp Op_leq.

Instance Op_geq : BinOp geq :=
  { TBOp := fun x y => isLeZero (Z.sub y x);
    TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_geq.

Instance Op_ltn : BinOp ltn :=
  { TBOp := fun x y => isLeZero (Z.sub (Z.add x (Zpos xH)) y);
    TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_ltn.

Instance Op_gtn : BinOp gtn :=
  { TBOp := fun x y => isLeZero (Z.sub (Z.add y (Zpos xH)) x);
    TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_gtn.

Lemma Op_minn_subproof n m :
  Z.of_nat (minn n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. rewrite /minn /=; case: leqP; rewrite /is_true; lia. Qed.

Instance Op_minn : BinOp minn :=
  {| TBOp := Z.min; TBOpInj := Op_minn_subproof |}.
Add BinOp Op_minn.

Lemma Op_maxn_subproof n m :
  Z.of_nat (maxn n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. rewrite /maxn /=; case: leqP; rewrite /is_true; lia. Qed.

Instance Op_maxn : BinOp maxn :=
  {| TBOp := Z.max; TBOpInj := Op_maxn_subproof |}.
Add BinOp Op_maxn.

Lemma Z_of_nat_of_boolE (b : bool) : Z.of_nat b = Z_of_bool b.
Proof. by case: b. Qed.

Instance Op_nat_of_bool : UnOp nat_of_bool :=
  {| TUOp := fun x => x; TUOpInj := Z_of_nat_of_boolE |}.
Add UnOp Op_nat_of_bool.

Lemma Op_double_subproof n :
  Z.of_nat n.*2 = Z.mul (Z.of_nat n) 2.
Proof. rewrite -muln2 /=; lia. Qed.

Instance Op_double : UnOp double :=
  {| TUOp := fun x => Z.mul x 2;
     TUOpInj := Op_double_subproof |}.
Add UnOp Op_double.

(* missing (but cannot be handled by Micromega): *)
(* Print expn_rec. *)
(* Print expn. *)
(* Print fact_rec. *)
(* Print factorial. *)

(******************************************************************************)
(* natdiv                                                                     *)
(******************************************************************************)

Lemma Op_divn_subproof n m :
  Z.of_nat (n %/ m) = Z.div (Z.of_nat n) (Z.of_nat m).
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

Lemma Op_odd_subproof n : Z_of_bool (odd n) = Z.modulo (Z.of_nat n) 2.
Proof. rewrite -Z_of_nat_of_boolE -modn2; lia. Qed.

Instance Op_odd : UnOp odd :=
  {| TUOp := fun x => Z.modulo x 2; TUOpInj := Op_odd_subproof |}.

Lemma Op_half_subproof n : Z.of_nat n./2 = Z.div (Z.of_nat n) 2.
Proof. rewrite -divn2; lia. Qed.

Instance Op_half : UnOp half :=
  {| TUOp := fun x => Z.div x 2; TUOpInj := Op_half_subproof |}.

End zify.

From Coq Require Import BinInt Zify.
From mathcomp Require Import all_ssreflect zify ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* FIXME: dual instances are not exported *)
Import Order.Theory.

Local Delimit Scope Z_scope with Z.

Implicit Types (b : bool) (n m : nat).

(******************************************************************************)
(* ssrbool                                                                    *)
(******************************************************************************)

Fact test_andb b1 b2 : b1 (+) b2 = Bool.eqb b1 (~~ b2).
Proof. zify_op; reflexivity. Qed.

Fact test_eqb b1 b2 : eqb b1 b2 = Bool.eqb b1 b2.
Proof. zify_op; reflexivity. Qed.

Fact test_eq_op_bool b1 b2 : (b1 == b2) = Bool.eqb b1 b2.
Proof. zify_op; reflexivity. Qed.

Fact test_le_bool b1 b2 : (b1 <= b2)%O = implb b1 b2.
Proof. zify_op; reflexivity. Qed.

Fact test_ge_bool b1 b2 : (b1 >= b2)%O = implb b2 b1.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_le_bool (b1 b2 : bool^d) : (b1 <=^d b2)%O = implb b2 b1.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_ge_bool (b1 b2 : bool^d) : (b1 >=^d b2)%O = implb b1 b2.
Proof. zify_op; reflexivity. Qed.

Fact test_lt_bool b1 b2 : (b1 < b2)%O = ~~ b1 && b2.
Proof. zify_op; reflexivity. Qed.

Fact test_gt_bool b1 b2 : (b1 > b2)%O = ~~ b2 && b1.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_lt_bool (b1 b2 : bool^d) : (b1 <^d b2)%O = b1 && ~~ b2.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_gt_bool (b1 b2 : bool^d) : (b1 >^d b2)%O = b2 && ~~ b1.
Proof. zify_op; reflexivity. Qed.

(* FIXME: ge, gt *)

Fact test_min_bool b1 b2 : Order.min b1 b2 = b1 && b2.
Proof. zify_op; reflexivity. Qed.

Fact test_max_bool b1 b2 : Order.max b1 b2 = b1 || b2.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_min_bool (b1 b2 : bool^d) : Order.dual_min b1 b2 = b1 || b2.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_max_bool (b1 b2 : bool^d) : Order.dual_max b1 b2 = b1 && b2.
Proof. zify_op; reflexivity. Qed.

(* FIXME: meet and join below are broken but the tests pass because they are  *)
(* convertible anyway.                                                        *)
Fact test_meet_bool b1 b2 : (b1 `&` b2)%O = b1 && b2.
Proof. zify_op; reflexivity. Qed.

Fact test_join_bool b1 b2 : (b1 `|` b2)%O = b1 || b2.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_meet_bool (b1 b2 : bool^d) : (b1 `&^d` b2)%O = b1 || b2.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_join_bool (b1 b2 : bool^d) : (b1 `|^d` b2)%O = b1 && b2.
Proof. zify_op; reflexivity. Qed.

Fact test_bottom_bool : \bot%O = false :> bool.
Proof. zify_op; reflexivity. Qed.

Fact test_top_bool : \top%O = true :> bool.
Proof. zify_op; reflexivity. Qed.

(* FIXME: Notations 0^d and 1^d are broken. *)
Fact test_dual_bottom_bool : \bot%O = true :> bool^d.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_top_bool : \top%O = false :> bool^d.
Proof. zify_op; reflexivity. Qed.

Fact test_sub_bool b1 b2 : (b1 `\` b2)%O = b1 && ~~ b2.
Proof. zify_op; reflexivity. Qed.

Fact test_compl_bool b : (~` b)%O = ~~ b.
Proof. zify_op; reflexivity. Qed.

(******************************************************************************)
(* ssrnat                                                                     *)
(******************************************************************************)

Fact test_eqn n m : eqn n m = Z.eqb (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_eq_op_nat n m : (n == m) = Z.eqb (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_addn n m : Z.of_nat (n + m) = (Z.of_nat n + Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_addn_trec n m :
  Z.of_nat (NatTrec.add n m) = (Z.of_nat n + Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_subn n m :
  Z.of_nat (n - m) = Z.max 0 (Z.of_nat n - Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_muln n m : Z.of_nat (n * m) = (Z.of_nat n * Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_muln_trec n m :
  Z.of_nat (NatTrec.mul n m) = (Z.of_nat n * Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_leq n m : (n <= m) = (Z.of_nat n <=? Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

(* FIXME: geq, ltn, gtn *)

Fact test_minn n m : Z.of_nat (minn n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_maxn n m : Z.of_nat (maxn n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_nat_of_bool b : Z.of_nat (nat_of_bool b) = Z.b2z b.
Proof. zify_op; reflexivity. Qed.

Fact test_double n : Z.of_nat n.*2 = (2 * Z.of_nat n)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_double_trec n : Z.of_nat (NatTrec.double n) = (2 * Z.of_nat n)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_expn n m : Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_expn_trec n m :
  Z.of_nat (NatTrec.exp n m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_eq_op_N (n m : N) : (n == m) = (Z.of_N n =? Z.of_N m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_nat_of_pos p : Z.of_nat (nat_of_pos p) = Z.pos p.
Proof. zify_op; reflexivity. Qed.

Fact test_nat_of_bin (n : N) : Z.of_nat (nat_of_bin n) = Z.of_N n.
Proof. zify_op; reflexivity. Qed.

Fact test_pos_of_nat n m :
  Z.pos (pos_of_nat n m) = Z.max 1 (Z.of_nat n * 2 - Z.of_nat m + 1).
Proof. zify_op; reflexivity. Qed.

Fact test_bin_of_nat n : Z.of_N (bin_of_nat n) = Z.of_nat n.
Proof. zify_op; reflexivity. Qed.

Fact test_le_nat n m : (n <= m)%O = (Z.of_nat n <=? Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_ge_nat n m : (n >= m)%O = (Z.of_nat m <=? Z.of_nat n)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_le_nat (n m : nat^d) :
  (n <=^d m)%O = (Z.of_nat n >=? Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_ge_nat (n m : nat^d) :
  (n >=^d m)%O = (Z.of_nat m >=? Z.of_nat n)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_lt_nat n m : (n < m)%O = (Z.of_nat n <? Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_gt_nat n m : (n > m)%O = (Z.of_nat m <? Z.of_nat n)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_lt_nat (n m : nat^d) :
  (n <^d m)%O = (Z.of_nat n >? Z.of_nat m)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_gt_nat (n m : nat^d) :
  (n >^d m)%O = (Z.of_nat m >? Z.of_nat n)%Z.
Proof. zify_op; reflexivity. Qed.

(* FIXME: ge, gt *)

Fact test_min_nat n m :
  Z.of_nat (Order.min n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_max_nat n m :
  Z.of_nat (Order.max n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_dual_min_nat (n m : nat^d) :
  Z.of_nat (Order.dual_min n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_dual_max_nat (n m : nat^d) :
  Z.of_nat (Order.dual_max n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_meet_nat n m : Z.of_nat (n `&` m)%O = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_join_nat n m : Z.of_nat (n `|` m)%O = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_dual_meet_nat (n m : nat^d) :
  Z.of_nat (n `&^d` m)%O = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_dual_join_nat (n m : nat^d) :
  Z.of_nat (n `|^d` m)%O = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_bottom_nat : Z.of_nat \bot%O = 0%Z.
Proof. zify_op; reflexivity. Qed.

(******************************************************************************)
(* div (divn, modn, dvdn, gcdn, lcmn, and coprime)                            *)
(******************************************************************************)

Notation divZ := zify_ssreflect.SsreflectZifyInstances.divZ.
Notation modZ := zify_ssreflect.SsreflectZifyInstances.modZ.

Fact test_divn n m : Z.of_nat (divn n m) = divZ (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_modn n m : Z.of_nat (modn n m) = modZ (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_dvdn n m : dvdn n m = (modZ (Z.of_nat m) (Z.of_nat n) =? 0)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_odd n : odd n = (modZ (Z.of_nat n) 2 =? 1)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_odd_trec n : NatTrec.odd n = (modZ (Z.of_nat n) 2 =? 1)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_half n : Z.of_nat (half n) = divZ (Z.of_nat n) 2.
Proof. zify_op; reflexivity. Qed.

Fact test_uphalf n : Z.of_nat (uphalf n) = divZ (Z.of_nat n + 1) 2.
Proof. zify_op; reflexivity. Qed.

Fact test_gcdn n m : Z.of_nat (gcdn n m) = Z.gcd (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_lcmn n m : Z.of_nat (lcmn n m) = Z.lcm (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_coprime n m : coprime n m = (Z.gcd (Z.of_nat n) (Z.of_nat m) =? 1)%Z.
Proof. zify_op; reflexivity. Qed.

(******************************************************************************)
(* natdvd in order.v                                                          *)
(******************************************************************************)

Fact test_le_natdvd (n m : natdvd) :
  (n <= m)%O = (modZ (Z.of_nat m) (Z.of_nat n) =? 0)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_lt_natdvd (n m : natdvd) :
  (n < m)%O =
    ~~ (Z.of_nat m =? Z.of_nat n)%Z && (modZ (Z.of_nat m) (Z.of_nat n) =? 0)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_le_natdvd (n m : natdvd^d) :
  (m <= n)%O = (modZ (Z.of_nat m) (Z.of_nat n) =? 0)%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_lt_natdvd (n m : natdvd^d) :
  (m < n)%O =
    ~~ (Z.of_nat m =? Z.of_nat n)%Z && (modZ (Z.of_nat m) (Z.of_nat n) =? 0)%Z.
Proof. zify_op; reflexivity. Qed.

(* FIXME: ge, gt *)

Fact test_meet_natdvd (n m : natdvd) :
  Z.of_nat (n `&` m)%O = Z.gcd (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_join_natdvd (n m : natdvd) :
  Z.of_nat (n `|` m)%O = Z.lcm (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_dual_meet_natdvd (n m : natdvd^d) :
  Z.of_nat (n `&` m)%O = Z.lcm (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_dual_join_natdvd (n m : natdvd^d) :
  Z.of_nat (n `|` m)%O = Z.gcd (Z.of_nat n) (Z.of_nat m).
Proof. zify_op; reflexivity. Qed.

Fact test_bottom_natdvd : Z.of_nat (\bot%O : natdvd) = 1%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_top_natdvd : Z.of_nat (\top%O : natdvd) = 0%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_bottom_natdvd : Z.of_nat (\bot^d%O : natdvd^d) = 0%Z.
Proof. zify_op; reflexivity. Qed.

Fact test_dual_top_natdvd : Z.of_nat (\top^d%O : natdvd^d) = 1%Z.
Proof. zify_op; reflexivity. Qed.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import binomial ssralg countalg ssrnum ssrint rat intdiv.
From mathcomp Require Import zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma odd_add (n m : nat) : odd (m + n) = odd m (+) odd n.
Proof. lia. Qed.

Lemma dvdz_lcm_6_4 (m : int) : (6 %| m -> 4 %| m -> 12 %| m)%Z.
Proof. lia. Qed.

Lemma dvdz_lcm_6_4' (m : int) : (6 %| m)%Z && (4 %| m)%Z = (12 %| m)%Z.
Proof. lia. Qed.

Lemma divzMA_ge0 (m n p : int) :
  (0 <= n)%R -> (m %/ (n * p))%Z = ((m %/ n) %/ p)%Z.
Proof. nia. Qed.

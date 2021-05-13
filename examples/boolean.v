From mathcomp Require Import all_ssreflect zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma odd_add (n m : nat) : odd (m + n) = odd m (+) odd n.
Proof. lia. Qed.

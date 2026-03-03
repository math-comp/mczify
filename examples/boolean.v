From mathcomp Require Import all_ssreflect zify.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma odd_add (n m : nat) : odd (m + n) = odd m (+) odd n.
Proof. lia. Qed.

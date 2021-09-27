From mathcomp Require Import all_ssreflect zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma zagierK x y z : 0 < x -> 0 < z -> 
  let zagier t :=
    let: (x, y, z) := t in
    if x < y - z then (x + z.*2, z, y - z - x)
    else if x < y.*2 then (y.*2 - x, y, x + z - y)
    else (x - y.*2, x + z - y, y) in
  zagier (zagier (x, y, z)) = (x, y, z).
Proof.
move=> xP zP /=.
repeat case: leqP => *; congr (_,_,_); lia.
Qed.

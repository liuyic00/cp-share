From Stdlib Require Import ZArith Lia Zmod.Bits.
Open Scope Z_scope.

Lemma bit_cases (x : bits 1) : x=Zmod.zero \/ x=Zmod.one.
Proof.
  pose proof (bits.unsigned_range x ltac:(lia)) as bound.
  change (0 <= Zmod.unsigned x < 2) in bound.
  assert (cases : Zmod.unsigned x=0 \/ Zmod.unsigned x=1) by lia.
  destruct cases as [zero|one].
  - left; apply Zmod.to_Z_inj; rewrite Zmod.unsigned_0; exact zero.
  - right; apply Zmod.to_Z_inj; rewrite bits.unsigned_1 by lia; exact one.
Qed.
Print Assumptions bit_cases.

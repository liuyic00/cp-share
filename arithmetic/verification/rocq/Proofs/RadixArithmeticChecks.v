From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import Words RadixControl RadixBalance RadixDatapath.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixBalance.RadixBalance RadixDatapath.RadixDatapath.
Open Scope Z_scope.
Module RadixArithmeticChecks.
Definition arithmeticChecks s i := forallb (fun b => b) (firstn 5 (assertionChecks s i)) = true.
Lemma sufficient s i
  (zero : v416 s i = 0 \/ (v414 s i = 1 /\ v418 s i = 1))
  (nonzero : v421 s i = 0 \/ (v419 s i = 1 /\ v430 s i = 1 /\ v431 s i = 1)) :
  arithmeticChecks s i.
Proof.
  unfold arithmeticChecks, assertionChecks; cbn [firstn forallb].
  destruct zero as [z|[z1 z2]]; destruct nonzero as [n|[n1 [n2 n3]]];
    rewrite ?z, ?z1, ?z2, ?n, ?n1, ?n2, ?n3;
    cbn [Z.eqb negb]; rewrite ?Bool.orb_true_r; reflexivity.
Qed.
Lemma widened_identity s i
  (identity : v40 s i * word 64 (r5_nbReg s) + v402 s i = v417 s i) : v430 s i = 1.
Proof.
  assert (hq : 0 <= v40 s i < 2^64) by (unfold v40; apply bounds; lia).
  assert (hb : 0 <= word 64 (r5_nbReg s) < 2^64) by (apply bounds; lia).
  assert (hr : 0 <= v402 s i < 2^64) by (unfold v402; apply bounds; lia).
  assert (ha : 0 <= v417 s i < 2^64) by (unfold v417; apply bounds; lia).
  assert (qnorm : word 128 (v40 s i) = v40 s i).
  { apply small; split; [lia | eapply Z.lt_le_trans; [exact (proj2 hq) | apply Z.pow_le_mono_r; lia]]. }
  assert (rnorm : word 129 (v402 s i) = v402 s i).
  { apply small; split; [lia | eapply Z.lt_le_trans; [exact (proj2 hr) | apply Z.pow_le_mono_r; lia]]. }
  assert (product : word 128 (v40 s i*word 64 (r5_nbReg s)) = v40 s i*word 64 (r5_nbReg s)).
  { apply small; split; [nia | assert (2^64 <= 2^128) by (apply Z.pow_le_mono_r; lia); nia]. }
  assert (product129 : word 129 (v40 s i*word 64 (r5_nbReg s)) = v40 s i*word 64 (r5_nbReg s)).
  { apply small; split; [nia | assert (2^64 <= 2^129) by (apply Z.pow_le_mono_r; lia); nia]. }
  unfold v430, v428, v429, v427, v425, v424, v423, v422, v426, v26, v20.
  change (word 65 0) with 0; change (word 1 0) with 0; change (word 64 0) with 0.
  rewrite !Z.shiftl_0_l, !Z.add_0_l, qnorm, (widen 64 128) by lia.
  rewrite product, product129, rnorm, identity, Z.eqb_refl; reflexivity.
Qed.
Theorem arithmetic_checks_nonzero s i
  (flag : word 1 (r1_ndivBy0Reg s) = 0)
  (positive : 0 < word 64 (r5_nbReg s))
  (quotient : v40 s i = v417 s i / word 64 (r5_nbReg s))
  (remainder : v402 s i = v417 s i mod word 64 (r5_nbReg s)) : arithmeticChecks s i.
Proof.
  apply sufficient.
  - left; unfold v416; rewrite flag, Z.land_0_r, Z.land_0_l; reflexivity.
  - right; split.
    + unfold v419, v20; change (word 64 0) with 0.
      assert (h : (word 64 (r5_nbReg s) =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite h; reflexivity.
    + split.
      * apply widened_identity; rewrite quotient, remainder.
        pose proof (Z.div_mod (v417 s i) (word 64 (r5_nbReg s)) ltac:(lia)); nia.
      * unfold v431; rewrite remainder.
        assert (h : (v417 s i mod word 64 (r5_nbReg s) <? word 64 (r5_nbReg s)) = true).
        { apply Z.ltb_lt; pose proof (Z.mod_pos_bound (v417 s i) (word 64 (r5_nbReg s)) positive); lia. }
        rewrite h; reflexivity.
Qed.
Theorem arithmetic_checks_zero s i
  (flag : word 1 (r1_ndivBy0Reg s) = 1)
  (quotient : v40 s i = base-1) (remainder : v402 s i = v417 s i) : arithmeticChecks s i.
Proof.
  apply sufficient.
  - right; split.
    + unfold v414, v413; rewrite quotient; change (word 64 18446744073709551615) with (base-1); rewrite Z.eqb_refl; reflexivity.
    + unfold v418; rewrite remainder, Z.eqb_refl; reflexivity.
  - left; unfold v421, v420, v22; rewrite flag.
    change (word 1 (Z.lxor 1 (word 1 1))) with 0; rewrite Z.land_0_r, Z.land_0_l; reflexivity.
Qed.
Lemma inactive_valid s i (h : v399 s i = 0) : arithmeticChecks s i.
Proof.
  apply sufficient; left; [unfold v416 | unfold v421]; rewrite h, !Z.land_0_l; reflexivity.
Qed.
Lemma inactive_reset s i (h : word 1 (nreset i) = 1) : arithmeticChecks s i.
Proof.
  assert (off : v415 s i = 0) by (unfold v415, v22; rewrite h; reflexivity).
  apply sufficient; left; [unfold v416 | unfold v421]; rewrite off, Z.land_0_r; reflexivity.
Qed.
Theorem arithmetic_checks_inactive s i
  (inactive : word 3 (r0_nstate s) <> 4 \/ word 1 (nreset i) = 1) : arithmeticChecks s i.
Proof.
  destruct inactive as [h|h]; [apply inactive_valid | apply inactive_reset; exact h].
  unfold v399, v11; change (word 3 4) with 4.
  assert (off : (word 3 (r0_nstate s) =? 4) = false) by (apply Z.eqb_neq; exact h).
  rewrite off; reflexivity.
Qed.
End RadixArithmeticChecks.
Print Assumptions RadixArithmeticChecks.arithmetic_checks_nonzero.
Print Assumptions RadixArithmeticChecks.arithmetic_checks_zero.
Print Assumptions RadixArithmeticChecks.arithmetic_checks_inactive.

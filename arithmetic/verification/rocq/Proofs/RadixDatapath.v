From Coq Require Import ZArith Lia.
From Proofs Require Import Words WordBits RadixControl.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl.
Open Scope Z_scope.
Module RadixDatapath.
Definition candidate sh := word 65 (Z.shiftr (word 129 sh) 64).
Definition lowCandidate sh := word 64 (Z.shiftr (word 129 sh) 64).
Definition quotientBit sh d := if Z.leb (word 64 d) (candidate sh) then 1 else 0.
Definition reducedWord sh d := word 64
  (if Z.leb (word 64 d) (candidate sh) then lowCandidate sh - word 64 d else lowCandidate sh).
Definition restoringStep sh d := word 129
  (Z.shiftl (Z.shiftl (reducedWord sh d) 64 + word 64 (Z.shiftr (word 129 sh) 0)) 1 + quotientBit sh d).
Lemma widen w v x (hw : 0 <= w) (hv : w <= v) : word v (word w x) = word w x.
Proof. exact (Words.word_widen w v x hw hv). Qed.
Lemma compute_datapath s i (hs : word 3 (r0_nstate s) = 3) :
  r2_nshiftReg (step s i) = restoringStep (r2_nshiftReg s) (r5_nbReg s).
Proof.
  assert (h2 : v2 s i = 0) by (unfold v2, v1, v0; rewrite hs; reflexivity).
  assert (h4 : v4 s i = 0) by (unfold v4, v3; rewrite hs; reflexivity).
  assert (h6 : v6 s i = 0) by (unfold v6, v5; rewrite hs; reflexivity).
  assert (h8 : v8 s i = 1) by (unfold v8, v7; rewrite hs; reflexivity).
  assert (h25 : v25 s i = 0) by (unfold v25; rewrite h2, h4; reflexivity).
  cbn [step r2_nshiftReg]. unfold v44, v43, v42.
  rewrite h25, h6, h8; cbn [Z.eqb].
  unfold v41, v40, v39, v38, v37, v36, v35, v34, v33, v26.
  change (word 1 0) with 0; change (Z.shiftl 0 64) with 0; rewrite Z.add_0_l.
  repeat rewrite (widen 64 65) by lia.
  cbn [Z.eqb Pos.eqb].
  unfold restoringStep, reducedWord, quotientBit, candidate, lowCandidate.
  destruct (Z.leb (word 64 (r5_nbReg s)) (word 65 (Z.shiftr (word 129 (r2_nshiftReg s)) 64)));
    constants; cbn [Z.eqb Pos.eqb]; repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma compute_preserves_captured s i (hs : word 3 (r0_nstate s) = 3) :
  r5_nbReg (step s i) = word 64 (r5_nbReg s) /\
  r6_naValx2Reg (step s i) = word 65 (r6_naValx2Reg s) /\
  r3_naSignReg (step s i) = word 1 (r3_naSignReg s) /\
  r4_nqSignReg (step s i) = word 1 (r4_nqSignReg s) /\
  r7_nctrlReg_5FisW (step s i) = word 1 (r7_nctrlReg_5FisW s) /\
  r8_nctrlReg_5FisHi (step s i) = word 1 (r8_nctrlReg_5FisHi s) /\
  r1_ndivBy0Reg (step s i) = word 1 (r1_ndivBy0Reg s).
Proof.
  assert (h2 : v2 s i = 0) by (unfold v2, v1, v0; rewrite hs; reflexivity).
  cbn [step r5_nbReg r6_naValx2Reg r3_naSignReg r4_nqSignReg r7_nctrlReg_5FisW r8_nctrlReg_5FisHi r1_ndivBy0Reg].
  unfold v55, v59, v47, v52, v60, v61, v24; rewrite h2; cbn [Z.eqb].
  repeat rewrite normalize by lia; repeat split; reflexivity.
Qed.
Lemma lowCandidate_mod sh : lowCandidate sh = word 64 (candidate sh).
Proof.
  unfold lowCandidate, candidate.
  pose proof (WordBits.extract_normal 65 64 0 (Z.shiftr (word 129 sh) 64) ltac:(lia) ltac:(lia) ltac:(lia)) as h.
  rewrite !Z.shiftr_0_r in h; symmetry; exact h.
Qed.
Lemma sub_normal x y : word 64 (word 64 x - y) = word 64 (x-y).
Proof. unfold word; apply Zminus_mod_idemp_l. Qed.
Lemma selected_digit_correct sh d (positive : 0 < word 64 d)
  (bound : candidate sh < 2 * word 64 d) :
  candidate sh = quotientBit sh d * word 64 d + reducedWord sh d /\
  0 <= reducedWord sh d < word 64 d.
Proof.
  pose proof (Words.word_bound 64 d ltac:(lia)) as hd.
  change (0 <= word 64 d < 18446744073709551616) in hd.
  pose proof (Words.word_bound 65 (Z.shiftr (word 129 sh) 64) ltac:(lia)) as hc.
  change (0 <= candidate sh < 2^65) in hc.
  unfold quotientBit, reducedWord; rewrite lowCandidate_mod.
  destruct (Z.leb (word 64 d) (candidate sh)) eqn:h.
  - apply Z.leb_le in h.
    assert (heq : word 64 (word 64 (candidate sh) - word 64 d) = candidate sh - word 64 d).
    { rewrite sub_normal. apply Words.word_small.
      change (0 <= candidate sh - word 64 d < 18446744073709551616); lia. }
    rewrite heq; split; nia.
  - apply Z.leb_gt in h. rewrite normalize by lia.
    assert (heq : word 64 (candidate sh) = candidate sh).
    { apply Words.word_small.
      change (0 <= candidate sh < 18446744073709551616); lia. }
    rewrite heq; split; nia.
Qed.
End RadixDatapath.
Print Assumptions RadixDatapath.compute_datapath.
Print Assumptions RadixDatapath.selected_digit_correct.

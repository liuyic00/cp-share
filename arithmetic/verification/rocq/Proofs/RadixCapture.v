From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixBalance.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixBalance.RadixBalance.
Open Scope Z_scope.
Module RadixCapture.
Definition signBit x sign := word 1 (Z.land (word 1 (Z.shiftr (word 64 x) 63)) (word 1 sign)).
Definition magnitude x sign := word 64
  (if Z.eqb (signBit x sign) 1 then -word 64 x else word 64 x).
Lemma accepting s i (hs : word 3 (r0_nstate s) = 0)
  (hv : word 1 (nio_5Fin_5Fvalid i) = 1) : v2 s i = 1.
Proof. unfold v2, v1, v0; rewrite hs, hv; reflexivity. Qed.
Theorem capture_magnitudes s i (hs : word 3 (r0_nstate s) = 0)
  (hv : word 1 (nio_5Fin_5Fvalid i) = 1) :
  r6_naValx2Reg (step s i) = 2*magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i) /\
  r5_nbReg (step s i) = magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 i) (nctrl_5Fsign i).
Proof.
  pose proof (accepting s i hs hv) as h.
  assert (a : v57 s i = magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i)).
  { unfold v57, v56, v46, v45, v20, magnitude, signBit.
    change (word 64 0) with 0; rewrite Z.sub_0_l.
    destruct (word 1 (Z.land (word 1 (Z.shiftr (word 64 (nio_5Fin_5Fbits_5Fsrc_5F0 i)) 63)) (word 1 (nctrl_5Fsign i))) =? 1);
      repeat rewrite normalize by lia; reflexivity. }
  assert (b : v54 s i = magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 i) (nctrl_5Fsign i)).
  { unfold v54, v53, v49, v48, v20, magnitude, signBit.
    change (word 64 0) with 0; rewrite Z.sub_0_l.
    destruct (word 1 (Z.land (word 1 (Z.shiftr (word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 i)) 63)) (word 1 (nctrl_5Fsign i))) =? 1);
      repeat rewrite normalize by lia; reflexivity. }
  cbn [step r6_naValx2Reg r5_nbReg]. unfold v59, v55; rewrite h.
  change (word 65 (v58 s i) = 2*magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i) /\ word 64 (v54 s i) = magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 i) (nctrl_5Fsign i)).
  split.
  - unfold v58, v26; change (word 1 0) with 0; rewrite Z.add_0_r, normalize by lia.
    rewrite a, Z.shiftl_mul_pow2 by lia.
    rewrite small.
    + ring.
    + pose proof (bounds 64 (if signBit (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i) =? 1 then -word 64 (nio_5Fin_5Fbits_5Fsrc_5F0 i) else word 64 (nio_5Fin_5Fbits_5Fsrc_5F0 i)) ltac:(lia)) as ha.
      change (0 <= magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i) < 18446744073709551616) in ha.
      change (0 <= magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i)*2 < 36893488147419103232); lia.
  - rewrite b; unfold magnitude; apply normalize; lia.
Qed.
Lemma magnitude_zero x sign : magnitude x sign = 0 <-> word 64 x = 0.
Proof.
  unfold magnitude; destruct (signBit x sign =? 1).
  - destruct (Z.eq_dec (word 64 x) 0) as [hz|hn].
    + rewrite hz; split; reflexivity.
    + pose proof (bounds 64 x ltac:(lia)) as hb.
      assert (he : word 64 (-word 64 x) = 2^64-word 64 x).
      { unfold word; rewrite Z.mod_opp_l_nz by (try discriminate; rewrite Z.mod_mod by discriminate; exact hn).
        rewrite Z.mod_mod by discriminate; reflexivity. }
      rewrite he; split; [intro h; lia | contradiction].
  - rewrite normalize by lia; tauto.
Qed.
Theorem capture_zero_flag s i (hs : word 3 (r0_nstate s) = 0)
  (hv : word 1 (nio_5Fin_5Fvalid i) = 1) :
  (r1_ndivBy0Reg (step s i) = 1 <-> r5_nbReg (step s i) = 0).
Proof.
  destruct (capture_magnitudes s i hs hv) as [ha hb].
  rewrite hb, magnitude_zero.
  cbn [step r1_ndivBy0Reg]; unfold v24; rewrite (accepting s i hs hv).
  unfold v23, v21, v22, v20.
  change (word 64 0) with 0.
  destruct (word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 i) =? 0) eqn:h.
  - apply Z.eqb_eq in h; rewrite h; split; reflexivity.
  - apply Z.eqb_neq in h.
    change (0 = 1 <-> word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 i) = 0).
    split; [discriminate | contradiction].
Qed.
End RadixCapture.
Print Assumptions RadixCapture.capture_magnitudes.
Print Assumptions RadixCapture.capture_zero_flag.

From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixExecution RadixDatapath.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixExecution.RadixExecution.
Open Scope Z_scope.
Module RadixSetup.
Lemma busy_no_accept s i (hs : word 3 (r0_nstate s) <> 0) : v2 s i = 0.
Proof.
  unfold v2, v1, v0; change (word 3 0) with 0.
  assert (h : (word 3 (r0_nstate s) =? 0) = false) by (apply Z.eqb_neq; exact hs).
  rewrite h; reflexivity.
Qed.
Lemma busy_captured s i (hs : word 3 (r0_nstate s) <> 0) : captured (step s i) = captured s.
Proof.
  pose proof (busy_no_accept s i hs) as h.
  unfold captured; cbn [step r5_nbReg r6_naValx2Reg r3_naSignReg r4_nqSignReg r7_nctrlReg_5FisW r8_nctrlReg_5FisHi r1_ndivBy0Reg].
  unfold v55, v59, v47, v52, v60, v61, v24; rewrite h; cbn [Z.eqb].
  repeat rewrite normalize by lia; reflexivity.
Qed.
Theorem setup_captured s i j (hs : word 3 (r0_nstate s) = 1)
  (hr : word 1 (nreset i) = 0) :
  captured (step (step s i) j) = captured s.
Proof.
  rewrite busy_captured.
  - apply busy_captured; lia.
  - rewrite (log2_state s i hr hs); discriminate.
Qed.
Lemma log2_dividend s i (hs : word 3 (r0_nstate s) = 1) :
  r6_naValx2Reg (step s i) = word 65 (r6_naValx2Reg s).
Proof.
  cbn [step r6_naValx2Reg]; unfold v59.
  rewrite busy_no_accept by lia; cbn [Z.eqb]; apply normalize; lia.
Qed.
Lemma log2_zero_count s i (hs : word 3 (r0_nstate s) = 1)
  (hr : word 1 (nreset i) = 0) (flag : word 1 (r1_ndivBy0Reg s) = 1) :
  r9_ncnt_5Fvalue (step s i) = 0.
Proof.
  assert (h2 : v2 s i = 0) by (apply busy_no_accept; lia).
  assert (h4 : v4 s i = 1) by (unfold v4, v3; rewrite hs; reflexivity).
  cbn [step r9_ncnt_5Fvalue]; rewrite hr.
  unfold v398, v397, v391; rewrite h2, h4, flag; reflexivity.
Qed.
Lemma shift_count s i (hs : word 3 (r0_nstate s) = 2)
  (hr : word 1 (nreset i) = 0) :
  r9_ncnt_5Fvalue (step s i) = word 6 (r9_ncnt_5Fvalue s).
Proof.
  assert (h2 : v2 s i = 0) by (apply busy_no_accept; lia).
  assert (h4 : v4 s i = 0) by (unfold v4, v3; rewrite hs; reflexivity).
  assert (h6 : v6 s i = 1) by (unfold v6, v5; rewrite hs; reflexivity).
  assert (h8 : v8 s i = 0) by (unfold v8, v7; rewrite hs; reflexivity).
  cbn [step r9_ncnt_5Fvalue]; rewrite hr.
  unfold v398, v397, v396, v393, v392, v22; rewrite h2, h4, h6, h8.
  change (word 6 (word 6 (word 6 (word 6 (r9_ncnt_5Fvalue s)))) = word 6 (r9_ncnt_5Fvalue s)).
  repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma shift_zero_datapath s i (hs : word 3 (r0_nstate s) = 2)
  (hc : word 6 (r9_ncnt_5Fvalue s) = 0) :
  r2_nshiftReg (step s i) = word 65 (r6_naValx2Reg s).
Proof.
  assert (h2 : v2 s i = 0) by (apply busy_no_accept; lia).
  assert (h4 : v4 s i = 0) by (unfold v4, v3; rewrite hs; reflexivity).
  assert (h6 : v6 s i = 1) by (unfold v6, v5; rewrite hs; reflexivity).
  assert (h25 : v25 s i = 0) by (unfold v25; rewrite h2, h4; reflexivity).
  cbn [step r2_nshiftReg]; unfold v44, v43; rewrite h25, h6.
  change (word 129 (word 129 (v32 s i)) = word 65 (r6_naValx2Reg s)).
  unfold v32, v31, v30, v29, v28, v27, v26; rewrite hc.
  change (word 63 0) with 0; change (word 122 0) with 0; change (word 1 0) with 0.
  rewrite !Z.shiftl_0_l, !Z.add_0_l.
  change (word 128 0) with 0; rewrite Z.shiftl_0_r.
  repeat rewrite normalize by lia.
  rewrite (RadixDatapath.RadixDatapath.widen 65 128) by lia.
  apply RadixDatapath.RadixDatapath.widen; lia.
Qed.
Theorem zero_setup s i j (hs : word 3 (r0_nstate s) = 1)
  (flag : word 1 (r1_ndivBy0Reg s) = 1)
  (hr : word 1 (nreset i) = 0) (hj : word 1 (nreset j) = 0) :
  r9_ncnt_5Fvalue (step (step s i) j) = 0 /\
  r2_nshiftReg (step (step s i) j) = word 65 (r6_naValx2Reg s).
Proof.
  assert (hstate : word 3 (r0_nstate (step s i)) = 2) by (rewrite (log2_state s i hr hs); reflexivity).
  assert (hcount : word 6 (r9_ncnt_5Fvalue (step s i)) = 0) by (rewrite (log2_zero_count s i hs hr flag); reflexivity).
  split.
  - rewrite (shift_count (step s i) j hstate hj); exact hcount.
  - rewrite (shift_zero_datapath (step s i) j hstate hcount), (log2_dividend s i hs).
    apply normalize; lia.
Qed.
End RadixSetup.
Print Assumptions RadixSetup.setup_captured.
Print Assumptions RadixSetup.log2_zero_count.
Print Assumptions RadixSetup.zero_setup.

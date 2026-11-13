From Coq Require Import ZArith Lia.
From Proofs Require Import Words.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Open Scope Z_scope.
Module RadixControl.
Lemma normalize w x (hw : 0 <= w) : word w (word w x) = word w x.
Proof. exact (Words.word_idem w x hw). Qed.
Ltac constants :=
  repeat match goal with
  | |- context[word ?w ?x] => integer_literal w; integer_literal x;
      let y := eval vm_compute in (word w x) in change (word w x) with y
  end; cbn [Z.eqb Z.land].
Ltac control :=
  unfold v19, v18, v17, v16, v15, v14, v13, v12, v11,
    v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0;
  constants.
Lemma reset_idle s i (hr : word 1 (nreset i) = 1) :
  r0_nstate (step s i) = 0.
Proof. cbn [step r0_nstate]; rewrite hr; reflexivity. Qed.
Lemma accept_state s i (hr : word 1 (nreset i) = 0)
  (hs : word 3 (r0_nstate s) = 0)
  (hv : word 1 (nio_5Fin_5Fvalid i) = 1) :
  r0_nstate (step s i) = 1.
Proof. cbn [step r0_nstate]; rewrite hr; control; rewrite hs, hv; reflexivity. Qed.
Lemma log2_state s i (hr : word 1 (nreset i) = 0)
  (hs : word 3 (r0_nstate s) = 1) :
  r0_nstate (step s i) = 2.
Proof. cbn [step r0_nstate]; rewrite hr; control; rewrite hs; reflexivity. Qed.
Lemma shift_state s i (hr : word 1 (nreset i) = 0)
  (hs : word 3 (r0_nstate s) = 2) :
  r0_nstate (step s i) = 3.
Proof. cbn [step r0_nstate]; rewrite hr; control; rewrite hs; reflexivity. Qed.
Lemma compute_state s i (hr : word 1 (nreset i) = 0)
  (hs : word 3 (r0_nstate s) = 3) :
  r0_nstate (step s i) = if Z.eqb (word 6 (r9_ncnt_5Fvalue s)) 63 then 4 else 3.
Proof.
  cbn [step r0_nstate]; rewrite hr; control; rewrite hs.
  destruct (Z.eqb (word 6 (r9_ncnt_5Fvalue s)) 63); reflexivity.
Qed.
Lemma finish_valid s i (hs : word 3 (r0_nstate s) = 4) :
  nio_5Fout_5Fvalid (observe s i) = 1.
Proof. cbn [observe nio_5Fout_5Fvalid]; unfold v399, v11; rewrite hs; reflexivity. Qed.
Lemma compute_count s i (hr : word 1 (nreset i) = 0)
  (hs : word 3 (r0_nstate s) = 3) :
  r9_ncnt_5Fvalue (step s i) = word 6 (word 6 (r9_ncnt_5Fvalue s) + 1).
Proof.
  cbn [step r9_ncnt_5Fvalue]; rewrite hr.
  unfold v398, v397, v396, v395, v394, v393, v392, v22,
    v8, v7, v6, v5, v4, v3, v2, v1, v0.
  rewrite hs; cbn [Z.eqb Pos.eqb Z.land]; constants.
  cbn [Z.eqb Pos.eqb Z.land Z.lor Z.lxor]; constants.
  cbn [Z.eqb Pos.eqb]; constants.
  change (Z.lxor 1 1) with 0; constants.
  change (Z.lor 0 0) with 0; constants.
  repeat rewrite normalize by lia. reflexivity.
Qed.
Lemma finish_state s i (hr : word 1 (nreset i) = 0)
  (hs : word 3 (r0_nstate s) = 4)
  (ready : word 1 (nio_5Fout_5Fready i) = 0) :
  r0_nstate (step s i) = 4.
Proof. cbn [step r0_nstate]; rewrite hr; control; rewrite hs, ready; reflexivity. Qed.
Lemma finish_registers s i (hs : word 3 (r0_nstate s) = 4) :
  word 129 (r2_nshiftReg (step s i)) = word 129 (r2_nshiftReg s) /\
  word 1 (r3_naSignReg (step s i)) = word 1 (r3_naSignReg s) /\
  word 1 (r4_nqSignReg (step s i)) = word 1 (r4_nqSignReg s) /\
  word 1 (r7_nctrlReg_5FisW (step s i)) = word 1 (r7_nctrlReg_5FisW s) /\
  word 1 (r8_nctrlReg_5FisHi (step s i)) = word 1 (r8_nctrlReg_5FisHi s).
Proof.
  assert (h2 : v2 s i = 0) by (unfold v2, v1, v0; rewrite hs; reflexivity).
  assert (h4 : v4 s i = 0) by (unfold v4, v3; rewrite hs; reflexivity).
  assert (h6 : v6 s i = 0) by (unfold v6, v5; rewrite hs; reflexivity).
  assert (h8 : v8 s i = 0) by (unfold v8, v7; rewrite hs; reflexivity).
  assert (h25 : v25 s i = 0) by (unfold v25; rewrite h2, h4; reflexivity).
  cbn [step r2_nshiftReg r3_naSignReg r4_nqSignReg r7_nctrlReg_5FisW r8_nctrlReg_5FisHi].
  unfold v44, v43, v42, v47, v52, v60, v61.
  rewrite h2, h6, h8, h25; cbn [Z.eqb].
  repeat rewrite normalize by lia. repeat split; reflexivity.
Qed.
Lemma output_congruent s t i j
  (hshift : word 129 (r2_nshiftReg s) = word 129 (r2_nshiftReg t))
  (ha : word 1 (r3_naSignReg s) = word 1 (r3_naSignReg t))
  (hq : word 1 (r4_nqSignReg s) = word 1 (r4_nqSignReg t))
  (hw : word 1 (r7_nctrlReg_5FisW s) = word 1 (r7_nctrlReg_5FisW t))
  (hh : word 1 (r8_nctrlReg_5FisHi s) = word 1 (r8_nctrlReg_5FisHi t)) :
  nio_5Fout_5Fbits_5Fdata (observe s i) = nio_5Fout_5Fbits_5Fdata (observe t j).
Proof.
  cbn [observe nio_5Fout_5Fbits_5Fdata].
  unfold v412, v411, v410, v409, v408, v407, v406, v405,
    v404, v403, v402, v40, v20.
  now rewrite hshift, ha, hq, hw, hh.
Qed.
Theorem stall_stable s i j (hs : word 3 (r0_nstate s) = 4)
  (hr : word 1 (nreset i) = 0)
  (ready : word 1 (nio_5Fout_5Fready i) = 0) :
  nio_5Fout_5Fvalid (observe (step s i) j) = 1 /\
  nio_5Fout_5Fbits_5Fdata (observe (step s i) j) = nio_5Fout_5Fbits_5Fdata (observe s i).
Proof.
  split.
  - apply finish_valid; rewrite (finish_state s i hr hs ready); reflexivity.
  - destruct (finish_registers s i hs) as [hshift [ha [hq [hw hh]]]].
    exact (output_congruent (step s i) s j i hshift ha hq hw hh).
Qed.
Lemma run_from_next s inputs n :
  run s inputs (S n) = run (step s (inputs O)) (fun t => inputs (S t)) n.
Proof. induction n; [reflexivity | change (step (run s inputs (S n)) (inputs (S n)) = step (run (step s (inputs O)) (fun t => inputs (S t)) n) (inputs (S n))); now rewrite IHn]. Qed.
End RadixControl.
Print Assumptions RadixControl.compute_count.
Print Assumptions RadixControl.compute_state.
Print Assumptions RadixControl.stall_stable.

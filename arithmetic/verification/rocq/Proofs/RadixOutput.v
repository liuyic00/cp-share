From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixBalance RadixCapture RadixExecution RadixAccepted RadixZeroAccepted RadixFormat RadixMetadata.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixBalance.RadixBalance RadixCapture.RadixCapture RadixExecution.RadixExecution
  RadixAccepted.RadixAccepted RadixZeroAccepted.RadixZeroAccepted RadixFormat.RadixFormat RadixMetadata.RadixMetadata.
Open Scope Z_scope.
Module RadixOutput.
Definition formatMetadata flags q r :=
  let '(aN,qN,w,rem) := flags in formatResult aN qN w rem q r.
Definition specification i :=
  let a := magnitude (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i) in
  let b := magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 i) (nctrl_5Fsign i) in
  formatMetadata (requestMetadata i)
    (if word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 i) =? 0 then base-1 else a/b) (a mod b).
Lemma observe_metadata s i : nio_5Fout_5Fbits_5Fdata (observe s i) =
  formatMetadata (metadata s) (v40 s i) (v402 s i).
Proof.
  rewrite observe_format; unfold formatMetadata, metadata, formatResult, correctSign.
  repeat rewrite normalize by lia; reflexivity.
Qed.
Local Opaque run step.
Theorem accepted_nonzero_result s inputs
  (idle : word 3 (r0_nstate s) = 0)
  (valid : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (reset : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0)
  (nonzero : word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) <> 0) :
  exists n, (4 <= n <= 67)%nat /\
    nio_5Fout_5Fvalid (observe (run s inputs n) (inputs n)) = 1 /\
    nio_5Fout_5Fbits_5Fdata (observe (run s inputs n) (inputs n)) = specification (inputs O).
Proof.
  destruct (accepted_magnitudes_correct s inputs idle valid reset nonzero) as [n [size [hv [hq [hr kept]]]]].
  exists n; split; [exact size | split; [exact hv |]].
  rewrite observe_metadata, (captured_metadata _ _ kept), (capture_metadata s (inputs O) idle valid), hq, hr.
  unfold specification; assert (h : (word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) =? 0) = false) by (apply Z.eqb_neq; exact nonzero).
  rewrite h; reflexivity.
Qed.
Theorem accepted_result s inputs
  (idle : word 3 (r0_nstate s) = 0)
  (valid : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (reset : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0) :
  exists n, (4 <= n <= 67)%nat /\
    nio_5Fout_5Fvalid (observe (run s inputs n) (inputs n)) = 1 /\
    nio_5Fout_5Fbits_5Fdata (observe (run s inputs n) (inputs n)) = specification (inputs O).
Proof.
  destruct (Z.eq_dec (word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O))) 0) as [zero|nonzero].
  - destruct (accepted_zero_magnitudes s inputs idle valid reset zero) as [hv [hq [hr kept]]].
    exists 67%nat; split; [lia | split; [exact hv |]].
    rewrite observe_metadata, (captured_metadata _ _ kept), (capture_metadata s (inputs O) idle valid), hq, hr.
    assert (b : magnitude (nio_5Fin_5Fbits_5Fsrc_5F1 (inputs O)) (nctrl_5Fsign (inputs O)) = 0) by (apply magnitude_zero; exact zero).
    unfold specification; rewrite b, zero, Zmod_0_r; reflexivity.
  - exact (accepted_nonzero_result s inputs idle valid reset nonzero).
Qed.
Theorem after_reset_result initial resetInput inputs
  (resetEdge : word 1 (nreset resetInput) = 1)
  (valid : word 1 (nio_5Fin_5Fvalid (inputs O)) = 1)
  (reset : forall t, (t < 67)%nat -> word 1 (nreset (inputs t)) = 0) :
  exists n, (4 <= n <= 67)%nat /\
    nio_5Fout_5Fvalid (observe (run (step initial resetInput) inputs n) (inputs n)) = 1 /\
    nio_5Fout_5Fbits_5Fdata (observe (run (step initial resetInput) inputs n) (inputs n)) = specification (inputs O).
Proof.
  apply accepted_result; [rewrite (reset_idle initial resetInput resetEdge); reflexivity | exact valid | exact reset].
Qed.
End RadixOutput.
Print Assumptions RadixOutput.accepted_result.
Print Assumptions RadixOutput.after_reset_result.

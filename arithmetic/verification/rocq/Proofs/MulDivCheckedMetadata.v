From Coq Require Import ZArith Lia List Bool.
From Proofs Require Import MulDivCheckedHistory MulDivCheckedControl.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedMetadata.
Definition Invariant s := word 1 (r9_ncontractPending s)=1 ->
  word 5 (r2_nreq_5Ftag s)=word 5 (r15_ncontractTag s) /\ word 1 (r1_nreq_5Fdw s)=word 1 (r12_ncontractDw s).
Theorem reset_invariant s i (reset : word 1 (nreset i)=1) : Invariant (step s i).
Proof. intro flag; destruct (reset_monitors s i reset) as [pending rest]; rewrite pending in flag; discriminate. Qed.
Theorem step_invariant s i (previous : Invariant s) : Invariant (step s i).
Proof.
  intro pending; destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending) as [reset [accepted|[absent [old live]]]].
  - cbn [step r2_nreq_5Ftag r15_ncontractTag r1_nreq_5Fdw r12_ncontractDw].
    unfold v63,v173,v62,v170; rewrite accepted; cbn [Z.eqb Pos.eqb]; split; reflexivity.
  - cbn [step r2_nreq_5Ftag r15_ncontractTag r1_nreq_5Fdw r12_ncontractDw].
    unfold v63,v173,v62,v170; rewrite absent; cbn [Z.eqb]; repeat rewrite normalize by lia; apply previous; exact old.
Qed.
Local Opaque run step.
Theorem run_invariant initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  Invariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH]; [apply reset_invariant; exact reset|].
  change (run (step initial resetInput) pins (S n)) with (step (run (step initial resetInput) pins n) (pins n)); apply step_invariant; exact IH.
Qed.
Lemma response_gate_pending s i (enabled : v234 s i=1) : word 1 (r9_ncontractPending s)=1.
Proof.
  destruct (bit_cases (r9_ncontractPending s)) as [zero|one]; [|exact one].
  unfold v234,v233,v227 in enabled; rewrite zero in enabled; change (0=1) in enabled; discriminate.
Qed.
Theorem tag_assertion s i (metadata : Invariant s) : nth 2 (assertionChecks s i) false=true.
Proof.
  change (orb (negb (v234 s i=?1)) (v232 s i=?1)=true).
  destruct (v234 s i=?1) eqn:enabled; [|reflexivity].
  apply Z.eqb_eq in enabled; destruct (metadata (response_gate_pending s i enabled)) as [tag width].
  unfold v232; rewrite tag,Z.eqb_refl; reflexivity.
Qed.
Theorem tag_assertion_after_reset initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  nth 2 (assertionChecks (run (step initial resetInput) pins n) (pins n)) false=true.
Proof. apply tag_assertion; apply run_invariant; exact reset. Qed.
Definition LegalInvariant s := word 1 (r9_ncontractPending s)=1 ->
  word 4 (r11_ncontractFn s)<8 /\ (word 1 (r12_ncontractDw s)=1 \/ word 4 (r11_ncontractFn s)=0 \/ 4<=word 4 (r11_ncontractFn s)).
Theorem legal_reset s i (reset : word 1 (nreset i)=1) : LegalInvariant (step s i).
Proof. intro flag; destruct (reset_monitors s i reset) as [pending rest]; rewrite pending in flag; discriminate. Qed.
Lemma legal_decode s i (enabled : v160 s i=1) : legal i.
Proof.
  pose proof (bounds 4 (nio_5Freq_5Fbits_5Ffn i) ltac:(lia)) as range; change (2^4) with 16 in range.
  assert (cases : word 4 (nio_5Freq_5Fbits_5Ffn i)=0 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=2 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=3 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=8 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=9 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=10 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=11 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=12 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=13 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=14 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=15) by lia.
  unfold v160,v159,v158,v157,v156,v155,v154,v153,v152,v31,v15 in enabled.
  destruct (bit_cases (nio_5Freq_5Fbits_5Fdw i)) as [dw|dw];
    destruct (bit_cases (nio_5Fkill i)) as [kill|kill];
    destruct cases as [h|[h|[h|[h|[h|[h|[h|[h|[h|[h|[h|[h|[h|[h|[h|h]]]]]]]]]]]]]]];
    rewrite h,dw,kill in enabled; vm_compute in enabled; try discriminate;
    unfold legal; rewrite h,dw; vm_compute; intuition discriminate.
Qed.
Theorem legal_step s i (previous : LegalInvariant s) : LegalInvariant (step s i).
Proof.
  intro pending; destruct (MulDivCheckedControl.MulDivCheckedControl.pending_origin s i pending) as [reset [accepted|[absent [old live]]]].
  - assert (enabled : v160 s i=1).
    { change (word 1 (if word 1 (nreset i)=?1 then v8 s i else v163 s i)=1) in pending.
      rewrite reset in pending; unfold v163 in pending; rewrite accepted in pending; cbn [Z.eqb Pos.eqb] in pending.
      unfold v160 in *; repeat rewrite normalize in pending by lia; exact pending. }
    pose proof (legal_decode s i enabled) as request.
    change (word 4 (v169 s i)<8 /\ (word 1 (v170 s i)=1 \/ word 4 (v169 s i)=0 \/ 4<=word 4 (v169 s i))).
    unfold v169,v170; rewrite accepted; cbn [Z.eqb Pos.eqb]; repeat rewrite normalize by lia; exact request.
  - change (word 4 (v169 s i)<8 /\ (word 1 (v170 s i)=1 \/ word 4 (v169 s i)=0 \/ 4<=word 4 (v169 s i))).
    unfold v169,v170; rewrite absent; cbn [Z.eqb]; repeat rewrite normalize by lia; apply previous; exact old.
Qed.
Theorem legal_run initial resetInput (reset : word 1 (nreset resetInput)=1) pins n :
  LegalInvariant (run (step initial resetInput) pins n).
Proof.
  induction n as [|n IH]; [apply legal_reset; exact reset|].
  change (run (step initial resetInput) pins (S n)) with (step (run (step initial resetInput) pins n) (pins n)); apply legal_step; exact IH.
Qed.
End MulDivCheckedMetadata.
Print Assumptions MulDivCheckedMetadata.run_invariant.
Print Assumptions MulDivCheckedMetadata.tag_assertion_after_reset.
Print Assumptions MulDivCheckedMetadata.legal_run.

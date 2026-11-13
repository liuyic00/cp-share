From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords MulDivControl MulDivTiming MulDivRefinement MulDivMultiply MulDivMultiplyMetadata MulDivMulHigh MulDivMulLowCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivMultiply.MulDivMultiply MulDivMultiplyMetadata.MulDivMultiplyMetadata MulDivMulLowCapture.MulDivMulLowCapture.
Open Scope Z_scope.
Module MulDivMulLow.
Lemma packed_low s : word 64 (packed s)=word 64 (r8_nremainder s).
Proof.
  rewrite MulDivMultiplyRun.MulDivMultiplyRun.packed_exact.
  rewrite Z.add_comm; unfold word at 1; rewrite Z.mod_add by discriminate.
  unfold MulDivMultiplyRun.MulDivMultiplyRun.low; apply normalize; lia.
Qed.
Lemma observe_low s i (full : word 1 (r1_nreq_5Fdw s)=1)
  (selection : word 1 (r6_nresHi s)=0) :
  nio_5Fresp_5Fbits_5Fdata (observe s i)=word 64 (packed s).
Proof.
  assert (width : v154 s i=1).
  { unfold v154; rewrite full; unfold v153.
    destruct (bit_cases (Z.shiftr (word 3 (r0_nstate s)) 0)) as [h|h]; rewrite h; reflexivity. }
  assert (normal : word 64 (v145 s i)=v145 s i) by (unfold v145; apply normalize; lia).
  cbn [observe nio_5Fresp_5Fbits_5Fdata].
  unfold v160,v159,v156; rewrite full,width; cbn [Z.eqb Pos.eqb].
  unfold v152,v155; repeat rewrite normalize by lia.
  rewrite <- normal at 1 2; rewrite MulDivFormat.MulDivFormat.join_halves,normal.
  unfold v145; rewrite selection; cbn [Z.eqb Pos.eqb]; unfold v119.
  rewrite Z.shiftr_0_r; repeat rewrite normalize by lia; rewrite narrow by lia.
  symmetry; apply packed_low.
Qed.
Local Opaque run step observe.
Theorem request_control s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1) (live : active inputs 65) :
  word 3 (r0_nstate (run s inputs 65))=6 /\
  word 1 (r6_nresHi (run s inputs 65))=0 /\
  metadata (run s inputs 65)=(1,word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)),0).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture s (inputs O) idle valid hr operation full) as [st [ct [dv [sh [neg [dw [tag hi]]]]]]].
  destruct (multiply_finish (step s (inputs O)) (fun t => inputs (S t))
    ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [finish [selection meta]].
  rewrite (run_from_next s inputs 64); split; [exact finish|].
  rewrite selection,meta; unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; split; reflexivity.
Qed.
Definition specification i := word 64 (word 64 (nio_5Freq_5Fbits_5Fin1 i)*word 64 (nio_5Freq_5Fbits_5Fin2 i)).
Theorem accepted_result s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1) (live : active inputs 65) :
  nio_5Fresp_5Fvalid (observe (run s inputs 65) (inputs 65%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs 65) (inputs 65%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs 65) (inputs 65%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (request_control s inputs idle valid operation full live) as [state [selection meta]].
  unfold metadata in meta; injection meta as width tag hi.
  split; [apply done_valid; left; exact state|]; split.
  - rewrite observe_low by assumption.
    exact (accepted_product s inputs idle valid operation full live).
  - exact tag.
Qed.
Theorem after_reset_result initial resetInput inputs (hr : word 1 (nreset resetInput)=1)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=0)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1) (live : active inputs 65) :
  nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof. apply accepted_result; try assumption; rewrite (reset_ready initial resetInput hr); reflexivity. Qed.
End MulDivMulLow.
Print Assumptions MulDivMulLow.accepted_result.
Print Assumptions MulDivMulLow.after_reset_result.

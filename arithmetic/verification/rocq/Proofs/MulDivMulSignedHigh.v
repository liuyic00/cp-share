From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords MulDivControl MulDivTiming MulDivRefinement MulDivMultiply MulDivMultiplyMetadata MulDivMulHigh MulDivMulSignedCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivMultiply.MulDivMultiply MulDivMultiplyMetadata.MulDivMultiplyMetadata MulDivMulSignedCapture.MulDivMulSignedCapture.
Open Scope Z_scope.
Module MulDivMulSignedHigh.
Lemma high_signed s : word 64 (packed s/2^64)=word 64 (SignedWords.signed 129 (packed s)/2^64).
Proof.
  assert (normal : word 129 (packed s)=packed s) by (unfold packed; apply normalize; lia).
  assert (encoded : word 129 (SignedWords.signed 129 (packed s))=packed s).
  { rewrite SignedWords.word_signed by lia; exact normal. }
  rewrite <- (Z.shiftr_div_pow2 (packed s) 64) by lia.
  rewrite <- encoded at 1; rewrite extract_normal by lia.
  rewrite Z.shiftr_div_pow2 by lia; reflexivity.
Qed.
Local Opaque run step observe.
Theorem request_control s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=2)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1) (live : active inputs 65) :
  word 3 (r0_nstate (run s inputs 65))=6 /\
  word 1 (r6_nresHi (run s inputs 65))=1 /\
  metadata (run s inputs 65)=(1,word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)),1).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (capture s (inputs O) idle valid hr operation full) as [st [ct [dv [sh [neg [dw [tag hi]]]]]]].
  destruct (multiply_finish (step s (inputs O)) (fun t => inputs (S t))
    ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [finish [selection meta]].
  rewrite (run_from_next s inputs 64); split; [exact finish|].
  rewrite selection,meta; unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; split; reflexivity.
Qed.
Definition specification i := word 64 ((SignedWords.signed 64 (nio_5Freq_5Fbits_5Fin1 i)*multiplicand i)/2^64).
Theorem accepted_result s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=2)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1) (live : active inputs 65) :
  nio_5Fresp_5Fvalid (observe (run s inputs 65) (inputs 65%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs 65) (inputs 65%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs 65) (inputs 65%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (request_control s inputs idle valid operation full live) as [state [selection meta]].
  unfold metadata in meta; injection meta as width tag hi.
  split; [apply done_valid; left; exact state|]; split.
  - rewrite MulDivMulHigh.MulDivMulHigh.observe_high by assumption.
    rewrite high_signed,(accepted_product s inputs idle valid operation full live); reflexivity.
  - exact tag.
Qed.
Theorem after_reset_result initial resetInput inputs (hr : word 1 (nreset resetInput)=1)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=1 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=2)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1) (live : active inputs 65) :
  nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof. apply accepted_result; try assumption; rewrite (reset_ready initial resetInput hr); reflexivity. Qed.
End MulDivMulSignedHigh.
Print Assumptions MulDivMulSignedHigh.accepted_result.
Print Assumptions MulDivMulSignedHigh.after_reset_result.

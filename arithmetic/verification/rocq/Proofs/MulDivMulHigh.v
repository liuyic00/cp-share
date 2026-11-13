From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivRefinement MulDivFormat MulDivMultiply MulDivMultiplyRun MulDivMultiplyCapture MulDivMultiplyMetadata.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivFormat.MulDivFormat MulDivMultiply.MulDivMultiply MulDivMultiplyRun.MulDivMultiplyRun MulDivMultiplyCapture.MulDivMultiplyCapture MulDivMultiplyMetadata.MulDivMultiplyMetadata.
Open Scope Z_scope.
Module MulDivMulHigh.
Lemma high_packed s : word 64 (Z.shiftr (word 130 (r8_nremainder s)) 65)=word 64 (packed s/2^64).
Proof.
  rewrite packed_exact.
  assert (quot : (accumulator s*2^64+low s)/2^64=accumulator s).
  { symmetry; apply Z.div_unique with (r:=low s); [left; unfold low; apply bounds; lia|ring]. }
  rewrite quot; unfold accumulator; rewrite narrow by lia; reflexivity.
Qed.
Lemma observe_high s i (full : word 1 (r1_nreq_5Fdw s)=1)
  (selection : word 1 (r6_nresHi s)=1) :
  nio_5Fresp_5Fbits_5Fdata (observe s i)=word 64 (packed s/2^64).
Proof.
  assert (width : v154 s i=1).
  { unfold v154; rewrite full; unfold v153.
    destruct (bit_cases (Z.shiftr (word 3 (r0_nstate s)) 0)) as [h|h]; rewrite h; reflexivity. }
  assert (normal : word 64 (v145 s i)=v145 s i) by (unfold v145; apply normalize; lia).
  cbn [observe nio_5Fresp_5Fbits_5Fdata].
  unfold v160,v159,v156; rewrite full,width; cbn [Z.eqb Pos.eqb].
  unfold v152,v155; repeat rewrite normalize by lia.
  rewrite <- normal at 1 2; rewrite join_halves,normal.
  unfold v145; rewrite selection; cbn [Z.eqb Pos.eqb]; unfold v144.
  rewrite normalize by lia; apply high_packed.
Qed.
Definition specification i := word 64 ((word 64 (nio_5Freq_5Fbits_5Fin1 i)*word 64 (nio_5Freq_5Fbits_5Fin2 i))/2^64).
Local Opaque run step observe.
Theorem accepted_result s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=3)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1)
  (live : active inputs 65) :
  nio_5Fresp_5Fvalid (observe (run s inputs 65) (inputs 65%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs 65) (inputs 65%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs 65) (inputs 65%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (unsigned_request_control s inputs idle valid operation full live) as [state [selection meta]].
  pose proof (accepted_product s inputs idle valid operation full live) as product.
  unfold metadata in meta; injection meta as width tag hi.
  split; [apply done_valid; left; exact state|]; split.
  - rewrite observe_high by (rewrite ?width; assumption).
    rewrite product; reflexivity.
  - exact tag.
Qed.
Theorem after_reset_result initial resetInput inputs (hr : word 1 (nreset resetInput)=1)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=3)
  (full : word 1 (nio_5Freq_5Fbits_5Fdw (inputs O))=1)
  (live : active inputs 65) :
  nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run (step initial resetInput) inputs 65) (inputs 65%nat))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof. apply accepted_result; try assumption; rewrite (reset_ready initial resetInput hr); reflexivity. Qed.
End MulDivMulHigh.
Print Assumptions MulDivMulHigh.accepted_result.
Print Assumptions MulDivMulHigh.after_reset_result.

From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivMetadata MulDivFormat MulDivSignedInputEdge MulDivSignedOperands MulDivSignedCapture MulDivSignedPreparation MulDivSignedExecution MulDivSignedCore.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivMetadata.MulDivMetadata MulDivFormat.MulDivFormat MulDivSignedInputEdge.MulDivSignedInputEdge MulDivSignedOperands.MulDivSignedOperands MulDivSignedCapture.MulDivSignedCapture MulDivSignedPreparation.MulDivSignedPreparation MulDivSignedExecution.MulDivSignedExecution MulDivSignedCore.MulDivSignedCore.
Open Scope Z_scope.
Module MulDivSigned.
Definition specification i := format (nio_5Freq_5Fbits_5Fdw i)
  (coreResult (magnitude (operand i (nio_5Freq_5Fbits_5Fin1 i)))
    (magnitude (operand i (nio_5Freq_5Fbits_5Fin2 i)))
    (if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0) (outputNegative i)).
Definition acceptedEdges i := Nat.add (Nat.add (preparationEdges i) 65) (correctionEdges
  (magnitude (operand i (nio_5Freq_5Fbits_5Fin2 i)))
  (if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0) (outputNegative i)).
Local Opaque run step observe.
Theorem accepted_result_exact s inputs (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=6)
  (live : active inputs 68) :
  exists n, n=acceptedEdges (inputs O) /\ (66<=n<=68)%nat /\
  nio_5Fresp_5Fvalid (observe (run s inputs n) (inputs n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s inputs n) (inputs n))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s inputs n) (inputs n))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof.
  destruct (live O ltac:(lia)) as [hr hk].
  destruct (live 1%nat ltac:(lia)) as [hr1 hk1].
  destruct (preparation s (inputs O) (inputs 1%nat) idle valid hr hr1 hk1 operation)
    as [st [ct [dv [sh [neg meta]]]]].
  assert (future : active (afterPreparation inputs) 66).
  { intros t ht; unfold afterPreparation; destruct (needsNegation (inputs O)); apply live; lia. }
  destruct (prepared_result_exact (prepared s (inputs O) (inputs 1%nat)) (afterPreparation inputs)
    (magnitude (operand (inputs O) (nio_5Freq_5Fbits_5Fin1 (inputs O))))
    (magnitude (operand (inputs O) (nio_5Freq_5Fbits_5Fin2 (inputs O)))) st ct dv sh future)
    as [n [cycle [size [response [data tag]]]]].
  assert (pins : afterPreparation inputs n=inputs (preparationEdges (inputs O)+n)%nat).
  { unfold afterPreparation,preparationEdges; destruct (needsNegation (inputs O)); reflexivity. }
  rewrite <- (run_prepared s inputs n),pins in response,data,tag.
  unfold metadata,requestMetadata in meta; injection meta as width originalTag selection.
  exists (preparationEdges (inputs O)+n)%nat.
  split.
  - rewrite cycle; unfold acceptedEdges,correctionEdges,effectiveNegative.
    rewrite selection,neg,negative_normal.
    destruct (word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=?6); rewrite Nat.add_assoc; reflexivity.
  - split.
    + unfold preparationEdges; destruct (needsNegation (inputs O)); lia.
    + split; [exact response|]; split.
      * rewrite data; unfold specification,format,coreResult,effectiveNegative.
        rewrite width,selection,neg,negative_normal.
        destruct (word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=?6); reflexivity.
      * rewrite tag; exact originalTag.
Qed.
Theorem after_reset_result initial resetInput inputs (hr : word 1 (nreset resetInput)=1)
  (valid : word 1 (nio_5Freq_5Fvalid (inputs O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn (inputs O))=6)
  (live : active inputs 68) :
  exists n, n=acceptedEdges (inputs O) /\ (66<=n<=68)%nat /\
  nio_5Fresp_5Fvalid (observe (run (step initial resetInput) inputs n) (inputs n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run (step initial resetInput) inputs n) (inputs n))=specification (inputs O) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run (step initial resetInput) inputs n) (inputs n))=word 5 (nio_5Freq_5Fbits_5Ftag (inputs O)).
Proof. apply accepted_result_exact; try assumption; rewrite (reset_ready initial resetInput hr); reflexivity. Qed.
End MulDivSigned.
Print Assumptions MulDivSigned.accepted_result_exact.
Print Assumptions MulDivSigned.after_reset_result.

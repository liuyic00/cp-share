From Coq Require Import ZArith Lia Bool.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivRefinement MulDivMetadata MulDivSignedInputEdge MulDivSignedBits MulDivSignedOperands MulDivSignedCapture.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivMetadata.MulDivMetadata MulDivSignedInputEdge.MulDivSignedInputEdge MulDivSignedBits.MulDivSignedBits MulDivSignedOperands.MulDivSignedOperands MulDivSignedCapture.MulDivSignedCapture.
Open Scope Z_scope.
Module MulDivSignedPreparation.
Definition prepared s i later := if needsNegation i then step (step s i) later else step s i.
Definition requestMetadata i := (word 1 (nio_5Freq_5Fbits_5Fdw i),word 5 (nio_5Freq_5Fbits_5Ftag i),if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0).
Lemma negative_normal i : word 1 (outputNegative i)=outputNegative i.
Proof.
  unfold outputNegative; destruct (word 4 (nio_5Freq_5Fbits_5Ffn i)=?6).
  - destruct (sign_cases i (nio_5Freq_5Fbits_5Fin1 i)) as [h|h]; rewrite h; reflexivity.
  - destruct (inputSign i (nio_5Freq_5Fbits_5Fin1 i)=?inputSign i (nio_5Freq_5Fbits_5Fin2 i)); reflexivity.
Qed.
Theorem preparation s i later (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1) (reset : word 1 (nreset i)=0)
  (laterReset : word 1 (nreset later)=0) (laterKill : word 1 (nio_5Fkill later)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) :
  word 3 (r0_nstate (prepared s i later))=3 /\ word 7 (r3_ncount (prepared s i later))=0 /\
  word 65 (r7_ndivisor (prepared s i later))=word 64 (magnitude (operand i (nio_5Freq_5Fbits_5Fin2 i))) /\
  packed (prepared s i later)=word 64 (magnitude (operand i (nio_5Freq_5Fbits_5Fin1 i))) /\
  word 1 (r4_nneg_5Fout (prepared s i later))=outputNegative i /\
  metadata (prepared s i later)=requestMetadata i.
Proof.
  destruct (capture_control s i idle valid reset operation) as [st [ct [hi [neg [dw [tag select]]]]]].
  destruct (capture_data s i idle valid operation) as [dv sh].
  assert (captured : metadata (step s i)=requestMetadata i).
  { unfold metadata,requestMetadata; rewrite dw,tag,select; repeat rewrite normalize by lia.
    destruct (word 4 (nio_5Freq_5Fbits_5Ffn i)=?6); reflexivity. }
  unfold prepared; destruct (needsNegation i) eqn:needed.
  - destruct (prepared_edge (step s i) later (operand i (nio_5Freq_5Fbits_5Fin1 i)) (operand i (nio_5Freq_5Fbits_5Fin2 i))
      ltac:(rewrite st; reflexivity) ltac:(rewrite ct; reflexivity) dv
      ltac:(rewrite operand_normal; exact sh) ltac:(rewrite hi; reflexivity) laterReset laterKill)
      as [state [count [divisor [initial [meta flag]]]]].
    repeat split; try assumption.
    + rewrite flag,neg; apply negative_normal.
    + rewrite meta; exact captured.
  - assert (aSign : inputSign i (nio_5Freq_5Fbits_5Fin1 i)=0).
    { unfold needsNegation in needed; apply orb_false_iff in needed; destruct needed as [ha hb].
      destruct (sign_cases i (nio_5Freq_5Fbits_5Fin1 i)) as [h|h]; [exact h|rewrite h in ha; discriminate]. }
    assert (dSign : inputSign i (nio_5Freq_5Fbits_5Fin2 i)=0).
    { unfold needsNegation in needed; apply orb_false_iff in needed; destruct needed as [ha hb].
      destruct (sign_cases i (nio_5Freq_5Fbits_5Fin2 i)) as [h|h]; [exact h|rewrite h in hb; discriminate]. }
    split; [rewrite st; reflexivity|].
    split; [rewrite ct; reflexivity|].
    split.
    + rewrite dv; unfold extended65,magnitude; rewrite !operand_sign,dSign,operand_normal.
      change (Z.shiftl 0 64) with 0; rewrite Z.add_0_l; cbn [Z.eqb].
      repeat rewrite normalize by lia; rewrite operand_normal.
      rewrite <- (operand_normal i (nio_5Freq_5Fbits_5Fin2 i)) at 1.
      transitivity (word 64 (operand i (nio_5Freq_5Fbits_5Fin2 i))); [apply Words.word_widen; lia|apply operand_normal].
    + split.
      * rewrite sh; unfold magnitude; rewrite operand_sign,aSign; cbn [Z.eqb]; rewrite normalize,operand_normal by lia; reflexivity.
      * split; [rewrite neg; apply negative_normal|exact captured].
Qed.
Definition preparationEdges i : nat := if needsNegation i then 2%nat else 1%nat.
Definition afterPreparation inputs t := inputs (if needsNegation (inputs O) then S (S t) else S t).
Local Opaque run step.
Lemma run_prepared s inputs n :
  run s inputs (preparationEdges (inputs O)+n)=
    run (prepared s (inputs O) (inputs 1%nat)) (afterPreparation inputs) n.
Proof.
  unfold preparationEdges,prepared,afterPreparation; destruct (needsNegation (inputs O)).
  - change (run s inputs (S (S n))=run (step (step s (inputs O)) (inputs 1%nat)) (fun t => inputs (S (S t))) n).
    rewrite (MulDivTiming.MulDivTiming.run_from_next s inputs (S n)),
      (MulDivTiming.MulDivTiming.run_from_next (step s (inputs O)) (fun t => inputs (S t)) n); reflexivity.
  - change (run s inputs (S n)=run (step s (inputs O)) (fun t => inputs (S t)) n).
    apply MulDivTiming.MulDivTiming.run_from_next.
Qed.
End MulDivSignedPreparation.
Print Assumptions MulDivSignedPreparation.preparation.
Print Assumptions MulDivSignedPreparation.run_prepared.

From Coq Require Import ZArith Lia Bool.
From Proofs Require Import MulDivCheckedSignedTimingInit MulDivSignedCapture.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedLatency.MulDivCheckedLatency MulDivCheckedSignedTiming.MulDivCheckedSignedTiming
  MulDivCheckedSignedTimingEdges.MulDivCheckedSignedTimingEdges
  MulDivCheckedSignedOperands.MulDivCheckedSignedOperands
  MulDivCheckedSignedTimingInit.MulDivCheckedSignedTimingInit.
Open Scope Z_scope.
Module MulDivCheckedSignedTimingCapture.
Module C := MulDivSignedCapture.MulDivSignedCapture.
Lemma operand_capture t i x y (width : word 1 (r12_ncontractDw t)=word 1 (nio_5Freq_5Fbits_5Fdw i))
  (value : word 64 x=word 64 y) : operand t x=O.operand (P.inputs i) y.
Proof.
  assert (low : Words.word 32 x=Words.word 32 y).
  { change (word 32 x=word 32 y); rewrite <-(narrow 64 32 x ltac:(lia) ltac:(lia)),
      <-(narrow 64 32 y ltac:(lia) ltac:(lia)),value; reflexivity. }
  unfold operand,O.operand; change (MulDiv.CIRCTBits.word 1 (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fdw (P.inputs i))) with (word 1 (nio_5Freq_5Fbits_5Fdw i)).
  rewrite width; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); [exact value|].
  unfold SignedWords.signed; rewrite low; reflexivity.
Qed.
Lemma capture_values s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1) :
  operand (step s i) (r13_ncontractA (step s i))=O.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin1 i) /\
  operand (step s i) (r14_ncontractB (step s i))=O.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i) /\
  word 4 (r11_ncontractFn (step s i))=word 4 (nio_5Freq_5Fbits_5Ffn i).
Proof.
  pose proof (capture s i idle valid) as history.
  assert (a : word 64 (r13_ncontractA (step s i))=word 64 (nio_5Freq_5Fbits_5Fin1 i))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin1 history).
  assert (b : word 64 (r14_ncontractB (step s i))=word 64 (nio_5Freq_5Fbits_5Fin2 i))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2 history).
  assert (width : word 1 (r12_ncontractDw (step s i))=word 1 (nio_5Freq_5Fbits_5Fdw i))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fdw history).
  repeat split; try (apply operand_capture; assumption).
  exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn history).
Qed.
Lemma capture_costs s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) :
  inputExtra (step s i)=(if C.needsNegation (P.inputs i) then 1 else 0) /\
  hi (step s i)=(if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0) /\
  rawNegative (step s i)=C.outputNegative (P.inputs i).
Proof.
  destruct (capture_values s i idle valid) as [a [b fn]].
  assert (op : Operation (step s i)) by (unfold Operation; rewrite fn; exact operation).
  assert (sa : E.sign64 (operand (step s i) (r13_ncontractA (step s i)))=O.inputSign (P.inputs i) (nio_5Freq_5Fbits_5Fin1 i)) by (rewrite a; apply O.operand_sign).
  assert (sb : E.sign64 (operand (step s i) (r14_ncontractB (step s i)))=O.inputSign (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i)) by (rewrite b; apply O.operand_sign).
  split.
  - unfold inputExtra,v211; rewrite (a_negative _ quiet op),(b_negative _ quiet op),sa,sb.
    unfold C.needsNegation.
    destruct (C.sign_cases (P.inputs i) (nio_5Freq_5Fbits_5Fin1 i)) as [ha|ha];
      destruct (C.sign_cases (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i)) as [hb|hb];
      change (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin1 (P.inputs i)) with (nio_5Freq_5Fbits_5Fin1 i);
      change (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2 (P.inputs i)) with (nio_5Freq_5Fbits_5Fin2 i);
      rewrite ha,hb; reflexivity.
  - split; [unfold hi; rewrite fn; reflexivity|].
    unfold rawNegative,C.outputNegative; rewrite fn,sa,sb; reflexivity.
Qed.
Theorem capture_phase s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1) (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) :
  Negating (step s i) \/ Prepared (step s i).
Proof.
  destruct (capture_values s i idle valid) as [a [b fn]].
  destruct (capture_costs s i idle valid operation) as [extra [high negative]].
  destruct (C.capture_control (P.state s) (P.inputs i) idle valid reset operation)
    as [st [ct [select [neg [dw [tag highCore]]]]]].
  destruct (C.capture_data (P.state s) (P.inputs i) idle valid operation) as [dv rem].
  rewrite <-P.step_projects in st,ct,select,neg,dw,tag,highCore,dv,rem.
  change (r0_nstate (step s i)=if C.needsNegation (P.inputs i) then 1 else 3) in st.
  change (r3_ncount (step s i)=0) in ct.
  change (r6_nresHi (step s i)=0) in select.
  change (r4_nneg_5Fout (step s i)=C.outputNegative (P.inputs i)) in neg.
  change (r5_nisHi (step s i)=if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0) in highCore.
  change (r7_ndivisor (step s i)=MulDivSignedBits.MulDivSignedBits.extended65 (O.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i))) in dv.
  change (R.packed (P.state (step s i))=O.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin1 i)) in rem.
  assert (highNorm : word 1 (r5_nisHi (step s i))=hi (step s i)).
  { rewrite highCore,<-high; apply hi_normal. }
  assert (negNorm : word 1 (r4_nneg_5Fout (step s i))=rawNegative (step s i)).
  { rewrite neg,<-negative; apply negative_normal. }
  pose proof (capture_age s i idle valid) as age.
  destruct (C.needsNegation (P.inputs i)) eqn:needed.
  - left; unfold Negating; rewrite st,ct,age,extra,a,b,select.
    repeat split; try reflexivity; try assumption.
    rewrite rem; symmetry; apply O.operand_normal.
  - assert (aSign : E.sign64 (O.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin1 i))=0).
    { rewrite O.operand_sign; unfold C.needsNegation in needed; apply orb_false_iff in needed.
      destruct (C.sign_cases (P.inputs i) (nio_5Freq_5Fbits_5Fin1 i)) as [h|h]; [exact h|].
      destruct needed as [ha hb]; change (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin1 (P.inputs i)) with (nio_5Freq_5Fbits_5Fin1 i) in ha; rewrite h in ha; discriminate. }
    assert (bSign : E.sign64 (O.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i))=0).
    { rewrite O.operand_sign; unfold C.needsNegation in needed; apply orb_false_iff in needed.
      destruct (C.sign_cases (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i)) as [h|h]; [exact h|].
      destruct needed as [ha hb]; change (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2 (P.inputs i)) with (nio_5Freq_5Fbits_5Fin2 i) in hb; rewrite h in hb; discriminate. }
    right; unfold Prepared; rewrite st,ct,age,extra,a,b.
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    split.
    + rewrite dv; unfold MulDivSignedBits.MulDivSignedBits.extended65,E.magnitude; rewrite bSign.
      rewrite <-word_bridge; change (Z.shiftl 0 64) with 0; rewrite Z.add_0_l; cbn [Z.eqb].
      repeat rewrite normalize by lia; apply Words.word_widen; lia.
    + split.
      * rewrite rem; unfold E.magnitude; rewrite aSign; cbn [Z.eqb].
        rewrite <-word_bridge; repeat rewrite normalize by lia; symmetry; apply O.operand_normal.
      * split; assumption.
Qed.
End MulDivCheckedSignedTimingCapture.
Print Assumptions MulDivCheckedSignedTimingCapture.capture_phase.
Print Assumptions MulDivCheckedSignedTimingCapture.capture_costs.

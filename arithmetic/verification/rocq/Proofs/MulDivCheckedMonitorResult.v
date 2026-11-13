From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedSignedTimingCapture MulDivSigned.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked.
Open Scope Z_scope.
Module MulDivCheckedMonitorResult.
Module P := MulDivCheckedProjection.MulDivCheckedProjection.
Module L := MulDivCheckedLatency.MulDivCheckedLatency.
Module O := MulDivCheckedSignedOperands.MulDivCheckedSignedOperands.
Module C := MulDivCheckedSignedTimingCapture.MulDivCheckedSignedTimingCapture.
Module S := MulDivSigned.MulDivSigned.
Lemma capture_cycle s i (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=6) :
  (Z.to_nat (L.latency (step s i))+1)%nat=S.acceptedEdges (P.inputs i).
Proof.
  destruct (C.capture_values s i idle valid) as [a [b fn]].
  destruct (C.capture_costs s i idle valid operation) as [extra [hi negative]].
  assert (op : MulDivCheckedSignedTiming.MulDivCheckedSignedTiming.Operation (step s i)).
  { unfold MulDivCheckedSignedTiming.MulDivCheckedSignedTiming.Operation; rewrite fn; exact operation. }
  rewrite L.division_latency by (unfold MulDivCheckedSignedTiming.MulDivCheckedSignedTiming.Operation in op; intuition).
  rewrite O.corrected_negative by exact op.
  rewrite extra,b,hi,negative.
  unfold S.acceptedEdges, MulDivSignedPreparation.MulDivSignedPreparation.preparationEdges,
    MulDivSignedCore.MulDivSignedCore.correctionEdges.
  change (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2 (P.inputs i)) with (nio_5Freq_5Fbits_5Fin2 i).
  change (MulDiv.CIRCTBits.word 4 (MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn (P.inputs i))) with (word 4 (nio_5Freq_5Fbits_5Ffn i)).
  destruct (Words.bit_cases (C.C.outputNegative (P.inputs i))) as [neg|neg];
    unfold MulDivSignedExecution.MulDivSignedExecution.effectiveNegative;
    change (Words.word 1 (C.C.outputNegative (P.inputs i))) with (MulDiv.CIRCTBits.word 1 (C.C.outputNegative (P.inputs i))) in neg;
    rewrite neg;
    destruct (C.C.needsNegation (P.inputs i));
    destruct (MulDiv.CIRCTBits.word 1 (if word 4 (nio_5Freq_5Fbits_5Ffn i)=?6 then 1 else 0)=?1);
    destruct (MulDiv.CIRCTBits.word 64 (O.E.magnitude (O.O.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i)))=?0);
    reflexivity.
Qed.
Local Opaque run step observe MulDiv.nMulDiv.run MulDiv.nMulDiv.step MulDiv.nMulDiv.observe.
Theorem signed_result_at_monitor_cycle s pins
  (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (pins O))=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=4 \/ word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=6)
  (resets : forall t, (t<68)%nat -> word 1 (nreset (pins t))=0)
  (kills : forall t, (t<68)%nat -> word 1 (nio_5Fkill (pins t))=0) :
  let n := (Z.to_nat (L.latency (step s (pins O)))+1)%nat in
  nio_5Fresp_5Fvalid (observe (run s pins n) (pins n))=1 /\
  nio_5Fresp_5Fbits_5Fdata (observe (run s pins n) (pins n))=S.specification (P.inputs (pins O)) /\
  nio_5Fresp_5Fbits_5Ftag (observe (run s pins n) (pins n))=word 5 (nio_5Freq_5Fbits_5Ftag (pins O)).
Proof.
  assert (live : MulDivTiming.MulDivTiming.active (fun t => P.inputs (pins t)) 68).
  { intros t bound; split; [apply resets|apply kills]; exact bound. }
  destruct (S.accepted_result_exact (P.state s) (fun t => P.inputs (pins t)) idle valid operation live)
    as [n [cycle [bound [response [data tag]]]]].
  rewrite <- (capture_cycle s (pins O) idle valid operation) in cycle; subst n.
  rewrite <-P.trace_projects in response,data,tag.
  exact (conj response (conj data tag)).
Qed.
End MulDivCheckedMonitorResult.
Print Assumptions MulDivCheckedMonitorResult.capture_cycle.
Print Assumptions MulDivCheckedMonitorResult.signed_result_at_monitor_cycle.

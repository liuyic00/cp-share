From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedData MulDivCheckedWitness MulDivCheckedLatency MulDivSignedOutput.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked MulDivCheckedHistory.MulDivCheckedHistory
  MulDivCheckedData.MulDivCheckedData MulDivCheckedLatency.MulDivCheckedLatency.
Open Scope Z_scope.
Module MulDivCheckedDivisionOutput.
Module P := MulDivCheckedProjection.MulDivCheckedProjection.
Module W := MulDivCheckedWitness.MulDivCheckedWitness.
Definition hi s := word 1 (Z.shiftr (word 4 (r11_ncontractFn s)) 1).
Definition chosen s := if hi s=?1 then snd (W.selected s) else fst (W.selected s).
Definition ResultRelation s :=
  (word 1 (r6_nresHi s)=hi s /\ word 1 (r16_ncontractWasNegated s)=0 /\ outputExtra s=0) \/
  (word 1 (r6_nresHi s)=0 /\ word 1 (r16_ncontractWasNegated s)=1 /\ outputExtra s=1 /\
    word 64 (r8_nremainder s)=word 64 (-chosen s)).
Lemma chosen_normal s : word 64 (chosen s)=chosen s.
Proof.
  unfold chosen,W.selected,witness,W.raw; destruct (hi s=?1);
    destruct (word 1 (r16_ncontractWasNegated s)=?1); cbn [fst snd]; apply normalize; lia.
Qed.
Lemma selected_node s i : v237 s i=chosen s.
Proof.
  pose proof (f_equal fst (W.source_nodes s i)) as q; pose proof (f_equal snd (W.source_nodes s i)) as r.
  cbn [fst snd] in q,r; unfold v237; rewrite q,r; change (word 64 (chosen s)=chosen s); apply chosen_normal.
Qed.
Lemma negative_node s i : v219 s i=outputExtra s.
Proof. unfold outputExtra; expand_latency; reflexivity. Qed.
Lemma division_value s i : v239 s i=word 64 (if outputExtra s=?1 then -chosen s else chosen s).
Proof.
  unfold v239,v238,v143; rewrite negative_node,selected_node; change (word 64 0) with 0; rewrite Z.sub_0_l.
  destruct (outputExtra s=?1); [apply normalize; lia|reflexivity].
Qed.
Lemma output_format s i (state : word 3 (r0_nstate s)=7) :
  nio_5Fresp_5Fbits_5Fdata (observe s i)=format (r1_nreq_5Fdw s)
    (if word 1 (r6_nresHi s)=?1 then word 64 (Z.shiftr (word 130 (r8_nremainder s)) 65) else word 64 (r8_nremainder s)).
Proof.
  pose proof (MulDivFormat.MulDivFormat.observe_format (P.state s) (P.inputs i) state) as result.
  rewrite <-P.observe_projects in result; exact result.
Qed.
Theorem output_correct s i (state : word 3 (r0_nstate s)=7) (division : v191 s i=1)
  (width : word 1 (r1_nreq_5Fdw s)=word 1 (r12_ncontractDw s)) (relation : ResultRelation s) :
  nio_5Fresp_5Fbits_5Fdata (observe s i)=v263 s i.
Proof.
  rewrite output_format by exact state; rewrite division_expected by exact division.
  rewrite division_value,format_normal.
  destruct relation as [[high [flag negative]]|[high [flag [negative value]]]].
  - rewrite high,negative; cbn [Z.eqb].
    unfold chosen; rewrite (W.from_raw s flag); unfold W.raw; cbn [fst snd].
    unfold format; rewrite width; reflexivity.
  - rewrite high,negative; cbn [Z.eqb]; rewrite value,format_normal.
    unfold format; rewrite width; reflexivity.
Qed.
Lemma hi_hold s i (busy : word 3 (r0_nstate s)<>0) : hi (step s i)=hi s.
Proof.
  pose proof (MulDivCheckedHistory.MulDivCheckedHistory.hold s i (or_introl busy)) as history.
  pose proof (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn history) as fn.
  change (word 4 (r11_ncontractFn (step s i))=word 4 (r11_ncontractFn s)) in fn.
  unfold hi; rewrite fn; reflexivity.
Qed.
Theorem negate_relation s i (state : word 3 (r0_nstate s)=5)
  (high : word 1 (r6_nresHi s)=hi s) (negative : outputExtra s=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) : ResultRelation (step s i).
Proof.
  destruct (MulDivSignedOutput.MulDivSignedOutput.negate_response (P.state s) (P.inputs i) state reset kill)
    as [next [select [value meta]]].
  rewrite <-P.step_projects in select,value.
  change (r6_nresHi (step s i)=0) in select.
  assert (flag : word 1 (r16_ncontractWasNegated (step s i))=1).
  { pose proof (f_equal (fun p=>fst (fst p)) (capture_witness s i state reset)) as h; exact h. }
  assert (busy : word 3 (r0_nstate s)<>0) by lia.
  destruct (captured_congruent (step s i) s (MulDivCheckedHistory.MulDivCheckedHistory.hold s i (or_introl busy))) as [extra [neg latency]].
  assert (chosenNext : chosen (step s i)=MulDivSignedOutput.MulDivSignedOutput.selected (P.state s)).
  { unfold chosen; rewrite (W.capture s i state reset),(hi_hold s i ltac:(lia)).
    unfold W.raw,MulDivSignedOutput.MulDivSignedOutput.selected.
    change (MulDiv.CIRCTBits.word 1 (MulDiv.nMulDiv.r6_nresHi (P.state s))) with (word 1 (r6_nresHi s)).
    rewrite high; reflexivity. }
  unfold ResultRelation; right; rewrite select,flag,neg,negative; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  rewrite chosenNext; exact value.
Qed.
End MulDivCheckedDivisionOutput.
Print Assumptions MulDivCheckedDivisionOutput.output_correct.

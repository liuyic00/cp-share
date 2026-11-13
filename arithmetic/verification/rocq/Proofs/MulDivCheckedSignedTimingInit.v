From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedSignedTimingEdges MulDivCheckedSignedOperands MulDivSignedBits.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedAge.MulDivCheckedAge
  MulDivCheckedLatency.MulDivCheckedLatency MulDivCheckedSignedTiming.MulDivCheckedSignedTiming
  MulDivCheckedSignedTimingEdges.MulDivCheckedSignedTimingEdges
  MulDivCheckedSignedOperands.MulDivCheckedSignedOperands.
Open Scope Z_scope.
Module MulDivCheckedSignedTimingInit.
Module X := MulDivSignedExecution.MulDivSignedExecution.
Module R := MulDivRefinement.MulDivRefinement.
Definition Prepared s :=
  word 3 (r0_nstate s)=3 /\ word 7 (r3_ncount s)=0 /\
  word 7 (r10_ncontractAge s)=inputExtra s /\
  word 65 (r7_ndivisor s)=word 64 (E.magnitude (operand s (r14_ncontractB s))) /\
  R.packed (P.state s)=word 64 (E.magnitude (operand s (r13_ncontractA s))) /\
  word 1 (r5_nisHi s)=hi s /\ word 1 (r4_nneg_5Fout s)=rawNegative s.
Lemma prepared_timing s (prepared : Prepared s) : TimingPhases s.
Proof. unfold Prepared,TimingPhases in *; right; left; intuition lia. Qed.
Lemma hi_normal s : word 1 (hi s)=hi s.
Proof. unfold hi; destruct (word 4 (r11_ncontractFn s)=?6); reflexivity. Qed.
Lemma negative_normal s : word 1 (rawNegative s)=rawNegative s.
Proof.
  unfold rawNegative; destruct (word 4 (r11_ncontractFn s)=?6).
  - unfold E.sign64; rewrite <-word_bridge; apply normalize; lia.
  - destruct (E.sign64 (operand s (r13_ncontractA s))=?E.sign64 (operand s (r14_ncontractB s))); reflexivity.
Qed.
Theorem first_edge s i (operation : Operation s) (prepared : Prepared s)
  (pending : word 1 (r9_ncontractPending s)=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) : LatePhases (step s i).
Proof.
  destruct prepared as [state [count [age [divisor [initial [high negative]]]]]].
  destruct (stable s i ltac:(lia)) as [sa [sb sl]].
  destruct (extra_bounds s) as [a b].
  pose proof (age_advance s i (or_introl state) ltac:(lia) pending reset) as increment.
  assert (next : r0_nstate (step s i)=3).
  { change (r0_nstate (step s i)) with (MulDiv.nMulDiv.r0_nstate (P.state (step s i))).
    rewrite P.step_projects,(MulDivControl.MulDivControl.div_state (P.state s) (P.inputs i) state reset kill).
    change (MulDiv.CIRCTBits.word 7 (MulDiv.nMulDiv.r3_ncount (P.state s))) with (word 7 (r3_ncount s)); rewrite count; reflexivity. }
  assert (counter : word 7 (r3_ncount (step s i))=1).
  { change (word 7 (MulDiv.nMulDiv.r3_ncount (P.state (step s i)))=1).
    rewrite P.step_projects,(MulDivControl.MulDivControl.compute_count (P.state s) (P.inputs i) (or_intror state)).
    change (word 7 (word 7 (word 7 (r3_ncount s)+1))=1); rewrite count; reflexivity. }
  assert (flag : r4_nneg_5Fout (step s i)=outputExtra s).
  { change (MulDiv.nMulDiv.r4_nneg_5Fout (P.state (step s i))=outputExtra s).
    rewrite P.step_projects,(X.first_flag (P.state s) (P.inputs i)
      (E.magnitude (operand s (r13_ncontractA s))) (E.magnitude (operand s (r14_ncontractB s))) state count divisor initial).
    rewrite (corrected_negative s operation); unfold X.effectiveNegative.
    change (MulDiv.CIRCTBits.word 1 (MulDiv.nMulDiv.r5_nisHi (P.state s))) with (word 1 (r5_nisHi s)).
    change (MulDiv.CIRCTBits.word 1 (MulDiv.nMulDiv.r4_nneg_5Fout (P.state s))) with (word 1 (r4_nneg_5Fout s)).
    rewrite high,negative; rewrite <-word_bridge; rewrite hi_normal,negative_normal; reflexivity. }
  unfold LatePhases; left; rewrite next,counter,increment,flag,sa,sb.
  assert (normal : word 1 (outputExtra s)=outputExtra s).
  { unfold outputExtra,v219; apply normalize; lia. }
  rewrite normal; repeat split; try reflexivity; lia.
Qed.
Lemma operand_congruent s t x y
  (width : word 1 (r12_ncontractDw s)=word 1 (r12_ncontractDw t))
  (value : word 64 x=word 64 y) : operand s x=operand t y.
Proof.
  assert (low : Words.word 32 x=Words.word 32 y).
  { change (word 32 x=word 32 y); rewrite <-(narrow 64 32 x ltac:(lia) ltac:(lia)),
      <-(narrow 64 32 y ltac:(lia) ltac:(lia)),value; reflexivity. }
  unfold operand; rewrite width; destruct (word 1 (r12_ncontractDw t)=?1); [exact value|].
  unfold SignedWords.signed; rewrite low; reflexivity.
Qed.
Lemma values_stable s i (state : word 3 (r0_nstate s)<>0) :
  operand (step s i) (r13_ncontractA (step s i))=operand s (r13_ncontractA s) /\
  operand (step s i) (r14_ncontractB (step s i))=operand s (r14_ncontractB s) /\
  hi (step s i)=hi s /\ rawNegative (step s i)=rawNegative s.
Proof.
  pose proof (hold s i (or_introl state)) as history.
  assert (a : word 64 (r13_ncontractA (step s i))=word 64 (r13_ncontractA s))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin1 history).
  assert (b : word 64 (r14_ncontractB (step s i))=word 64 (r14_ncontractB s))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fin2 history).
  assert (width : word 1 (r12_ncontractDw (step s i))=word 1 (r12_ncontractDw s))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fdw history).
  assert (fn : word 4 (r11_ncontractFn (step s i))=word 4 (r11_ncontractFn s))
    by exact (f_equal MulDiv.nMulDiv.nio_5Freq_5Fbits_5Ffn history).
  pose proof (operand_congruent _ _ _ _ width a) as oa.
  pose proof (operand_congruent _ _ _ _ width b) as ob.
  repeat split; try assumption; unfold hi,rawNegative; rewrite fn; try rewrite oa,ob; reflexivity.
Qed.
Definition Negating s :=
  word 3 (r0_nstate s)=1 /\ word 7 (r3_ncount s)=0 /\
  word 7 (r10_ncontractAge s)=0 /\ inputExtra s=1 /\
  r7_ndivisor s=MulDivSignedBits.MulDivSignedBits.extended65 (operand s (r14_ncontractB s)) /\
  R.packed (P.state s)=word 64 (operand s (r13_ncontractA s)) /\
  word 1 (r6_nresHi s)=0 /\ word 1 (r5_nisHi s)=hi s /\ word 1 (r4_nneg_5Fout s)=rawNegative s.
Theorem input_negation_edge s i (phase : Negating s)
  (pending : word 1 (r9_ncontractPending s)=1)
  (reset : word 1 (nreset i)=0) (kill : word 1 (nio_5Fkill i)=0) : Prepared (step s i).
Proof.
  destruct phase as [state [count [age [extra [divisor [initial [select [high negative]]]]]]]].
  destruct (values_stable s i ltac:(lia)) as [oa [ob [hiStable negStable]]].
  destruct (stable s i ltac:(lia)) as [sa [sb sl]].
  destruct (MulDivSignedBits.MulDivSignedBits.prepared_edge (P.state s) (P.inputs i)
    (operand s (r13_ncontractA s)) (operand s (r14_ncontractB s)) state count divisor initial select reset kill)
    as [next [counter [dv [rem [meta flag]]]]].
  rewrite <-P.step_projects in next,counter,dv,rem,meta,flag.
  assert (absent : v2 s i=0) by (apply busy; lia).
  pose proof (advance s i reset absent pending (phase_valid s i (or_introl state))) as increment.
  assert (highNext : word 1 (r5_nisHi (step s i))=word 1 (r5_nisHi s)).
  { exact (f_equal snd meta). }
  unfold Prepared; rewrite oa,ob,hiStable,negStable,sa.
  split; [exact next|]; split; [exact counter|]; split.
  - rewrite increment,age,extra; reflexivity.
  - split; [exact dv|]; split; [exact rem|]; split; [rewrite highNext; exact high|].
    change (word 1 (r4_nneg_5Fout (step s i))=word 1 (r4_nneg_5Fout s)) in flag; rewrite flag; exact negative.
Qed.
End MulDivCheckedSignedTimingInit.
Print Assumptions MulDivCheckedSignedTimingInit.first_edge.
Print Assumptions MulDivCheckedSignedTimingInit.input_negation_edge.

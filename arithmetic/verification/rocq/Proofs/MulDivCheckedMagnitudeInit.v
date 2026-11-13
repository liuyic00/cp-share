From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedMagnitude MulDivCheckedSignedTimingCapture MulDivUnsignedCapture.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedMagnitude.MulDivCheckedMagnitude
  MulDivCheckedLatency.MulDivCheckedLatency MulDivCheckedSignedTiming.MulDivCheckedSignedTiming
  MulDivCheckedSignedOperands.MulDivCheckedSignedOperands
  MulDivCheckedSignedTimingInit.MulDivCheckedSignedTimingInit.
Open Scope Z_scope.
Module MulDivCheckedMagnitudeInit.
Module U := MulDivUnsignedCapture.MulDivUnsignedCapture.
Lemma a_magnitude s i (operation : Operation s) : v272 s i=E.magnitude (operand s (r13_ncontractA s)).
Proof.
  unfold v272,v271,v143; rewrite (a_negative s i operation),(a_operand s i operation).
  unfold E.magnitude; change (MulDiv.CIRCTBits.word 64 (operand s (r13_ncontractA s))) with (word 64 (operand s (r13_ncontractA s))).
  rewrite operand_normal; change (word 64 0) with 0.
  destruct (E.sign64 (operand s (r13_ncontractA s))=?1).
  - change (word 64 (word 64 (-operand s (r13_ncontractA s)))=word 64 (-operand s (r13_ncontractA s))); apply normalize; lia.
  - apply operand_normal.
Qed.
Theorem signed_prepared s (operation : Operation s) (prepared : Prepared s) : Computing s.
Proof.
  destruct prepared as [state [count [age [dv [initial rest]]]]].
  assert (a : dividend s=E.magnitude (operand s (r13_ncontractA s))) by (apply a_magnitude; exact operation).
  assert (d : divisor s=E.magnitude (operand s (r14_ncontractB s))) by (apply b_magnitude; exact operation).
  destruct (parameter_bounds s) as [ab db].
  assert (an : word 64 (dividend s)=dividend s) by (apply Words.word_small; exact ab).
  assert (dn : word 64 (divisor s)=divisor s) by (apply Words.word_small; exact db).
  apply initialized_computing; try assumption.
  - rewrite <-d in dv; rewrite dn in dv; exact dv.
  - rewrite <-a in initial; rewrite an in initial; exact initial.
Qed.
Definition unsignedOperand s x := if word 1 (r12_ncontractDw s)=?1 then word 64 x else word 32 x.
Lemma unsigned_parameters s (operation : word 4 (r11_ncontractFn s)=5 \/ word 4 (r11_ncontractFn s)=7) :
  dividend s=unsignedOperand s (r13_ncontractA s) /\ divisor s=unsignedOperand s (r14_ncontractB s).
Proof.
  assert (sign : v194 s quiet=0).
  { unfold v194,v193,v31; destruct operation as [fn|fn]; rewrite fn; reflexivity. }
  assert (a : v202 s quiet=0) by (unfold v202; rewrite sign,Z.land_0_l; reflexivity).
  assert (b : v210 s quiet=0) by (unfold v210; rewrite sign,Z.land_0_l; reflexivity).
  unfold dividend,divisor,v272,v216; rewrite a,b; cbn [Z.eqb].
  unfold v200,v208,v199,v207,v197,v205,v196,v204,v198,v206; rewrite sign,!Z.land_0_l.
  change (word 32 (repeatWord 32 1 (word 1 0))) with 0.
  rewrite !Z.shiftl_0_l,!Z.add_0_l,!Z.shiftr_0_r.
  unfold unsignedOperand; destruct (word 1 (r12_ncontractDw s)=?1);
    repeat rewrite normalize by lia; [split; reflexivity|].
  rewrite (narrow 64 32 (r13_ncontractA s)),(narrow 64 32 (r14_ncontractB s)) by lia; split; apply Words.word_widen; lia.
Qed.
Lemma unsigned_capture_parameters s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7) :
  dividend (step s i)=U.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin1 i) /\
  divisor (step s i)=U.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i).
Proof.
  pose proof (capture s i idle valid) as history.
  assert (fn : word 4 (r11_ncontractFn (step s i))=word 4 (nio_5Freq_5Fbits_5Ffn i)) by exact (f_equal Core.nio_5Freq_5Fbits_5Ffn history).
  assert (dw : word 1 (r12_ncontractDw (step s i))=word 1 (nio_5Freq_5Fbits_5Fdw i)) by exact (f_equal Core.nio_5Freq_5Fbits_5Fdw history).
  assert (a : word 64 (r13_ncontractA (step s i))=word 64 (nio_5Freq_5Fbits_5Fin1 i)) by exact (f_equal Core.nio_5Freq_5Fbits_5Fin1 history).
  assert (b : word 64 (r14_ncontractB (step s i))=word 64 (nio_5Freq_5Fbits_5Fin2 i)) by exact (f_equal Core.nio_5Freq_5Fbits_5Fin2 history).
  destruct (unsigned_parameters (step s i) ltac:(rewrite fn; exact operation)) as [pa pd]; rewrite pa,pd.
  unfold unsignedOperand,U.operand; change (MulDiv.CIRCTBits.word 1 (Core.nio_5Freq_5Fbits_5Fdw (P.inputs i))) with (word 1 (nio_5Freq_5Fbits_5Fdw i)); rewrite dw.
  destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); [split; assumption|].
  split.
  - rewrite <-(narrow 64 32 (r13_ncontractA (step s i)) ltac:(lia) ltac:(lia)),a,narrow by lia; reflexivity.
  - rewrite <-(narrow 64 32 (r14_ncontractB (step s i)) ltac:(lia) ltac:(lia)),b,narrow by lia; reflexivity.
Qed.
Theorem unsigned_capture s i (idle : word 3 (r0_nstate s)=0) (valid : word 1 (nio_5Freq_5Fvalid i)=1)
  (reset : word 1 (nreset i)=0)
  (operation : word 4 (nio_5Freq_5Fbits_5Ffn i)=5 \/ word 4 (nio_5Freq_5Fbits_5Ffn i)=7) :
  word 3 (r0_nstate (step s i))=3 /\ word 7 (r3_ncount (step s i))=0 /\ Computing (step s i).
Proof.
  destruct (U.capture (P.state s) (P.inputs i) idle valid reset operation) as [st [ct [dv [initial rest]]]].
  rewrite <-P.step_projects in st,ct,dv,initial.
  change (r0_nstate (step s i)=3) in st; change (r3_ncount (step s i)=0) in ct.
  destruct (unsigned_capture_parameters s i idle valid operation) as [a d].
  split; [rewrite st; reflexivity|]; split; [rewrite ct; reflexivity|].
  apply initialized_computing; [rewrite st; reflexivity|rewrite ct; reflexivity| |].
  - change (word 65 (Core.r7_ndivisor (P.state (step s i)))=divisor (step s i)).
    rewrite dv,d; apply Words.word_small.
    pose proof (U.operand_bound (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i));
      change (2^64) with 18446744073709551616 in *; change (0<=U.operand (P.inputs i) (nio_5Freq_5Fbits_5Fin2 i)<36893488147419103232); lia.
  - rewrite a; exact initial.
Qed.
End MulDivCheckedMagnitudeInit.
Print Assumptions MulDivCheckedMagnitudeInit.signed_prepared.
Print Assumptions MulDivCheckedMagnitudeInit.unsigned_capture.

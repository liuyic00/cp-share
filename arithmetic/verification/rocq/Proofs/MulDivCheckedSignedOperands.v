From Coq Require Import ZArith Lia Bool.
From Proofs Require Import MulDivCheckedSignedTiming MulDivCheckedHistory MulDivSignedOperands MulDivSignedCapture MulDivFormat MulDivSignedExecution.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivChecked.nMulDivChecked
  MulDivCheckedHistory.MulDivCheckedHistory MulDivCheckedSignedTiming.MulDivCheckedSignedTiming
  MulDivCheckedLatency.MulDivCheckedLatency.
Open Scope Z_scope.
Module MulDivCheckedSignedOperands.
Module O := MulDivSignedOperands.MulDivSignedOperands.
Module E := MulDivSignedInputEdge.MulDivSignedInputEdge.
Definition operand s x := if word 1 (r12_ncontractDw s)=?1 then word 64 x else word 64 (SignedWords.signed 32 x).
Lemma core_operand s x : operand s x=O.operand (captured s) x.
Proof.
  unfold operand,O.operand,captured; cbn [MulDiv.nMulDiv.nio_5Freq_5Fbits_5Fdw].
  change (MulDiv.CIRCTBits.word 1 (word 1 (r12_ncontractDw s))) with (word 1 (word 1 (r12_ncontractDw s))).
  rewrite normalize by lia; reflexivity.
Qed.
Lemma word_bridge : word=MulDiv.CIRCTBits.word. Proof. reflexivity. Qed.
Lemma repeat_bridge : repeatWord=MulDiv.CIRCTBits.repeatWord. Proof. reflexivity. Qed.
Local Opaque word MulDiv.CIRCTBits.word repeatWord MulDiv.CIRCTBits.repeatWord.
Lemma extend_wire x : word 64 (Z.shiftl (word 32 (repeatWord 32 1 (word 1 (Z.shiftr (word 64 x) 31)))) 32+
  word 32 (Z.shiftr (word 64 x) 0))=word 64 (SignedWords.signed 32 x).
Proof.
  transitivity (word 64 (SignedWords.signed 32 (word 64 x))).
  - pose proof (MulDivFormat.MulDivFormat.extend_wire (word 64 x)) as result.
    rewrite <-word_bridge,<-repeat_bridge in result; exact result.
  - unfold SignedWords.signed; change (Words.word 32 (word 64 x)) with (word 32 (word 64 x));
      rewrite narrow by lia; reflexivity.
Qed.
Local Transparent word MulDiv.CIRCTBits.word repeatWord MulDiv.CIRCTBits.repeatWord.
Lemma signed_bit s i (operation : Operation s) : v194 s i=1.
Proof. unfold v194,v193,v31; destruct operation as [fn|fn]; rewrite fn; reflexivity. Qed.
Lemma a_operand s i (operation : Operation s) : v200 s i=operand s (r13_ncontractA s).
Proof.
  unfold v200,v199,v198,v197,v196; rewrite (signed_bit s i operation).
  assert (sign : word 1 (Z.land 1 (v195 s i))=v195 s i).
  { unfold v195; destruct (bit_cases (Z.shiftr (word 64 (r13_ncontractA s)) 31)) as [h|h]; rewrite h; reflexivity. }
  rewrite sign; unfold operand; destruct (word 1 (r12_ncontractDw s)=?1).
  - apply normalize; lia.
  - rewrite normalize by lia; unfold v195; apply extend_wire.
Qed.
Lemma b_operand s i (operation : Operation s) : v208 s i=operand s (r14_ncontractB s).
Proof.
  unfold v208,v207,v206,v205,v204; rewrite (signed_bit s i operation).
  assert (sign : word 1 (Z.land 1 (v203 s i))=v203 s i).
  { unfold v203; destruct (bit_cases (Z.shiftr (word 64 (r14_ncontractB s)) 31)) as [h|h]; rewrite h; reflexivity. }
  rewrite sign; unfold operand; destruct (word 1 (r12_ncontractDw s)=?1).
  - apply normalize; lia.
  - rewrite normalize by lia; unfold v203; apply extend_wire.
Qed.
Lemma operand_normal s x : word 64 (operand s x)=operand s x.
Proof. unfold operand; destruct (word 1 (r12_ncontractDw s)=?1); apply normalize; lia. Qed.
Lemma a_negative s i (operation : Operation s) : v202 s i=E.sign64 (operand s (r13_ncontractA s)).
Proof.
  unfold v202,v201; rewrite (signed_bit s i operation),(a_operand s i operation).
  unfold E.sign64; change (MulDiv.CIRCTBits.word 64 (operand s (r13_ncontractA s))) with (word 64 (operand s (r13_ncontractA s))).
  rewrite operand_normal.
  rewrite <-word_bridge.
  destruct (bit_cases (Z.shiftr (operand s (r13_ncontractA s)) 63)) as [h|h]; rewrite h; reflexivity.
Qed.
Lemma b_negative s i (operation : Operation s) : v210 s i=E.sign64 (operand s (r14_ncontractB s)).
Proof.
  unfold v210,v209; rewrite (signed_bit s i operation),(b_operand s i operation).
  unfold E.sign64; change (MulDiv.CIRCTBits.word 64 (operand s (r14_ncontractB s))) with (word 64 (operand s (r14_ncontractB s))).
  rewrite operand_normal.
  rewrite <-word_bridge.
  destruct (bit_cases (Z.shiftr (operand s (r14_ncontractB s)) 63)) as [h|h]; rewrite h; reflexivity.
Qed.
Lemma b_magnitude s i (operation : Operation s) : v216 s i=E.magnitude (operand s (r14_ncontractB s)).
Proof.
  unfold v216,v215,v143; rewrite (b_negative s i operation),(b_operand s i operation).
  unfold E.magnitude; change (MulDiv.CIRCTBits.word 64 (operand s (r14_ncontractB s))) with (word 64 (operand s (r14_ncontractB s))).
  rewrite operand_normal; change (word 64 0) with 0.
  destruct (E.sign64 (operand s (r14_ncontractB s))=?1).
  - change (word 64 (word 64 (-operand s (r14_ncontractB s)))=word 64 (-operand s (r14_ncontractB s))); apply normalize; lia.
  - apply operand_normal.
Qed.
Definition hi s := if word 4 (r11_ncontractFn s)=?6 then 1 else 0.
Definition rawNegative s := if word 4 (r11_ncontractFn s)=?6 then E.sign64 (operand s (r13_ncontractA s))
  else if E.sign64 (operand s (r13_ncontractA s))=?E.sign64 (operand s (r14_ncontractB s)) then 0 else 1.
Lemma corrected_negative s (operation : Operation s) : outputExtra s=
  MulDivSignedExecution.MulDivSignedExecution.effectiveNegative
    (E.magnitude (operand s (r14_ncontractB s))) (hi s) (rawNegative s).
Proof.
  assert (a : E.sign64 (operand s (r13_ncontractA s))=0 \/ E.sign64 (operand s (r13_ncontractA s))=1)
    by (unfold E.sign64; apply Words.bit_cases).
  assert (b : E.sign64 (operand s (r14_ncontractB s))=0 \/ E.sign64 (operand s (r14_ncontractB s))=1)
    by (unfold E.sign64; apply Words.bit_cases).
  assert (mag : MulDiv.CIRCTBits.word 64 (E.magnitude (operand s (r14_ncontractB s)))=E.magnitude (operand s (r14_ncontractB s))).
  { unfold E.magnitude; destruct (E.sign64 (operand s (r14_ncontractB s))=?1); apply Words.word_idem; lia. }
  unfold outputExtra,v219,v218,v217,v214; rewrite (a_negative s quiet operation),(b_negative s quiet operation),(b_magnitude s quiet operation).
  unfold MulDivSignedExecution.MulDivSignedExecution.effectiveNegative; rewrite mag.
  unfold v213,v143,hi,rawNegative.
  destruct operation as [fn|fn]; rewrite fn;
    destruct a as [a|a]; destruct b as [b|b]; rewrite a,b;
    change (word 64 0) with 0;
    destruct (E.magnitude (operand s (r14_ncontractB s))=?0); reflexivity.
Qed.
End MulDivCheckedSignedOperands.
Print Assumptions MulDivCheckedSignedOperands.corrected_negative.
Print Assumptions MulDivCheckedSignedOperands.a_operand.
Print Assumptions MulDivCheckedSignedOperands.b_magnitude.

From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords MulDivControl MulDivRefinement MulDivMultiply MulDivMultiplyBalance MulDivMultiplyRun MulDivMultiplySigned.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivMultiply.MulDivMultiply MulDivMultiplyBalance.MulDivMultiplyBalance MulDivMultiplyRun.MulDivMultiplyRun MulDivMultiplySigned.MulDivMultiplySigned.
Open Scope Z_scope.
Module MulDivMultiplySignedStep.
Lemma signed_definition w x : SignedWords.signed w x=
  if word w x <? 2^(w-1) then word w x else word w x-2^w.
Proof. reflexivity. Qed.
Lemma signed_concat w k x l (hw : 1<=w) (hk : 0<=k) (hl : 0<=l<2^k) :
  SignedWords.signed (w+k) (word w x*2^k+l)=SignedWords.signed w x*2^k+l.
Proof.
  pose proof (bounds w x ltac:(lia)) as hx.
  assert (pk : 0<2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (total : word (w+k) (word w x*2^k+l)=word w x*2^k+l).
  { apply Words.word_small; rewrite Z.pow_add_r by lia; nia. }
  rewrite !signed_definition,total.
  replace (w+k-1) with ((w-1)+k) by lia; rewrite !Z.pow_add_r by lia.
  destruct (Z.ltb_spec (word w x) (2^(w-1))) as [pos|neg];
    destruct (Z.ltb_spec (word w x*2^k+l) (2^(w-1)*2^k)); try nia; ring.
Qed.
Lemma packed_int s : SignedWords.signed 129 (packed s)=
  SignedWords.signed 65 (accumulator s)*2^64+low s.
Proof.
  rewrite packed_exact.
  assert (normal : word 65 (accumulator s)=accumulator s) by (unfold accumulator; apply normalize; lia).
  pose proof (signed_concat 65 64 (accumulator s) (low s) ltac:(lia) ltac:(lia)
    ltac:(unfold low; apply bounds; lia)) as result.
  rewrite normal in result; exact result.
Qed.
Lemma shifted_low s : word 63 (Z.shiftr (word 130 (r8_nremainder s)) 1)=low s/2.
Proof.
  rewrite (extract_normal 130 63 1 (r8_nremainder s)) by lia.
  rewrite <- (extract_normal 64 63 1 (r8_nremainder s)) by lia.
  rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; unfold low.
  apply Words.word_small; pose proof (bounds 64 (r8_nremainder s) ltac:(lia)) as hl.
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
  change (2^64) with 18446744073709551616 in hl; change (2^63) with 9223372036854775808; lia.
Qed.
Theorem signed_step_int s i (state : word 3 (r0_nstate s)=2)
  (digits : coefficient s= -1 \/ coefficient s=0 \/ coefficient s=1)
  (hb : -(2^64)<SignedWords.signed 65 (r7_ndivisor s)<2^64)
  (ha : -(2^64)<SignedWords.signed 65 (accumulator s)<2^64) :
  SignedWords.signed 129 (packed (step s i))=
    (coefficient s*SignedWords.signed 65 (r7_ndivisor s)+SignedWords.signed 65 (accumulator s))*2^63+low s/2.
Proof.
  rewrite product_edge by exact state.
  assert (normal : word 66 (rawProduct s)=rawProduct s) by (unfold rawProduct; apply normalize; lia).
  pose proof (signed_concat 66 63 (rawProduct s)
    (word 63 (Z.shiftr (word 130 (r8_nremainder s)) 1)) ltac:(lia) ltac:(lia)
    ltac:(apply bounds; lia)) as result.
  change (66+63) with 129 in result; rewrite normal in result; rewrite result,shifted_low,signed_raw_exact by assumption; reflexivity.
Qed.
Theorem signed_step_balance s i (state : word 3 (r0_nstate s)=2)
  (digits : coefficient s= -1 \/ coefficient s=0 \/ coefficient s=1)
  (hb : -(2^64)<SignedWords.signed 65 (r7_ndivisor s)<2^64)
  (ha : -(2^64)<SignedWords.signed 65 (accumulator s)<2^64) :
  2*SignedWords.signed 129 (packed (step s i))+digit s=
    SignedWords.signed 129 (packed s)+2^64*coefficient s*SignedWords.signed 65 (r7_ndivisor s).
Proof.
  rewrite signed_step_int by assumption; rewrite packed_int; unfold digit.
  pose proof (Z.div_mod (low s) 2 ltac:(lia)).
  change (2^64) with 18446744073709551616; change (2^63) with 9223372036854775808; nia.
Qed.
Lemma signed_half p (hp : 0<=p<2^66) :
  SignedWords.signed 65 (p/2)=SignedWords.signed 66 p/2.
Proof.
  pose proof (Z.div_mod p 2 ltac:(lia)) as split.
  pose proof (Z.mod_pos_bound p 2 ltac:(lia)) as bit.
  assert (half : 0<=p/2<2^65).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
    change (2^66) with 73786976294838206464 in hp; change (2^65) with 36893488147419103232; lia. }
  pose proof (signed_concat 65 1 (p/2) (p mod 2) ltac:(lia) ltac:(lia) bit) as join.
  assert (normal : word 65 (p/2)=p/2) by (apply Words.word_small; exact half).
  rewrite normal in join; change (65+1) with 66 in join; change (2^1) with 2 in join.
  replace (p/2*2+p mod 2) with p in join by lia.
  apply Z.div_unique with (r:=p mod 2); [left; exact bit|lia].
Qed.
Theorem accumulator_step s i (state : word 3 (r0_nstate s)=2) :
  SignedWords.signed 65 (accumulator (step s i))=SignedWords.signed 66 (rawProduct s)/2.
Proof.
  pose proof (product_edge s i state) as edge; rewrite packed_exact in edge.
  pose proof (bounds 66 (rawProduct s) ltac:(lia)) as productBound.
  assert (normal : word 66 (rawProduct s)=rawProduct s) by (unfold rawProduct; apply normalize; lia).
  rewrite normal in productBound.
  pose proof (bounds 64 (r8_nremainder (step s i)) ltac:(lia)) as lo; fold (low (step s i)) in lo.
  pose proof (bounds 63 (Z.shiftr (word 130 (r8_nremainder s)) 1) ltac:(lia)) as shift.
  pose proof (Z.div_mod (rawProduct s) 2 ltac:(lia)) as split.
  pose proof (Z.mod_pos_bound (rawProduct s) 2 ltac:(lia)) as bit.
  assert (half : accumulator (step s i)=rawProduct s/2).
  { change (2^64) with 18446744073709551616 in edge,lo;
      change (2^63) with 9223372036854775808 in edge,shift; nia. }
  rewrite half; apply signed_half; exact productBound.
Qed.
Theorem accumulator_range s i (state : word 3 (r0_nstate s)=2)
  (digits : coefficient s= -1 \/ coefficient s=0 \/ coefficient s=1)
  (hb : -(2^64)<SignedWords.signed 65 (r7_ndivisor s)<2^64)
  (ha : -(2^64)<SignedWords.signed 65 (accumulator s)<2^64) :
  -(2^64)<SignedWords.signed 65 (accumulator (step s i))<2^64.
Proof.
  rewrite accumulator_step by exact state; rewrite signed_raw_exact by assumption.
  apply signed_accumulator_bound; assumption.
Qed.
End MulDivMultiplySignedStep.
Print Assumptions MulDivMultiplySignedStep.signed_step_int.
Print Assumptions MulDivMultiplySignedStep.signed_step_balance.
Print Assumptions MulDivMultiplySignedStep.accumulator_range.

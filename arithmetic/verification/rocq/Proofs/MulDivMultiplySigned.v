From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords WordBits MulDivControl MulDivRefinement MulDivMultiply MulDivMultiplyRun.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivMultiply.MulDivMultiply MulDivMultiplyRun.MulDivMultiplyRun.
Open Scope Z_scope.
Module MulDivMultiplySigned.
Lemma coefficient_encoding sg bit (hs : sg=0 \/ sg=1) :
  word 66 (Z.shiftl (word 65 (repeatWord 65 1 sg)) 1+bit)=word 66 (bit-2*sg).
Proof.
  destruct hs as [hs|hs]; rewrite hs.
  - change (word 65 (repeatWord 65 1 0)) with 0; change (Z.shiftl 0 1) with 0.
    f_equal; ring.
  - change (word 65 (repeatWord 65 1 1)) with 36893488147419103231.
    change (Z.shiftl 36893488147419103231 1) with 73786976294838206462.
    replace (73786976294838206462+bit) with ((bit-2*1)+1*2^66) by (change (2^66) with 73786976294838206464; ring).
    unfold word; apply Z.mod_add; discriminate.
Qed.
Lemma multiply_add_normal c b a :
  word 66 (word 66 (word 66 c*word 66 b)+word 66 a)=word 66 (c*b+a).
Proof.
  assert (prod : word 66 (word 66 c*word 66 b)=word 66 (c*b)).
  { unfold word; symmetry; apply Z.mul_mod; discriminate. }
  rewrite prod; unfold word; symmetry; apply Z.add_mod; discriminate.
Qed.
Lemma divisor_encoding s :
  word 66 (Z.shiftl (word 1 (Z.shiftr (word 65 (r7_ndivisor s)) 64)) 65+word 65 (r7_ndivisor s))=
  word 66 (SignedWords.signed 65 (r7_ndivisor s)).
Proof.
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (word 1 (Z.shiftr (word 65 (r7_ndivisor s)) 64)*2^65) with
    (2^65*word 1 (Z.shiftr (word 65 (r7_ndivisor s)) 64)) by ring.
  exact (WordBits.extend_one 65 (r7_ndivisor s) ltac:(lia)).
Qed.
Lemma accumulator_encoding s :
  word 66 (Z.shiftl (word 1 (Z.shiftr (word 130 (r8_nremainder s)) 129)) 65+accumulator s)=
  word 66 (SignedWords.signed 65 (accumulator s)).
Proof.
  assert (bridge : word 1 (Z.shiftr (accumulator s) 64)=word 1 (Z.shiftr (word 130 (r8_nremainder s)) 129)).
  { unfold accumulator; exact (WordBits.extract_extract 65 1 65 64 (word 130 (r8_nremainder s)) ltac:(lia) ltac:(lia) ltac:(lia)). }
  rewrite <- bridge,Z.shiftl_mul_pow2 by lia.
  assert (normal : word 65 (accumulator s)=accumulator s) by (unfold accumulator; apply normalize; lia).
  pose proof (WordBits.extend_one 65 (accumulator s) ltac:(lia)) as ext.
  change (word 66 (2^65*word 1 (Z.shiftr (word 65 (accumulator s)) 64)+word 65 (accumulator s))=word 66 (SignedWords.signed 65 (accumulator s))) in ext.
  rewrite normal in ext; rewrite Z.mul_comm; exact ext.
Qed.
Theorem raw_signed s : rawProduct s=word 66
  ((word 1 (Z.shiftr (word 130 (r8_nremainder s)) 0)-2*sign s)*
    SignedWords.signed 65 (r7_ndivisor s)+SignedWords.signed 65 (accumulator s)).
Proof.
  unfold rawProduct; rewrite coefficient_encoding by (unfold sign; apply bit_cases).
  rewrite divisor_encoding; fold (accumulator s); rewrite accumulator_encoding; apply multiply_add_normal.
Qed.
Theorem signed_partial_sum c b a (digit : c= -1 \/ c=0 \/ c=1)
  (hb : -(2^64)<b<2^64) (ha : -(2^64)<a<2^64) :
  SignedWords.signed 66 (word 66 (word 66 (word 66 c*word 66 b)+word 66 a))=c*b+a.
Proof.
  rewrite multiply_add_normal; rewrite SignedWords.signed_normal by lia.
  apply SignedWords.signed_small; [lia|].
  change (2^(66-1)) with 36893488147419103232; change (2^64) with 18446744073709551616 in ha,hb.
  destruct digit as [h|[h|h]]; rewrite h; lia.
Qed.
Definition coefficient s := word 1 (Z.shiftr (word 130 (r8_nremainder s)) 0)-2*sign s.
Theorem signed_raw_exact s
  (digit : coefficient s= -1 \/ coefficient s=0 \/ coefficient s=1)
  (hb : -(2^64)<SignedWords.signed 65 (r7_ndivisor s)<2^64)
  (ha : -(2^64)<SignedWords.signed 65 (accumulator s)<2^64) :
  SignedWords.signed 66 (rawProduct s)=coefficient s*SignedWords.signed 65 (r7_ndivisor s)+SignedWords.signed 65 (accumulator s).
Proof.
  rewrite raw_signed; fold (coefficient s).
  rewrite <- multiply_add_normal; apply signed_partial_sum; assumption.
Qed.
Theorem signed_accumulator_bound c b a (digit : c= -1 \/ c=0 \/ c=1)
  (hb : -(2^64)<b<2^64) (ha : -(2^64)<a<2^64) :
  -(2^64)<(c*b+a)/2<2^64.
Proof.
  assert (sum : -2*2^64+2<=c*b+a<=2*2^64-2).
  { destruct digit as [h|[h|h]]; rewrite h; lia. }
  pose proof (Z.div_mod (c*b+a) 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound (c*b+a) 2 ltac:(lia)); lia.
Qed.
End MulDivMultiplySigned.
Print Assumptions MulDivMultiplySigned.raw_signed.
Print Assumptions MulDivMultiplySigned.signed_partial_sum.
Print Assumptions MulDivMultiplySigned.signed_accumulator_bound.
Print Assumptions MulDivMultiplySigned.signed_raw_exact.

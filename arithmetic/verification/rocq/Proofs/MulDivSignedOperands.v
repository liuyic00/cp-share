From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords MulDivControl MulDivRefinement MulDivFormat MulDivSignedInputEdge.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivFormat.MulDivFormat MulDivSignedInputEdge.MulDivSignedInputEdge.
Open Scope Z_scope.
Module MulDivSignedOperands.
Definition operand i x := if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then word 64 x else word 64 (SignedWords.signed 32 x).
Definition inputSign i x := if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then sign64 x else word 1 (Z.shiftr (word 64 x) 31).
Lemma operand_normal i x : word 64 (operand i x)=operand i x.
Proof. unfold operand; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1); apply normalize; lia. Qed.
Lemma extended32_sign x : sign64 (word 64 (SignedWords.signed 32 x))=word 1 (Z.shiftr (word 64 x) 31).
Proof.
  unfold sign64; rewrite normalize by lia; rewrite (extract_normal 64 1 31 x) by lia.
  rewrite <- (extract_normal 32 1 31 x) by lia.
  unfold SignedWords.signed.
  change (word 1 (Z.shiftr (word 64 (if word 32 x <? 2147483648 then word 32 x else word 32 x-4294967296)) 63)=word 1 (Z.shiftr (word 32 x) 31)).
  pose proof (Words.word_bound 32 x ltac:(lia)) as hx.
  change (0<=word 32 x<4294967296) in hx.
  destruct (word 32 x <? 2147483648) eqn:sgn.
  - apply Z.ltb_lt in sgn.
    assert (norm : word 64 (word 32 x)=word 32 x) by (apply Words.word_widen; lia).
    rewrite norm,!Z.shiftr_div_pow2 by lia.
    rewrite !Z.div_small by (change (0<=word 32 x<9223372036854775808) || change (0<=word 32 x<2147483648); lia).
    reflexivity.
  - apply Z.ltb_ge in sgn.
    assert (encoded : word 64 (word 32 x-4294967296)=word 32 x-4294967296+18446744073709551616).
    { unfold word at 1; symmetry; apply Z.mod_unique with (q:= -1); [left|]; change (2^64) with 18446744073709551616; lia. }
    rewrite encoded,!Z.shiftr_div_pow2 by lia.
    assert (high : (word 32 x-4294967296+18446744073709551616)/2^63=1).
    { symmetry; apply Z.div_unique with (r:=word 32 x-4294967296+9223372036854775808); [left|]; change (2^63) with 9223372036854775808; lia. }
    assert (low : word 32 x/2^31=1).
    { symmetry; apply Z.div_unique with (r:=word 32 x-2147483648); [left|]; change (2^31) with 2147483648; lia. }
    rewrite high,low; reflexivity.
Qed.
Lemma operand_sign i x : sign64 (operand i x)=inputSign i x.
Proof.
  unfold operand,inputSign; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1).
  - unfold sign64; rewrite normalize by lia; reflexivity.
  - apply extended32_sign.
Qed.
Definition highWord i x := word 32 (if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1
  then word 32 (Z.shiftr (word 64 x) 32) else word 32 (repeatWord 32 1 (inputSign i x))).
Lemma joined_operand i x :
  word 64 (Z.shiftl (highWord i x) 32+word 32 (Z.shiftr (word 64 x) 0))=operand i x.
Proof.
  unfold highWord,operand,inputSign; destruct (word 1 (nio_5Freq_5Fbits_5Fdw i)=?1).
  - rewrite normalize by lia; apply join_halves.
  - rewrite normalize by lia; rewrite extend_wire.
    unfold SignedWords.signed.
    change (word 64 (if word 32 (word 64 x) <? 2^(32-1) then word 32 (word 64 x) else word 32 (word 64 x)-2^32)=word 64 (if word 32 x <? 2^(32-1) then word 32 x else word 32 x-2^32)).
    rewrite narrow by lia; reflexivity.
Qed.
Lemma joined_exact i x : Z.shiftl (highWord i x) 32+word 32 (Z.shiftr (word 64 x) 0)=operand i x.
Proof.
  pose proof (joined_operand i x) as joined.
  assert (high : 0<=highWord i x<2^32) by (unfold highWord; apply Words.word_bound; lia).
  pose proof (Words.word_bound 32 (Z.shiftr (word 64 x) 0) ltac:(lia)) as low.
  change (0<=highWord i x<4294967296) in high.
  change (0<=word 32 (Z.shiftr (word 64 x) 0)<4294967296) in low.
  assert (normal : word 64 (Z.shiftl (highWord i x) 32+word 32 (Z.shiftr (word 64 x) 0))=Z.shiftl (highWord i x) 32+word 32 (Z.shiftr (word 64 x) 0)).
  { apply Words.word_small; rewrite Z.shiftl_mul_pow2 by lia.
    change (0<=highWord i x*4294967296+word 32 (Z.shiftr (word 64 x) 0)<18446744073709551616); lia. }
  rewrite normal in joined; exact joined.
Qed.
End MulDivSignedOperands.
Print Assumptions MulDivSignedOperands.operand_sign.
Print Assumptions MulDivSignedOperands.joined_operand.
Print Assumptions MulDivSignedOperands.joined_exact.

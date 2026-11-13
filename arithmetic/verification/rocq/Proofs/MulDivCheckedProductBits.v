From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivCheckedHistory SignedWords WordBits.
From Generated Require Import MulDivChecked.
Import MulDivChecked.CIRCTBits MulDivCheckedHistory.MulDivCheckedHistory.
Open Scope Z_scope.
Module MulDivCheckedProductBits.
Lemma product_mod a b : word 128 (word 128 a*word 128 b)=word 128 (a*b).
Proof. unfold word; symmetry; apply Z.mul_mod; discriminate. Qed.
Lemma high x : word 64 (Z.shiftr (word 128 x) 64)=word 64 (x/2^64).
Proof.
  pose proof (WordBits.extract_normal 128 64 64 x ltac:(lia) ltac:(lia) ltac:(lia)) as extract.
  rewrite !Z.shiftr_div_pow2 in extract by lia; rewrite Z.shiftr_div_pow2 by lia; exact extract.
Qed.
Lemma low x : word 64 (word 128 x)=word 64 x.
Proof. apply narrow; lia. Qed.
Lemma sign_extend x :
  word 128 (Z.shiftl (word 64 (repeatWord 64 1 (word 1 (Z.shiftr (word 64 x) 63)))) 64+word 64 x)=
  word 128 (SignedWords.signed 64 x).
Proof.
  rewrite SignedWords.signed_from_bits by lia.
  change (word 128 (Z.shiftl (word 64 (repeatWord 64 1 (word 1 (Z.shiftr (word 64 x) 63)))) 64+word 64 x)=
    word 128 (word 64 x-2^64*word 1 (Z.shiftr (word 64 x) 63))).
  destruct (bit_cases (Z.shiftr (word 64 x) 63)) as [bit|bit]; rewrite bit.
  - change (word 64 (repeatWord 64 1 0)) with 0; rewrite Z.shiftl_0_l,Z.add_0_l,Z.mul_0_r,Z.sub_0_r; reflexivity.
  - change (word 64 (repeatWord 64 1 1)) with (2^64-1).
    rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mul_1_r.
    replace ((2^64-1)*2^64+word 64 x) with ((word 64 x-2^64)+2^128) by (change (2^64) with 18446744073709551616; change (2^128) with 340282366920938463463374607431768211456; ring).
    unfold word at 1 3; rewrite Z.add_mod,Z.mod_same,Z.add_0_r,Z.mod_mod by discriminate; reflexivity.
Qed.
Lemma signed_high a b :
  word 64 (Z.shiftr (word 128 (word 128 (SignedWords.signed 64 a)*word 128 (SignedWords.signed 64 b))) 64)=
  word 64 ((SignedWords.signed 64 a*SignedWords.signed 64 b)/2^64).
Proof. rewrite product_mod; apply high. Qed.
Lemma mixed_high a b :
  word 64 (Z.shiftr (word 128 (word 128 (SignedWords.signed 64 a)*word 128 (word 64 b))) 64)=
  word 64 ((SignedWords.signed 64 a*word 64 b)/2^64).
Proof. rewrite product_mod; apply high. Qed.
Lemma product_word a b : word 32 (word 64 a*word 64 b)=word 32 (SignedWords.signed 32 b*word 32 a).
Proof.
  assert (signed : word 32 (SignedWords.signed 32 b)=word 32 b) by (apply SignedWords.word_signed; lia).
  assert (mod_product : forall x y, word 32 (x*y)=word 32 (word 32 x*word 32 y)) by (intros; unfold word; apply Z.mul_mod; discriminate).
  rewrite (mod_product (word 64 a) (word 64 b)),(mod_product (SignedWords.signed 32 b) (word 32 a)).
  rewrite !narrow,signed by lia; f_equal; ring.
Qed.
End MulDivCheckedProductBits.
Print Assumptions MulDivCheckedProductBits.sign_extend.
Print Assumptions MulDivCheckedProductBits.product_word.

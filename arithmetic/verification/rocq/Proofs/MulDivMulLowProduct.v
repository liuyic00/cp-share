From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords MulDivControl MulDivTiming MulDivMultiply MulDivMultiplyBalance MulDivMultiplyRun MulDivMultiplySigned MulDivMultiplySignedStep MulDivMultiplySignedRun MulDivMultiplySignedProduct.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivMultiply.MulDivMultiply MulDivMultiplyBalance.MulDivMultiplyBalance MulDivMultiplyRun.MulDivMultiplyRun MulDivMultiplySigned.MulDivMultiplySigned MulDivMultiplySignedStep.MulDivMultiplySignedStep MulDivMultiplySignedRun.MulDivMultiplySignedRun MulDivMultiplySignedProduct.MulDivMultiplySignedProduct.
Open Scope Z_scope.
Module MulDivMulLowProduct.
Lemma scaled_normal c l : word 64 (word 66 c*2^63+l)=word 64 (c*2^63+l).
Proof.
  pose proof (Z.div_mod c (2^66) ltac:(vm_compute; discriminate)) as split.
  change (c=2^66*(c/2^66)+word 66 c) in split.
  assert (eq : word 66 c*2^63+l=(c*2^63+l)+(-(c/2^66)*2^65)*2^64).
  { change (2^66) with 73786976294838206464 in *; change (2^63) with 9223372036854775808;
      change (2^65) with 36893488147419103232; change (2^64) with 18446744073709551616; nia. }
  rewrite eq; unfold word at 1 2; apply Z.mod_add; discriminate.
Qed.
Theorem low_edge s i (state : word 3 (r0_nstate s)=2) :
  word 64 (packed (step s i))=word 64
    ((digit s*SignedWords.signed 65 (r7_ndivisor s)+SignedWords.signed 65 (accumulator s))*2^63+low s/2).
Proof.
  rewrite product_edge by exact state; rewrite shifted_low,raw_signed; fold (coefficient s).
  rewrite scaled_normal,coefficient_value.
  replace (((digit s-2*sign s)*SignedWords.signed 65 (r7_ndivisor s)+SignedWords.signed 65 (accumulator s))*2^63+low s/2) with
    (((digit s*SignedWords.signed 65 (r7_ndivisor s)+SignedWords.signed 65 (accumulator s))*2^63+low s/2)+
      (-sign s*SignedWords.signed 65 (r7_ndivisor s))*2^64)
    by (change (2^63) with 9223372036854775808; change (2^64) with 18446744073709551616; ring).
  unfold word at 1 2; apply Z.mod_add; discriminate.
Qed.
Local Opaque run step.
Theorem low_product s inputs a b (ha : 0<=a<2^64) (hb : -(2^64)<b<2^64)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=0)
  (divisor : SignedWords.signed 65 (r7_ndivisor s)=b)
  (sg : sign s=0) (initial : packed s=a) (live : active inputs 64) :
  word 64 (packed (run s inputs 64))=word 64 (a*b).
Proof.
  destruct (initial_values s a ha initial) as [value acc].
  destruct (signed_prefix 63 s inputs a b ltac:(lia) state count divisor hb sg value
    ltac:(rewrite acc; change (2^64) with 18446744073709551616; lia)
    ltac:(intros t ht; apply live; lia)) as [_ [dv [bound [consumed [sz balance]]]]].
  change (Z.of_nat 63) with 63 in sz,balance.
  destruct (prefix_decode (run s inputs 63) a b consumed ha sz balance) as [decoded bit].
  destruct (compute_prefix 63 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  change (run s inputs 64) with (step (run s inputs 63) (inputs 63%nat)).
  rewrite low_edge by exact st; rewrite dv; f_equal.
  rewrite packed_int in balance.
  pose proof (Z.div_mod (low (run s inputs 63)) 2 ltac:(lia)) as parity.
  change (low (run s inputs 63)=2*(low (run s inputs 63)/2)+digit (run s inputs 63)) in parity.
  change (2^63) with 9223372036854775808 in decoded,balance |- *;
    change (2^64) with 18446744073709551616 in balance.
  nia.
Qed.
End MulDivMulLowProduct.
Print Assumptions MulDivMulLowProduct.low_edge.
Print Assumptions MulDivMulLowProduct.low_product.

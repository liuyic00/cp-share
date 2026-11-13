From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords MulDivControl MulDivTiming MulDivMultiply MulDivMultiplyBalance MulDivMultiplyRun MulDivMultiplySigned MulDivMultiplySignedStep MulDivMultiplySignedRun.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivMultiply.MulDivMultiply MulDivMultiplyBalance.MulDivMultiplyBalance MulDivMultiplyRun.MulDivMultiplyRun MulDivMultiplySigned.MulDivMultiplySigned MulDivMultiplySignedStep.MulDivMultiplySignedStep MulDivMultiplySignedRun.MulDivMultiplySignedRun.
Open Scope Z_scope.
Module MulDivMultiplySignedProduct.
Lemma coefficient_value s : coefficient s=digit s-2*sign s.
Proof.
  unfold coefficient,digit,low; rewrite Z.shiftr_0_r.
  rewrite MulDivRefinement.MulDivRefinement.narrow by lia.
  assert (bit : word 64 (r8_nremainder s) mod 2=word 1 (r8_nremainder s)).
  { change (word 1 (word 64 (r8_nremainder s))=word 1 (r8_nremainder s)).
    apply MulDivRefinement.MulDivRefinement.narrow; lia. }
  rewrite bit; reflexivity.
Qed.
Local Opaque run step.
Lemma negative_run n s inputs (state : word 3 (r0_nstate s)=2)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<=64) (live : active inputs n) :
  word 1 (r4_nneg_5Fout (run s inputs n))=word 1 (r4_nneg_5Fout s).
Proof.
  induction n as [|n IH]; [reflexivity|].
  assert (prior : word 1 (r4_nneg_5Fout (run s inputs n))=word 1 (r4_nneg_5Fout s))
    by (apply IH; [rewrite Nat2Z.inj_succ in remaining; lia|intros t ht; apply live; lia]).
  destruct (compute_prefix n s inputs state ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  destruct (preserve_operands (run s inputs n) (inputs n) st) as [_ [neg _]].
  change (run s inputs (S n)) with (step (run s inputs n) (inputs n)).
  rewrite neg,normalize by lia; exact prior.
Qed.
Lemma final_sign s inputs (state : word 3 (r0_nstate s)=2)
  (count : word 7 (r3_ncount s)=0) (live : active inputs 63) :
  sign (run s inputs 63)=word 1 (r4_nneg_5Fout s).
Proof.
  destruct (compute_prefix 62 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  change (sign (step (run s inputs 62) (inputs 62%nat))=word 1 (r4_nneg_5Fout s)).
  rewrite inject_sign by exact st; unfold injected; rewrite ct,count; cbn [Z.of_nat Z.add Z.eqb Pos.eqb].
  apply negative_run; [exact state|rewrite count; vm_compute; discriminate|intros t ht; apply live; lia].
Qed.
Theorem signed_product s inputs a b gamma
  (ha : 0<=a<2^64) (hb : -(2^64)<b<2^64)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=0)
  (divisor : SignedWords.signed 65 (r7_ndivisor s)=b)
  (sg : sign s=0) (initial : SignedWords.signed 129 (packed s)=a)
  (acc : -(2^64)<SignedWords.signed 65 (accumulator s)<2^64)
  (negative : word 1 (r4_nneg_5Fout s)=gamma)
  (weight : gamma=0 \/ gamma=a/2^63) (live : active inputs 64) :
  SignedWords.signed 129 (packed (run s inputs 64))=(a-2^64*gamma)*b.
Proof.
  destruct (signed_prefix 63 s inputs a b ltac:(lia) state count divisor hb sg initial acc
    ltac:(intros t ht; apply live; lia)) as [_ [dv [bound [consumed [sz balance]]]]].
  change (Z.of_nat 63) with 63 in sz,balance.
  destruct (prefix_decode (run s inputs 63) a b consumed ha sz balance) as [decoded bit].
  assert (finalSign : sign (run s inputs 63)=gamma).
  { rewrite final_sign by (try assumption; intros t ht; apply live; lia); exact negative. }
  assert (coef : coefficient (run s inputs 63)=digit (run s inputs 63)-2*gamma)
    by (rewrite coefficient_value,finalSign; reflexivity).
  assert (db : 0<=digit (run s inputs 63)<2) by (unfold digit; apply Z.mod_pos_bound; lia).
  assert (digits : coefficient (run s inputs 63)= -1 \/ coefficient (run s inputs 63)=0 \/ coefficient (run s inputs 63)=1).
  { destruct weight as [zero|signed]; rewrite coef; [rewrite zero|rewrite signed,<-bit]; lia. }
  destruct (compute_prefix 63 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  pose proof (signed_step_balance (run s inputs 63) (inputs 63%nat) st digits
    ltac:(rewrite dv; exact hb) bound) as edge.
  rewrite coef,dv in edge.
  change (run s inputs 64) with (step (run s inputs 63) (inputs 63%nat)).
  change (2^63) with 9223372036854775808 in decoded,balance;
    change (2^64) with 18446744073709551616 in balance,edge |- *.
  nia.
Qed.
Lemma initial_values s a (ha : 0<=a<2^64) (initial : packed s=a) :
  SignedWords.signed 129 (packed s)=a /\ SignedWords.signed 65 (accumulator s)=0.
Proof.
  split.
  - rewrite initial; apply SignedWords.signed_small; [lia|].
    change (2^(129-1)) with 340282366920938463463374607431768211456;
      change (2^64) with 18446744073709551616 in ha; lia.
  - pose proof (packed_exact s) as layout; rewrite initial in layout.
    pose proof (bounds 65 (Z.shiftr (word 130 (r8_nremainder s)) 65) ltac:(lia)) as hi; fold (accumulator s) in hi.
    pose proof (bounds 64 (r8_nremainder s) ltac:(lia)) as lo; fold (low s) in lo.
    assert (zero : accumulator s=0).
    { change (2^64) with 18446744073709551616 in ha,layout,lo; nia. }
    rewrite zero; reflexivity.
Qed.
Theorem product_from_packed s inputs a b gamma
  (ha : 0<=a<2^64) (hb : -(2^64)<b<2^64)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=0)
  (divisor : SignedWords.signed 65 (r7_ndivisor s)=b)
  (sg : sign s=0) (initial : packed s=a)
  (negative : word 1 (r4_nneg_5Fout s)=gamma)
  (weight : gamma=0 \/ gamma=a/2^63) (live : active inputs 64) :
  SignedWords.signed 129 (packed (run s inputs 64))=(a-2^64*gamma)*b.
Proof.
  destruct (initial_values s a ha initial) as [value acc].
  apply signed_product; try assumption.
  rewrite acc; change (2^64) with 18446744073709551616; lia.
Qed.
End MulDivMultiplySignedProduct.
Print Assumptions MulDivMultiplySignedProduct.final_sign.
Print Assumptions MulDivMultiplySignedProduct.signed_product.
Print Assumptions MulDivMultiplySignedProduct.product_from_packed.

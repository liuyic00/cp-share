From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords MulDivControl MulDivTiming MulDivMultiply MulDivMultiplyBalance MulDivMultiplyRun MulDivMultiplySigned MulDivMultiplySignedStep MulDivMultiplySignedRun MulDivMulLowProduct MulDivMultiplySignedProduct.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivMultiply.MulDivMultiply MulDivMultiplyBalance.MulDivMultiplyBalance MulDivMultiplyRun.MulDivMultiplyRun MulDivMultiplySigned.MulDivMultiplySigned MulDivMultiplySignedStep.MulDivMultiplySignedStep MulDivMultiplySignedRun.MulDivMultiplySignedRun MulDivMulLowProduct.MulDivMulLowProduct.
Open Scope Z_scope.
Module MulDivMulWordBalance.
Local Opaque run step.
Theorem signed_prefix_from_count n s inputs a b (remaining : word 7 (r3_ncount s)+Z.of_nat n<=63)
  (state : word 3 (r0_nstate s)=2)
  (divisor : SignedWords.signed 65 (r7_ndivisor s)=b)
  (hb : -(2^64)<b<2^64) (sg : sign s=0)
  (initial : SignedWords.signed 129 (packed s)=a)
  (ha : -(2^64)<SignedWords.signed 65 (accumulator s)<2^64)
  (live : active inputs n) :
  (word 7 (r3_ncount s)+Z.of_nat n<63 -> sign (run s inputs n)=0) /\
  SignedWords.signed 65 (r7_ndivisor (run s inputs n))=b /\
  -(2^64)<SignedWords.signed 65 (accumulator (run s inputs n))<2^64 /\
  exists consumed, 0<=consumed<2^(Z.of_nat n) /\
    2^(Z.of_nat n)*SignedWords.signed 129 (packed (run s inputs n))+consumed=
      a+2^64*b*consumed.
Proof.
  induction n as [|n IH].
  - change ((word 7 (r3_ncount s)+0<63 -> sign s=0) /\ SignedWords.signed 65 (r7_ndivisor s)=b /\
      -(2^64)<SignedWords.signed 65 (accumulator s)<2^64 /\
      exists consumed, 0<=consumed<1 /\ 1*SignedWords.signed 129 (packed s)+consumed=a+2^64*b*consumed).
    split; [intro; exact sg|]; split; [exact divisor|]; split; [exact ha|].
    exists 0; split; [lia|rewrite initial; ring].
  - destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia) ltac:(intros t ht; apply live; lia)) as [signs [dv [acc [consumed [sz bal]]]]].
    assert (sgn : sign (run s inputs n)=0) by (apply signs; rewrite Nat2Z.inj_succ in remaining; lia).
    destruct (compute_prefix n s inputs state ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros t ht; apply live; lia)) as [st cnt].
    assert (dc : coefficient (run s inputs n)=digit (run s inputs n)) by (apply unsigned_coefficient; exact sgn).
    assert (db : 0<=digit (run s inputs n)<2) by (unfold digit; apply Z.mod_pos_bound; lia).
    assert (digits : coefficient (run s inputs n)= -1 \/ coefficient (run s inputs n)=0 \/ coefficient (run s inputs n)=1) by lia.
    assert (bv : -(2^64)<SignedWords.signed 65 (r7_ndivisor (run s inputs n))<2^64) by (rewrite dv; exact hb).
    pose proof (signed_step_balance (run s inputs n) (inputs n) st digits bv acc) as edge.
    pose proof (accumulator_range (run s inputs n) (inputs n) st digits bv acc) as nextAcc.
    destruct (preserve_operands (run s inputs n) (inputs n) st) as [nextDiv rest].
    change (run s inputs (S n)) with (step (run s inputs n) (inputs n)).
    split.
    + intro earlier; rewrite inject_sign by exact st; unfold injected; rewrite cnt.
      assert (last : (word 7 (r3_ncount s)+Z.of_nat n=?62)=false) by (apply Z.eqb_neq; rewrite Nat2Z.inj_succ in earlier; lia).
      rewrite last; reflexivity.
    + split.
      * rewrite nextDiv,SignedWords.signed_normal by lia; exact dv.
      * split; [exact nextAcc|].
        exists (consumed+digit (run s inputs n)*2^(Z.of_nat n)).
        rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia; split.
        -- assert (positive : 0<2^(Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
           assert (cases : digit (run s inputs n)=0 \/ digit (run s inputs n)=1) by lia.
           destruct cases as [h|h]; rewrite h; lia.
        -- rewrite dc,dv in edge.
           replace (2^64*digit (run s inputs n)*b) with (2^64*b*digit (run s inputs n)) in edge by ring.
           exact (advance_balance (2^(Z.of_nat n)) _ _ _ b consumed a edge bal).
Qed.
Definition virtualNext s b := (digit s*b+SignedWords.signed 65 (accumulator s))*2^63+low s/2.
Lemma virtual_balance s b : 2*virtualNext s b+digit s=
  SignedWords.signed 129 (packed s)+2^64*b*digit s.
Proof.
  unfold virtualNext; rewrite packed_int; unfold digit.
  pose proof (Z.div_mod (low s) 2 ltac:(lia)).
  change (2^63) with 9223372036854775808; change (2^64) with 18446744073709551616; nia.
Qed.
Theorem word_balance s inputs a b (ha : 0<=a<2^64) (hb : -(2^64)<b<2^64)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=32)
  (divisor : SignedWords.signed 65 (r7_ndivisor s)=b)
  (sg : sign s=0) (initial : packed s=a) (live : active inputs 32) :
  exists value consumed, 0<=consumed<2^32 /\ word 64 (packed (run s inputs 32))=word 64 value /\
    2^32*value+consumed=a+2^64*b*consumed.
Proof.
  destruct (MulDivMultiplySignedProduct.MulDivMultiplySignedProduct.initial_values s a ha initial) as [init acc].
  destruct (signed_prefix_from_count 31 s inputs a b ltac:(rewrite count; vm_compute; discriminate) state divisor hb sg init
    ltac:(rewrite acc; change (2^64) with 18446744073709551616; lia)
    ltac:(intros t ht; apply live; lia)) as [_ [dv [bound [consumed [sz balance]]]]].
  destruct (compute_prefix 31 s inputs state ltac:(rewrite count; vm_compute; reflexivity)
    ltac:(intros t ht; apply live; lia)) as [st ct].
  exists (virtualNext (run s inputs 31) b), (consumed+digit (run s inputs 31)*2^31).
  assert (db : 0<=digit (run s inputs 31)<2) by (unfold digit; apply Z.mod_pos_bound; lia).
  change (Z.of_nat 31) with 31 in sz,balance.
  split.
  - change (2^31) with 2147483648 in *; change (2^32) with 4294967296; nia.
  - split.
    + change (run s inputs 32) with (step (run s inputs 31) (inputs 31%nat)).
      rewrite low_edge by exact st; rewrite dv; reflexivity.
    + pose proof (advance_balance (2^31) _ _ _ b consumed a (virtual_balance (run s inputs 31) b) balance) as result.
      change (2^31) with 2147483648 in *; change (2^32) with 4294967296; exact result.
Qed.
Theorem word_balance_decode a b value consumed (hc : 0<=consumed<2^32)
  (balance : 2^32*value+consumed=a+2^64*b*consumed) :
  consumed=a mod 2^32 /\ value=2^32*(b*consumed)+a/2^32.
Proof.
  assert (modulo : consumed mod 2^32=a mod 2^32).
  { apply (f_equal (fun x => x mod 2^32)) in balance.
    replace (2^32*value+consumed) with (consumed+value*2^32) in balance by ring.
    replace (a+2^64*b*consumed) with (a+(2^32*b*consumed)*2^32) in balance
      by (change (2^32) with 4294967296; change (2^64) with 18446744073709551616; ring).
    rewrite !Z.mod_add in balance by (vm_compute; discriminate); exact balance. }
  rewrite Z.mod_small in modulo by exact hc; split; [exact modulo|].
  pose proof (Z.div_mod a (2^32) ltac:(vm_compute; discriminate)) as split.
  rewrite <- modulo in split.
  change (2^32) with 4294967296 in *; change (2^64) with 18446744073709551616 in *; nia.
Qed.
Theorem word_slice_decode a b value consumed (ha : 0<=a<2^64)
  (hc : 0<=consumed<2^32) (balance : 2^32*value+consumed=a+2^64*b*consumed) :
  word 32 (Z.shiftr value 32)=word 32 (b*word 32 a).
Proof.
  destruct (word_balance_decode a b value consumed hc balance) as [consumedValue valueEq].
  assert (quotient : value/2^32=b*consumed).
  { symmetry; apply Z.div_unique with (r:=a/2^32).
    - left; split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      change (2^64) with 18446744073709551616 in ha; change (2^32) with 4294967296; lia.
    - rewrite valueEq; ring. }
  rewrite Z.shiftr_div_pow2 by lia; rewrite quotient,consumedValue; reflexivity.
Qed.
Theorem word_slice s inputs a b (ha : 0<=a<2^64) (hb : -(2^64)<b<2^64)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=32)
  (divisor : SignedWords.signed 65 (r7_ndivisor s)=b)
  (sg : sign s=0) (initial : packed s=a) (live : active inputs 32) :
  word 32 (Z.shiftr (packed (run s inputs 32)) 32)=word 32 (b*word 32 a).
Proof.
  destruct (word_balance s inputs a b ha hb state count divisor sg initial live) as [value [consumed [hc [same balance]]]].
  apply (f_equal (fun x => word 32 (Z.shiftr x 32))) in same.
  rewrite !MulDivRefinement.MulDivRefinement.extract_normal in same by lia.
  rewrite same; apply word_slice_decode with (consumed:=consumed); assumption.
Qed.
End MulDivMulWordBalance.
Print Assumptions MulDivMulWordBalance.signed_prefix_from_count.
Print Assumptions MulDivMulWordBalance.word_balance.
Print Assumptions MulDivMulWordBalance.word_balance_decode.
Print Assumptions MulDivMulWordBalance.word_slice.

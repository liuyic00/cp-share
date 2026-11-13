From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words SignedWords MulDivControl MulDivTiming MulDivMultiply MulDivMultiplyBalance MulDivMultiplyRun MulDivMultiplySigned MulDivMultiplySignedStep.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivMultiply.MulDivMultiply MulDivMultiplyBalance.MulDivMultiplyBalance MulDivMultiplyRun.MulDivMultiplyRun MulDivMultiplySigned.MulDivMultiplySigned MulDivMultiplySignedStep.MulDivMultiplySignedStep.
Open Scope Z_scope.
Module MulDivMultiplySignedRun.
Lemma unsigned_coefficient s (sg : sign s=0) : coefficient s=digit s.
Proof.
  unfold coefficient,digit,low; rewrite sg,Z.mul_0_r,Z.sub_0_r,Z.shiftr_0_r.
  rewrite MulDivRefinement.MulDivRefinement.narrow by lia.
  change (word 1 (r8_nremainder s)=word 1 (word 64 (r8_nremainder s))).
  rewrite MulDivRefinement.MulDivRefinement.narrow by lia; reflexivity.
Qed.
Local Opaque run step.
Theorem signed_prefix n s inputs a b (limit : (n<=63)%nat)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=0)
  (divisor : SignedWords.signed 65 (r7_ndivisor s)=b)
  (hb : -(2^64)<b<2^64) (sg : sign s=0)
  (initial : SignedWords.signed 129 (packed s)=a)
  (ha : -(2^64)<SignedWords.signed 65 (accumulator s)<2^64)
  (live : active inputs n) :
  ((n<63)%nat -> sign (run s inputs n)=0) /\
  SignedWords.signed 65 (r7_ndivisor (run s inputs n))=b /\
  -(2^64)<SignedWords.signed 65 (accumulator (run s inputs n))<2^64 /\
  exists consumed, 0<=consumed<2^(Z.of_nat n) /\
    2^(Z.of_nat n)*SignedWords.signed 129 (packed (run s inputs n))+consumed=
      a+2^64*b*consumed.
Proof.
  induction n as [|n IH].
  - change (((0<63)%nat -> sign s=0) /\ SignedWords.signed 65 (r7_ndivisor s)=b /\
      -(2^64)<SignedWords.signed 65 (accumulator s)<2^64 /\
      exists consumed, 0<=consumed<1 /\ 1*SignedWords.signed 129 (packed s)+consumed=a+2^64*b*consumed).
    split; [intro; exact sg|]; split; [exact divisor|]; split; [exact ha|].
    exists 0; split; [lia|rewrite initial; ring].
  - destruct (IH ltac:(lia) ltac:(intros t ht; apply live; lia)) as [signs [dv [acc [consumed [sz bal]]]]].
    assert (sgn : sign (run s inputs n)=0) by (apply signs; lia).
    destruct (compute_prefix n s inputs state ltac:(rewrite count; lia)
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
    + intro earlier; rewrite inject_sign by exact st; unfold injected; rewrite cnt,count.
      assert (last : (0+Z.of_nat n=?62)=false) by (apply Z.eqb_neq; lia).
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
Lemma packed_parity s : SignedWords.signed 129 (packed s) mod 2=digit s.
Proof.
  rewrite packed_int; unfold digit.
  replace (SignedWords.signed 65 (accumulator s)*2^64+low s) with
    (low s+(SignedWords.signed 65 (accumulator s)*9223372036854775808)*2)
    by (change (2^64) with 18446744073709551616; ring).
  apply Z.mod_add; lia.
Qed.
Theorem prefix_decode s a b consumed (ha : 0<=a<2^64)
  (hc : 0<=consumed<2^63)
  (balance : 2^63*SignedWords.signed 129 (packed s)+consumed=a+2^64*b*consumed) :
  consumed+digit s*2^63=a /\ digit s=a/2^63.
Proof.
  pose proof (Z.div_mod (SignedWords.signed 129 (packed s)) 2 ltac:(lia)) as parity.
  rewrite packed_parity in parity.
  pose proof (Z.mod_pos_bound (low s) 2 ltac:(lia)) as db; fold (digit s) in db.
  assert (decode : consumed+digit s*2^63=a).
  { change (2^64) with 18446744073709551616 in ha,balance;
      change (2^63) with 9223372036854775808 in hc,balance |- *.
    nia. }
  split; [exact decode|].
  apply Z.div_unique with (r:=consumed); [left; exact hc|lia].
Qed.
End MulDivMultiplySignedRun.
Print Assumptions MulDivMultiplySignedRun.signed_prefix.
Print Assumptions MulDivMultiplySignedRun.prefix_decode.

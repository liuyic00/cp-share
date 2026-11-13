From Coq Require Import ZArith Lia Bool.
From Generated Require Import ArrayMulDataModule.
From Proofs Require Import Words SignedWords.
Import ArrayMulDataModule.CIRCTBits ArrayMulDataModule.nArrayMulDataModule.
Open Scope Z_scope.
Module ArrayContract.
Definition specification (i : Inputs) : Z :=
  word 130 (SignedWords.signed 65 (nio_5Fa i) * SignedWords.signed 65 (nio_5Fb i)).

Lemma repeat_bit n b : repeatWord n 1 b = (2^(Z.of_nat n)-1)*b.
Proof.
  induction n as [|n IH].
  - change (0 = (1-1)*b); ring.
  - cbn [repeatWord]; rewrite IH, Z.shiftl_mul_pow2 by lia.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    change (2^1) with 2; ring.
Qed.
Lemma sign_bit x :
  word 1 (Z.shiftr (word 65 x) 64) =
    if Z.ltb (word 65 x) (2^64) then 0 else 1.
Proof.
  pose proof (Words.word_bound 65 x ltac:(lia)) as bound.
  change (0 <= word 65 x < 36893488147419103232) in bound.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616.
  unfold word at 1; change (2^1) with 2.
  pose proof (Z.div_mod (word 65 x) 18446744073709551616 ltac:(lia)) as split.
  pose proof (Z.mod_pos_bound (word 65 x) 18446744073709551616 ltac:(lia)) as remainder.
  destruct (Z.ltb_spec (word 65 x) 18446744073709551616).
  - assert (q : word 65 x / 18446744073709551616 = 0) by lia.
    rewrite q; reflexivity.
  - assert (q : word 65 x / 18446744073709551616 = 1) by lia.
    rewrite q; reflexivity.
Qed.
Lemma sign_extension x :
  word 130 (Z.shiftl (word 65 (repeatWord 65 1 (word 1 (Z.shiftr (word 65 x) 64)))) 65 + word 65 x) =
  word 130 (SignedWords.signed 65 x).
Proof.
  rewrite repeat_bit, sign_bit.
  unfold SignedWords.signed.
  change (2^(65-1)) with (2^64).
  change (Words.word 65 x) with (word 65 x).
  destruct (Z.ltb (word 65 x) (2^64)).
  - change (word 130 (0 + word 65 x) = word 130 (word 65 x)).
    rewrite Z.add_0_l; reflexivity.
  - change (word 130 (Z.shiftl (word 65 (2^65-1)) 65 + word 65 x) =
      word 130 (word 65 x - 2^65)).
    replace (word 65 (2^65-1)) with (2^65-1) by reflexivity.
    rewrite Z.shiftl_mul_pow2 by lia.
    replace ((2^65-1)*2^65 + word 65 x) with ((word 65 x - 2^65) + 1 * 2^130)
      by (replace (2^130) with (2^65 * 2^65) by reflexivity; ring).
    unfold word at 1 3; rewrite Z.mod_add by (apply Z.pow_nonzero; lia); reflexivity.
Qed.
Lemma captured_product (s : State) (i : Inputs) : v16200 s i = specification i.
Proof.
  unfold v16200, v16199, v16198, v16197, v16196, v16195, v16194.
  rewrite !sign_extension.
  unfold specification, word.
  rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.
Theorem first_capture (s : State) (i : Inputs)
  (enabled : word 1 (nio_5FregEnables_5F0 i) = 1) :
  r2534_nexpectedFirst (step s i) = specification i.
Proof.
  change (v16201 s i = specification i).
  unfold v16201; rewrite enabled; cbn [Z.eqb Pos.eqb].
  rewrite captured_product. unfold specification; apply Words.word_idem; lia.
Qed.
Theorem transfer (s : State) (i : Inputs)
  (enabled : word 1 (nio_5FregEnables_5F1 i) = 1) :
  r2536_nexpectedResult (step s i) = word 130 (r2534_nexpectedFirst s).
Proof.
  change (v16203 s i = word 130 (r2534_nexpectedFirst s)).
  unfold v16203; rewrite enabled; cbn [Z.eqb Pos.eqb].
  apply Words.word_idem; lia.
Qed.
Theorem first_hold (s : State) (i : Inputs)
  (disabled : word 1 (nio_5FregEnables_5F0 i) = 0) :
  r2534_nexpectedFirst (step s i) = word 130 (r2534_nexpectedFirst s).
Proof.
  change (v16201 s i = word 130 (r2534_nexpectedFirst s)).
  unfold v16201; rewrite disabled; cbn [Z.eqb].
  apply Words.word_idem; lia.
Qed.
Theorem second_hold (s : State) (i : Inputs)
  (disabled : word 1 (nio_5FregEnables_5F1 i) = 0) :
  r2536_nexpectedResult (step s i) = word 130 (r2536_nexpectedResult s).
Proof.
  change (v16203 s i = word 130 (r2536_nexpectedResult s)).
  unfold v16203; rewrite disabled; cbn [Z.eqb].
  apply Words.word_idem; lia.
Qed.
Theorem reset_unknown (s : State) (i : Inputs) (reset : word 1 (nreset i) = 1) :
  r2535_nvalidFirst (step s i) = 0 /\ r2537_nresultKnown (step s i) = 0.
Proof.
  change ((if Z.eqb (word 1 (nreset i)) 1 then v6 s i else v16202 s i) = 0 /\
          (if Z.eqb (word 1 (nreset i)) 1 then v6 s i else v16204 s i) = 0).
  rewrite reset; split; reflexivity.
Qed.
Theorem two_edges (s : State) (first second : Inputs)
  (capture : word 1 (nio_5FregEnables_5F0 first) = 1)
  (move : word 1 (nio_5FregEnables_5F1 second) = 1) :
  r2536_nexpectedResult (step (step s first) second) = specification first.
Proof.
  rewrite transfer by assumption; rewrite first_capture by assumption.
  unfold specification; apply Words.word_idem; lia.
Qed.
Theorem known_after_two_edges (s : State) (first second : Inputs)
  (capture : word 1 (nio_5FregEnables_5F0 first) = 1)
  (move : word 1 (nio_5FregEnables_5F1 second) = 1)
  (r0 : word 1 (nreset first) = 0) (r1 : word 1 (nreset second) = 0) :
  r2537_nresultKnown (step (step s first) second) = 1.
Proof.
  change ((if Z.eqb (word 1 (nreset second)) 1 then v6 (step s first) second else v16204 (step s first) second) = 1).
  rewrite r1; cbn [Z.eqb].
  unfold v16204; rewrite move; cbn [Z.eqb Pos.eqb].
  change (word 1 (word 1 (if Z.eqb (word 1 (nreset first)) 1 then v6 s first else v16202 s first)) = 1).
  rewrite r0; cbn [Z.eqb]; unfold v16202; rewrite capture.
  assert (cases : word 1 (r2535_nvalidFirst s) = 0 \/ word 1 (r2535_nvalidFirst s) = 1) by (apply Words.bit_cases).
  destruct cases as [h|h]; rewrite h; reflexivity.
Qed.
Print Assumptions known_after_two_edges.
Print Assumptions captured_product.
Print Assumptions two_edges.
End ArrayContract.

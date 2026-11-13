From Coq Require Import ZArith Lia.
From Proofs Require Import Words WordBits MulDivControl MulDivTiming MulDivRefinement MulDivMultiply MulDivMultiplyBalance.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement MulDivMultiply.MulDivMultiply MulDivMultiplyBalance.MulDivMultiplyBalance.
Open Scope Z_scope.
Module MulDivMultiplyRun.
Definition accumulator s := word 65 (Z.shiftr (word 130 (r8_nremainder s)) 65).
Definition low s := word 64 (r8_nremainder s).
Definition digit s := low s mod 2.
Lemma packed_exact s : packed s=accumulator s*2^64+low s.
Proof.
  unfold packed,accumulator,low; rewrite Z.shiftl_mul_pow2 by lia.
  apply Words.word_small.
  pose proof (bounds 65 (Z.shiftr (word 130 (r8_nremainder s)) 65) ltac:(lia)) as a.
  pose proof (bounds 64 (r8_nremainder s) ltac:(lia)) as l.
  change (2^65) with 36893488147419103232 in a; change (2^64) with 18446744073709551616 in *;
    change (2^129) with 680564733841876926926749214863536422912; lia.
Qed.
Lemma accumulator_fit s (fit : packed s<2^128) : 0<=accumulator s<2^64.
Proof.
  rewrite packed_exact in fit.
  pose proof (bounds 65 (Z.shiftr (word 130 (r8_nremainder s)) 65) ltac:(lia)) as a.
  pose proof (bounds 64 (r8_nremainder s) ltac:(lia)) as l.
  fold (accumulator s) in a; fold (low s) in l.
  change (2^128) with 340282366920938463463374607431768211456 in fit;
    change (2^64) with 18446744073709551616 in *; lia.
Qed.
Lemma top_zero s (fit : packed s<2^128) :
  word 1 (Z.shiftr (word 130 (r8_nremainder s)) 129)=0.
Proof.
  assert (bridge : word 1 (Z.shiftr (accumulator s) 64)=word 1 (Z.shiftr (word 130 (r8_nremainder s)) 129)).
  { unfold accumulator; exact (WordBits.extract_extract 65 1 65 64 (word 130 (r8_nremainder s)) ltac:(lia) ltac:(lia) ltac:(lia)). }
  rewrite <- bridge,Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by (apply accumulator_fit; exact fit); reflexivity.
Qed.
Theorem unsigned_edge s i b (state : word 3 (r0_nstate s)=2)
  (hb : 0<=b<2^64) (divisor : word 65 (r7_ndivisor s)=b)
  (sg : sign s=0) (fit : packed s<2^128) :
  packed (step s i)<2^128 /\
  2*packed (step s i)+digit s=packed s+2^64*b*digit s.
Proof.
  pose proof (accumulator_fit s fit) as ha.
  pose proof (bounds 64 (r8_nremainder s) ltac:(lia)) as hl; fold (low s) in hl.
  rewrite (MulDivMultiplyBalance.unsigned_edge s i (accumulator s) b state ha hb sg eq_refl (top_zero s fit) divisor).
  fold (low s); split; [apply unsigned_step_fits; assumption|].
  unfold digit; rewrite unsigned_step_balance,packed_exact; ring.
Qed.
Local Opaque step run.
Theorem unsigned_execution n s inputs a b (limit : (n<=64)%nat)
  (ha : 0<=a<2^64) (hb : 0<=b<2^64)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=0)
  (divisor : word 65 (r7_ndivisor s)=b) (sg : sign s=0)
  (negative : word 1 (r4_nneg_5Fout s)=0) (initial : packed s=a)
  (live : active inputs n) :
  sign (run s inputs n)=0 /\ word 65 (r7_ndivisor (run s inputs n))=b /\
  word 1 (r4_nneg_5Fout (run s inputs n))=0 /\ packed (run s inputs n)<2^128 /\
  exists consumed, 0<=consumed<2^(Z.of_nat n) /\
    2^(Z.of_nat n)*packed (run s inputs n)+consumed=a+2^64*b*consumed.
Proof.
  induction n as [|n IH].
  - change (sign s=0 /\ word 65 (r7_ndivisor s)=b /\ word 1 (r4_nneg_5Fout s)=0 /\ packed s<2^128 /\
      exists consumed, 0<=consumed<1 /\ 1*packed s+consumed=a+2^64*b*consumed).
    split; [exact sg|]; split; [exact divisor|]; split; [exact negative|]; split.
    + rewrite initial; change (2^128) with 340282366920938463463374607431768211456; change (2^64) with 18446744073709551616 in ha; lia.
    + exists 0; split; [lia|rewrite initial; ring].
  - destruct (IH ltac:(lia) ltac:(intros t ht; apply live; lia)) as [sgn [dv [neg [fit [consumed [sz bal]]]]]].
    destruct (compute_prefix n s inputs state ltac:(rewrite count; lia)
      ltac:(intros t ht; apply live; lia)) as [st cnt].
    destruct (preserve_operands (run s inputs n) (inputs n) st) as [dvnext [negnext meta]].
    destruct (unsigned_edge (run s inputs n) (inputs n) b st hb dv sgn fit) as [fits edge].
    assert (sgnext : sign (step (run s inputs n) (inputs n))=0).
    { rewrite inject_sign by exact st; unfold injected; rewrite neg; destruct (word 7 (r3_ncount (run s inputs n))=?62); reflexivity. }
    change (run s inputs (S n)) with (step (run s inputs n) (inputs n)).
    split; [exact sgnext|]; split; [rewrite dvnext,normalize by lia; exact dv|].
    split; [rewrite negnext,normalize by lia; exact neg|]; split; [exact fits|].
    exists (consumed+digit (run s inputs n)*2^(Z.of_nat n)).
    assert (digits : 0<=digit (run s inputs n)<2) by (unfold digit; apply Z.mod_pos_bound; lia).
    assert (positive : 0<2^(Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia; split.
    + assert (digit (run s inputs n)=0 \/ digit (run s inputs n)=1) by lia.
      destruct H as [H|H]; rewrite H; lia.
    + exact (advance_balance (2^(Z.of_nat n)) _ _ _ b consumed a edge bal).
Qed.
Theorem unsigned_product s inputs a b
  (ha : 0<=a<2^64) (hb : 0<=b<2^64)
  (state : word 3 (r0_nstate s)=2) (count : word 7 (r3_ncount s)=0)
  (divisor : word 65 (r7_ndivisor s)=b) (sg : sign s=0)
  (negative : word 1 (r4_nneg_5Fout s)=0) (initial : packed s=a)
  (live : active inputs 64) : packed (run s inputs 64)=a*b.
Proof.
  destruct (unsigned_execution 64 s inputs a b ltac:(lia) ha hb state count divisor sg negative initial live)
    as [_ [_ [_ [_ [consumed [sz bal]]]]]].
  change (Z.of_nat 64) with 64 in sz,bal.
  change (2^64) with 18446744073709551616 in *.
  assert (modulo : consumed mod 18446744073709551616=a mod 18446744073709551616).
  { apply (f_equal (fun x => x mod 18446744073709551616)) in bal.
    replace (18446744073709551616*packed (run s inputs 64)+consumed) with
      (consumed+packed (run s inputs 64)*18446744073709551616) in bal by ring.
    rewrite Z.mod_add in bal by lia.
    replace (a+18446744073709551616*b*consumed) with (a+(b*consumed)*18446744073709551616) in bal by ring.
    rewrite Z.mod_add in bal by lia; exact bal. }
  rewrite !Z.mod_small in modulo by lia; subst consumed; nia.
Qed.
End MulDivMultiplyRun.
Print Assumptions MulDivMultiplyRun.unsigned_edge.
Print Assumptions MulDivMultiplyRun.unsigned_execution.
Print Assumptions MulDivMultiplyRun.unsigned_product.

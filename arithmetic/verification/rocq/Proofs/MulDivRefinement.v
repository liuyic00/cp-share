From Coq Require Import ZArith Lia.
From Proofs Require Import Words WordBits RadixDatapath MulDivControl MulDivDivision.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivDivision.MulDivDivision.
Open Scope Z_scope.
Module MulDivRefinement.
Lemma extract_normal w k offset x (hk : 0<=k) (ho : 0<=offset) (fits : offset+k<=w) :
  word k (Z.shiftr (word w x) offset)=word k (Z.shiftr x offset).
Proof. exact (WordBits.extract_normal w k offset x hk ho fits). Qed.
Lemma narrow w k x (hk : 0<=k) (fits : k<=w) : word k (word w x)=word k x.
Proof. pose proof (extract_normal w k 0 x hk ltac:(lia) ltac:(lia)) as h; now rewrite !Z.shiftr_0_r in h. Qed.
Lemma candidate_packed sh : candidate sh=RadixDatapath.RadixDatapath.candidate (word 129 sh).
Proof.
  unfold candidate, RadixDatapath.RadixDatapath.candidate.
  change (word 65 (Z.shiftr (word 130 sh) 64)=word 65 (Z.shiftr (word 129 (word 129 sh)) 64)).
  rewrite normalize by lia; rewrite !extract_normal by lia; reflexivity.
Qed.
Lemma sub_normal x y : word 64 (word 64 x-y)=word 64 (x-y).
Proof. unfold word; apply Zminus_mod_idemp_l. Qed.
Lemma difference_low sh d :
  word 64 (Z.shiftr (difference sh (word 64 d)) 0)=
  word 64 (word 64 (Z.shiftr (word 130 sh) 64)-word 64 d).
Proof.
  rewrite Z.shiftr_0_r; unfold difference, candidate.
  rewrite (narrow 65 64) by lia.
  assert (widen : word 65 (word 64 d)=word 64 d) by (apply Words.word_widen; lia).
  rewrite widen.
  rewrite <- (sub_normal (word 65 (Z.shiftr (word 130 sh) 64)) (word 64 d)).
  rewrite (narrow 65 64) by lia; reflexivity.
Qed.
Lemma step_refines_restoring sh d (bound : candidate sh<2*word 64 d) :
  word 129 (divisionStep sh (word 64 d))=
    RadixDatapath.RadixDatapath.restoringStep (word 129 sh) d.
Proof.
  unfold divisionStep; rewrite (narrow 130 129) by lia.
  rewrite signBit_correct by exact bound.
  rewrite difference_low.
  unfold RadixDatapath.RadixDatapath.restoringStep,
    RadixDatapath.RadixDatapath.reducedWord,
    RadixDatapath.RadixDatapath.quotientBit,
    RadixDatapath.RadixDatapath.lowCandidate.
  change (word 129
    (Z.shiftl (Z.shiftl
      (word 64 (if (if word 64 d<=?candidate sh then 0 else 1)=?1
         then word 64 (Z.shiftr (word 130 sh) 64)
         else word 64 (word 64 (Z.shiftr (word 130 sh) 64)-word 64 d))) 64 +
      word 64 (Z.shiftr (word 130 sh) 0)) 1 +
      word 1 (Z.lxor (if word 64 d<=?candidate sh then 0 else 1) 1)) =
    word 129 (Z.shiftl (Z.shiftl
      (word 64 (if word 64 d<=?RadixDatapath.RadixDatapath.candidate (word 129 sh)
        then word 64 (Z.shiftr (word 129 (word 129 sh)) 64)-word 64 d
        else word 64 (Z.shiftr (word 129 (word 129 sh)) 64))) 64 +
      word 64 (Z.shiftr (word 129 (word 129 sh)) 0)) 1 +
      (if word 64 d<=?RadixDatapath.RadixDatapath.candidate (word 129 sh) then 1 else 0))).
  rewrite <- candidate_packed.
  rewrite (normalize 129) by lia.
  rewrite !extract_normal by lia.
  destruct (word 64 d<=?candidate sh); cbn [Z.eqb Pos.eqb];
    change (word 1 (Z.lxor 0 1)) with 1 || change (word 1 (Z.lxor 1 1)) with 0;
    repeat rewrite normalize by lia; reflexivity.
Qed.
Definition packed s := word 129 (r8_nremainder s).
Theorem packed_step s i d (state : word 3 (r0_nstate s)=3)
  (divisor : word 65 (r7_ndivisor s)=word 64 d)
  (bound : candidate (r8_nremainder s)<2*word 64 d) :
  packed (step s i)=RadixDatapath.RadixDatapath.restoringStep (packed s) d.
Proof.
  unfold packed; rewrite compute_datapath by exact state.
  assert (normal : divisionStep (r8_nremainder s) (r7_ndivisor s)=
    divisionStep (r8_nremainder s) (word 64 d)).
  { unfold divisionStep, signBit, difference.
    rewrite divisor.
    assert (widen : word 65 (word 64 d)=word 64 d) by (apply Words.word_widen; lia).
    rewrite widen; reflexivity. }
  rewrite normal; apply step_refines_restoring; exact bound.
Qed.
End MulDivRefinement.
Print Assumptions MulDivRefinement.step_refines_restoring.
Print Assumptions MulDivRefinement.packed_step.

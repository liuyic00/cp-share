From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords MulDivControl MulDivRefinement MulDivSignedInputEdge.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement MulDivSignedInputEdge.MulDivSignedInputEdge.
Open Scope Z_scope.
Module MulDivSignedBits.
Definition extended65 x := word 65 (Z.shiftl (sign64 x) 64+word 64 x).
Lemma extended_low x : word 64 (extended65 x)=word 64 x.
Proof.
  unfold extended65; rewrite narrow by lia; rewrite Z.shiftl_mul_pow2 by lia.
  unfold word at 1; rewrite Z.add_comm,Z.mod_add by (vm_compute; discriminate).
  apply normalize; lia.
Qed.
Lemma extended_sign x : sign64 (extended65 x)=sign64 x.
Proof. unfold sign64 at 1; rewrite extended_low; reflexivity. Qed.
Lemma extended_signed x : extended65 x=word 65 (SignedWords.signed 64 x).
Proof.
  rewrite SignedWords.signed_from_bits by lia.
  change (extended65 x=word 65 (word 64 x-2^64*sign64 x)).
  unfold extended65; rewrite Z.shiftl_mul_pow2 by lia.
  replace (sign64 x*2^64+word 64 x) with ((word 64 x-2^64*sign64 x)+sign64 x*2^65) by (change (2^64) with 18446744073709551616; change (2^65) with 36893488147419103232; ring).
  unfold word at 1; rewrite Z.mod_add by (vm_compute; discriminate); reflexivity.
Qed.
Theorem divisor_magnitude x :
  (if sign64 (extended65 x)=?1 then word 65 (-word 65 (extended65 x)) else word 65 (extended65 x))=magnitude x.
Proof.
  rewrite extended_sign; unfold magnitude.
  destruct (bit_cases (Z.shiftr (word 64 x) 63)) as [sign|sign]; change (sign64 x=0) in sign || change (sign64 x=1) in sign;
    rewrite sign; cbn [Z.eqb Pos.eqb].
  - unfold extended65; rewrite sign; change (Z.shiftl 0 64) with 0; rewrite Z.add_0_l,normalize by lia.
    apply Words.word_widen; lia.
  - pose proof (Words.word_bound 64 x ltac:(lia)) as hx.
    change (0<=word 64 x<18446744073709551616) in hx.
    assert (positive : 0<word 64 x).
    { assert (nonzero : word 64 x<>0) by (intro zero; unfold sign64 in sign; rewrite zero in sign; discriminate); lia. }
    assert (encoded : extended65 x=word 64 x+18446744073709551616).
    { unfold extended65; rewrite sign; change (Z.shiftl 1 64) with 18446744073709551616.
      rewrite Words.word_small by (change (0<=18446744073709551616+word 64 x<36893488147419103232); lia); ring. }
    assert (normal : word 65 (extended65 x)=extended65 x) by (unfold extended65; apply normalize; lia).
    rewrite normal,encoded.
    assert (neg65 : word 65 (-(word 64 x+18446744073709551616))=18446744073709551616-word 64 x).
    { unfold word at 1; symmetry; apply Z.mod_unique with (q:= -1); [left|]; change (2^65) with 36893488147419103232; lia. }
    rewrite neg65; unfold word at 2; apply Z.mod_unique with (q:= -1); [left|]; change (2^64) with 18446744073709551616; lia.
Qed.
Lemma magnitude_bound x : 0<=magnitude x<2^64.
Proof. unfold magnitude; destruct (sign64 x=?1); apply Words.word_bound; lia. Qed.
Theorem prepared_edge s i a d (state : word 3 (r0_nstate s)=1)
  (count : word 7 (r3_ncount s)=0) (divisor : r7_ndivisor s=extended65 d)
  (initial : packed s=word 64 a) (select : word 1 (r6_nresHi s)=0)
  (hr : word 1 (nreset i)=0) (hk : word 1 (nio_5Fkill i)=0) :
  word 3 (r0_nstate (step s i))=3 /\ word 7 (r3_ncount (step s i))=0 /\
  word 65 (r7_ndivisor (step s i))=word 64 (magnitude d) /\
  packed (step s i)=word 64 (magnitude a) /\
  MulDivMetadata.MulDivMetadata.metadata (step s i)=MulDivMetadata.MulDivMetadata.metadata s /\
  word 1 (r4_nneg_5Fout (step s i))=word 1 (r4_nneg_5Fout s).
Proof.
  destruct (input_edge s i a state initial select) as [dv [sh [meta flag]]].
  rewrite divisor,divisor_magnitude in dv.
  split; [rewrite (negate_inputs_state s i state hr hk); reflexivity|].
  split; [rewrite (negate_inputs_count s i state),count; reflexivity|].
  split.
  - rewrite dv.
    assert (md : word 65 (magnitude d)=magnitude d) by (apply Words.word_small; pose proof (magnitude_bound d); change (2^64) with 18446744073709551616 in H; change (0<=magnitude d<36893488147419103232); lia).
    rewrite md; symmetry; apply Words.word_small; apply magnitude_bound.
  - split; [rewrite sh; symmetry; apply Words.word_small; apply magnitude_bound|].
    split; [exact meta|rewrite flag; apply normalize; lia].
Qed.
End MulDivSignedBits.
Print Assumptions MulDivSignedBits.divisor_magnitude.
Print Assumptions MulDivSignedBits.prepared_edge.

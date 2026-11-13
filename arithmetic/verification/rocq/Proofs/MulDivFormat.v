From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords RadixFormat MulDivControl MulDivRefinement.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivRefinement.MulDivRefinement.
Open Scope Z_scope.
Module MulDivFormat.
Definition format width x := if word 1 width=?1 then word 64 x else word 64 (SignedWords.signed 32 x).
Lemma join_halves x : word 64 (Z.shiftl (word 32 (Z.shiftr (word 64 x) 32)) 32+word 32 (Z.shiftr (word 64 x) 0))=word 64 x.
Proof.
  rewrite Z.shiftr_0_r,Z.shiftr_div_pow2,Z.shiftl_mul_pow2 by lia.
  assert (high : word 32 (word 64 x/2^32)=word 64 x/2^32).
  { apply Words.word_small; pose proof (Words.word_bound 64 x ltac:(lia)) as h.
    change (0<=word 64 x<18446744073709551616) in h.
    change (0<=word 64 x/4294967296<4294967296); split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  rewrite high.
  pose proof (Z.div_mod (word 64 x) (2^32) ltac:(vm_compute; discriminate)) as split.
  change (word 64 x=2^32*(word 64 x/2^32)+word 32 (word 64 x)) in split.
  replace (word 64 x/2^32*2^32+word 32 (word 64 x)) with (word 64 x) by lia.
  apply normalize; lia.
Qed.
Lemma extend_wire x :
  word 64 (Z.shiftl (word 32 (repeatWord 32 1 (word 1 (Z.shiftr x 31)))) 32+word 32 (Z.shiftr x 0))=word 64 (SignedWords.signed 32 x).
Proof.
  rewrite SignedWords.signed_from_bits by lia.
  pose proof (WordBits.WordBits.extract_normal 32 1 31 x ltac:(lia) ltac:(lia) ltac:(lia)) as bit.
  change (word 1 (Z.shiftr (word 32 x) 31) = word 1 (Z.shiftr x 31)) in bit.
  change (word 64 (Z.shiftl (word 32 (repeatWord 32 1 (word 1 (Z.shiftr x 31)))) 32 + word 32 (Z.shiftr x 0)) = word 64 (word 32 x-4294967296*word 1 (Z.shiftr (word 32 x) 31))).
  rewrite bit, Z.shiftr_0_r.
  assert (cases : word 1 (Z.shiftr x 31) = 0 \/ word 1 (Z.shiftr x 31) = 1) by apply bit_cases.
  destruct cases as [h|h]; rewrite h.
  - change (word 64 (0+word 32 x) = word 64 (word 32 x-4294967296*0)); f_equal; ring.
  - change (word 64 (18446744069414584320+word 32 x) = word 64 (word 32 x-4294967296*1)).
    replace (18446744069414584320+word 32 x) with ((word 32 x-4294967296*1)+1*2^64) by ring.
    unfold word at 1 3; apply Z.mod_add; discriminate.
Qed.
Lemma observe_format s i (state : word 3 (r0_nstate s)=7) :
  nio_5Fresp_5Fbits_5Fdata (observe s i)=format (r1_nreq_5Fdw s)
    (if word 1 (r6_nresHi s)=?1 then word 64 (Z.shiftr (word 130 (r8_nremainder s)) 65)
     else word 64 (r8_nremainder s)).
Proof.
  assert (low : v156 s i=word 32 (Z.shiftr (v145 s i) 0)).
  { unfold v156,v155,v154,v153; rewrite state.
    destruct (bit_cases (r1_nreq_5Fdw s)) as [h|h]; rewrite h; clean; apply normalize; lia. }
  assert (normal : word 64 (v145 s i)=v145 s i) by (unfold v145; apply normalize; lia).
  assert (value : v145 s i=word 64 (if word 1 (r6_nresHi s)=?1
    then word 64 (Z.shiftr (word 130 (r8_nremainder s)) 65) else word 64 (r8_nremainder s))).
  { unfold v145,v144,v119; rewrite Z.shiftr_0_r,narrow by lia; reflexivity. }
  cbn [observe nio_5Fresp_5Fbits_5Fdata].
  unfold v160,v159,v158,v157,v152; rewrite low.
  destruct (word 1 (r1_nreq_5Fdw s)=?1) eqn:width.
  - rewrite normalize by lia.
    rewrite <- normal at 1 2.
    rewrite join_halves,normal,value.
    unfold format; rewrite width.
    destruct (word 1 (r6_nresHi s)=?1); repeat rewrite normalize by lia; reflexivity.
  - rewrite extract_normal by lia; rewrite Z.shiftr_0_r.
    repeat rewrite normalize by lia.
    pose proof (extend_wire (v145 s i)) as ext; rewrite Z.shiftr_0_r in ext.
    rewrite ext,value.
    unfold format; rewrite width.
    destruct (word 1 (r6_nresHi s)=?1); repeat rewrite normalize by lia; reflexivity.
Qed.
End MulDivFormat.
Print Assumptions MulDivFormat.observe_format.

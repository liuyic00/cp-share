From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl.
Open Scope Z_scope.
Module MulDivDivision.
Definition candidate sh := word 65 (Z.shiftr (word 130 sh) 64).
Definition difference sh d := word 65 (candidate sh-word 65 d).
Definition signBit sh d := word 1 (Z.shiftr (difference sh d) 64).
Definition divisionStep sh d := word 130
  (Z.shiftl (Z.shiftl
    (word 64 (if signBit sh d=?1 then word 64 (Z.shiftr (word 130 sh) 64)
      else word 64 (Z.shiftr (difference sh d) 0))) 64 +
    word 64 (Z.shiftr (word 130 sh) 0)) 1 + word 1 (Z.lxor (signBit sh d) 1)).
Lemma compute_datapath s i (hs : word 3 (r0_nstate s)=3) :
  r8_nremainder (step s i)=divisionStep (r8_nremainder s) (r7_ndivisor s).
Proof.
  assert (accept : v2 s i=0) by (apply busy_no_accept; lia).
  assert (div : v42 s i=1) by (unfold v42,v41; rewrite hs; reflexivity).
  cbn [step r8_nremainder]; unfold v151,v150; rewrite accept,div.
  cbn [Z.eqb Pos.eqb]; repeat rewrite normalize by lia.
  unfold v121,v120,v119,v118,v117,v116,v86,v85,v84,v31,v8.
  change (word 1 0) with 0; change (Z.shiftl 0 64) with 0; rewrite Z.add_0_l.
  change (word 1 1) with 1.
  unfold divisionStep, signBit, difference, candidate.
  rewrite normalize by lia; reflexivity.
Qed.
Lemma divisor_stable s i (hs : word 3 (r0_nstate s)=3) :
  r7_ndivisor (step s i)=word 65 (r7_ndivisor s).
Proof.
  assert (accept : v2 s i=0) by (apply busy_no_accept; lia).
  cbn [step r7_ndivisor]; unfold v109,v108,v107,v55,v54.
  rewrite accept,hs; clean; repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma word_small w x (h : 0<=x<2^w) : word w x=x.
Proof. exact (Words.word_small w x h). Qed.
Lemma word_bound w x (h : 0<=w) : 0<=word w x<2^w.
Proof. exact (Words.word_bound w x h). Qed.
(* The sign of the 65-bit difference implements unsigned comparison only
   under the restoring bound; it is not assumed to work for arbitrary words. *)
Lemma subtraction_sign a d (ha : 0<=a<2*d) (hd : 0<=d<2^64) :
  word 1 (Z.shiftr (word 65 (a-d)) 64)=if d<=?a then 0 else 1.
Proof.
  rewrite Z.shiftr_div_pow2 by lia.
  destruct (d<=?a) eqn:choose.
  - apply Z.leb_le in choose.
    rewrite (word_small 65 (a-d)) by (change (0<=a-d<36893488147419103232); change (0<=d<18446744073709551616) in hd; lia).
    rewrite Z.div_small by (change (0<=a-d<18446744073709551616); change (0<=d<18446744073709551616) in hd; lia).
    reflexivity.
  - apply Z.leb_gt in choose.
    assert (wrap : word 65 (a-d)=a-d+2^65).
    { unfold word; symmetry; apply Z.mod_unique with (q := -1); [left|]; change (2^65) with 36893488147419103232; change (0<=d<18446744073709551616) in hd; lia. }
    rewrite wrap.
    assert (quot : (a-d+2^65)/2^64=1).
    { symmetry; apply Z.div_unique with (r := a-d+2^64); [left|]; change (2^65) with 36893488147419103232; change (2^64) with 18446744073709551616; change (0<=d<18446744073709551616) in hd; lia. }
    rewrite quot; reflexivity.
Qed.
Lemma signBit_correct sh d (bound : candidate sh<2*word 64 d) :
  signBit sh (word 64 d)=if word 64 d<=?candidate sh then 0 else 1.
Proof.
  unfold signBit, difference.
  assert (widen : word 65 (word 64 d)=word 64 d) by (apply Words.word_widen; lia).
  rewrite widen; apply subtraction_sign.
  - pose proof (word_bound 65 (Z.shiftr (word 130 sh) 64) ltac:(lia)); unfold candidate in *; lia.
  - apply word_bound; lia.
Qed.
End MulDivDivision.
Print Assumptions MulDivDivision.compute_datapath.
Print Assumptions MulDivDivision.subtraction_sign.
Print Assumptions MulDivDivision.signBit_correct.

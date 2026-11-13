From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivMetadata MulDivRefinement.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivMetadata.MulDivMetadata MulDivRefinement.MulDivRefinement.
Open Scope Z_scope.
Module MulDivMultiply.
Lemma bounds w x (hw : 0<=w) : 0<=word w x<2^w.
Proof. exact (Words.word_bound w x hw). Qed.
Definition sign s := word 1 (Z.shiftr (word 130 (r8_nremainder s)) 64).
Definition packed s := word 129 (Z.shiftl (word 65 (Z.shiftr (word 130 (r8_nremainder s)) 65)) 64+word 64 (r8_nremainder s)).
Definition rawProduct s := word 66
  (word 66 (word 66 (Z.shiftl (word 65 (repeatWord 65 1 (sign s))) 1+
    word 1 (Z.shiftr (word 130 (r8_nremainder s)) 0)) *
    word 66 (Z.shiftl (word 1 (Z.shiftr (word 65 (r7_ndivisor s)) 64)) 65+word 65 (r7_ndivisor s)))+
   word 66 (Z.shiftl (word 1 (Z.shiftr (word 130 (r8_nremainder s)) 129)) 65+
    word 65 (Z.shiftr (word 130 (r8_nremainder s)) 65))).
Definition injected s := if word 7 (r3_ncount s)=?62 then word 1 (r4_nneg_5Fout s) else 0.
Definition physical u sg b l := word 130 (Z.shiftl (Z.shiftl (Z.shiftl u 1+sg) 1+b) 63+l).
Theorem physical_edge s i (state : word 3 (r0_nstate s)=2) :
  r8_nremainder (step s i)=physical (word 65 (Z.shiftr (rawProduct s) 1)) (injected s)
    (word 1 (Z.shiftr (rawProduct s) 0)) (word 63 (Z.shiftr (word 130 (r8_nremainder s)) 1)).
Proof.
  assert (accept : v2 s i=0) by (apply busy_no_accept; lia).
  assert (div : v42 s i=0) by (unfold v42,v41; rewrite state; reflexivity).
  assert (mul : v48 s i=1) by (unfold v48,v7; rewrite state; reflexivity).
  assert (flag : v136 s i=injected s).
  { unfold v136,v135,v134,injected; change (word 7 62) with 62.
    destruct (word 7 (r3_ncount s)=?62); clean; [|reflexivity].
    destruct (bit_cases (r4_nneg_5Fout s)) as [h|h]; rewrite h; reflexivity. }
  cbn [step r8_nremainder]; unfold v151,v150,v149; rewrite accept,div,mul; cbn [Z.eqb Pos.eqb].
  unfold v139,v138,v137,v133; rewrite flag; repeat rewrite normalize by lia.
  unfold v132,v131,v130,v129,v128,v127,v126,v125,v124,v123,v122.
  unfold physical,rawProduct,sign; reflexivity.
Qed.
Lemma physical_sign u sg b l (hu : 0<=u<2^65) (hs : 0<=sg<2)
  (hb : 0<=b<2) (hl : 0<=l<2^63) : word 1 (Z.shiftr (word 130 (physical u sg b l)) 64)=sg.
Proof.
  unfold physical; rewrite normalize by lia; rewrite !Z.shiftl_mul_pow2 by lia.
  change (2^1) with 2; change (2^63) with 9223372036854775808.
  assert (normal : word 130 (((u*2+sg)*2+b)*9223372036854775808+l)=((u*2+sg)*2+b)*9223372036854775808+l).
  { apply Words.word_small; change (0<=u<36893488147419103232) in hu; change (0<=l<9223372036854775808) in hl;
    change (0<=((u*2+sg)*2+b)*9223372036854775808+l<1361129467683753853853498429727072845824); lia. }
  rewrite normal,Z.shiftr_div_pow2 by lia.
  assert (quot : (((u*2+sg)*2+b)*9223372036854775808+l)/2^64=2*u+sg).
  { symmetry; apply Z.div_unique with (r:=b*9223372036854775808+l); [left|]; change (2^64) with 18446744073709551616; change (0<=l<9223372036854775808) in hl; lia. }
  rewrite quot; unfold word; symmetry; apply Z.mod_unique with (q:=u); [left|]; change (2^1) with 2; lia.
Qed.
(* Removing the physical sign slot preserves every product bit. *)
Lemma physical_packed u sg b l (hu : 0<=u<2^65) (hs : 0<=sg<2)
  (hb : 0<=b<2) (hl : 0<=l<2^63) :
  word 129 (Z.shiftl (word 65 (Z.shiftr (word 130 (physical u sg b l)) 65)) 64+
    word 64 (physical u sg b l)) = (2*u+b)*2^63+l.
Proof.
  unfold physical; rewrite normalize by lia; rewrite !Z.shiftl_mul_pow2 by lia.
  change (2^1) with 2; change (2^63) with 9223372036854775808 in *.
  change (2^65) with 36893488147419103232 in *.
  assert (normal : word 130 (((u*2+sg)*2+b)*9223372036854775808+l)=((u*2+sg)*2+b)*9223372036854775808+l).
  { apply Words.word_small; change (0<=((u*2+sg)*2+b)*9223372036854775808+l<1361129467683753853853498429727072845824); lia. }
  rewrite normal,Z.shiftr_div_pow2 by lia.
  assert (quot : (((u*2+sg)*2+b)*9223372036854775808+l)/36893488147419103232=u).
  { symmetry; apply Z.div_unique with (r:=(sg*2+b)*9223372036854775808+l); [left|]; lia. }
  change (2^65) with 36893488147419103232; rewrite quot.
  assert (uw : word 65 u=u) by (apply Words.word_small; exact hu).
  assert (lo : word 64 (((u*2+sg)*2+b)*9223372036854775808+l)=b*9223372036854775808+l).
  { unfold word; symmetry; apply Z.mod_unique with (q:=2*u+sg); [left|]; change (2^64) with 18446744073709551616; lia. }
  rewrite uw,lo.
  assert (fit : word 129 (u*2^64+(b*9223372036854775808+l))=u*2^64+(b*9223372036854775808+l)).
  { apply Words.word_small; change (2^64) with 18446744073709551616; change (2^129) with 680564733841876926926749214863536422912; lia. }
  rewrite fit; change (2^64) with 18446744073709551616; lia.
Qed.
Theorem packed_edge s i (state : word 3 (r0_nstate s)=2) :
  packed (step s i)=
    (2*word 65 (Z.shiftr (rawProduct s) 1)+word 1 (Z.shiftr (rawProduct s) 0))*2^63+
    word 63 (Z.shiftr (word 130 (r8_nremainder s)) 1).
Proof.
  unfold packed; rewrite physical_edge by exact state; apply physical_packed.
  - exact (bounds 65 _ ltac:(lia)).
  - unfold injected; destruct (word 7 (r3_ncount s)=?62); [exact (bounds 1 _ ltac:(lia))|lia].
  - exact (bounds 1 _ ltac:(lia)).
  - exact (bounds 63 _ ltac:(lia)).
Qed.
Theorem inject_sign s i (state : word 3 (r0_nstate s)=2) : sign (step s i)=injected s.
Proof.
  unfold sign at 1; rewrite physical_edge by exact state; apply physical_sign.
  - exact (bounds 65 _ ltac:(lia)).
  - unfold injected; destruct (word 7 (r3_ncount s)=?62); [exact (bounds 1 _ ltac:(lia))|lia].
  - exact (bounds 1 _ ltac:(lia)).
  - exact (bounds 63 _ ltac:(lia)).
Qed.
Theorem preserve_operands s i (state : word 3 (r0_nstate s)=2) :
  r7_ndivisor (step s i)=word 65 (r7_ndivisor s) /\
  r4_nneg_5Fout (step s i)=word 1 (r4_nneg_5Fout s) /\ metadata (step s i)=metadata s.
Proof.
  assert (accept : v2 s i=0) by (apply busy_no_accept; lia).
  assert (input : v55 s i=0) by (unfold v55,v54; rewrite state; reflexivity).
  assert (div : v42 s i=0) by (unfold v42,v41; rewrite state; reflexivity).
  split.
  - cbn [step r7_ndivisor]; unfold v109,v108,v107; rewrite accept,input; clean; repeat rewrite normalize by lia; reflexivity.
  - split.
    + cbn [step r4_nneg_5Fout]; unfold v92,v91,v90,v89,v31; rewrite accept,div; clean.
      destruct (bit_cases (r4_nneg_5Fout s)) as [h|h]; rewrite h; reflexivity.
    + destruct (busy_request_metadata s i ltac:(lia)) as [dw tag].
      assert (hi : r5_nisHi (step s i)=word 1 (r5_nisHi s)).
      { cbn [step r5_nisHi]; unfold v93; rewrite accept; cbn [Z.eqb]; apply normalize; lia. }
      unfold metadata; rewrite dw,tag,hi; repeat rewrite normalize by lia; reflexivity.
Qed.
End MulDivMultiply.
Print Assumptions MulDivMultiply.physical_edge.
Print Assumptions MulDivMultiply.physical_packed.
Print Assumptions MulDivMultiply.packed_edge.
Print Assumptions MulDivMultiply.inject_sign.
Print Assumptions MulDivMultiply.preserve_operands.

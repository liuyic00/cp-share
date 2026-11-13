From Coq Require Import ZArith Lia Ring.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivRefinement MulDivMultiply.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivMultiply.MulDivMultiply.
Open Scope Z_scope.
Module MulDivMultiplyBalance.
Import MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivRefinement.MulDivRefinement.
Lemma product_split p (hp : 0<=p<2^66) :
  2*word 65 (Z.shiftr p 1)+word 1 (Z.shiftr p 0)=p.
Proof.
  rewrite Z.shiftr_0_r,Z.shiftr_div_pow2 by lia; change (2^1) with 2.
  assert (hq : 0<=p/2<2^65).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
    change (2^65) with 36893488147419103232; change (2^66) with 73786976294838206464 in hp; lia. }
  assert (small : word 65 (p/2)=p/2) by (apply Words.word_small; exact hq).
  rewrite small; unfold word; change (2^1) with 2.
  pose proof (Z.div_mod p 2 ltac:(lia)); lia.
Qed.
Theorem product_edge s i (state : word 3 (r0_nstate s)=2) :
  MulDivMultiply.MulDivMultiply.packed (step s i)=rawProduct s*2^63+
    word 63 (Z.shiftr (word 130 (r8_nremainder s)) 1).
Proof.
  rewrite packed_edge by exact state; rewrite product_split; [reflexivity|].
  unfold rawProduct; apply bounds; lia.
Qed.

(* Ordinary unsigned shift/add recurrence, with the discarded bit retained
   in the balance equation. The physical-edge connection is product_edge;
   operand/sign decoding is proved separately. *)
Definition unsignedStep a b low := (a+b*(low mod 2))*2^63+low/2.
Lemma raw_unsigned s a b
  (ha : 0<=a<2^64) (hb : 0<=b<2^64)
  (sg : sign s=0)
  (acc : word 65 (Z.shiftr (word 130 (r8_nremainder s)) 65)=a)
  (top : word 1 (Z.shiftr (word 130 (r8_nremainder s)) 129)=0)
  (dv : word 65 (r7_ndivisor s)=b) :
  rawProduct s=a+b*(word 64 (r8_nremainder s) mod 2).
Proof.
  assert (bs : word 1 (Z.shiftr b 64)=0).
  { rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_small by exact hb; reflexivity. }
  assert (digit : word 1 (Z.shiftr (word 130 (r8_nremainder s)) 0)=word 64 (r8_nremainder s) mod 2).
  { rewrite Z.shiftr_0_r,narrow by lia.
    change (word 1 (r8_nremainder s)=word 1 (word 64 (r8_nremainder s))).
    rewrite narrow by lia; reflexivity. }
  unfold rawProduct; rewrite sg,acc,top,dv,bs,digit.
  change (word 65 (repeatWord 65 1 0)) with 0.
  change (Z.shiftl 0 1) with 0; change (Z.shiftl 0 65) with 0; rewrite !Z.add_0_l.
  pose proof (Z.mod_pos_bound (word 64 (r8_nremainder s)) 2 ltac:(lia)) as hd.
  assert (dsmall : word 66 (word 64 (r8_nremainder s) mod 2)=word 64 (r8_nremainder s) mod 2)
    by (apply Words.word_small; change (2^66) with 73786976294838206464; lia).
  assert (asmall : word 66 a=a) by (apply Words.word_small; change (2^66) with 73786976294838206464; change (2^64) with 18446744073709551616 in ha; lia).
  assert (bsmall : word 66 b=b) by (apply Words.word_small; change (2^66) with 73786976294838206464; change (2^64) with 18446744073709551616 in hb; lia).
  rewrite dsmall,asmall,bsmall.
  assert (hdcases : word 64 (r8_nremainder s) mod 2=0 \/ word 64 (r8_nremainder s) mod 2=1) by lia.
  destruct hdcases as [h|h]; rewrite h.
  - rewrite Z.mul_0_l; change (word 66 0) with 0; rewrite Z.add_0_l,asmall; ring.
  - rewrite Z.mul_1_l,bsmall.
    assert (sum : word 66 (b+a)=b+a).
    { apply Words.word_small; change (2^66) with 73786976294838206464; change (2^64) with 18446744073709551616 in ha,hb; lia. }
    rewrite sum; ring.
Qed.
Theorem unsigned_edge s i a b
  (state : word 3 (r0_nstate s)=2)
  (ha : 0<=a<2^64) (hb : 0<=b<2^64) (sg : sign s=0)
  (acc : word 65 (Z.shiftr (word 130 (r8_nremainder s)) 65)=a)
  (top : word 1 (Z.shiftr (word 130 (r8_nremainder s)) 129)=0)
  (dv : word 65 (r7_ndivisor s)=b) :
  MulDivMultiply.MulDivMultiply.packed (step s i)=unsignedStep a b (word 64 (r8_nremainder s)).
Proof.
  rewrite product_edge by exact state; rewrite (raw_unsigned s a b ha hb sg acc top dv).
  unfold unsignedStep; f_equal.
  rewrite (extract_normal 130 63 1 (r8_nremainder s)) by lia.
  rewrite <- (extract_normal 64 63 1 (r8_nremainder s)) by lia.
  rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; apply Words.word_small.
  split; [apply Z.div_pos; [pose proof (bounds 64 (r8_nremainder s) ltac:(lia)); lia|lia]|].
  apply Z.div_lt_upper_bound; [lia|].
  pose proof (bounds 64 (r8_nremainder s) ltac:(lia)).
  change (2^64) with 18446744073709551616 in H; change (2^63) with 9223372036854775808; lia.
Qed.
Theorem unsigned_step_balance a b low :
  2*unsignedStep a b low+low mod 2=a*2^64+low+b*2^64*(low mod 2).
Proof.
  unfold unsignedStep; pose proof (Z.div_mod low 2 ltac:(lia)).
  change (2^63) with 9223372036854775808; change (2^64) with 18446744073709551616; nia.
Qed.
Theorem unsigned_step_fits a b low (ha : 0<=a<2^64)
  (hb : 0<=b<2^64) (hl : 0<=low<2^64) :
  0<=unsignedStep a b low<2^128.
Proof.
  pose proof (Z.mod_pos_bound low 2 ltac:(lia)) as parity.
  assert (half : 0<=low/2<2^63).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
    change (2^63) with 9223372036854775808; change (2^64) with 18446744073709551616 in hl; lia. }
  unfold unsignedStep; change (2^63) with 9223372036854775808 in *;
    change (2^64) with 18446744073709551616 in *;
    change (2^128) with 340282366920938463463374607431768211456.
  assert (low mod 2=0 \/ low mod 2=1) by lia; destruct H as [H|H]; rewrite H; lia.
Qed.
Theorem unsigned_accumulator_bound a b low (ha : 0<=a<=b)
  (hb : 0<=b<2^64) (hl : 0<=low<2^64) :
  0<=unsignedStep a b low/2^64<=b.
Proof.
  pose proof (unsigned_step_fits a b low ltac:(lia) hb hl) as fit.
  split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
  apply Z.lt_succ_r; apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  unfold unsignedStep.
  pose proof (Z.mod_pos_bound low 2 ltac:(lia)) as parity.
  assert (half : low/2<2^63).
  { apply Z.div_lt_upper_bound; [lia|]; change (2^63) with 9223372036854775808; change (2^64) with 18446744073709551616 in hl; lia. }
  change (2^63) with 9223372036854775808 in *; change (2^64) with 18446744073709551616 in *.
  assert (low mod 2=0 \/ low mod 2=1) by lia; destruct H as [H|H]; rewrite H; lia.
Qed.
Theorem advance_balance scale z next digit b consumed a
  (edge : 2*next+digit=z+2^64*b*digit)
  (balance : scale*z+consumed=a+2^64*b*consumed) :
  (2*scale)*next+(consumed+digit*scale)=a+2^64*b*(consumed+digit*scale).
Proof.
  replace ((2*scale)*next+(consumed+digit*scale)) with (scale*(2*next+digit)+consumed) by ring.
  rewrite edge; nia.
Qed.
Lemma compute_prefix n s inputs (state : word 3 (r0_nstate s)=2)
  (remaining : word 7 (r3_ncount s)+Z.of_nat n<64) (live : active inputs n) :
  word 3 (r0_nstate (run s inputs n))=2 /\
  word 7 (r3_ncount (run s inputs n))=word 7 (r3_ncount s)+Z.of_nat n.
Proof.
  induction n as [|n IH].
  - cbn [run]; rewrite Z.add_0_r; split; [exact state|reflexivity].
  - destruct (IH ltac:(rewrite Nat2Z.inj_succ in remaining; lia)
      ltac:(intros t ht; apply live; lia)) as [hs count].
    destruct (live n ltac:(lia)) as [hr hk].
    assert (last : (word 7 (r3_ncount (run s inputs n))=?63)=false) by (apply Z.eqb_neq; rewrite Nat2Z.inj_succ in remaining; lia).
    change (word 3 (r0_nstate (step (run s inputs n) (inputs n)))=2 /\
      word 7 (r3_ncount (step (run s inputs n) (inputs n)))=word 7 (r3_ncount s)+Z.of_nat (S n)).
    split.
    + rewrite (mul_state _ _ hs hr hk),last; reflexivity.
    + rewrite (compute_count _ _ (or_introl hs)),normalize by lia.
      rewrite small by (pose proof (count_bound s); rewrite count; change (0<=word 7 (r3_ncount s)+Z.of_nat n+1<128); rewrite Nat2Z.inj_succ in remaining; lia).
      rewrite count,Nat2Z.inj_succ; lia.
Qed.
End MulDivMultiplyBalance.
Print Assumptions MulDivMultiplyBalance.product_edge.
Print Assumptions MulDivMultiplyBalance.unsigned_edge.
Print Assumptions MulDivMultiplyBalance.unsigned_step_balance.
Print Assumptions MulDivMultiplyBalance.unsigned_accumulator_bound.
Print Assumptions MulDivMultiplyBalance.unsigned_step_fits.
Print Assumptions MulDivMultiplyBalance.advance_balance.
Print Assumptions MulDivMultiplyBalance.compute_prefix.

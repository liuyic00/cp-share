From Coq Require Import ZArith Lia.
From Proofs Require Import Words MulDivControl MulDivTiming MulDivDivision MulDivRefinement MulDivSimulation.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl MulDivTiming.MulDivTiming MulDivDivision.MulDivDivision MulDivRefinement.MulDivRefinement MulDivSimulation.MulDivSimulation.
Open Scope Z_scope.
Module MulDivZero.
Lemma zero_sign sh (bound : candidate sh<2^64) : signBit sh 0=0.
Proof.
  unfold signBit,difference; change (word 65 0) with 0; rewrite Z.sub_0_r.
  unfold candidate; rewrite normalize by lia.
  fold (candidate sh); rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small; [reflexivity|].
  pose proof (Words.word_bound 65 (Z.shiftr (word 130 sh) 64) ltac:(lia)) as h.
  change (0<=candidate sh<2^65) in h; lia.
Qed.
Lemma zero_step sh (bound : candidate sh<2^64) :
  word 129 (divisionStep sh 0)=2*word 129 sh+1.
Proof.
  pose proof (Words.word_bound 129 sh ltac:(lia)) as hs.
  change (0<=word 129 sh<680564733841876926926749214863536422912) in hs.
  pose proof (RB.split_shift sh) as split.
  change (word 129 sh=RD.candidate sh*RB.base+word 64 sh) in split.
  assert (cand : candidate sh=RD.candidate sh) by (rewrite candidate_packed,candidate_normal; reflexivity).
  assert (hc : 0<=candidate sh) by (pose proof (Words.word_bound 65 (Z.shiftr (word 130 sh) 64) ltac:(lia)); exact (proj1 H)).
  pose proof (Words.word_bound 64 sh ltac:(lia)) as hl.
  change (0<=word 64 sh<18446744073709551616) in hl.
  unfold divisionStep; rewrite narrow by lia; rewrite zero_sign by exact bound.
  change (word 1 (Z.lxor 0 1)) with 1; cbn [Z.eqb].
  unfold difference; change (word 65 0) with 0; rewrite Z.sub_0_r,Z.shiftr_0_r.
  unfold candidate at 1; rewrite normalize,narrow by lia.
  rewrite !extract_normal by lia; rewrite Z.shiftr_0_r.
  assert (low : word 64 (Z.shiftr sh 64)=candidate sh).
  { assert (c : word 64 (candidate sh)=word 64 (Z.shiftr sh 64)).
    { unfold candidate; rewrite narrow,extract_normal by lia; reflexivity. }
    rewrite <- c; apply Words.word_small; lia. }
  rewrite narrow by lia; rewrite low.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (word 129 ((candidate sh*18446744073709551616+word 64 sh)*2+1)=2*word 129 sh+1).
  rewrite <- cand in split; unfold RB.base in split.
  replace ((candidate sh*18446744073709551616+word 64 sh)*2+1) with (2*word 129 sh+1) by lia.
  apply Words.word_small.
  change (0<=2*word 129 sh+1<680564733841876926926749214863536422912).
  change (candidate sh<18446744073709551616) in bound; nia.
Qed.
Theorem zero_execution n s inputs a (limit : (n<=65)%nat)
  (state : word 3 (r0_nstate s)=3) (count : word 7 (r3_ncount s)=0)
  (divisor : word 65 (r7_ndivisor s)=0) (initial : packed s=word 64 a)
  (live : active inputs n) :
  word 65 (r7_ndivisor (run s inputs n))=0 /\
  packed (run s inputs n)=word 64 a*2^Z.of_nat n+(2^Z.of_nat n-1).
Proof.
  induction n as [|n IH].
  - split; [exact divisor|change (packed s=word 64 a*1+(1-1)); rewrite initial; ring].
  - destruct (IH ltac:(lia) ltac:(intros t ht; apply live; lia)) as [dv sh].
    destruct (div_prefix n s inputs state ltac:(rewrite count; lia)
      ltac:(intros t ht; apply live; lia)) as [st ct].
    pose proof (Words.word_bound 64 a ltac:(lia)) as ha.
    change (0<=word 64 a<18446744073709551616) in ha.
    assert (power : 0<2^Z.of_nat n<=2^64).
    { split; [apply Z.pow_pos_nonneg|apply Z.pow_le_mono_r]; lia. }
    change (0<2^Z.of_nat n<=18446744073709551616) in power.
    assert (bound : candidate (r8_nremainder (run s inputs n))<2^64).
    { rewrite candidate_packed,RB.candidate_div.
      change (word 129 (packed (run s inputs n))/RB.base<2^64).
      assert (normal : word 129 (packed (run s inputs n))=packed (run s inputs n)) by (unfold packed; apply normalize; lia).
      rewrite normal,sh; apply Z.div_lt_upper_bound; unfold RB.base;
      change (2^64) with 18446744073709551616; nia. }
    change (word 65 (r7_ndivisor (step (run s inputs n) (inputs n)))=0 /\
      packed (step (run s inputs n) (inputs n))=word 64 a*2^Z.of_nat (S n)+(2^Z.of_nat (S n)-1)).
    split.
    + rewrite divisor_stable,normalize by assumption || lia; exact dv.
    + unfold packed at 1; rewrite compute_datapath by exact st.
      assert (zero : divisionStep (r8_nremainder (run s inputs n)) (r7_ndivisor (run s inputs n))=divisionStep (r8_nremainder (run s inputs n)) 0).
      { unfold divisionStep,signBit,difference; rewrite dv; reflexivity. }
      rewrite zero,zero_step by exact bound.
      change (2*packed (run s inputs n)+1=word 64 a*2^Z.of_nat (S n)+(2^Z.of_nat (S n)-1)).
      rewrite sh,Nat2Z.inj_succ,Z.pow_succ_r by lia; ring.
Qed.
Local Opaque run step.
Theorem zero_magnitudes s inputs a (state : word 3 (r0_nstate s)=3)
  (count : word 7 (r3_ncount s)=0) (divisor : word 65 (r7_ndivisor s)=0)
  (initial : packed s=word 64 a) (live : active inputs 65) :
  word 64 (r8_nremainder (run s inputs 65))=2^64-1 /\
  word 64 (Z.shiftr (word 130 (r8_nremainder (run s inputs 65))) 65)=word 64 a.
Proof.
  destruct (zero_execution 65 s inputs a ltac:(lia) state count divisor initial live) as [dv sh].
  change (packed (run s inputs 65)=word 64 a*36893488147419103232+36893488147419103231) in sh.
  split.
  - rewrite <- (narrow 129 64 (r8_nremainder (run s inputs 65))) by lia.
    change (word 64 (packed (run s inputs 65))=2^64-1).
    rewrite sh; unfold word at 1; symmetry; apply Z.mod_unique with (q:=2*word 64 a+1); [left|]; change (2^64) with 18446744073709551616; lia.
  - rewrite extract_normal by lia.
    rewrite <- (extract_normal 129 64 65 (r8_nremainder (run s inputs 65))) by lia.
    change (word 64 (Z.shiftr (packed (run s inputs 65)) 65)=word 64 a).
    rewrite sh,Z.shiftr_div_pow2 by lia.
    assert (quot : (word 64 a*36893488147419103232+36893488147419103231)/2^65=word 64 a).
    { symmetry; apply Z.div_unique with (r:=36893488147419103231); [left|]; change (2^65) with 36893488147419103232; lia. }
    rewrite quot; apply normalize; lia.
Qed.
End MulDivZero.
Print Assumptions MulDivZero.zero_step.
Print Assumptions MulDivZero.zero_execution.
Print Assumptions MulDivZero.zero_magnitudes.

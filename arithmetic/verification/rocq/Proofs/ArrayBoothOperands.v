From Coq Require Import ZArith Lia.
From Generated Require Import ArrayMulDataModule.
From Proofs Require Import Words SignedWords WordBits ArrayOutput.
Import ArrayMulDataModule.CIRCTBits ArrayMulDataModule.nArrayMulDataModule.
Open Scope Z_scope.
Module ArrayBoothOperands.
Lemma extend_one65 x :
  word 66 (2^65 * word 1 (Z.shiftr (word 65 x) 64) + word 65 x) =
  word 66 (SignedWords.signed 65 x).
Proof. exact (WordBits.extend_one 65 x ltac:(lia)). Qed.
Lemma extend_twice65 x :
  word 66 (Z.shiftl (word 65 x) 1) =
  word 66 (Z.shiftl (word 66 (SignedWords.signed 65 x)) 1).
Proof. exact (WordBits.extend_twice 65 x ltac:(lia)). Qed.

Definition positive (i : Inputs) : Z := word 66 (SignedWords.signed 65 (nio_5Fb i)).
Definition negative (i : Inputs) : Z := word 66 (Z.lnot (positive i)).
Definition twice (i : Inputs) : Z := word 66 (Z.shiftl (positive i) 1).
Definition negativeTwice (i : Inputs) : Z := word 66 (Z.shiftl (negative i) 1).

Lemma complement65 (s : State) (i : Inputs) :
  v3 s i = word 65 (Z.lnot (word 65 (nio_5Fb i))).
Proof.
  unfold v3, v2; change (word 65 36893488147419103231) with 36893488147419103231.
  exact (WordBits.xor_mask 65 (word 65 (nio_5Fb i)) ltac:(lia)).
Qed.
Lemma positive_10 (s : State) (i : Inputs) : v10 s i = positive i.
Proof.
  unfold v10, v9, positive; rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mul_comm; exact (WordBits.extend_one 65 (nio_5Fb i) ltac:(lia)).
Qed.
Lemma negative_integer (i : Inputs) : negative i = word 66 (-SignedWords.signed 65 (nio_5Fb i)-1).
Proof.
  unfold negative, positive.
  change (Words.word 66 (Z.lnot (Words.word 66 (SignedWords.signed 65 (nio_5Fb i)))) = Words.word 66 (-SignedWords.signed 65 (nio_5Fb i)-1)).
  rewrite WordBits.word_complement, lnot_as_opp by lia; reflexivity.
Qed.
Lemma negative_sign (i : Inputs) :
  SignedWords.signed 65 (Z.lnot (word 65 (nio_5Fb i))) = -SignedWords.signed 65 (nio_5Fb i)-1.
Proof.
  change (SignedWords.signed 65 (Z.lnot (Words.word 65 (nio_5Fb i))) = -SignedWords.signed 65 (nio_5Fb i)-1).
  rewrite <- (signed_normal 65 (Z.lnot (Words.word 65 (nio_5Fb i)))) by lia.
  rewrite WordBits.signed_complement, signed_normal by lia; reflexivity.
Qed.
Lemma negative_5 (s : State) (i : Inputs) : v5 s i = negative i.
Proof.
  unfold v5, v4; rewrite complement65.
  rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mul_comm.
  rewrite (extend_one65 (Z.lnot (word 65 (nio_5Fb i)))).
  rewrite negative_sign, negative_integer; reflexivity.
Qed.
Lemma twice_44 (s : State) (i : Inputs) : v44 s i = twice i.
Proof.
  unfold v44, v6, twice, positive; change (word 1 0) with 0; rewrite Z.add_0_r.
  exact (WordBits.extend_twice 65 (nio_5Fb i) ltac:(lia)).
Qed.
Lemma negative_twice_7 (s : State) (i : Inputs) : v7 s i = negativeTwice i.
Proof.
  unfold v7, v6; change (word 1 0) with 0; rewrite Z.add_0_r, complement65.
  rewrite (extend_twice65 (Z.lnot (word 65 (nio_5Fb i)))).
  rewrite negative_sign; unfold negativeTwice; rewrite negative_integer; reflexivity.
Qed.
Lemma positive_50 (s : State) (i : Inputs) : v50 s i = positive i.
Proof. exact (positive_10 s i). Qed.
Lemma negative_38 (s : State) (i : Inputs) : v38 s i = negative i.
Proof. exact (negative_5 s i). Qed.
Lemma negative_twice_41 (s : State) (i : Inputs) : v41 s i = negativeTwice i.
Proof. exact (negative_twice_7 s i). Qed.

Print Assumptions positive_10.
Print Assumptions negative_5.
Print Assumptions twice_44.
Print Assumptions negative_twice_7.


Lemma first_bit0 (s : State) (i : Inputs) : v1 s i = word 1 (Z.shiftr (v16 s i) 0).
Proof.
  unfold v1, v16; rewrite !Z.shiftr_0_r.
  pose proof (WordBits.extract_normal 2 1 0 (word 65 (nio_5Fa i)) ltac:(lia) ltac:(lia) ltac:(lia)) as h.
  rewrite !Z.shiftr_0_r in h; exact (eq_sym h).
Qed.
Lemma first_bit1 (s : State) (i : Inputs) : v0 s i = word 1 (Z.shiftr (v16 s i) 1).
Proof.
  unfold v0, v16; rewrite Z.shiftr_0_r.
  exact (eq_sym (WordBits.extract_normal 2 1 1 (word 65 (nio_5Fa i)) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.
End ArrayBoothOperands.

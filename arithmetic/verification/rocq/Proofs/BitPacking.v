From Coq Require Import ZArith Lia.
From Proofs Require Import Words.
Open Scope Z_scope.
Module BitPacking.

(* Reconstruct a word from its low bits, with their actual positional weights. *)
Fixpoint packed_bits (n : nat) (x : Z) : Z :=
  match n with
  | O => 0
  | S k => packed_bits k x + 2^(Z.of_nat k) * word 1 (Z.shiftr x (Z.of_nat k))
  end.

Theorem packed_bits_word n x : packed_bits n x = word (Z.of_nat n) x.
Proof.
  induction n as [|n IH].
  - cbn [packed_bits Z.of_nat]; unfold word; change (2^0) with 1.
    rewrite Z.mod_1_r; reflexivity.
  - cbn [packed_bits]; rewrite IH.
    unfold word; rewrite Z.shiftr_div_pow2 by lia.
    change (2^1) with 2.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite (Z.mul_comm 2 (2^Z.of_nat n)).
    symmetry; apply Z.rem_mul_r; [apply Z.pow_nonzero; lia | lia].
Qed.

Theorem packed_bits_normal n x : packed_bits n (word (Z.of_nat n) x) = packed_bits n x.
Proof. rewrite !packed_bits_word; apply word_idem; lia. Qed.

Print Assumptions packed_bits_word.
End BitPacking.

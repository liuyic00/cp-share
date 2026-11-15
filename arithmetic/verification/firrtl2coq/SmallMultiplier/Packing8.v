From Coq Require Import ZArith Lia.
Open Scope Z_scope.
Definition extract_bit x k := (x / 2^Z.of_nat k) mod 2.
Fixpoint packed_bits (n : nat) (x : Z) : Z :=
 match n with O => 0 | S k => packed_bits k x + 2^Z.of_nat k * extract_bit x k end.
Lemma packed_bits_mod n x : packed_bits n x = x mod 2^Z.of_nat n.
Proof.
 induction n as [|n IH].
 - simpl. rewrite Z.mod_1_r. reflexivity.
 - cbn [packed_bits]. rewrite IH. unfold extract_bit.
   rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
   replace (2 * 2^Z.of_nat n) with (2^Z.of_nat n * 2) by ring.
   symmetry. apply Z.rem_mul_r; [apply Z.pow_nonzero; lia|lia].
Qed.
Lemma packed_bits_exact n x (H : 0 <= x < 2^Z.of_nat n) : packed_bits n x = x.
Proof. rewrite packed_bits_mod. apply Z.mod_small. exact H. Qed.
Print Assumptions packed_bits_exact.

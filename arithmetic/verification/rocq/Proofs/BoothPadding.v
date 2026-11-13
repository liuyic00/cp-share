From Coq Require Import ZArith Lia List.
From Proofs Require Import Words SignedWords.
Import ListNotations.
Open Scope Z_scope.
Module BoothPadding.

Definition sign (p : Z) := word 1 (Z.shiftr (word 66 p) 65).
Definition inverted (p : Z) := word 1 (Z.lxor (sign p) 1).
Definition firstPadded (p : Z) :=
  word 69 (2^68 * inverted p + 2^67 * sign p + 2^66 * sign p + word 66 p).
Definition middlePadded (p c : Z) :=
  word 70 (2^69 + 2^68 * inverted p + 4 * word 66 p + word 2 c).
Definition finalPadded (p c : Z) :=
  word 69 (2^68 * inverted p + 4 * word 66 p + word 2 c).

Lemma inverted_sign p : inverted p = 1 - sign p.
Proof.
  unfold inverted, sign; destruct (bit_cases (Z.shiftr (word 66 p) 65)) as [h|h];
    rewrite h; reflexivity.
Qed.
Lemma signed_row p : signed 66 p = word 66 p - 2^66 * sign p.
Proof. exact (signed_from_bits 66 p ltac:(lia)). Qed.
Lemma first_padding p : firstPadded p = signed 66 p + 2^68.
Proof.
  unfold firstPadded; rewrite inverted_sign.
  replace (2^68 * (1-sign p) + 2^67*sign p + 2^66*sign p + word 66 p)
    with (signed 66 p + 2^68) by (rewrite signed_row; change (2^68) with (4*2^66); change (2^67) with (2*2^66); ring).
  apply word_small; pose proof (signed_range 66 p ltac:(lia));
    change (2^(66-1)) with 36893488147419103232 in *; lia.
Qed.
Lemma middle_padding p c : middlePadded p c = 4*signed 66 p + word 2 c + 3*2^68.
Proof.
  unfold middlePadded; rewrite inverted_sign.
  replace (2^69 + 2^68*(1-sign p) + 4*word 66 p + word 2 c)
    with (4*signed 66 p + word 2 c + 3*2^68)
    by (rewrite signed_row; change (2^68) with (4*2^66); change (2^69) with (8*2^66); ring).
  apply word_small; pose proof (signed_range 66 p ltac:(lia)); pose proof (word_bound 2 c ltac:(lia));
    change (2^(66-1)) with 36893488147419103232 in *; lia.
Qed.
Lemma final_padding p c : finalPadded p c = 4*signed 66 p + word 2 c + 2^68.
Proof.
  unfold finalPadded; rewrite inverted_sign.
  replace (2^68*(1-sign p) + 4*word 66 p + word 2 c)
    with (4*signed 66 p + word 2 c + 2^68)
    by (rewrite signed_row; change (2^68) with (4*2^66); ring).
  apply word_small; pose proof (signed_range 66 p ltac:(lia)); pose proof (word_bound 2 c ltac:(lia));
    change (2^(66-1)) with 36893488147419103232 in *; lia.
Qed.

Definition Row := (Z * Z)%type.
Fixpoint correctedSum (rows : list Row) : Z :=
  match rows with
  | [] => 0
  | (p,c)::rest => signed 66 p + word 2 c + 4*correctedSum rest
  end.
Fixpoint packedTail (previous : Z) (rows : list Row) : Z :=
  match rows with
  | [] => word 2 previous
  | [(p,c)] => finalPadded p previous + 4*word 2 c
  | (p,c)::rest => middlePadded p previous + 4*packedTail c rest
  end.
Fixpoint tailOffset (n : nat) : Z :=
  match n with O => 0 | S O => 2^68 | S n => 3*2^68+4*tailOffset n end.

Lemma packed_tail_eq rows previous :
  packedTail previous rows = word 2 previous + 4*correctedSum rows + tailOffset (length rows).
Proof.
  revert previous; induction rows as [|[p c] rest IH]; intros previous.
  - cbn [packedTail correctedSum tailOffset length]; ring.
  - destruct rest as [|next rest].
    + cbn [packedTail correctedSum tailOffset length]; rewrite final_padding; ring.
    + change (middlePadded p previous + 4*packedTail c (next::rest) =
        word 2 previous + 4*(signed 66 p + word 2 c + 4*correctedSum (next::rest)) +
        (3*2^68+4*tailOffset (length (next::rest)))).
      rewrite IH, middle_padding; ring.
Qed.

Theorem packed_sum_65 first rows (count : length rows = 32%nat) :
  word 130 (firstPadded (fst first) + packedTail (snd first) rows) =
  word 130 (correctedSum (first::rows)).
Proof.
  destruct first as [p c]; cbn [fst snd].
  rewrite first_padding, packed_tail_eq, count.
  assert (offsets : 2^68 + tailOffset 32 = 2*2^130) by reflexivity.
  cbn [correctedSum].
  replace (signed 66 p + 2^68 + (word 2 c + 4*correctedSum rows + tailOffset 32))
    with (signed 66 p + word 2 c + 4*correctedSum rows + 2*2^130) by (rewrite <- offsets; ring).
  unfold word at 1; rewrite Z.mod_add by (apply Z.pow_nonzero; lia); reflexivity.
Qed.
Print Assumptions packed_sum_65.
End BoothPadding.

(* The final inverted sign bit lies beyond the 130-bit output boundary. *)
Lemma final_low p c :
  4 * word 66 p + word 2 c =
    BoothPadding.finalPadded p c - 2^68 * BoothPadding.inverted p.
Proof.
  rewrite BoothPadding.final_padding, BoothPadding.inverted_sign, BoothPadding.signed_row.
  change (2^68) with (4*2^66); ring.
Qed.

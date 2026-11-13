From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords WordBits BoothRecoding BoothWide.
Open Scope Z_scope.
Module BoothWindows.
Definition digit (w : Z) : Z :=
  word 1 (Z.shiftr w 0) + word 1 (Z.shiftr w 1) - 2*word 1 (Z.shiftr w 2).

Theorem corrected_window b w (bound : 0 <= w < 8) :
  word 130 (signed 66 (BoothRecoding.BoothRecoding.row (word 66 (signed 65 b)) w) +
    word 2 (BoothRecoding.BoothRecoding.correction w)) = word 130 (signed 65 b * digit w).
Proof.
  assert (cases : w=0 \/ w=1 \/ w=2 \/ w=3 \/ w=4 \/ w=5 \/ w=6 \/ w=7) by lia.
  destruct cases as [h|[h|[h|[h|[h|[h|[h|h]]]]]]]; subst w.
  - exact (BoothWide.corrected_row_wide b false false false).
  - exact (BoothWide.corrected_row_wide b true false false).
  - exact (BoothWide.corrected_row_wide b false true false).
  - exact (BoothWide.corrected_row_wide b true true false).
  - exact (BoothWide.corrected_row_wide b false false true).
  - exact (BoothWide.corrected_row_wide b true false true).
  - exact (BoothWide.corrected_row_wide b false true true).
  - exact (BoothWide.corrected_row_wide b true true true).
Qed.

Lemma middle_digit x offset :
  digit (word 3 (Z.shiftr x offset)) =
  word 1 (Z.shiftr x offset) + word 1 (Z.shiftr x (offset+1)) -
    2*word 1 (Z.shiftr x (offset+2)).
Proof.
  unfold digit; rewrite !WordBits.extract_extract by lia.
  rewrite Z.add_0_r; reflexivity.
Qed.
Lemma first_digit_small w (bound : 0 <= w < 4) :
  digit (2*w) = word 1 (Z.shiftr w 0) - 2*word 1 (Z.shiftr w 1).
Proof.
  assert (cases : w=0 \/ w=1 \/ w=2 \/ w=3) by lia.
  destruct cases as [h|[h|[h|h]]]; subst w; reflexivity.
Qed.
Lemma last_digit_small w (bound : 0 <= w < 4) :
  digit (word 3 (4*word 1 (Z.shiftr w 1)+w)) =
    word 1 (Z.shiftr w 0) - word 1 (Z.shiftr w 1).
Proof.
  assert (cases : w=0 \/ w=1 \/ w=2 \/ w=3) by lia.
  destruct cases as [h|[h|[h|h]]]; subst w; reflexivity.
Qed.
Lemma first_digit x :
  digit (2*word 2 x) = word 1 (Z.shiftr x 0) - 2*word 1 (Z.shiftr x 1).
Proof.
  rewrite first_digit_small by exact (word_bound 2 x ltac:(lia)).
  rewrite !WordBits.extract_normal by lia; reflexivity.
Qed.
Lemma last_digit x :
  digit (word 3 (4*word 1 (Z.shiftr x 64)+word 2 (Z.shiftr x 63))) =
    word 1 (Z.shiftr x 63) - word 1 (Z.shiftr x 64).
Proof.
  pose proof (WordBits.extract_extract 2 1 63 1 x ltac:(lia) ltac:(lia) ltac:(lia)) as high.
  change (word 1 (Z.shiftr (word 2 (Z.shiftr x 63)) 1) = word 1 (Z.shiftr x 64)) in high.
  rewrite <- high at 1.
  rewrite last_digit_small by exact (word_bound 2 (Z.shiftr x 63) ltac:(lia)).
  rewrite !WordBits.extract_extract by lia; reflexivity.
Qed.
Print Assumptions corrected_window.
Print Assumptions middle_digit.
Print Assumptions first_digit.
Print Assumptions last_digit.
End BoothWindows.

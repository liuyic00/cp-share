From Coq Require Import ZArith Lia Bool Ring.
From Proofs Require Import Words SignedWords BoothRecoding.
Import BoothRecoding.BoothRecoding.
Open Scope Z_scope.
Module BoothWide.

Lemma row_integer_form b (previous even odd : bool) :
  let w := bit previous + 2 * bit even + 4 * bit odd in
  row (word 66 b) w = word 66 (digit previous (even,odd) * b - correction w).
Proof.
  destruct previous, even, odd;
  unfold row, correction, digit, bit; cbn [fst snd]; cbn zeta;
  repeat rewrite Words.word_idem by lia;
  word_constants; cbn beta iota zeta delta [orb]; word_constants;
  try rewrite Z.shiftl_mul_pow2 by lia;
  try rewrite lnot_as_opp;
  try reflexivity.
  all: match goal with
    | |- word 66 ?lhs = word 66 (?a * ?x - ?c) =>
      replace lhs with (a * word 66 x + (-c)) by (try change (2^1) with 2; ring);
      replace (a*x-c) with (a*x+(-c)) by ring;
      apply word_affine; lia
    end.
Qed.

(* Widen the signed row before adding its unsigned correction. This includes
   b = -2^64 and digit = -2, whose positive 2^65 result does not fit signed 66. *)
Theorem corrected_row_wide b (previous even odd : bool) :
  let w := bit previous + 2 * bit even + 4 * bit odd in
  word 130 (SignedWords.signed 66 (row (word 66 (SignedWords.signed 65 b)) w) + correction w) =
  word 130 (SignedWords.signed 65 b * digit previous (even,odd)).
Proof.
  cbn zeta; rewrite row_integer_form.
  pose proof (signed_range 65 b ltac:(lia)) as bound.
  change (-(2^64) <= SignedWords.signed 65 b < 2^64) in bound.
  destruct previous, even, odd;
    unfold digit, bit, correction; cbn [fst snd]; cbn zeta;
    word_constants; cbn beta iota zeta delta [orb]; word_constants;
    rewrite signed_normal by lia;
    rewrite signed_small by (try lia; change (2^(66-1)) with (2*2^64); lia);
    apply f_equal; ring.
Qed.
Print Assumptions corrected_row_wide.
End BoothWide.

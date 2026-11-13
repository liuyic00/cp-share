From Coq Require Import ZArith Lia.
From Proofs Require Import Words.
Open Scope Z_scope.
Lemma decompose8 x :
  word 8 x =
    word 1 (Z.shiftr (word 8 x) 0) +
    2 * word 1 (Z.shiftr (word 8 x) 1) +
    4 * word 1 (Z.shiftr (word 8 x) 2) +
    8 * word 1 (Z.shiftr (word 8 x) 3) +
    16 * word 1 (Z.shiftr (word 8 x) 4) +
    32 * word 1 (Z.shiftr (word 8 x) 5) +
    64 * word 1 (Z.shiftr (word 8 x) 6) +
    128 * word 1 (Z.shiftr (word 8 x) 7).
Proof.
  remember (word 8 x) as y eqn:Hy.
  assert (bound : 0 <= y < 256).
  { subst y; exact (word_bound 8 x ltac:(lia)). }
  rewrite !Z.shiftr_div_pow2 by lia.
  unfold word.
  change (2^0) with 1; change (2^1) with 2; change (2^2) with 4;
  change (2^3) with 8; change (2^4) with 16; change (2^5) with 32;
  change (2^6) with 64; change (2^7) with 128.
  rewrite Z.div_1_r.
  replace y with (y mod 256) at 1 by (rewrite Z.mod_small by exact bound; reflexivity).
  change (y mod 256) with (y mod (2 * 128)).
  rewrite (Z.rem_mul_r y 2 128) by lia.
  change ((y / 2) mod 128) with ((y / 2) mod (2 * 64)).
  rewrite (Z.rem_mul_r (y / 2) 2 64) by lia.
  rewrite Z.div_div by lia. word_constants.
  change ((y / 4) mod 64) with ((y / 4) mod (2 * 32)).
  rewrite (Z.rem_mul_r (y / 4) 2 32) by lia.
  rewrite Z.div_div by lia. word_constants.
  change ((y / 8) mod 32) with ((y / 8) mod (2 * 16)).
  rewrite (Z.rem_mul_r (y / 8) 2 16) by lia.
  rewrite Z.div_div by lia. word_constants.
  change ((y / 16) mod 16) with ((y / 16) mod (2 * 8)).
  rewrite (Z.rem_mul_r (y / 16) 2 8) by lia.
  rewrite Z.div_div by lia. word_constants.
  change ((y / 32) mod 8) with ((y / 32) mod (2 * 4)).
  rewrite (Z.rem_mul_r (y / 32) 2 4) by lia.
  rewrite Z.div_div by lia. word_constants.
  change ((y / 64) mod 4) with ((y / 64) mod (2 * 2)).
  rewrite (Z.rem_mul_r (y / 64) 2 2) by lia.
  rewrite Z.div_div by lia. word_constants.
  ring.
Qed.

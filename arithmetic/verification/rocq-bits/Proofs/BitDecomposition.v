From Stdlib Require Import ZArith Lia Zmod.Bits.
Open Scope Z_scope.
(* Decompose an arbitrary typed byte, not a finite sample of inputs. *)
Lemma decompose8 (x : bits 8) :
  Zmod.unsigned x =
    1 * Zmod.unsigned (Zmod.slice 0 1 x) +
    2 * Zmod.unsigned (Zmod.slice 1 2 x) +
    4 * Zmod.unsigned (Zmod.slice 2 3 x) +
    8 * Zmod.unsigned (Zmod.slice 3 4 x) +
    16 * Zmod.unsigned (Zmod.slice 4 5 x) +
    32 * Zmod.unsigned (Zmod.slice 5 6 x) +
    64 * Zmod.unsigned (Zmod.slice 6 7 x) +
    128 * Zmod.unsigned (Zmod.slice 7 8 x).
Proof.
  rewrite !bits.unsigned_slice by lia.
  pose proof (bits.unsigned_range x ltac:(lia)) as bound.
  remember (Zmod.unsigned x) as y.
  change (0 <= y < 256) in bound.
  change (y = 1 * ((y / 1) mod 2) + 2 * ((y / 2) mod 2) + 4 * ((y / 4) mod 2) + 8 * ((y / 8) mod 2) + 16 * ((y / 16) mod 2) + 32 * ((y / 32) mod 2) + 64 * ((y / 64) mod 2) + 128 * ((y / 128) mod 2)).
  rewrite Z.div_1_r.
  replace y with (y mod 256) at 1 by (rewrite Z.mod_small by exact bound; reflexivity).
  change (y mod 256) with (y mod (2 * 128)).
  rewrite (Z.rem_mul_r y 2 128) by lia.
  change ((y / 2) mod 128) with ((y / 2) mod (2 * 64)).
  rewrite (Z.rem_mul_r (y / 2) 2 64) by lia.
  rewrite Z.div_div by lia. change (2 * 2) with 4.
  change ((y / 4) mod 64) with ((y / 4) mod (2 * 32)).
  rewrite (Z.rem_mul_r (y / 4) 2 32) by lia.
  rewrite Z.div_div by lia. change (4 * 2) with 8.
  change ((y / 8) mod 32) with ((y / 8) mod (2 * 16)).
  rewrite (Z.rem_mul_r (y / 8) 2 16) by lia.
  rewrite Z.div_div by lia. change (8 * 2) with 16.
  change ((y / 16) mod 16) with ((y / 16) mod (2 * 8)).
  rewrite (Z.rem_mul_r (y / 16) 2 8) by lia.
  rewrite Z.div_div by lia. change (16 * 2) with 32.
  change ((y / 32) mod 8) with ((y / 32) mod (2 * 4)).
  rewrite (Z.rem_mul_r (y / 32) 2 4) by lia.
  rewrite Z.div_div by lia. change (32 * 2) with 64.
  change ((y / 64) mod 4) with ((y / 64) mod (2 * 2)).
  rewrite (Z.rem_mul_r (y / 64) 2 2) by lia.
  rewrite Z.div_div by lia. change (64 * 2) with 128.
  ring.
Qed.
Print Assumptions decompose8.

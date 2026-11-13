From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords RadixControl RadixTemporal RadixBalance RadixZero RadixResult.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixTemporal.RadixTemporal RadixBalance.RadixBalance RadixZero.RadixZero.
Open Scope Z_scope.
Module RadixZeroResult.
Lemma affine w a x c (hw : 0 <= w) : word w (a*word w x+c) = word w (a*x+c).
Proof. exact (SignedWords.word_affine w a x c hw). Qed.
Theorem zeroRun_closed n sh : zeroRun n sh = word 129 (2^Z.of_nat n * sh + (2^Z.of_nat n-1)).
Proof.
  induction n as [|n IH].
  - change (word 129 sh = word 129 (1*sh+(1-1))); f_equal; ring.
  - cbn [zeroRun]; unfold zeroStep; rewrite zeroRun_normal, IH, affine by lia.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; f_equal; ring.
Qed.
Theorem zeroRun_full a : zeroRun 64 (word 65 a) = word 65 a*base+(base-1).
Proof.
  rewrite zeroRun_closed; change (word 129 (base*word 65 a+(base-1)) = word 65 a*base+(base-1)).
  rewrite small; [ring |].
  pose proof (bounds 65 a ltac:(lia)) as h.
  change (0 <= word 65 a < 36893488147419103232) in h.
  unfold base; change (0 <= 18446744073709551616*word 65 a+(18446744073709551616-1) < 680564733841876926926749214863536422912); lia.
Qed.
Lemma zeroRun_low a : low (zeroRun 64 (word 65 a)) = base-1.
Proof.
  rewrite zeroRun_full; unfold low, word.
  change ((a mod 2^65*base+(base-1)) mod base = base-1).
  replace (a mod 2^65*base+(base-1)) with ((base-1)+(a mod 2^65)*base) by ring.
  rewrite Z.mod_add by (unfold base; lia); apply Z.mod_small; unfold base; lia.
Qed.
Lemma zeroRun_remainder a :
  word 64 (Z.shiftr (word 129 (zeroRun 64 (word 65 a))) 65) = word 65 a / 2.
Proof.
  rewrite RadixResult.RadixResult.final_remainder, zeroRun_normal, zeroRun_full.
  pose proof (Z.div_mod (word 65 a) 2 ltac:(lia)) as h.
  pose proof (Z.mod_pos_bound (word 65 a) 2 ltac:(lia)) as hm.
  symmetry; apply Z.div_unique with (r := (word 65 a mod 2)*base+(base-1)).
  - left; unfold base; lia.
  - nia.
Qed.
Local Opaque run step zeroRun.
Theorem zero_segment_result s inputs
  (hs : word 3 (r0_nstate s) = 3)
  (hc : word 6 (r9_ncnt_5Fvalue s) = 0)
  (hd : word 64 (r5_nbReg s) = 0)
  (initial : word 129 (r2_nshiftReg s) = word 65 (r6_naValx2Reg s))
  (reset : forall t, (t < 64)%nat -> word 1 (nreset (inputs t)) = 0) :
  nio_5Fout_5Fvalid (observe (run s inputs 64) (inputs 64%nat)) = 1 /\
  v40 (run s inputs 64) (inputs 64%nat) = base-1 /\
  v402 (run s inputs 64) (inputs 64%nat) = word 65 (r6_naValx2Reg s)/2.
Proof.
  destruct (compute_zero_run 64 s inputs hs ltac:(rewrite hc; reflexivity) reset hd) as [divisor result].
  assert (hn : zeroRun 64 (r2_nshiftReg s) = zeroRun 64 (word 65 (r6_naValx2Reg s))).
  { rewrite !zeroRun_closed.
    rewrite <- (affine 129 (2^Z.of_nat 64) (r2_nshiftReg s) (2^Z.of_nat 64-1)) by lia.
    rewrite initial; reflexivity. }
  rewrite hn in result.
  split.
  - apply finish_valid; apply compute_finishes; [exact hs | rewrite hc; reflexivity | exact reset].
  - split.
    + unfold v40; rewrite Z.shiftr_0_r, result; apply zeroRun_low.
    + unfold v402; rewrite result.
      rewrite <- (zeroRun_normal 64 (word 65 (r6_naValx2Reg s))) at 1.
      apply zeroRun_remainder.
Qed.
End RadixZeroResult.
Print Assumptions RadixZeroResult.zero_segment_result.

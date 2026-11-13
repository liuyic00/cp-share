From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixTemporal RadixDatapath RadixBalance RadixExecution.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixDatapath.RadixDatapath RadixBalance.RadixBalance RadixExecution.RadixExecution.
Open Scope Z_scope.
Module RadixResult.
Lemma decode_balance z a d q (hz : 0 <= z) (hq : 0 <= q < base)
  (bound : z / base < 2*d)
  (balance : z + 2*base*d*q = 2*base*a+q) :
  z mod base = a/d /\ z/(2*base) = a mod d.
Proof.
  assert (hd : 0 < d).
  { assert (0 <= z/base) by (apply Z.div_pos; unfold base; lia). lia. }
  assert (split : z = (2*base)*(a-d*q)+q) by nia.
  assert (hr : z/(2*base) = a-d*q).
  { symmetry; apply Z.div_unique with (r:=q); [left; unfold base in *; lia | nia]. }
  assert (low : z mod base = q).
  { symmetry; apply Z.mod_unique with (q:=2*(a-d*q)); [left; exact hq | nia]. }
  assert (rbound : 0 <= a-d*q < d).
  { pose proof (Z.div_mod z base ltac:(unfold base; lia)) as hsplit.
    rewrite low in hsplit.
    assert (z/base = 2*(a-d*q)) by (unfold base in *; nia).
    assert (0 <= z/(2*base)) by (apply Z.div_pos; unfold base; lia).
    lia. }
  rewrite low, hr; split.
  - apply Z.div_unique with (r:=a-d*q); [left; exact rbound | ring].
  - apply Z.mod_unique with (q:=q); [left; exact rbound | ring].
Qed.
Lemma final_remainder sh : word 64 (Z.shiftr (word 129 sh) 65) = word 129 sh/(2*base).
Proof.
  rewrite Z.shiftr_div_pow2 by lia; apply small.
  pose proof (bounds 129 sh ltac:(lia)) as h.
  change (0 <= word 129 sh < 680564733841876926926749214863536422912) in h.
  change (0 <= word 129 sh/36893488147419103232 < 18446744073709551616).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Theorem compute_result n s inputs a
  (hs : word 3 (r0_nstate s) = 3)
  (remaining : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n <= 64)
  (reset : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0)
  (initialBound : candidate (r2_nshiftReg s) < 2*word 64 (r5_nbReg s))
  (alignment : 2^Z.of_nat n * word 129 (r2_nshiftReg s) = 2*base*a) :
  low (r2_nshiftReg (run s inputs n)) = a / word 64 (r5_nbReg s) /\
  word 64 (Z.shiftr (word 129 (r2_nshiftReg (run s inputs n))) 65) = a mod word 64 (r5_nbReg s).
Proof.
  destruct (compute_execution n s inputs hs remaining reset initialBound)
    as [divisor [bound [q [size balance]]]].
  pose proof (RadixTemporal.RadixTemporal.count_bound s) as hc.
  assert (power : 2^Z.of_nat n <= base).
  { change (2^Z.of_nat n <= 2^64); apply Z.pow_le_mono_r; lia. }
  rewrite alignment in balance; rewrite candidate_div in bound.
  pose proof (decode_balance (word 129 (r2_nshiftReg (run s inputs n))) a
    (word 64 (r5_nbReg s)) q ltac:(pose proof (bounds 129 (r2_nshiftReg (run s inputs n)) ltac:(lia)); lia)
    ltac:(lia) bound balance) as [hq hr].
  split.
  - rewrite <- low_normal. exact hq.
  - rewrite final_remainder; exact hr.
Qed.
(* Direct connection to the generated quotient/remainder wires. Signed and
   word-mode output selection is a separate, still outstanding obligation. *)
Theorem compute_finished_result n s inputs a
  (hs : word 3 (r0_nstate s) = 3)
  (remaining : word 6 (r9_ncnt_5Fvalue s) + Z.of_nat n = 64)
  (reset : forall t, (t < n)%nat -> word 1 (nreset (inputs t)) = 0)
  (initialBound : candidate (r2_nshiftReg s) < 2*word 64 (r5_nbReg s))
  (alignment : 2^Z.of_nat n * word 129 (r2_nshiftReg s) = 2*base*a) :
  nio_5Fout_5Fvalid (observe (run s inputs n) (inputs n)) = 1 /\
  v40 (run s inputs n) (inputs n) = a / word 64 (r5_nbReg s) /\
  v402 (run s inputs n) (inputs n) = a mod word 64 (r5_nbReg s).
Proof.
  split.
  - apply RadixControl.RadixControl.finish_valid.
    exact (RadixTemporal.RadixTemporal.compute_finishes n s inputs hs remaining reset).
  - destruct (compute_result n s inputs a hs ltac:(lia) reset initialBound alignment) as [hq hr].
    split; [unfold v40; rewrite Z.shiftr_0_r; change (low (word 129 (r2_nshiftReg (run s inputs n))) = a / word 64 (r5_nbReg s)); rewrite low_normal; exact hq | exact hr].
Qed.
End RadixResult.
Print Assumptions RadixResult.compute_result.
Print Assumptions RadixResult.compute_finished_result.

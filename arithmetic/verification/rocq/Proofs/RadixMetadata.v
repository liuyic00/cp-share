From Coq Require Import ZArith Lia.
From Proofs Require Import Words RadixControl RadixCapture RadixExecution.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl RadixCapture.RadixCapture RadixExecution.RadixExecution.
Open Scope Z_scope.
Module RadixMetadata.
Definition metadata s := (word 1 (r3_naSignReg s), word 1 (r4_nqSignReg s),
  word 1 (r7_nctrlReg_5FisW s), word 1 (r8_nctrlReg_5FisHi s)).
Definition requestMetadata i :=
  (signBit (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i),
   word 1 (Z.land
     (Z.lxor (signBit (nio_5Fin_5Fbits_5Fsrc_5F0 i) (nctrl_5Fsign i))
       (signBit (nio_5Fin_5Fbits_5Fsrc_5F1 i) (nctrl_5Fsign i)))
     (if word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 i) =? 0 then 0 else 1)),
   word 1 (nctrl_5FisW i), word 1 (nctrl_5FisHi i)).
Lemma xor_normal x y : Z.lxor (word 1 x) (word 1 y) = word 1 (Z.lxor (word 1 x) (word 1 y)).
Proof.
  destruct (Words.bit_cases x) as [hx|hx]; destruct (Words.bit_cases y) as [hy|hy];
    change (Words.word 1 x) with (word 1 x) in hx;
    change (Words.word 1 y) with (word 1 y) in hy; rewrite hx, hy; reflexivity.
Qed.
Theorem capture_metadata s i (hs : word 3 (r0_nstate s) = 0)
  (hv : word 1 (nio_5Fin_5Fvalid i) = 1) : metadata (step s i) = requestMetadata i.
Proof.
  unfold metadata; cbn [step r3_naSignReg r4_nqSignReg r7_nctrlReg_5FisW r8_nctrlReg_5FisHi].
  unfold v47, v52, v60, v61; rewrite (accepting s i hs hv).
  change ((word 1 (word 1 (v46 s i)), word 1 (word 1 (v51 s i)),
    word 1 (word 1 (word 1 (nctrl_5FisW i))), word 1 (word 1 (word 1 (nctrl_5FisHi i)))) = requestMetadata i).
  repeat rewrite normalize by lia.
  unfold requestMetadata, v51, v50, v49, v48, v46, v45, v21, v20, signBit.
  change (word 64 0) with 0.
  rewrite <- xor_normal.
  destruct (word 64 (nio_5Fin_5Fbits_5Fsrc_5F1 i) =? 0); repeat rewrite normalize by lia; reflexivity.
Qed.
Lemma captured_metadata s t (h : captured s = captured t) : metadata s = metadata t.
Proof. unfold captured in h; unfold metadata; inversion h; reflexivity. Qed.
End RadixMetadata.
Print Assumptions RadixMetadata.capture_metadata.

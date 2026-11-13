From Coq Require Import ZArith Lia.
From Proofs Require Import Words SignedWords WordBits RadixControl.
From Generated Require Import Radix2Divider.
Import Radix2Divider.CIRCTBits Radix2Divider.nRadix2Divider.
Import RadixControl.RadixControl.
Open Scope Z_scope.
Module RadixFormat.
Definition signExtend32 x := word 64 (SignedWords.signed 32 x).
Lemma extend_wire x :
  word 64 (Z.shiftl (word 32 (repeatWord 32 1 (word 1 (Z.shiftr x 31)))) 32 + word 32 (Z.shiftr x 0)) = signExtend32 x.
Proof.
  unfold signExtend32; rewrite SignedWords.signed_from_bits by lia.
  pose proof (WordBits.WordBits.extract_normal 32 1 31 x ltac:(lia) ltac:(lia) ltac:(lia)) as bit.
  change (word 1 (Z.shiftr (word 32 x) 31) = word 1 (Z.shiftr x 31)) in bit.
  change (word 64 (Z.shiftl (word 32 (repeatWord 32 1 (word 1 (Z.shiftr x 31)))) 32 + word 32 (Z.shiftr x 0)) = word 64 (word 32 x-4294967296*word 1 (Z.shiftr (word 32 x) 31))).
  rewrite bit, Z.shiftr_0_r.
  assert (cases : word 1 (Z.shiftr x 31) = 0 \/ word 1 (Z.shiftr x 31) = 1) by apply Words.bit_cases.
  destruct cases as [h|h]; rewrite h.
  - change (word 64 (0+word 32 x) = word 64 (word 32 x-4294967296*0)); f_equal; ring.
  - change (word 64 (18446744069414584320+word 32 x) = word 64 (word 32 x-4294967296*1)).
    replace (18446744069414584320+word 32 x) with ((word 32 x-4294967296*1)+1*2^64) by ring.
    unfold word at 1 3; apply Z.mod_add; discriminate.
Qed.
Definition correctSign negative x := word 64 (if word 1 negative =? 1 then -word 64 x else word 64 x).
Definition formatResult aNegative qNegative isWord isRemainder q r :=
  let selected := word 64 (if word 1 isRemainder =? 1 then correctSign aNegative r else correctSign qNegative q) in
  if word 1 isWord =? 1 then signExtend32 selected else selected.
Theorem observe_format s i : nio_5Fout_5Fbits_5Fdata (observe s i) =
  formatResult (r3_naSignReg s) (r4_nqSignReg s) (r7_nctrlReg_5FisW s) (r8_nctrlReg_5FisHi s) (v40 s i) (v402 s i).
Proof.
  assert (hq : word 64 (v40 s i) = v40 s i) by (unfold v40; apply normalize; lia).
  assert (hr : word 64 (v402 s i) = v402 s i) by (unfold v402; apply normalize; lia).
  assert (q : v406 s i = correctSign (r4_nqSignReg s) (v40 s i)).
  { unfold v406, v405, v20, correctSign; rewrite hq; change (word 64 0) with 0; rewrite Z.sub_0_l.
    destruct (word 1 (r4_nqSignReg s) =? 1); repeat rewrite normalize by lia; reflexivity. }
  assert (r : v404 s i = correctSign (r3_naSignReg s) (v402 s i)).
  { unfold v404, v403, v20, correctSign; rewrite hr; change (word 64 0) with 0; rewrite Z.sub_0_l.
    destruct (word 1 (r3_naSignReg s) =? 1); repeat rewrite normalize by lia; reflexivity. }
  assert (w : v411 s i = signExtend32 (v407 s i)).
  { unfold v411, v410, v409, v408; apply extend_wire. }
  cbn [observe nio_5Fout_5Fbits_5Fdata]; unfold v412; rewrite w.
  destruct (word 1 (r7_nctrlReg_5FisW s) =? 1) eqn:hw.
  - unfold signExtend32 at 1; rewrite normalize by lia.
    unfold formatResult; rewrite hw; unfold v407; rewrite q, r; reflexivity.
  - unfold formatResult; rewrite hw; unfold v407; rewrite normalize by lia; rewrite q, r; reflexivity.
Qed.
End RadixFormat.
Print Assumptions RadixFormat.observe_format.

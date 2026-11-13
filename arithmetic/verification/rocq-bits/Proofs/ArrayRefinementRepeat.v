From Stdlib Require Import ZArith Zmod.Bits.
From BitsProofs Require Import ArrayRefinementBase BitFacts.
Open Scope Z_scope.
(* The array uses replication only to extend its one-bit sign to 65 bits. *)
Lemma repeat65 (x : bits 1) :
  ReferenceGenerated.ArrayMulDataModule.CIRCTBits.repeatWord 65 1
    (Zmod.unsigned x) mod 2^65 =
  Zmod.unsigned (BitsGenerated.ArrayMulDataModule.CIRCTBits.repeatBits 65 65 x).
Proof.
  destruct (BitFacts.bit_cases x) as [h|h]; rewrite h;
  vm_compute; reflexivity.
Qed.
Print Assumptions repeat65.

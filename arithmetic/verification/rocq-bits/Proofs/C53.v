From Stdlib Require Import ZArith Zmod.Bits.
From BitsGenerated Require Import C53.
From BitsProofs Require Import BitFacts.
Import C53.nC53.
Open Scope Z_scope.
Theorem assertions_hold (s : State) (i : Inputs) : asserts s i.
Proof.
  destruct s; destruct i.
  repeat match goal with
  | x : bits 1 |- _ => destruct (bit_cases x) as [h|h]; subst x
  end;
  vm_compute; reflexivity.
Qed.
Print Assumptions assertions_hold.

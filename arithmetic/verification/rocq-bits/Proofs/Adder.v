From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsGenerated Require Import Adder.
From BitsProofs Require Import BitFacts.
Import Adder.nAdder.
Open Scope Z_scope.

Theorem result_correct s i :
  nio_5Fout (observe s i) =
  if Zmod.eqb (nio_5Fvalid i) Zmod.one
  then Zmod.add (nio_5Fin1 i) (nio_5Fin2 i) else Zmod.zero.
Proof. reflexivity. Qed.

Theorem assertions_hold s i : asserts s i.
Proof.
  destruct (bit_cases (nio_5Fvalid i)) as [valid|valid];
    destruct (bit_cases (nreset i)) as [reset|reset];
    unfold asserts, assertionChecks, v11, v10, v9, v8, v7, v6, v5, v4,
      v3, v2, v1, v0;
    rewrite valid,reset;
    cbn [Zmod.eqb]; repeat rewrite Z.eqb_refl; reflexivity.
Qed.
Print Assumptions result_correct.
Print Assumptions assertions_hold.

From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementBase
  ArrayRefinementChecks000 ArrayRefinementChecks001 ArrayRefinementChecks002 ArrayRefinementChecks003 ArrayRefinementChecks004 ArrayRefinementChecks005 ArrayRefinementChecks006 ArrayRefinementChecks007 ArrayRefinementChecks008 ArrayRefinementChecks009 ArrayRefinementChecks010 ArrayRefinementChecks011 ArrayRefinementChecks012 ArrayRefinementChecks013 ArrayRefinementChecks014 ArrayRefinementChecks015 ArrayRefinementChecks016 ArrayRefinementChecks017 ArrayRefinementChecks018 ArrayRefinementChecks019 ArrayRefinementChecks020 ArrayRefinementChecks021 ArrayRefinementChecks022 ArrayRefinementChecks023 ArrayRefinementChecks024 ArrayRefinementChecks025 ArrayRefinementChecks026 ArrayRefinementChecks027 ArrayRefinementChecks028 ArrayRefinementChecks029 ArrayRefinementChecks030 ArrayRefinementChecks031 ArrayRefinementChecks032 ArrayRefinementChecks033 ArrayRefinementChecks034.
Import ListNotations.
Open Scope Z_scope.
Theorem checks_refine s i : R.assertionChecks (state s) (inputs i) = N.assertionChecks s i.
Proof.
  change ((reference_checks_0 s i ++ reference_checks_1 s i ++ reference_checks_2 s i ++ reference_checks_3 s i ++ reference_checks_4 s i ++ reference_checks_5 s i ++ reference_checks_6 s i ++ reference_checks_7 s i ++ reference_checks_8 s i ++ reference_checks_9 s i ++ reference_checks_10 s i ++ reference_checks_11 s i ++ reference_checks_12 s i ++ reference_checks_13 s i ++ reference_checks_14 s i ++ reference_checks_15 s i ++ reference_checks_16 s i ++ reference_checks_17 s i ++ reference_checks_18 s i ++ reference_checks_19 s i ++ reference_checks_20 s i ++ reference_checks_21 s i ++ reference_checks_22 s i ++ reference_checks_23 s i ++ reference_checks_24 s i ++ reference_checks_25 s i ++ reference_checks_26 s i ++ reference_checks_27 s i ++ reference_checks_28 s i ++ reference_checks_29 s i ++ reference_checks_30 s i ++ reference_checks_31 s i ++ reference_checks_32 s i ++ reference_checks_33 s i ++ reference_checks_34 s i) =
          (native_checks_0 s i ++ native_checks_1 s i ++ native_checks_2 s i ++ native_checks_3 s i ++ native_checks_4 s i ++ native_checks_5 s i ++ native_checks_6 s i ++ native_checks_7 s i ++ native_checks_8 s i ++ native_checks_9 s i ++ native_checks_10 s i ++ native_checks_11 s i ++ native_checks_12 s i ++ native_checks_13 s i ++ native_checks_14 s i ++ native_checks_15 s i ++ native_checks_16 s i ++ native_checks_17 s i ++ native_checks_18 s i ++ native_checks_19 s i ++ native_checks_20 s i ++ native_checks_21 s i ++ native_checks_22 s i ++ native_checks_23 s i ++ native_checks_24 s i ++ native_checks_25 s i ++ native_checks_26 s i ++ native_checks_27 s i ++ native_checks_28 s i ++ native_checks_29 s i ++ native_checks_30 s i ++ native_checks_31 s i ++ native_checks_32 s i ++ native_checks_33 s i ++ native_checks_34 s i)).
  rewrite checks_0.
  rewrite checks_1.
  rewrite checks_2.
  rewrite checks_3.
  rewrite checks_4.
  rewrite checks_5.
  rewrite checks_6.
  rewrite checks_7.
  rewrite checks_8.
  rewrite checks_9.
  rewrite checks_10.
  rewrite checks_11.
  rewrite checks_12.
  rewrite checks_13.
  rewrite checks_14.
  rewrite checks_15.
  rewrite checks_16.
  rewrite checks_17.
  rewrite checks_18.
  rewrite checks_19.
  rewrite checks_20.
  rewrite checks_21.
  rewrite checks_22.
  rewrite checks_23.
  rewrite checks_24.
  rewrite checks_25.
  rewrite checks_26.
  rewrite checks_27.
  rewrite checks_28.
  rewrite checks_29.
  rewrite checks_30.
  rewrite checks_31.
  rewrite checks_32.
  rewrite checks_33.
  rewrite checks_34.
  reflexivity.
Qed.
Theorem asserts_refine s i : N.asserts s i <-> R.asserts (state s) (inputs i).
Proof. unfold N.asserts, R.asserts; rewrite checks_refine; reflexivity. Qed.
Print Assumptions asserts_refine.

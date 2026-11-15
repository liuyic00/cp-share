From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing Muxes MuxShapes LeafWords Controls ReferenceNormalization Commit StateNext DataNext CountNext OutputLink RuntimeRepresentation.
Local Open Scope Z_scope.
Lemma adapted_word_size width bits : size (zext_to width (take width bits)) = width.
Proof. rewrite /zext_to size_zext. apply subnKC. rewrite size_take. apply geq_minl. Qed.
Lemma next_13_size v : size (next_word_13 v) = 3%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_13.
Lemma next_13_clock v clock : next_word_13 (with_clock v clock) = next_word_13 v.
Proof. unfold next_word_13, next_raw_word_13, next_closed_13. rewrite word_1_clock word_402_clock. reflexivity. Qed.
Opaque next_raw_word_13.
Lemma next_18_size v : size (next_word_18 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_18.
Lemma next_18_clock v clock : next_word_18 (with_clock v clock) = next_word_18 v.
Proof. unfold next_word_18, next_raw_word_18, next_closed_18. rewrite word_19_clock. reflexivity. Qed.
Opaque next_raw_word_18.
Lemma next_20_size v : size (next_word_20 v) = 129%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_20.
Lemma next_20_clock v clock : next_word_20 (with_clock v clock) = next_word_20 v.
Proof. unfold next_word_20, next_raw_word_20, next_closed_20. rewrite word_404_clock. reflexivity. Qed.
Opaque next_raw_word_20.
Lemma next_33_size v : size (next_word_33 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_33.
Lemma next_33_clock v clock : next_word_33 (with_clock v clock) = next_word_33 v.
Proof. unfold next_word_33, next_raw_word_33, next_closed_33. rewrite word_34_clock. reflexivity. Qed.
Opaque next_raw_word_33.
Lemma next_38_size v : size (next_word_38 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_38.
Lemma next_38_clock v clock : next_word_38 (with_clock v clock) = next_word_38 v.
Proof. unfold next_word_38, next_raw_word_38, next_closed_38. rewrite word_39_clock. reflexivity. Qed.
Opaque next_raw_word_38.
Lemma next_40_size v : size (next_word_40 v) = 64%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_40.
Lemma next_40_clock v clock : next_word_40 (with_clock v clock) = next_word_40 v.
Proof. unfold next_word_40, next_raw_word_40, next_closed_40. rewrite word_41_clock. reflexivity. Qed.
Opaque next_raw_word_40.
Lemma next_43_size v : size (next_word_43 v) = 65%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_43.
Lemma next_43_clock v clock : next_word_43 (with_clock v clock) = next_word_43 v.
Proof. unfold next_word_43, next_raw_word_43, next_closed_43. rewrite word_44_clock. reflexivity. Qed.
Opaque next_raw_word_43.
Lemma next_45_size v : size (next_word_45 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_45.
Lemma next_45_clock v clock : next_word_45 (with_clock v clock) = next_word_45 v.
Proof. unfold next_word_45, next_raw_word_45, next_closed_45. rewrite word_50_clock. reflexivity. Qed.
Opaque next_raw_word_45.
Lemma next_46_size v : size (next_word_46 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_46.
Lemma next_46_clock v clock : next_word_46 (with_clock v clock) = next_word_46 v.
Proof. unfold next_word_46, next_raw_word_46, next_closed_46. rewrite word_49_clock. reflexivity. Qed.
Opaque next_raw_word_46.
Lemma next_47_size v : size (next_word_47 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_47.
Lemma next_47_clock v clock : next_word_47 (with_clock v clock) = next_word_47 v.
Proof. unfold next_word_47, next_raw_word_47, next_closed_47. rewrite word_48_clock. reflexivity. Qed.
Opaque next_raw_word_47.
Lemma next_51_size v : size (next_word_51 v) = 6%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_51.
Lemma next_51_clock v clock : next_word_51 (with_clock v clock) = next_word_51 v.
Proof. unfold next_word_51, next_raw_word_51, next_closed_51. rewrite word_1_clock word_403_clock. reflexivity. Qed.
Opaque next_raw_word_51.
Lemma next_445_size v : size (next_word_445 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_445.
Lemma next_445_clock v clock : next_word_445 (with_clock v clock) = next_word_445 v.
Proof. unfold next_word_445, next_raw_word_445, next_closed_445. rewrite word_1_clock. reflexivity. Qed.
Opaque next_raw_word_445.
Lemma next_446_size v : size (next_word_446 v) = 3%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_446.
Lemma next_446_clock v clock : next_word_446 (with_clock v clock) = next_word_446 v.
Proof. unfold next_word_446, next_raw_word_446, next_closed_446. rewrite word_13_clock. reflexivity. Qed.
Opaque next_raw_word_446.
Lemma next_447_size v : size (next_word_447 v) = 6%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_447.
Lemma next_447_clock v clock : next_word_447 (with_clock v clock) = next_word_447 v.
Proof. unfold next_word_447, next_raw_word_447, next_closed_447. rewrite word_51_clock. reflexivity. Qed.
Opaque next_raw_word_447.
Lemma next_475_size v : size (next_word_475 v) = 1%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_475.
Lemma next_475_clock v clock : next_word_475 (with_clock v clock) = next_word_475 v.
Proof. unfold next_word_475, next_raw_word_475, next_closed_475. rewrite word_1_clock word_474_clock. reflexivity. Qed.
Opaque next_raw_word_475.
Lemma next_476_size v : size (next_word_476 v) = 64%nat.
Proof. apply adapted_word_size. Qed.
Transparent next_raw_word_476.
Lemma next_476_clock v clock : next_word_476 (with_clock v clock) = next_word_476 v.
Proof. unfold next_word_476, next_raw_word_476, next_closed_476. rewrite word_9_clock. reflexivity. Qed.
Opaque next_raw_word_476.
Transparent next_raw_word_18.
Lemma next_18_raw v : next_raw_word_18 v = word_19 v.
Proof. unfold next_raw_word_18, next_closed_18, next_expr_18, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_18.
Lemma next_18_reference s i ghost : to_Zpos (next_word_18 (encoded_leaves s i ghost)) = Reference.r1_ndivBy0Reg (Reference.step s i).
Proof. unfold next_word_18. rewrite unsigned_adapt next_18_raw control_19_reference reference_24_normalized. reflexivity. Qed.
Transparent next_raw_word_33.
Lemma next_33_raw v : next_raw_word_33 v = word_34 v.
Proof. unfold next_raw_word_33, next_closed_33, next_expr_33, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_33.
Lemma next_33_reference s i ghost : to_Zpos (next_word_33 (encoded_leaves s i ghost)) = Reference.r3_naSignReg (Reference.step s i).
Proof. unfold next_word_33. rewrite unsigned_adapt next_33_raw control_34_reference reference_47_normalized. reflexivity. Qed.
Transparent next_raw_word_38.
Lemma next_38_raw v : next_raw_word_38 v = word_39 v.
Proof. unfold next_raw_word_38, next_closed_38, next_expr_38, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_38.
Lemma next_38_reference s i ghost : to_Zpos (next_word_38 (encoded_leaves s i ghost)) = Reference.r4_nqSignReg (Reference.step s i).
Proof. unfold next_word_38. rewrite unsigned_adapt next_38_raw control_39_reference reference_52_normalized. reflexivity. Qed.
Transparent next_raw_word_40.
Lemma next_40_raw v : next_raw_word_40 v = word_41 v.
Proof. unfold next_raw_word_40, next_closed_40, next_expr_40, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_40.
Lemma next_40_reference s i ghost : to_Zpos (next_word_40 (encoded_leaves s i ghost)) = Reference.r5_nbReg (Reference.step s i).
Proof. unfold next_word_40. rewrite unsigned_adapt next_40_raw control_41_reference reference_55_normalized. reflexivity. Qed.
Transparent next_raw_word_43.
Lemma next_43_raw v : next_raw_word_43 v = word_44 v.
Proof. unfold next_raw_word_43, next_closed_43, next_expr_43, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_43.
Lemma next_43_reference s i ghost : to_Zpos (next_word_43 (encoded_leaves s i ghost)) = Reference.r6_naValx2Reg (Reference.step s i).
Proof. unfold next_word_43. rewrite unsigned_adapt next_43_raw control_44_reference reference_59_normalized. reflexivity. Qed.
Transparent next_raw_word_46.
Lemma next_46_raw v : next_raw_word_46 v = word_49 v.
Proof. unfold next_raw_word_46, next_closed_46, next_expr_46, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_46.
Lemma next_46_reference s i ghost : to_Zpos (next_word_46 (encoded_leaves s i ghost)) = Reference.r7_nctrlReg_5FisW (Reference.step s i).
Proof. unfold next_word_46. rewrite unsigned_adapt next_46_raw control_49_reference reference_60_normalized. reflexivity. Qed.
Transparent next_raw_word_47.
Lemma next_47_raw v : next_raw_word_47 v = word_48 v.
Proof. unfold next_raw_word_47, next_closed_47, next_expr_47, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_47.
Lemma next_47_reference s i ghost : to_Zpos (next_word_47 (encoded_leaves s i ghost)) = Reference.r8_nctrlReg_5FisHi (Reference.step s i).
Proof. unfold next_word_47. rewrite unsigned_adapt next_47_raw control_48_reference reference_61_normalized. reflexivity. Qed.
Transparent next_raw_word_476.
Lemma next_476_raw v : next_raw_word_476 v = word_9 v.
Proof. unfold next_raw_word_476, next_closed_476, next_expr_476, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_476.
Lemma next_476_reference s i ghost : to_Zpos (next_word_476 (encoded_leaves s i ghost)) = Reference.r14_npreviousOutput (Reference.step s i).
Proof. unfold next_word_476. rewrite unsigned_adapt next_476_raw output_9_reference reference_412_normalized. reflexivity. Qed.
Transparent next_raw_word_446.
Lemma next_446_raw v : next_raw_word_446 v = word_13 v.
Proof. unfold next_raw_word_446, next_closed_446, next_expr_446, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_446.
Lemma next_446_reference s i ghost : to_Zpos (next_word_446 (encoded_leaves s i ghost)) = Reference.r11_npreviousState (Reference.step s i).
Proof. unfold next_word_446. rewrite unsigned_adapt next_446_raw leaf_13_integer normalize_nested; [reflexivity|lia]. Qed.
Transparent next_raw_word_447.
Lemma next_447_raw v : next_raw_word_447 v = word_51 v.
Proof. unfold next_raw_word_447, next_closed_447, next_expr_447, word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque next_raw_word_447.
Lemma next_447_reference s i ghost : to_Zpos (next_word_447 (encoded_leaves s i ghost)) = Reference.r12_npreviousCount (Reference.step s i).
Proof. unfold next_word_447. rewrite unsigned_adapt next_447_raw leaf_51_integer normalize_nested; [reflexivity|lia]. Qed.

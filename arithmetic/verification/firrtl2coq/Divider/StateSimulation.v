From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing Muxes MuxShapes LeafWords Controls ReferenceNormalization Commit StateNext DataNext CountNext NextState.
Local Open Scope Z_scope.
Lemma extend_7_6 bits : extend_hvalue_as_type (Gval (Fuint 7) bits) (Gtyp (Fuint 6)) = Some (Gval (Fuint 7) (zext_to 7 (take 7 bits))).
Proof. reflexivity. Qed.
Lemma constant_zero6_type env : eval_type_of_expr (Econst VarOrder.T (Fuint 6) [::false;false;false;false;false;false]) env = Some (Gtyp (Fuint 6)).
Proof. reflexivity. Qed.
Lemma constant_zero1_type env : eval_type_of_expr (Econst VarOrder.T (Fuint 1) [::false]) env = Some (Gtyp (Fuint 1)).
Proof. reflexivity. Qed.
Transparent next_raw_word_51 next_raw_word_445 next_raw_word_475.
Lemma next_51_raw v : next_raw_word_51 v =
 take 6 (if is_zero (word_1 v) then zext_to 7 (take 7 (word_403 v)) else zext_to 7 (take 7 [::false;false;false;false;false;false])).
Proof.
 unfold next_raw_word_51, next_closed_51, next_expr_51, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_1 v)); try rewrite constant_zero6_type; try rewrite constant_zero1_type; try rewrite extend_7_6; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type eval_unop];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type eval_unop]; try change ((0 <= 5 < 7)%nat) with true; try rewrite drop0; reflexivity.
Qed.
Lemma next_445_raw v : next_raw_word_445 v =
 if is_zero (word_1 v) then [::true] else [::false].
Proof.
 unfold next_raw_word_445, next_closed_445, next_expr_445, word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
 destruct (is_zero (word_1 v)); reflexivity.
Qed.
Lemma next_475_raw v : next_raw_word_475 v =
 if is_zero (word_1 v) then zext_to 1 (take 1 (word_474 v)) else [::false].
Proof.
 unfold next_raw_word_475, next_closed_475, next_expr_475, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_1 v)); try rewrite constant_zero6_type; try rewrite constant_zero1_type; try rewrite extend_7_6; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type eval_unop]; try change ((0 <= 5 < 7)%nat) with true; try rewrite drop0; reflexivity.
Qed.
Opaque next_raw_word_51 next_raw_word_445 next_raw_word_475.
Local Opaque Reference.v398 Reference.v401.
Lemma next_51_reference s i ghost : to_Zpos (next_word_51 (encoded_leaves s i ghost)) = Reference.r9_ncnt_5Fvalue (Reference.step s i).
Proof.
 unfold next_word_51. rewrite unsigned_adapt next_51_raw unsigned_take.
 rewrite (is_zero_onebit _ (encoded_word_1_size s i ghost)) leaf_1_integer.
 cbn [Reference.step Reference.r9_ncnt_5Fvalue].
 change (Radix2Divider.CIRCTBits.word 1 (Reference.nreset i)) with (normalize 1 (Reference.nreset i)).
 destruct (Z.eqb (normalize 1 (Reference.nreset i)) 1); cbn [negb].
 - reflexivity.
 - rewrite unsigned_adapt. repeat (rewrite normalize_nested; [|lia]).
   apply count_403_reference.
Qed.
Lemma next_445_reference s i ghost : to_Zpos (next_word_445 (encoded_leaves s i ghost)) = Reference.r10_nhistoryValid (Reference.step s i).
Proof.
 unfold next_word_445. rewrite unsigned_adapt next_445_raw.
 rewrite (is_zero_onebit _ (encoded_word_1_size s i ghost)) leaf_1_integer.
 cbn [Reference.step Reference.r10_nhistoryValid].
 change (Radix2Divider.CIRCTBits.word 1 (Reference.nreset i)) with (normalize 1 (Reference.nreset i)).
 destruct (Z.eqb (normalize 1 (Reference.nreset i)) 1); reflexivity.
Qed.
Lemma next_475_reference s i ghost : to_Zpos (next_word_475 (encoded_leaves s i ghost)) = Reference.r13_nwasStalled (Reference.step s i).
Proof.
 unfold next_word_475. rewrite unsigned_adapt next_475_raw.
 rewrite (is_zero_onebit _ (encoded_word_1_size s i ghost)) leaf_1_integer.
 cbn [Reference.step Reference.r13_nwasStalled].
 change (Radix2Divider.CIRCTBits.word 1 (Reference.nreset i)) with (normalize 1 (Reference.nreset i)).
 destruct (Z.eqb (normalize 1 (Reference.nreset i)) 1); cbn [negb].
 - reflexivity.
 - rewrite unsigned_adapt control_474_reference !reference_401_normalized. reflexivity.
Qed.
Definition next_projected_state v := Reference.mkState
 (to_Zpos (next_word_13 v)) (to_Zpos (next_word_18 v)) (to_Zpos (next_word_20 v))
 (to_Zpos (next_word_33 v)) (to_Zpos (next_word_38 v)) (to_Zpos (next_word_40 v))
 (to_Zpos (next_word_43 v)) (to_Zpos (next_word_46 v)) (to_Zpos (next_word_47 v))
 (to_Zpos (next_word_51 v)) (to_Zpos (next_word_445 v)) (to_Zpos (next_word_446 v))
 (to_Zpos (next_word_447 v)) (to_Zpos (next_word_475 v)) (to_Zpos (next_word_476 v)).
Lemma next_state_simulation s i ghost : next_projected_state (encoded_leaves s i ghost) = Reference.step s i.
Proof.
 unfold next_projected_state.
 rewrite next_state_reference next_18_reference next_data_reference next_33_reference next_38_reference next_40_reference next_43_reference next_46_reference next_47_reference next_51_reference next_445_reference next_446_reference next_447_reference next_475_reference next_476_reference.
 destruct (Reference.step s i). reflexivity.
Qed.
Print Assumptions next_state_simulation.

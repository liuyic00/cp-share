From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing MuxShapes ScalarOps LeafWords ControlStart Commit.
Local Open Scope Z_scope.
Lemma state_402_reference s i ghost :
 to_Zpos (word_402 (encoded_leaves s i ghost)) = Reference.v19 s i.
Proof.
 rewrite mux_integer_402 mux_integer_400 mux_integer_397 mux_integer_395 mux_integer_389 mux_integer_392 mux_integer_391.
 rewrite control_16_reference scalar_integer_52 scalar_integer_375 scalar_integer_377 scalar_integer_388 scalar_integer_390.
 rewrite !leaf_13_integer leaf_7_integer leaf_51_integer.
 unfold Reference.v19, Reference.v18, Reference.v17, Reference.v16, Reference.v15,
 Reference.v14, Reference.v13, Reference.v12, Reference.v11, Reference.v10,
 Reference.v9, Reference.v8, Reference.v7, Reference.v6, Reference.v5,
 Reference.v4, Reference.v3, Reference.v2, Reference.v1, Reference.v0,
 Radix2Divider.CIRCTBits.word.
 have SB := normalize_range 3 (Reference.r0_nstate s).
 have VB := normalize_range 1 (Reference.nio_5Fin_5Fvalid i).
 have RB := normalize_range 1 (Reference.nio_5Fout_5Fready i).
 unfold normalize, modulus in *.
 change (2 ^ Z.of_nat 3) with 8 in *.
 change (2 ^ Z.of_nat 1) with 2 in *.
 change (2 ^ Z.of_nat 6) with 64 in *.
 change (2 ^ 3) with 8.
 change (2 ^ 1) with 2.
 change (2 ^ 6) with 64.
 change (to_Zpos ([::true; true; true; true; true; true])) with 63.
 change (63 mod 64) with 63.
 change (0 <= Reference.r0_nstate s mod 8 < 8) in SB.
 change (0 <= Reference.nio_5Fin_5Fvalid i mod 2 < 2) in VB.
 change (0 <= Reference.nio_5Fout_5Fready i mod 2 < 2) in RB.
 remember (Reference.r0_nstate s mod 8) as state eqn:S.
 remember (Reference.nio_5Fin_5Fvalid i mod 2) as valid eqn:V.
 remember (Reference.nio_5Fout_5Fready i mod 2) as ready eqn:R.
 assert (States : state=0 \/ state=1 \/ state=2 \/ state=3 \/ state=4 \/ state=5 \/ state=6 \/ state=7) by lia.
 assert (Valids : valid=0 \/ valid=1) by lia.
 assert (Readies : ready=0 \/ ready=1) by lia.
 destruct States as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
 destruct Valids as [-> | ->]; destruct Readies as [-> | ->].
 all: destruct (Z.eqb (Reference.r9_ncnt_5Fvalue s mod 64) 63).
 all: vm_compute; reflexivity.
Qed.
Print Assumptions state_402_reference.

Transparent next_raw_word_13.
Lemma next_raw_state_shape v : next_raw_word_13 v =
 if is_zero (word_1 v) then zext_to 3 (take 3 (word_402 v)) else zext_to 3 (take 3 [::false;false;false]).
Proof.
 unfold next_raw_word_13, next_closed_13, next_expr_13, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_1 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_13.
Local Opaque Reference.v19.
Lemma next_state_reference s i ghost :
 to_Zpos (next_word_13 (encoded_leaves s i ghost)) = Reference.r0_nstate (Reference.step s i).
Proof.
 have Normal : normalize 3 (Reference.v19 s i) = Reference.v19 s i.
 { rewrite -(state_402_reference s i ghost). apply unsigned_normalized. apply encoded_word_402_size. }
 unfold next_word_13. rewrite unsigned_adapt next_raw_state_shape.
 rewrite (Muxes.is_zero_onebit _ (encoded_word_1_size s i ghost)) leaf_1_integer.
 cbn [Reference.step Reference.r0_nstate].
 change (Radix2Divider.CIRCTBits.word 1 (Reference.nreset i)) with (normalize 1 (Reference.nreset i)).
 destruct (Z.eqb (normalize 1 (Reference.nreset i)) 1); cbn [negb].
 - reflexivity.
 - rewrite unsigned_adapt state_402_reference Normal Normal. reflexivity.
Qed.
Print Assumptions next_state_reference.

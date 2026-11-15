From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing Muxes.
Local Open Scope Z_scope.
Lemma unsigned_adapt width bits : to_Zpos (zext_to width (take width bits)) = normalize width (to_Zpos bits).
Proof. unfold zext_to. rewrite unsigned_zero_extend unsigned_take. reflexivity. Qed.

Transparent word_19.
Lemma mux_shape_19 v : word_19 v = if is_zero (word_16 v) then zext_to 1 (take 1 (word_18 v)) else zext_to 1 (take 1 (word_17 v)).
Proof. unfold word_19, closed_19, expr_19, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_19.
Lemma mux_integer_19 s i ghost : to_Zpos (word_19 (encoded_leaves s i ghost)) = normalize 1 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_17 (encoded_leaves s i ghost)) else to_Zpos (word_18 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_19 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_27.
Lemma mux_shape_27 v : word_27 v = if is_zero (word_24 v) then zext_to 64 (take 64 (word_4 v)) else zext_to 64 (take 64 (word_26 v)).
Proof. unfold word_27, closed_27, expr_27, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_24 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_27.
Lemma mux_integer_27 s i ghost : to_Zpos (word_27 (encoded_leaves s i ghost)) = normalize 64 (if Z.eqb (to_Zpos (word_24 (encoded_leaves s i ghost))) 1 then to_Zpos (word_26 (encoded_leaves s i ghost)) else to_Zpos (word_4 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_27 (is_zero_onebit _ (encoded_word_24_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_24 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_32.
Lemma mux_shape_32 v : word_32 v = if is_zero (word_29 v) then zext_to 64 (take 64 (word_5 v)) else zext_to 64 (take 64 (word_31 v)).
Proof. unfold word_32, closed_32, expr_32, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_29 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_32.
Lemma mux_integer_32 s i ghost : to_Zpos (word_32 (encoded_leaves s i ghost)) = normalize 64 (if Z.eqb (to_Zpos (word_29 (encoded_leaves s i ghost))) 1 then to_Zpos (word_31 (encoded_leaves s i ghost)) else to_Zpos (word_5 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_32 (is_zero_onebit _ (encoded_word_29_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_29 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_34.
Lemma mux_shape_34 v : word_34 v = if is_zero (word_16 v) then zext_to 1 (take 1 (word_33 v)) else zext_to 1 (take 1 (word_24 v)).
Proof. unfold word_34, closed_34, expr_34, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_34.
Lemma mux_integer_34 s i ghost : to_Zpos (word_34 (encoded_leaves s i ghost)) = normalize 1 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_24 (encoded_leaves s i ghost)) else to_Zpos (word_33 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_34 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_39.
Lemma mux_shape_39 v : word_39 v = if is_zero (word_16 v) then zext_to 1 (take 1 (word_38 v)) else zext_to 1 (take 1 (word_37 v)).
Proof. unfold word_39, closed_39, expr_39, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_39.
Lemma mux_integer_39 s i ghost : to_Zpos (word_39 (encoded_leaves s i ghost)) = normalize 1 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_37 (encoded_leaves s i ghost)) else to_Zpos (word_38 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_39 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_41.
Lemma mux_shape_41 v : word_41 v = if is_zero (word_16 v) then zext_to 64 (take 64 (word_40 v)) else zext_to 64 (take 64 (word_32 v)).
Proof. unfold word_41, closed_41, expr_41, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_41.
Lemma mux_integer_41 s i ghost : to_Zpos (word_41 (encoded_leaves s i ghost)) = normalize 64 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_32 (encoded_leaves s i ghost)) else to_Zpos (word_40 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_41 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_44.
Lemma mux_shape_44 v : word_44 v = if is_zero (word_16 v) then zext_to 65 (take 65 (word_43 v)) else zext_to 65 (take 65 (word_42 v)).
Proof. unfold word_44, closed_44, expr_44, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_44.
Lemma mux_integer_44 s i ghost : to_Zpos (word_44 (encoded_leaves s i ghost)) = normalize 65 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_42 (encoded_leaves s i ghost)) else to_Zpos (word_43 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_44 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_48.
Lemma mux_shape_48 v : word_48 v = if is_zero (word_16 v) then zext_to 1 (take 1 (word_47 v)) else zext_to 1 (take 1 (word_12 v)).
Proof. unfold word_48, closed_48, expr_48, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_48.
Lemma mux_integer_48 s i ghost : to_Zpos (word_48 (encoded_leaves s i ghost)) = normalize 1 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_12 (encoded_leaves s i ghost)) else to_Zpos (word_47 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_48 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_49.
Lemma mux_shape_49 v : word_49 v = if is_zero (word_16 v) then zext_to 1 (take 1 (word_46 v)) else zext_to 1 (take 1 (word_11 v)).
Proof. unfold word_49, closed_49, expr_49, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_49.
Lemma mux_integer_49 s i ghost : to_Zpos (word_49 (encoded_leaves s i ghost)) = normalize 1 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_11 (encoded_leaves s i ghost)) else to_Zpos (word_46 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_49 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_50.
Lemma mux_shape_50 v : word_50 v = if is_zero (word_16 v) then zext_to 1 (take 1 (word_45 v)) else zext_to 1 (take 1 (word_10 v)).
Proof. unfold word_50, closed_50, expr_50, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_50.
Lemma mux_integer_50 s i ghost : to_Zpos (word_50 (encoded_leaves s i ghost)) = normalize 1 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_10 (encoded_leaves s i ghost)) else to_Zpos (word_45 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_50 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_68.
Lemma mux_shape_68 v : word_68 v = if is_zero (word_66 v) then zext_to 2 (take 2 (word_67 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_68, closed_68, expr_68, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_66 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_68.
Lemma mux_integer_68 s i ghost : to_Zpos (word_68 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_66 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_67 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_68 (is_zero_onebit _ (encoded_word_66_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_66 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_69.
Lemma mux_shape_69 v : word_69 v = if is_zero (word_65 v) then zext_to 2 (take 2 (word_68 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_69, closed_69, expr_69, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_65 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_69.
Lemma mux_integer_69 s i ghost : to_Zpos (word_69 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_65 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_68 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_69 (is_zero_onebit _ (encoded_word_65_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_65 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_73.
Lemma mux_shape_73 v : word_73 v = if is_zero (word_71 v) then zext_to 2 (take 2 (word_72 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_73, closed_73, expr_73, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_71 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_73.
Lemma mux_integer_73 s i ghost : to_Zpos (word_73 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_71 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_72 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_73 (is_zero_onebit _ (encoded_word_71_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_71 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_74.
Lemma mux_shape_74 v : word_74 v = if is_zero (word_70 v) then zext_to 2 (take 2 (word_73 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_74, closed_74, expr_74, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_70 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_74.
Lemma mux_integer_74 s i ghost : to_Zpos (word_74 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_70 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_73 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_74 (is_zero_onebit _ (encoded_word_70_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_70 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_75.
Lemma mux_shape_75 v : word_75 v = if is_zero (word_64 v) then zext_to 2 (take 2 (word_74 v)) else zext_to 2 (take 2 (word_69 v)).
Proof. unfold word_75, closed_75, expr_75, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_64 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_75.
Lemma mux_integer_75 s i ghost : to_Zpos (word_75 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_64 (encoded_leaves s i ghost))) 1 then to_Zpos (word_69 (encoded_leaves s i ghost)) else to_Zpos (word_74 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_75 (is_zero_onebit _ (encoded_word_64_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_64 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_83.
Lemma mux_shape_83 v : word_83 v = if is_zero (word_81 v) then zext_to 2 (take 2 (word_82 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_83, closed_83, expr_83, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_81 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_83.
Lemma mux_integer_83 s i ghost : to_Zpos (word_83 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_81 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_82 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_83 (is_zero_onebit _ (encoded_word_81_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_81 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_84.
Lemma mux_shape_84 v : word_84 v = if is_zero (word_80 v) then zext_to 2 (take 2 (word_83 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_84, closed_84, expr_84, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_80 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_84.
Lemma mux_integer_84 s i ghost : to_Zpos (word_84 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_80 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_83 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_84 (is_zero_onebit _ (encoded_word_80_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_80 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_88.
Lemma mux_shape_88 v : word_88 v = if is_zero (word_86 v) then zext_to 2 (take 2 (word_87 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_88, closed_88, expr_88, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_86 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_88.
Lemma mux_integer_88 s i ghost : to_Zpos (word_88 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_86 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_87 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_88 (is_zero_onebit _ (encoded_word_86_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_86 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_89.
Lemma mux_shape_89 v : word_89 v = if is_zero (word_85 v) then zext_to 2 (take 2 (word_88 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_89, closed_89, expr_89, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_85 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_89.
Lemma mux_integer_89 s i ghost : to_Zpos (word_89 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_85 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_88 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_89 (is_zero_onebit _ (encoded_word_85_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_85 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_90.
Lemma mux_shape_90 v : word_90 v = if is_zero (word_79 v) then zext_to 2 (take 2 (word_89 v)) else zext_to 2 (take 2 (word_84 v)).
Proof. unfold word_90, closed_90, expr_90, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_79 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_90.
Lemma mux_integer_90 s i ghost : to_Zpos (word_90 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_79 (encoded_leaves s i ghost))) 1 then to_Zpos (word_84 (encoded_leaves s i ghost)) else to_Zpos (word_89 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_90 (is_zero_onebit _ (encoded_word_79_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_79 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_92.
Lemma mux_shape_92 v : word_92 v = if is_zero (word_61 v) then zext_to 3 (take 3 (word_91 v)) else zext_to 3 (take 3 (word_76 v)).
Proof. unfold word_92, closed_92, expr_92, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_61 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_92.
Lemma mux_integer_92 s i ghost : to_Zpos (word_92 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_61 (encoded_leaves s i ghost))) 1 then to_Zpos (word_76 (encoded_leaves s i ghost)) else to_Zpos (word_91 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_92 (is_zero_onebit _ (encoded_word_61_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_61 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_103.
Lemma mux_shape_103 v : word_103 v = if is_zero (word_101 v) then zext_to 2 (take 2 (word_102 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_103, closed_103, expr_103, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_101 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_103.
Lemma mux_integer_103 s i ghost : to_Zpos (word_103 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_101 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_102 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_103 (is_zero_onebit _ (encoded_word_101_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_101 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_104.
Lemma mux_shape_104 v : word_104 v = if is_zero (word_100 v) then zext_to 2 (take 2 (word_103 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_104, closed_104, expr_104, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_100 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_104.
Lemma mux_integer_104 s i ghost : to_Zpos (word_104 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_100 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_103 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_104 (is_zero_onebit _ (encoded_word_100_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_100 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_108.
Lemma mux_shape_108 v : word_108 v = if is_zero (word_106 v) then zext_to 2 (take 2 (word_107 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_108, closed_108, expr_108, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_106 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_108.
Lemma mux_integer_108 s i ghost : to_Zpos (word_108 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_106 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_107 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_108 (is_zero_onebit _ (encoded_word_106_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_106 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_109.
Lemma mux_shape_109 v : word_109 v = if is_zero (word_105 v) then zext_to 2 (take 2 (word_108 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_109, closed_109, expr_109, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_105 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_109.
Lemma mux_integer_109 s i ghost : to_Zpos (word_109 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_105 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_108 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_109 (is_zero_onebit _ (encoded_word_105_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_105 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_110.
Lemma mux_shape_110 v : word_110 v = if is_zero (word_99 v) then zext_to 2 (take 2 (word_109 v)) else zext_to 2 (take 2 (word_104 v)).
Proof. unfold word_110, closed_110, expr_110, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_99 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_110.
Lemma mux_integer_110 s i ghost : to_Zpos (word_110 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_99 (encoded_leaves s i ghost))) 1 then to_Zpos (word_104 (encoded_leaves s i ghost)) else to_Zpos (word_109 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_110 (is_zero_onebit _ (encoded_word_99_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_99 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_118.
Lemma mux_shape_118 v : word_118 v = if is_zero (word_116 v) then zext_to 2 (take 2 (word_117 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_118, closed_118, expr_118, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_116 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_118.
Lemma mux_integer_118 s i ghost : to_Zpos (word_118 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_116 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_117 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_118 (is_zero_onebit _ (encoded_word_116_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_116 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_119.
Lemma mux_shape_119 v : word_119 v = if is_zero (word_115 v) then zext_to 2 (take 2 (word_118 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_119, closed_119, expr_119, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_115 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_119.
Lemma mux_integer_119 s i ghost : to_Zpos (word_119 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_115 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_118 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_119 (is_zero_onebit _ (encoded_word_115_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_115 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_123.
Lemma mux_shape_123 v : word_123 v = if is_zero (word_121 v) then zext_to 2 (take 2 (word_122 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_123, closed_123, expr_123, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_121 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_123.
Lemma mux_integer_123 s i ghost : to_Zpos (word_123 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_121 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_122 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_123 (is_zero_onebit _ (encoded_word_121_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_121 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_124.
Lemma mux_shape_124 v : word_124 v = if is_zero (word_120 v) then zext_to 2 (take 2 (word_123 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_124, closed_124, expr_124, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_120 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_124.
Lemma mux_integer_124 s i ghost : to_Zpos (word_124 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_120 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_123 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_124 (is_zero_onebit _ (encoded_word_120_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_120 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_125.
Lemma mux_shape_125 v : word_125 v = if is_zero (word_114 v) then zext_to 2 (take 2 (word_124 v)) else zext_to 2 (take 2 (word_119 v)).
Proof. unfold word_125, closed_125, expr_125, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_114 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_125.
Lemma mux_integer_125 s i ghost : to_Zpos (word_125 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_114 (encoded_leaves s i ghost))) 1 then to_Zpos (word_119 (encoded_leaves s i ghost)) else to_Zpos (word_124 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_125 (is_zero_onebit _ (encoded_word_114_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_114 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_127.
Lemma mux_shape_127 v : word_127 v = if is_zero (word_96 v) then zext_to 3 (take 3 (word_126 v)) else zext_to 3 (take 3 (word_111 v)).
Proof. unfold word_127, closed_127, expr_127, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_96 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_127.
Lemma mux_integer_127 s i ghost : to_Zpos (word_127 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_96 (encoded_leaves s i ghost))) 1 then to_Zpos (word_111 (encoded_leaves s i ghost)) else to_Zpos (word_126 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_127 (is_zero_onebit _ (encoded_word_96_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_96 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_129.
Lemma mux_shape_129 v : word_129 v = if is_zero (word_58 v) then zext_to 4 (take 4 (word_128 v)) else zext_to 4 (take 4 (word_93 v)).
Proof. unfold word_129, closed_129, expr_129, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_58 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_129.
Lemma mux_integer_129 s i ghost : to_Zpos (word_129 (encoded_leaves s i ghost)) = normalize 4 (if Z.eqb (to_Zpos (word_58 (encoded_leaves s i ghost))) 1 then to_Zpos (word_93 (encoded_leaves s i ghost)) else to_Zpos (word_128 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_129 (is_zero_onebit _ (encoded_word_58_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_58 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_143.
Lemma mux_shape_143 v : word_143 v = if is_zero (word_141 v) then zext_to 2 (take 2 (word_142 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_143, closed_143, expr_143, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_141 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_143.
Lemma mux_integer_143 s i ghost : to_Zpos (word_143 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_141 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_142 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_143 (is_zero_onebit _ (encoded_word_141_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_141 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_144.
Lemma mux_shape_144 v : word_144 v = if is_zero (word_140 v) then zext_to 2 (take 2 (word_143 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_144, closed_144, expr_144, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_140 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_144.
Lemma mux_integer_144 s i ghost : to_Zpos (word_144 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_140 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_143 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_144 (is_zero_onebit _ (encoded_word_140_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_140 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_148.
Lemma mux_shape_148 v : word_148 v = if is_zero (word_146 v) then zext_to 2 (take 2 (word_147 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_148, closed_148, expr_148, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_146 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_148.
Lemma mux_integer_148 s i ghost : to_Zpos (word_148 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_146 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_147 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_148 (is_zero_onebit _ (encoded_word_146_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_146 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_149.
Lemma mux_shape_149 v : word_149 v = if is_zero (word_145 v) then zext_to 2 (take 2 (word_148 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_149, closed_149, expr_149, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_145 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_149.
Lemma mux_integer_149 s i ghost : to_Zpos (word_149 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_145 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_148 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_149 (is_zero_onebit _ (encoded_word_145_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_145 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_150.
Lemma mux_shape_150 v : word_150 v = if is_zero (word_139 v) then zext_to 2 (take 2 (word_149 v)) else zext_to 2 (take 2 (word_144 v)).
Proof. unfold word_150, closed_150, expr_150, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_139 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_150.
Lemma mux_integer_150 s i ghost : to_Zpos (word_150 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_139 (encoded_leaves s i ghost))) 1 then to_Zpos (word_144 (encoded_leaves s i ghost)) else to_Zpos (word_149 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_150 (is_zero_onebit _ (encoded_word_139_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_139 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_158.
Lemma mux_shape_158 v : word_158 v = if is_zero (word_156 v) then zext_to 2 (take 2 (word_157 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_158, closed_158, expr_158, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_156 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_158.
Lemma mux_integer_158 s i ghost : to_Zpos (word_158 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_156 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_157 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_158 (is_zero_onebit _ (encoded_word_156_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_156 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_159.
Lemma mux_shape_159 v : word_159 v = if is_zero (word_155 v) then zext_to 2 (take 2 (word_158 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_159, closed_159, expr_159, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_155 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_159.
Lemma mux_integer_159 s i ghost : to_Zpos (word_159 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_155 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_158 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_159 (is_zero_onebit _ (encoded_word_155_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_155 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_163.
Lemma mux_shape_163 v : word_163 v = if is_zero (word_161 v) then zext_to 2 (take 2 (word_162 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_163, closed_163, expr_163, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_161 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_163.
Lemma mux_integer_163 s i ghost : to_Zpos (word_163 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_161 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_162 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_163 (is_zero_onebit _ (encoded_word_161_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_161 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_164.
Lemma mux_shape_164 v : word_164 v = if is_zero (word_160 v) then zext_to 2 (take 2 (word_163 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_164, closed_164, expr_164, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_160 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_164.
Lemma mux_integer_164 s i ghost : to_Zpos (word_164 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_160 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_163 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_164 (is_zero_onebit _ (encoded_word_160_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_160 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_165.
Lemma mux_shape_165 v : word_165 v = if is_zero (word_154 v) then zext_to 2 (take 2 (word_164 v)) else zext_to 2 (take 2 (word_159 v)).
Proof. unfold word_165, closed_165, expr_165, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_154 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_165.
Lemma mux_integer_165 s i ghost : to_Zpos (word_165 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_154 (encoded_leaves s i ghost))) 1 then to_Zpos (word_159 (encoded_leaves s i ghost)) else to_Zpos (word_164 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_165 (is_zero_onebit _ (encoded_word_154_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_154 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_167.
Lemma mux_shape_167 v : word_167 v = if is_zero (word_136 v) then zext_to 3 (take 3 (word_166 v)) else zext_to 3 (take 3 (word_151 v)).
Proof. unfold word_167, closed_167, expr_167, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_136 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_167.
Lemma mux_integer_167 s i ghost : to_Zpos (word_167 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_136 (encoded_leaves s i ghost))) 1 then to_Zpos (word_151 (encoded_leaves s i ghost)) else to_Zpos (word_166 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_167 (is_zero_onebit _ (encoded_word_136_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_136 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_178.
Lemma mux_shape_178 v : word_178 v = if is_zero (word_176 v) then zext_to 2 (take 2 (word_177 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_178, closed_178, expr_178, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_176 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_178.
Lemma mux_integer_178 s i ghost : to_Zpos (word_178 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_176 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_177 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_178 (is_zero_onebit _ (encoded_word_176_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_176 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_179.
Lemma mux_shape_179 v : word_179 v = if is_zero (word_175 v) then zext_to 2 (take 2 (word_178 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_179, closed_179, expr_179, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_175 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_179.
Lemma mux_integer_179 s i ghost : to_Zpos (word_179 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_175 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_178 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_179 (is_zero_onebit _ (encoded_word_175_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_175 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_183.
Lemma mux_shape_183 v : word_183 v = if is_zero (word_181 v) then zext_to 2 (take 2 (word_182 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_183, closed_183, expr_183, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_181 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_183.
Lemma mux_integer_183 s i ghost : to_Zpos (word_183 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_181 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_182 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_183 (is_zero_onebit _ (encoded_word_181_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_181 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_184.
Lemma mux_shape_184 v : word_184 v = if is_zero (word_180 v) then zext_to 2 (take 2 (word_183 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_184, closed_184, expr_184, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_180 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_184.
Lemma mux_integer_184 s i ghost : to_Zpos (word_184 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_180 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_183 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_184 (is_zero_onebit _ (encoded_word_180_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_180 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_185.
Lemma mux_shape_185 v : word_185 v = if is_zero (word_174 v) then zext_to 2 (take 2 (word_184 v)) else zext_to 2 (take 2 (word_179 v)).
Proof. unfold word_185, closed_185, expr_185, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_174 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_185.
Lemma mux_integer_185 s i ghost : to_Zpos (word_185 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_174 (encoded_leaves s i ghost))) 1 then to_Zpos (word_179 (encoded_leaves s i ghost)) else to_Zpos (word_184 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_185 (is_zero_onebit _ (encoded_word_174_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_174 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_193.
Lemma mux_shape_193 v : word_193 v = if is_zero (word_191 v) then zext_to 2 (take 2 (word_192 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_193, closed_193, expr_193, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_191 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_193.
Lemma mux_integer_193 s i ghost : to_Zpos (word_193 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_191 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_192 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_193 (is_zero_onebit _ (encoded_word_191_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_191 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_194.
Lemma mux_shape_194 v : word_194 v = if is_zero (word_190 v) then zext_to 2 (take 2 (word_193 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_194, closed_194, expr_194, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_190 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_194.
Lemma mux_integer_194 s i ghost : to_Zpos (word_194 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_190 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_193 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_194 (is_zero_onebit _ (encoded_word_190_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_190 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_198.
Lemma mux_shape_198 v : word_198 v = if is_zero (word_196 v) then zext_to 2 (take 2 (word_197 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_198, closed_198, expr_198, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_196 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_198.
Lemma mux_integer_198 s i ghost : to_Zpos (word_198 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_196 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_197 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_198 (is_zero_onebit _ (encoded_word_196_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_196 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_199.
Lemma mux_shape_199 v : word_199 v = if is_zero (word_195 v) then zext_to 2 (take 2 (word_198 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_199, closed_199, expr_199, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_195 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_199.
Lemma mux_integer_199 s i ghost : to_Zpos (word_199 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_195 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_198 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_199 (is_zero_onebit _ (encoded_word_195_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_195 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_200.
Lemma mux_shape_200 v : word_200 v = if is_zero (word_189 v) then zext_to 2 (take 2 (word_199 v)) else zext_to 2 (take 2 (word_194 v)).
Proof. unfold word_200, closed_200, expr_200, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_189 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_200.
Lemma mux_integer_200 s i ghost : to_Zpos (word_200 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_189 (encoded_leaves s i ghost))) 1 then to_Zpos (word_194 (encoded_leaves s i ghost)) else to_Zpos (word_199 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_200 (is_zero_onebit _ (encoded_word_189_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_189 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_202.
Lemma mux_shape_202 v : word_202 v = if is_zero (word_171 v) then zext_to 3 (take 3 (word_201 v)) else zext_to 3 (take 3 (word_186 v)).
Proof. unfold word_202, closed_202, expr_202, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_171 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_202.
Lemma mux_integer_202 s i ghost : to_Zpos (word_202 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_171 (encoded_leaves s i ghost))) 1 then to_Zpos (word_186 (encoded_leaves s i ghost)) else to_Zpos (word_201 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_202 (is_zero_onebit _ (encoded_word_171_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_171 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_204.
Lemma mux_shape_204 v : word_204 v = if is_zero (word_133 v) then zext_to 4 (take 4 (word_203 v)) else zext_to 4 (take 4 (word_168 v)).
Proof. unfold word_204, closed_204, expr_204, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_133 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_204.
Lemma mux_integer_204 s i ghost : to_Zpos (word_204 (encoded_leaves s i ghost)) = normalize 4 (if Z.eqb (to_Zpos (word_133 (encoded_leaves s i ghost))) 1 then to_Zpos (word_168 (encoded_leaves s i ghost)) else to_Zpos (word_203 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_204 (is_zero_onebit _ (encoded_word_133_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_133 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_206.
Lemma mux_shape_206 v : word_206 v = if is_zero (word_55 v) then zext_to 5 (take 5 (word_205 v)) else zext_to 5 (take 5 (word_130 v)).
Proof. unfold word_206, closed_206, expr_206, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_55 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_206.
Lemma mux_integer_206 s i ghost : to_Zpos (word_206 (encoded_leaves s i ghost)) = normalize 5 (if Z.eqb (to_Zpos (word_55 (encoded_leaves s i ghost))) 1 then to_Zpos (word_130 (encoded_leaves s i ghost)) else to_Zpos (word_205 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_206 (is_zero_onebit _ (encoded_word_55_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_55 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_228.
Lemma mux_shape_228 v : word_228 v = if is_zero (word_226 v) then zext_to 2 (take 2 (word_227 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_228, closed_228, expr_228, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_226 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_228.
Lemma mux_integer_228 s i ghost : to_Zpos (word_228 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_226 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_227 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_228 (is_zero_onebit _ (encoded_word_226_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_226 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_229.
Lemma mux_shape_229 v : word_229 v = if is_zero (word_225 v) then zext_to 2 (take 2 (word_228 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_229, closed_229, expr_229, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_225 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_229.
Lemma mux_integer_229 s i ghost : to_Zpos (word_229 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_225 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_228 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_229 (is_zero_onebit _ (encoded_word_225_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_225 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_233.
Lemma mux_shape_233 v : word_233 v = if is_zero (word_231 v) then zext_to 2 (take 2 (word_232 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_233, closed_233, expr_233, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_231 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_233.
Lemma mux_integer_233 s i ghost : to_Zpos (word_233 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_231 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_232 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_233 (is_zero_onebit _ (encoded_word_231_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_231 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_234.
Lemma mux_shape_234 v : word_234 v = if is_zero (word_230 v) then zext_to 2 (take 2 (word_233 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_234, closed_234, expr_234, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_230 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_234.
Lemma mux_integer_234 s i ghost : to_Zpos (word_234 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_230 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_233 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_234 (is_zero_onebit _ (encoded_word_230_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_230 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_235.
Lemma mux_shape_235 v : word_235 v = if is_zero (word_224 v) then zext_to 2 (take 2 (word_234 v)) else zext_to 2 (take 2 (word_229 v)).
Proof. unfold word_235, closed_235, expr_235, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_224 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_235.
Lemma mux_integer_235 s i ghost : to_Zpos (word_235 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_224 (encoded_leaves s i ghost))) 1 then to_Zpos (word_229 (encoded_leaves s i ghost)) else to_Zpos (word_234 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_235 (is_zero_onebit _ (encoded_word_224_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_224 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_243.
Lemma mux_shape_243 v : word_243 v = if is_zero (word_241 v) then zext_to 2 (take 2 (word_242 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_243, closed_243, expr_243, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_241 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_243.
Lemma mux_integer_243 s i ghost : to_Zpos (word_243 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_241 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_242 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_243 (is_zero_onebit _ (encoded_word_241_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_241 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_244.
Lemma mux_shape_244 v : word_244 v = if is_zero (word_240 v) then zext_to 2 (take 2 (word_243 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_244, closed_244, expr_244, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_240 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_244.
Lemma mux_integer_244 s i ghost : to_Zpos (word_244 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_240 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_243 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_244 (is_zero_onebit _ (encoded_word_240_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_240 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_248.
Lemma mux_shape_248 v : word_248 v = if is_zero (word_246 v) then zext_to 2 (take 2 (word_247 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_248, closed_248, expr_248, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_246 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_248.
Lemma mux_integer_248 s i ghost : to_Zpos (word_248 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_246 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_247 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_248 (is_zero_onebit _ (encoded_word_246_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_246 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_249.
Lemma mux_shape_249 v : word_249 v = if is_zero (word_245 v) then zext_to 2 (take 2 (word_248 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_249, closed_249, expr_249, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_245 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_249.
Lemma mux_integer_249 s i ghost : to_Zpos (word_249 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_245 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_248 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_249 (is_zero_onebit _ (encoded_word_245_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_245 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_250.
Lemma mux_shape_250 v : word_250 v = if is_zero (word_239 v) then zext_to 2 (take 2 (word_249 v)) else zext_to 2 (take 2 (word_244 v)).
Proof. unfold word_250, closed_250, expr_250, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_239 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_250.
Lemma mux_integer_250 s i ghost : to_Zpos (word_250 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_239 (encoded_leaves s i ghost))) 1 then to_Zpos (word_244 (encoded_leaves s i ghost)) else to_Zpos (word_249 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_250 (is_zero_onebit _ (encoded_word_239_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_239 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_252.
Lemma mux_shape_252 v : word_252 v = if is_zero (word_221 v) then zext_to 3 (take 3 (word_251 v)) else zext_to 3 (take 3 (word_236 v)).
Proof. unfold word_252, closed_252, expr_252, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_221 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_252.
Lemma mux_integer_252 s i ghost : to_Zpos (word_252 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_221 (encoded_leaves s i ghost))) 1 then to_Zpos (word_236 (encoded_leaves s i ghost)) else to_Zpos (word_251 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_252 (is_zero_onebit _ (encoded_word_221_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_221 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_263.
Lemma mux_shape_263 v : word_263 v = if is_zero (word_261 v) then zext_to 2 (take 2 (word_262 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_263, closed_263, expr_263, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_261 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_263.
Lemma mux_integer_263 s i ghost : to_Zpos (word_263 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_261 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_262 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_263 (is_zero_onebit _ (encoded_word_261_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_261 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_264.
Lemma mux_shape_264 v : word_264 v = if is_zero (word_260 v) then zext_to 2 (take 2 (word_263 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_264, closed_264, expr_264, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_260 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_264.
Lemma mux_integer_264 s i ghost : to_Zpos (word_264 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_260 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_263 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_264 (is_zero_onebit _ (encoded_word_260_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_260 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_268.
Lemma mux_shape_268 v : word_268 v = if is_zero (word_266 v) then zext_to 2 (take 2 (word_267 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_268, closed_268, expr_268, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_266 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_268.
Lemma mux_integer_268 s i ghost : to_Zpos (word_268 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_266 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_267 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_268 (is_zero_onebit _ (encoded_word_266_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_266 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_269.
Lemma mux_shape_269 v : word_269 v = if is_zero (word_265 v) then zext_to 2 (take 2 (word_268 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_269, closed_269, expr_269, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_265 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_269.
Lemma mux_integer_269 s i ghost : to_Zpos (word_269 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_265 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_268 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_269 (is_zero_onebit _ (encoded_word_265_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_265 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_270.
Lemma mux_shape_270 v : word_270 v = if is_zero (word_259 v) then zext_to 2 (take 2 (word_269 v)) else zext_to 2 (take 2 (word_264 v)).
Proof. unfold word_270, closed_270, expr_270, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_259 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_270.
Lemma mux_integer_270 s i ghost : to_Zpos (word_270 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_259 (encoded_leaves s i ghost))) 1 then to_Zpos (word_264 (encoded_leaves s i ghost)) else to_Zpos (word_269 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_270 (is_zero_onebit _ (encoded_word_259_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_259 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_278.
Lemma mux_shape_278 v : word_278 v = if is_zero (word_276 v) then zext_to 2 (take 2 (word_277 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_278, closed_278, expr_278, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_276 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_278.
Lemma mux_integer_278 s i ghost : to_Zpos (word_278 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_276 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_277 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_278 (is_zero_onebit _ (encoded_word_276_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_276 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_279.
Lemma mux_shape_279 v : word_279 v = if is_zero (word_275 v) then zext_to 2 (take 2 (word_278 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_279, closed_279, expr_279, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_275 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_279.
Lemma mux_integer_279 s i ghost : to_Zpos (word_279 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_275 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_278 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_279 (is_zero_onebit _ (encoded_word_275_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_275 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_283.
Lemma mux_shape_283 v : word_283 v = if is_zero (word_281 v) then zext_to 2 (take 2 (word_282 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_283, closed_283, expr_283, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_281 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_283.
Lemma mux_integer_283 s i ghost : to_Zpos (word_283 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_281 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_282 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_283 (is_zero_onebit _ (encoded_word_281_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_281 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_284.
Lemma mux_shape_284 v : word_284 v = if is_zero (word_280 v) then zext_to 2 (take 2 (word_283 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_284, closed_284, expr_284, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_280 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_284.
Lemma mux_integer_284 s i ghost : to_Zpos (word_284 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_280 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_283 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_284 (is_zero_onebit _ (encoded_word_280_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_280 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_285.
Lemma mux_shape_285 v : word_285 v = if is_zero (word_274 v) then zext_to 2 (take 2 (word_284 v)) else zext_to 2 (take 2 (word_279 v)).
Proof. unfold word_285, closed_285, expr_285, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_274 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_285.
Lemma mux_integer_285 s i ghost : to_Zpos (word_285 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_274 (encoded_leaves s i ghost))) 1 then to_Zpos (word_279 (encoded_leaves s i ghost)) else to_Zpos (word_284 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_285 (is_zero_onebit _ (encoded_word_274_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_274 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_287.
Lemma mux_shape_287 v : word_287 v = if is_zero (word_256 v) then zext_to 3 (take 3 (word_286 v)) else zext_to 3 (take 3 (word_271 v)).
Proof. unfold word_287, closed_287, expr_287, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_256 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_287.
Lemma mux_integer_287 s i ghost : to_Zpos (word_287 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_256 (encoded_leaves s i ghost))) 1 then to_Zpos (word_271 (encoded_leaves s i ghost)) else to_Zpos (word_286 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_287 (is_zero_onebit _ (encoded_word_256_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_256 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_289.
Lemma mux_shape_289 v : word_289 v = if is_zero (word_218 v) then zext_to 4 (take 4 (word_288 v)) else zext_to 4 (take 4 (word_253 v)).
Proof. unfold word_289, closed_289, expr_289, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_218 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_289.
Lemma mux_integer_289 s i ghost : to_Zpos (word_289 (encoded_leaves s i ghost)) = normalize 4 (if Z.eqb (to_Zpos (word_218 (encoded_leaves s i ghost))) 1 then to_Zpos (word_253 (encoded_leaves s i ghost)) else to_Zpos (word_288 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_289 (is_zero_onebit _ (encoded_word_218_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_218 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_303.
Lemma mux_shape_303 v : word_303 v = if is_zero (word_301 v) then zext_to 2 (take 2 (word_302 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_303, closed_303, expr_303, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_301 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_303.
Lemma mux_integer_303 s i ghost : to_Zpos (word_303 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_301 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_302 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_303 (is_zero_onebit _ (encoded_word_301_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_301 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_304.
Lemma mux_shape_304 v : word_304 v = if is_zero (word_300 v) then zext_to 2 (take 2 (word_303 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_304, closed_304, expr_304, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_300 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_304.
Lemma mux_integer_304 s i ghost : to_Zpos (word_304 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_300 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_303 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_304 (is_zero_onebit _ (encoded_word_300_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_300 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_308.
Lemma mux_shape_308 v : word_308 v = if is_zero (word_306 v) then zext_to 2 (take 2 (word_307 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_308, closed_308, expr_308, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_306 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_308.
Lemma mux_integer_308 s i ghost : to_Zpos (word_308 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_306 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_307 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_308 (is_zero_onebit _ (encoded_word_306_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_306 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_309.
Lemma mux_shape_309 v : word_309 v = if is_zero (word_305 v) then zext_to 2 (take 2 (word_308 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_309, closed_309, expr_309, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_305 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_309.
Lemma mux_integer_309 s i ghost : to_Zpos (word_309 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_305 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_308 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_309 (is_zero_onebit _ (encoded_word_305_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_305 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_310.
Lemma mux_shape_310 v : word_310 v = if is_zero (word_299 v) then zext_to 2 (take 2 (word_309 v)) else zext_to 2 (take 2 (word_304 v)).
Proof. unfold word_310, closed_310, expr_310, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_299 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_310.
Lemma mux_integer_310 s i ghost : to_Zpos (word_310 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_299 (encoded_leaves s i ghost))) 1 then to_Zpos (word_304 (encoded_leaves s i ghost)) else to_Zpos (word_309 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_310 (is_zero_onebit _ (encoded_word_299_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_299 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_318.
Lemma mux_shape_318 v : word_318 v = if is_zero (word_316 v) then zext_to 2 (take 2 (word_317 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_318, closed_318, expr_318, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_316 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_318.
Lemma mux_integer_318 s i ghost : to_Zpos (word_318 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_316 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_317 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_318 (is_zero_onebit _ (encoded_word_316_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_316 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_319.
Lemma mux_shape_319 v : word_319 v = if is_zero (word_315 v) then zext_to 2 (take 2 (word_318 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_319, closed_319, expr_319, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_315 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_319.
Lemma mux_integer_319 s i ghost : to_Zpos (word_319 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_315 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_318 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_319 (is_zero_onebit _ (encoded_word_315_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_315 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_323.
Lemma mux_shape_323 v : word_323 v = if is_zero (word_321 v) then zext_to 2 (take 2 (word_322 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_323, closed_323, expr_323, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_321 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_323.
Lemma mux_integer_323 s i ghost : to_Zpos (word_323 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_321 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_322 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_323 (is_zero_onebit _ (encoded_word_321_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_321 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_324.
Lemma mux_shape_324 v : word_324 v = if is_zero (word_320 v) then zext_to 2 (take 2 (word_323 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_324, closed_324, expr_324, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_320 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_324.
Lemma mux_integer_324 s i ghost : to_Zpos (word_324 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_320 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_323 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_324 (is_zero_onebit _ (encoded_word_320_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_320 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_325.
Lemma mux_shape_325 v : word_325 v = if is_zero (word_314 v) then zext_to 2 (take 2 (word_324 v)) else zext_to 2 (take 2 (word_319 v)).
Proof. unfold word_325, closed_325, expr_325, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_314 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_325.
Lemma mux_integer_325 s i ghost : to_Zpos (word_325 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_314 (encoded_leaves s i ghost))) 1 then to_Zpos (word_319 (encoded_leaves s i ghost)) else to_Zpos (word_324 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_325 (is_zero_onebit _ (encoded_word_314_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_314 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_327.
Lemma mux_shape_327 v : word_327 v = if is_zero (word_296 v) then zext_to 3 (take 3 (word_326 v)) else zext_to 3 (take 3 (word_311 v)).
Proof. unfold word_327, closed_327, expr_327, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_296 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_327.
Lemma mux_integer_327 s i ghost : to_Zpos (word_327 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_296 (encoded_leaves s i ghost))) 1 then to_Zpos (word_311 (encoded_leaves s i ghost)) else to_Zpos (word_326 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_327 (is_zero_onebit _ (encoded_word_296_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_296 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_338.
Lemma mux_shape_338 v : word_338 v = if is_zero (word_336 v) then zext_to 2 (take 2 (word_337 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_338, closed_338, expr_338, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_336 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_338.
Lemma mux_integer_338 s i ghost : to_Zpos (word_338 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_336 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_337 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_338 (is_zero_onebit _ (encoded_word_336_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_336 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_339.
Lemma mux_shape_339 v : word_339 v = if is_zero (word_335 v) then zext_to 2 (take 2 (word_338 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_339, closed_339, expr_339, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_335 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_339.
Lemma mux_integer_339 s i ghost : to_Zpos (word_339 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_335 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_338 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_339 (is_zero_onebit _ (encoded_word_335_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_335 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_343.
Lemma mux_shape_343 v : word_343 v = if is_zero (word_341 v) then zext_to 2 (take 2 (word_342 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_343, closed_343, expr_343, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_341 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_343.
Lemma mux_integer_343 s i ghost : to_Zpos (word_343 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_341 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_342 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_343 (is_zero_onebit _ (encoded_word_341_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_341 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_344.
Lemma mux_shape_344 v : word_344 v = if is_zero (word_340 v) then zext_to 2 (take 2 (word_343 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_344, closed_344, expr_344, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_340 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_344.
Lemma mux_integer_344 s i ghost : to_Zpos (word_344 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_340 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_343 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_344 (is_zero_onebit _ (encoded_word_340_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_340 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_345.
Lemma mux_shape_345 v : word_345 v = if is_zero (word_334 v) then zext_to 2 (take 2 (word_344 v)) else zext_to 2 (take 2 (word_339 v)).
Proof. unfold word_345, closed_345, expr_345, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_334 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_345.
Lemma mux_integer_345 s i ghost : to_Zpos (word_345 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_334 (encoded_leaves s i ghost))) 1 then to_Zpos (word_339 (encoded_leaves s i ghost)) else to_Zpos (word_344 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_345 (is_zero_onebit _ (encoded_word_334_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_334 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_353.
Lemma mux_shape_353 v : word_353 v = if is_zero (word_351 v) then zext_to 2 (take 2 (word_352 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_353, closed_353, expr_353, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_351 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_353.
Lemma mux_integer_353 s i ghost : to_Zpos (word_353 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_351 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_352 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_353 (is_zero_onebit _ (encoded_word_351_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_351 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_354.
Lemma mux_shape_354 v : word_354 v = if is_zero (word_350 v) then zext_to 2 (take 2 (word_353 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_354, closed_354, expr_354, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_350 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_354.
Lemma mux_integer_354 s i ghost : to_Zpos (word_354 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_350 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_353 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_354 (is_zero_onebit _ (encoded_word_350_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_350 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_358.
Lemma mux_shape_358 v : word_358 v = if is_zero (word_356 v) then zext_to 2 (take 2 (word_357 v)) else zext_to 2 (take 2 ([::false; true])).
Proof. unfold word_358, closed_358, expr_358, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_356 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_358.
Lemma mux_integer_358 s i ghost : to_Zpos (word_358 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_356 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true]) else to_Zpos (word_357 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_358 (is_zero_onebit _ (encoded_word_356_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_356 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_359.
Lemma mux_shape_359 v : word_359 v = if is_zero (word_355 v) then zext_to 2 (take 2 (word_358 v)) else zext_to 2 (take 2 ([::true; true])).
Proof. unfold word_359, closed_359, expr_359, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_355 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_359.
Lemma mux_integer_359 s i ghost : to_Zpos (word_359 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_355 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true]) else to_Zpos (word_358 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_359 (is_zero_onebit _ (encoded_word_355_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_355 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_360.
Lemma mux_shape_360 v : word_360 v = if is_zero (word_349 v) then zext_to 2 (take 2 (word_359 v)) else zext_to 2 (take 2 (word_354 v)).
Proof. unfold word_360, closed_360, expr_360, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_349 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_360.
Lemma mux_integer_360 s i ghost : to_Zpos (word_360 (encoded_leaves s i ghost)) = normalize 2 (if Z.eqb (to_Zpos (word_349 (encoded_leaves s i ghost))) 1 then to_Zpos (word_354 (encoded_leaves s i ghost)) else to_Zpos (word_359 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_360 (is_zero_onebit _ (encoded_word_349_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_349 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_362.
Lemma mux_shape_362 v : word_362 v = if is_zero (word_331 v) then zext_to 3 (take 3 (word_361 v)) else zext_to 3 (take 3 (word_346 v)).
Proof. unfold word_362, closed_362, expr_362, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_331 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_362.
Lemma mux_integer_362 s i ghost : to_Zpos (word_362 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_331 (encoded_leaves s i ghost))) 1 then to_Zpos (word_346 (encoded_leaves s i ghost)) else to_Zpos (word_361 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_362 (is_zero_onebit _ (encoded_word_331_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_331 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_364.
Lemma mux_shape_364 v : word_364 v = if is_zero (word_293 v) then zext_to 4 (take 4 (word_363 v)) else zext_to 4 (take 4 (word_328 v)).
Proof. unfold word_364, closed_364, expr_364, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_293 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_364.
Lemma mux_integer_364 s i ghost : to_Zpos (word_364 (encoded_leaves s i ghost)) = normalize 4 (if Z.eqb (to_Zpos (word_293 (encoded_leaves s i ghost))) 1 then to_Zpos (word_328 (encoded_leaves s i ghost)) else to_Zpos (word_363 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_364 (is_zero_onebit _ (encoded_word_293_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_293 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_366.
Lemma mux_shape_366 v : word_366 v = if is_zero (word_215 v) then zext_to 5 (take 5 (word_365 v)) else zext_to 5 (take 5 (word_290 v)).
Proof. unfold word_366, closed_366, expr_366, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_215 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_366.
Lemma mux_integer_366 s i ghost : to_Zpos (word_366 (encoded_leaves s i ghost)) = normalize 5 (if Z.eqb (to_Zpos (word_215 (encoded_leaves s i ghost))) 1 then to_Zpos (word_290 (encoded_leaves s i ghost)) else to_Zpos (word_365 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_366 (is_zero_onebit _ (encoded_word_215_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_215 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_368.
Lemma mux_shape_368 v : word_368 v = if is_zero (word_212 v) then zext_to 6 (take 6 (word_367 v)) else zext_to 6 (take 6 ([::false])).
Proof. unfold word_368, closed_368, expr_368, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_212 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_368.
Lemma mux_integer_368 s i ghost : to_Zpos (word_368 (encoded_leaves s i ghost)) = normalize 6 (if Z.eqb (to_Zpos (word_212 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false]) else to_Zpos (word_367 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_368 (is_zero_onebit _ (encoded_word_212_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_212 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_373.
Lemma mux_shape_373 v : word_373 v = if is_zero (word_372 v) then zext_to 7 (take 7 (word_371 v)) else zext_to 7 (take 7 ([::true; true; true; true; true; true])).
Proof. unfold word_373, closed_373, expr_373, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_372 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_373.
Lemma mux_integer_373 s i ghost : to_Zpos (word_373 (encoded_leaves s i ghost)) = normalize 7 (if Z.eqb (to_Zpos (word_372 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true; true; true; true; true]) else to_Zpos (word_371 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_373 (is_zero_onebit _ (encoded_word_372_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_372 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_374.
Lemma mux_shape_374 v : word_374 v = if is_zero (word_18 v) then zext_to 7 (take 7 (word_373 v)) else zext_to 7 (take 7 ([::false])).
Proof. unfold word_374, closed_374, expr_374, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_18 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_374.
Lemma mux_integer_374 s i ghost : to_Zpos (word_374 (encoded_leaves s i ghost)) = normalize 7 (if Z.eqb (to_Zpos (word_18 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false]) else to_Zpos (word_373 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_374 (is_zero_onebit _ (encoded_word_18_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_18 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_381.
Lemma mux_shape_381 v : word_381 v = if is_zero (word_378 v) then zext_to 65 (take 65 (word_21 v)) else zext_to 65 (take 65 (word_380 v)).
Proof. unfold word_381, closed_381, expr_381, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_378 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_381.
Lemma mux_integer_381 s i ghost : to_Zpos (word_381 (encoded_leaves s i ghost)) = normalize 65 (if Z.eqb (to_Zpos (word_378 (encoded_leaves s i ghost))) 1 then to_Zpos (word_380 (encoded_leaves s i ghost)) else to_Zpos (word_21 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_381 (is_zero_onebit _ (encoded_word_378_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_378 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_389.
Lemma mux_shape_389 v : word_389 v = if is_zero (word_388 v) then zext_to 3 (take 3 (word_13 v)) else zext_to 3 (take 3 ([::false; false; true])).
Proof. unfold word_389, closed_389, expr_389, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_388 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_389.
Lemma mux_integer_389 s i ghost : to_Zpos (word_389 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_388 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; false; true]) else to_Zpos (word_13 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_389 (is_zero_onebit _ (encoded_word_388_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_388 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_391.
Lemma mux_shape_391 v : word_391 v = if is_zero (word_7 v) then zext_to 3 (take 3 (word_13 v)) else zext_to 3 (take 3 ([::false; false; false])).
Proof. unfold word_391, closed_391, expr_391, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_7 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_391.
Lemma mux_integer_391 s i ghost : to_Zpos (word_391 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_7 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; false; false]) else to_Zpos (word_13 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_391 (is_zero_onebit _ (encoded_word_7_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_7 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_392.
Lemma mux_shape_392 v : word_392 v = if is_zero (word_390 v) then zext_to 3 (take 3 (word_13 v)) else zext_to 3 (take 3 (word_391 v)).
Proof. unfold word_392, closed_392, expr_392, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_390 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_392.
Lemma mux_integer_392 s i ghost : to_Zpos (word_392 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_390 (encoded_leaves s i ghost))) 1 then to_Zpos (word_391 (encoded_leaves s i ghost)) else to_Zpos (word_13 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_392 (is_zero_onebit _ (encoded_word_390_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_390 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_393.
Lemma mux_shape_393 v : word_393 v = if is_zero (word_377 v) then zext_to 129 (take 129 (word_20 v)) else zext_to 129 (take 129 (word_384 v)).
Proof. unfold word_393, closed_393, expr_393, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_377 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_393.
Lemma mux_integer_393 s i ghost : to_Zpos (word_393 (encoded_leaves s i ghost)) = normalize 129 (if Z.eqb (to_Zpos (word_377 (encoded_leaves s i ghost))) 1 then to_Zpos (word_384 (encoded_leaves s i ghost)) else to_Zpos (word_20 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_393 (is_zero_onebit _ (encoded_word_377_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_377 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_394.
Lemma mux_shape_394 v : word_394 v = if is_zero (word_377 v) then zext_to 6 (take 6 (word_51 v)) else zext_to 6 (take 6 (word_387 v)).
Proof. unfold word_394, closed_394, expr_394, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_377 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_394.
Lemma mux_integer_394 s i ghost : to_Zpos (word_394 (encoded_leaves s i ghost)) = normalize 6 (if Z.eqb (to_Zpos (word_377 (encoded_leaves s i ghost))) 1 then to_Zpos (word_387 (encoded_leaves s i ghost)) else to_Zpos (word_51 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_394 (is_zero_onebit _ (encoded_word_377_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_377 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_395.
Lemma mux_shape_395 v : word_395 v = if is_zero (word_377 v) then zext_to 3 (take 3 (word_392 v)) else zext_to 3 (take 3 (word_389 v)).
Proof. unfold word_395, closed_395, expr_395, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_377 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_395.
Lemma mux_integer_395 s i ghost : to_Zpos (word_395 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_377 (encoded_leaves s i ghost))) 1 then to_Zpos (word_389 (encoded_leaves s i ghost)) else to_Zpos (word_392 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_395 (is_zero_onebit _ (encoded_word_377_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_377 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_396.
Lemma mux_shape_396 v : word_396 v = if is_zero (word_375 v) then zext_to 129 (take 129 (word_393 v)) else zext_to 129 (take 129 (word_376 v)).
Proof. unfold word_396, closed_396, expr_396, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_375 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_396.
Lemma mux_integer_396 s i ghost : to_Zpos (word_396 (encoded_leaves s i ghost)) = normalize 129 (if Z.eqb (to_Zpos (word_375 (encoded_leaves s i ghost))) 1 then to_Zpos (word_376 (encoded_leaves s i ghost)) else to_Zpos (word_393 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_396 (is_zero_onebit _ (encoded_word_375_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_375 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_397.
Lemma mux_shape_397 v : word_397 v = if is_zero (word_375 v) then zext_to 3 (take 3 (word_395 v)) else zext_to 3 (take 3 ([::true; true; false])).
Proof. unfold word_397, closed_397, expr_397, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_375 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_397.
Lemma mux_integer_397 s i ghost : to_Zpos (word_397 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_375 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true; false]) else to_Zpos (word_395 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_397 (is_zero_onebit _ (encoded_word_375_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_375 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_398.
Lemma mux_shape_398 v : word_398 v = if is_zero (word_375 v) then zext_to 6 (take 6 (word_394 v)) else zext_to 6 (take 6 (word_51 v)).
Proof. unfold word_398, closed_398, expr_398, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_375 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_398.
Lemma mux_integer_398 s i ghost : to_Zpos (word_398 (encoded_leaves s i ghost)) = normalize 6 (if Z.eqb (to_Zpos (word_375 (encoded_leaves s i ghost))) 1 then to_Zpos (word_51 (encoded_leaves s i ghost)) else to_Zpos (word_394 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_398 (is_zero_onebit _ (encoded_word_375_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_375 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_399.
Lemma mux_shape_399 v : word_399 v = if is_zero (word_52 v) then zext_to 7 (take 7 (word_398 v)) else zext_to 7 (take 7 (word_374 v)).
Proof. unfold word_399, closed_399, expr_399, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_52 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_399.
Lemma mux_integer_399 s i ghost : to_Zpos (word_399 (encoded_leaves s i ghost)) = normalize 7 (if Z.eqb (to_Zpos (word_52 (encoded_leaves s i ghost))) 1 then to_Zpos (word_374 (encoded_leaves s i ghost)) else to_Zpos (word_398 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_399 (is_zero_onebit _ (encoded_word_52_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_52 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_400.
Lemma mux_shape_400 v : word_400 v = if is_zero (word_52 v) then zext_to 3 (take 3 (word_397 v)) else zext_to 3 (take 3 ([::false; true; false])).
Proof. unfold word_400, closed_400, expr_400, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_52 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_400.
Lemma mux_integer_400 s i ghost : to_Zpos (word_400 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_52 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; true; false]) else to_Zpos (word_397 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_400 (is_zero_onebit _ (encoded_word_52_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_52 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_401.
Lemma mux_shape_401 v : word_401 v = if is_zero (word_52 v) then zext_to 129 (take 129 (word_396 v)) else zext_to 129 (take 129 (word_20 v)).
Proof. unfold word_401, closed_401, expr_401, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_52 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_401.
Lemma mux_integer_401 s i ghost : to_Zpos (word_401 (encoded_leaves s i ghost)) = normalize 129 (if Z.eqb (to_Zpos (word_52 (encoded_leaves s i ghost))) 1 then to_Zpos (word_20 (encoded_leaves s i ghost)) else to_Zpos (word_396 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_401 (is_zero_onebit _ (encoded_word_52_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_52 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_402.
Lemma mux_shape_402 v : word_402 v = if is_zero (word_16 v) then zext_to 3 (take 3 (word_400 v)) else zext_to 3 (take 3 ([::true; false; false])).
Proof. unfold word_402, closed_402, expr_402, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_402.
Lemma mux_integer_402 s i ghost : to_Zpos (word_402 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; false; false]) else to_Zpos (word_400 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_402 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_403.
Lemma mux_shape_403 v : word_403 v = if is_zero (word_16 v) then zext_to 7 (take 7 (word_399 v)) else zext_to 7 (take 7 (word_51 v)).
Proof. unfold word_403, closed_403, expr_403, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_403.
Lemma mux_integer_403 s i ghost : to_Zpos (word_403 (encoded_leaves s i ghost)) = normalize 7 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_51 (encoded_leaves s i ghost)) else to_Zpos (word_399 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_403 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_404.
Lemma mux_shape_404 v : word_404 v = if is_zero (word_16 v) then zext_to 129 (take 129 (word_401 v)) else zext_to 129 (take 129 (word_20 v)).
Proof. unfold word_404, closed_404, expr_404, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_16 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_404.
Lemma mux_integer_404 s i ghost : to_Zpos (word_404 (encoded_leaves s i ghost)) = normalize 129 (if Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1 then to_Zpos (word_20 (encoded_leaves s i ghost)) else to_Zpos (word_401 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_404 (is_zero_onebit _ (encoded_word_16_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_16 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_408.
Lemma mux_shape_408 v : word_408 v = if is_zero (word_38 v) then zext_to 64 (take 64 (word_22 v)) else zext_to 64 (take 64 (word_407 v)).
Proof. unfold word_408, closed_408, expr_408, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_38 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_408.
Lemma mux_integer_408 s i ghost : to_Zpos (word_408 (encoded_leaves s i ghost)) = normalize 64 (if Z.eqb (to_Zpos (word_38 (encoded_leaves s i ghost))) 1 then to_Zpos (word_407 (encoded_leaves s i ghost)) else to_Zpos (word_22 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_408 (is_zero_onebit _ (encoded_word_38_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_38 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_411.
Lemma mux_shape_411 v : word_411 v = if is_zero (word_33 v) then zext_to 64 (take 64 (word_405 v)) else zext_to 64 (take 64 (word_410 v)).
Proof. unfold word_411, closed_411, expr_411, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_33 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_411.
Lemma mux_integer_411 s i ghost : to_Zpos (word_411 (encoded_leaves s i ghost)) = normalize 64 (if Z.eqb (to_Zpos (word_33 (encoded_leaves s i ghost))) 1 then to_Zpos (word_410 (encoded_leaves s i ghost)) else to_Zpos (word_405 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_411 (is_zero_onebit _ (encoded_word_33_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_33 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_412.
Lemma mux_shape_412 v : word_412 v = if is_zero (word_47 v) then zext_to 64 (take 64 (word_408 v)) else zext_to 64 (take 64 (word_411 v)).
Proof. unfold word_412, closed_412, expr_412, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_47 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_412.
Lemma mux_integer_412 s i ghost : to_Zpos (word_412 (encoded_leaves s i ghost)) = normalize 64 (if Z.eqb (to_Zpos (word_47 (encoded_leaves s i ghost))) 1 then to_Zpos (word_411 (encoded_leaves s i ghost)) else to_Zpos (word_408 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_412 (is_zero_onebit _ (encoded_word_47_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_47 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_416.
Lemma mux_shape_416 v : word_416 v = if is_zero (word_415 v) then zext_to 32 (take 32 ([::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])) else zext_to 32 (take 32 ([::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])).
Proof. unfold word_416, closed_416, expr_416, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_415 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_416.
Lemma mux_integer_416 s i ghost : to_Zpos (word_416 (encoded_leaves s i ghost)) = normalize 32 (if Z.eqb (to_Zpos (word_415 (encoded_leaves s i ghost))) 1 then to_Zpos ([::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) else to_Zpos ([::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Proof. rewrite mux_shape_416 (is_zero_onebit _ (encoded_word_415_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_415 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_418.
Lemma mux_shape_418 v : word_418 v = if is_zero (word_46 v) then zext_to 64 (take 64 (word_412 v)) else zext_to 64 (take 64 (word_417 v)).
Proof. unfold word_418, closed_418, expr_418, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_46 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_418.
Lemma mux_integer_418 s i ghost : to_Zpos (word_418 (encoded_leaves s i ghost)) = normalize 64 (if Z.eqb (to_Zpos (word_46 (encoded_leaves s i ghost))) 1 then to_Zpos (word_417 (encoded_leaves s i ghost)) else to_Zpos (word_412 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_418 (is_zero_onebit _ (encoded_word_46_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_46 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_460.
Lemma mux_shape_460 v : word_460 v = if is_zero (word_459 v) then zext_to 3 (take 3 ([::true; true; false])) else zext_to 3 (take 3 ([::false; false; true])).
Proof. unfold word_460, closed_460, expr_460, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_459 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_460.
Lemma mux_integer_460 s i ghost : to_Zpos (word_460 (encoded_leaves s i ghost)) = normalize 3 (if Z.eqb (to_Zpos (word_459 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false; false; true]) else to_Zpos ([::true; true; false])).
Proof. rewrite mux_shape_460 (is_zero_onebit _ (encoded_word_459_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_459 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Transparent word_468.
Lemma mux_shape_468 v : word_468 v = if is_zero (word_465 v) then zext_to 6 (take 6 (word_467 v)) else zext_to 6 (take 6 ([::false])).
Proof. unfold word_468, closed_468, expr_468, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 destruct (is_zero (word_465 v)); cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_468.
Lemma mux_integer_468 s i ghost : to_Zpos (word_468 (encoded_leaves s i ghost)) = normalize 6 (if Z.eqb (to_Zpos (word_465 (encoded_leaves s i ghost))) 1 then to_Zpos ([::false]) else to_Zpos (word_467 (encoded_leaves s i ghost))).
Proof. rewrite mux_shape_468 (is_zero_onebit _ (encoded_word_465_size s i ghost)).
 destruct (Z.eqb (to_Zpos (word_465 (encoded_leaves s i ghost))) 1); cbn [negb]; apply unsigned_adapt. Qed.
Print Assumptions mux_integer_418.

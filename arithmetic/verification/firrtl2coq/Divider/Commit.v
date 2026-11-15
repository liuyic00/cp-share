From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames ConnectionFacts RegisterCommitFacts
 RegisterWriteFacts ScalarEvaluation ScalarExtensionality.
From Divider Require Import Model Stable Frames SingleModule NodeProgress.
Local Open Scope N_scope.
Lemma divider_resets_inert old : registers_inert
 (fun expr => eval_hfexpr_with_memory empty_memory_map expr old old) generated_module_0_stmts_0.
Proof. cbn [registers_inert generated_module_0_stmts_0]. repeat split; intro proposed; reflexivity. Qed.
Definition next_expr_13 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 402))).
Definition next_closed_13 v : VM.t hvalue := (VM.add 402 (Gval (Fuint 3) (word_402 v)) (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue))).
Definition next_raw_word_13 v := word_of_eval (eval_hfexpr next_expr_13 (next_closed_13 v) (next_closed_13 v)).
Definition next_word_13 v := zext_to 3 (take 3 (next_raw_word_13 v)).
Lemma next_closed_13_value v : eval_hfexpr next_expr_13 (next_closed_13 v) (next_closed_13 v) = Some (Gval (Fuint 3) (next_raw_word_13 v)).
Proof. unfold next_raw_word_13, next_closed_13, next_expr_13, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_13.
Lemma next_expr_13_value v : eval_hfexpr next_expr_13 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (next_raw_word_13 v)).
Proof. change (eval_hfexpr next_expr_13 (next_closed_13 v) (next_closed_13 v) = Some (Gval (Fuint 3) (next_raw_word_13 v))). apply next_closed_13_value. Qed.
Lemma register_write_13 : register_write_certificate 13 (@Sfcnct VarOrder.T (@Eid VarOrder.T 13) next_expr_13) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_13 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 13 after = Some (Gval (Fuint 3) (next_word_13 v)).
Proof.
 have old_found : VM.find 13 old = Some (Gval (Fuint 3) (word_13 v)).
 { rewrite (agree 13); [exact (target_13_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_13 old old = Some (Gval (Fuint 3) (next_raw_word_13 v)).
 { rewrite (scalar_eval_empty_memory next_expr_13 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_13 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_13_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_13 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_13|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply unidirectional_eid_target with (expr:=next_expr_13) (value:=Gval (Fuint 3) (next_raw_word_13 v)) (ground:=Fuint 3) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old) (set_regs:=true).
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - reflexivity.
 - eapply one_statement_nonref; [reflexivity|exact step].
Qed.
Definition next_expr_18 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 19)).
Definition next_closed_18 v : VM.t hvalue := (VM.add 19 (Gval (Fuint 1) (word_19 v)) (VM.empty hvalue)).
Definition next_raw_word_18 v := word_of_eval (eval_hfexpr next_expr_18 (next_closed_18 v) (next_closed_18 v)).
Definition next_word_18 v := zext_to 1 (take 1 (next_raw_word_18 v)).
Lemma next_closed_18_value v : eval_hfexpr next_expr_18 (next_closed_18 v) (next_closed_18 v) = Some (Gval (Fuint 1) (next_raw_word_18 v)).
Proof. unfold next_raw_word_18, next_closed_18, next_expr_18, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_18.
Lemma next_expr_18_value v : eval_hfexpr next_expr_18 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_18 v)).
Proof. change (eval_hfexpr next_expr_18 (next_closed_18 v) (next_closed_18 v) = Some (Gval (Fuint 1) (next_raw_word_18 v))). apply next_closed_18_value. Qed.
Lemma register_write_18 : register_write_certificate 18 (@Sfcnct VarOrder.T (@Eid VarOrder.T 18) next_expr_18) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_18 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 18 after = Some (Gval (Fuint 1) (next_word_18 v)).
Proof.
 have old_found : VM.find 18 old = Some (Gval (Fuint 1) (word_18 v)).
 { rewrite (agree 18); [exact (target_18_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_18 old old = Some (Gval (Fuint 1) (next_raw_word_18 v)).
 { rewrite (scalar_eval_empty_memory next_expr_18 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_18 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_18_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_18 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_18|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_18 v)) (source:=19) (target:=18) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_20 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 404)).
Definition next_closed_20 v : VM.t hvalue := (VM.add 404 (Gval (Fuint 129) (word_404 v)) (VM.empty hvalue)).
Definition next_raw_word_20 v := word_of_eval (eval_hfexpr next_expr_20 (next_closed_20 v) (next_closed_20 v)).
Definition next_word_20 v := zext_to 129 (take 129 (next_raw_word_20 v)).
Lemma next_closed_20_value v : eval_hfexpr next_expr_20 (next_closed_20 v) (next_closed_20 v) = Some (Gval (Fuint 129) (next_raw_word_20 v)).
Proof. unfold next_raw_word_20, next_closed_20, next_expr_20, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_20.
Lemma next_expr_20_value v : eval_hfexpr next_expr_20 (stable_env v) (stable_env v) = Some (Gval (Fuint 129) (next_raw_word_20 v)).
Proof. change (eval_hfexpr next_expr_20 (next_closed_20 v) (next_closed_20 v) = Some (Gval (Fuint 129) (next_raw_word_20 v))). apply next_closed_20_value. Qed.
Lemma register_write_20 : register_write_certificate 20 (@Sfcnct VarOrder.T (@Eid VarOrder.T 20) next_expr_20) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_20 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 20 after = Some (Gval (Fuint 129) (next_word_20 v)).
Proof.
 have old_found : VM.find 20 old = Some (Gval (Fuint 129) (word_20 v)).
 { rewrite (agree 20); [exact (target_20_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_20 old old = Some (Gval (Fuint 129) (next_raw_word_20 v)).
 { rewrite (scalar_eval_empty_memory next_expr_20 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_20 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_20_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_20 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_20|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 129) (next_raw_word_20 v)) (source:=404) (target:=20) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_33 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 34)).
Definition next_closed_33 v : VM.t hvalue := (VM.add 34 (Gval (Fuint 1) (word_34 v)) (VM.empty hvalue)).
Definition next_raw_word_33 v := word_of_eval (eval_hfexpr next_expr_33 (next_closed_33 v) (next_closed_33 v)).
Definition next_word_33 v := zext_to 1 (take 1 (next_raw_word_33 v)).
Lemma next_closed_33_value v : eval_hfexpr next_expr_33 (next_closed_33 v) (next_closed_33 v) = Some (Gval (Fuint 1) (next_raw_word_33 v)).
Proof. unfold next_raw_word_33, next_closed_33, next_expr_33, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_33.
Lemma next_expr_33_value v : eval_hfexpr next_expr_33 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_33 v)).
Proof. change (eval_hfexpr next_expr_33 (next_closed_33 v) (next_closed_33 v) = Some (Gval (Fuint 1) (next_raw_word_33 v))). apply next_closed_33_value. Qed.
Lemma register_write_33 : register_write_certificate 33 (@Sfcnct VarOrder.T (@Eid VarOrder.T 33) next_expr_33) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_33 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 33 after = Some (Gval (Fuint 1) (next_word_33 v)).
Proof.
 have old_found : VM.find 33 old = Some (Gval (Fuint 1) (word_33 v)).
 { rewrite (agree 33); [exact (target_33_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_33 old old = Some (Gval (Fuint 1) (next_raw_word_33 v)).
 { rewrite (scalar_eval_empty_memory next_expr_33 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_33 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_33_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_33 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_33|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_33 v)) (source:=34) (target:=33) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_38 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 39)).
Definition next_closed_38 v : VM.t hvalue := (VM.add 39 (Gval (Fuint 1) (word_39 v)) (VM.empty hvalue)).
Definition next_raw_word_38 v := word_of_eval (eval_hfexpr next_expr_38 (next_closed_38 v) (next_closed_38 v)).
Definition next_word_38 v := zext_to 1 (take 1 (next_raw_word_38 v)).
Lemma next_closed_38_value v : eval_hfexpr next_expr_38 (next_closed_38 v) (next_closed_38 v) = Some (Gval (Fuint 1) (next_raw_word_38 v)).
Proof. unfold next_raw_word_38, next_closed_38, next_expr_38, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_38.
Lemma next_expr_38_value v : eval_hfexpr next_expr_38 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_38 v)).
Proof. change (eval_hfexpr next_expr_38 (next_closed_38 v) (next_closed_38 v) = Some (Gval (Fuint 1) (next_raw_word_38 v))). apply next_closed_38_value. Qed.
Lemma register_write_38 : register_write_certificate 38 (@Sfcnct VarOrder.T (@Eid VarOrder.T 38) next_expr_38) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_38 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 38 after = Some (Gval (Fuint 1) (next_word_38 v)).
Proof.
 have old_found : VM.find 38 old = Some (Gval (Fuint 1) (word_38 v)).
 { rewrite (agree 38); [exact (target_38_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_38 old old = Some (Gval (Fuint 1) (next_raw_word_38 v)).
 { rewrite (scalar_eval_empty_memory next_expr_38 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_38 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_38_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_38 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_38|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_38 v)) (source:=39) (target:=38) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_40 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 41)).
Definition next_closed_40 v : VM.t hvalue := (VM.add 41 (Gval (Fuint 64) (word_41 v)) (VM.empty hvalue)).
Definition next_raw_word_40 v := word_of_eval (eval_hfexpr next_expr_40 (next_closed_40 v) (next_closed_40 v)).
Definition next_word_40 v := zext_to 64 (take 64 (next_raw_word_40 v)).
Lemma next_closed_40_value v : eval_hfexpr next_expr_40 (next_closed_40 v) (next_closed_40 v) = Some (Gval (Fuint 64) (next_raw_word_40 v)).
Proof. unfold next_raw_word_40, next_closed_40, next_expr_40, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_40.
Lemma next_expr_40_value v : eval_hfexpr next_expr_40 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (next_raw_word_40 v)).
Proof. change (eval_hfexpr next_expr_40 (next_closed_40 v) (next_closed_40 v) = Some (Gval (Fuint 64) (next_raw_word_40 v))). apply next_closed_40_value. Qed.
Lemma register_write_40 : register_write_certificate 40 (@Sfcnct VarOrder.T (@Eid VarOrder.T 40) next_expr_40) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_40 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 40 after = Some (Gval (Fuint 64) (next_word_40 v)).
Proof.
 have old_found : VM.find 40 old = Some (Gval (Fuint 64) (word_40 v)).
 { rewrite (agree 40); [exact (target_40_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_40 old old = Some (Gval (Fuint 64) (next_raw_word_40 v)).
 { rewrite (scalar_eval_empty_memory next_expr_40 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_40 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_40_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_40 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_40|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 64) (next_raw_word_40 v)) (source:=41) (target:=40) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_43 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 44)).
Definition next_closed_43 v : VM.t hvalue := (VM.add 44 (Gval (Fuint 65) (word_44 v)) (VM.empty hvalue)).
Definition next_raw_word_43 v := word_of_eval (eval_hfexpr next_expr_43 (next_closed_43 v) (next_closed_43 v)).
Definition next_word_43 v := zext_to 65 (take 65 (next_raw_word_43 v)).
Lemma next_closed_43_value v : eval_hfexpr next_expr_43 (next_closed_43 v) (next_closed_43 v) = Some (Gval (Fuint 65) (next_raw_word_43 v)).
Proof. unfold next_raw_word_43, next_closed_43, next_expr_43, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_43.
Lemma next_expr_43_value v : eval_hfexpr next_expr_43 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (next_raw_word_43 v)).
Proof. change (eval_hfexpr next_expr_43 (next_closed_43 v) (next_closed_43 v) = Some (Gval (Fuint 65) (next_raw_word_43 v))). apply next_closed_43_value. Qed.
Lemma register_write_43 : register_write_certificate 43 (@Sfcnct VarOrder.T (@Eid VarOrder.T 43) next_expr_43) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_43 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 43 after = Some (Gval (Fuint 65) (next_word_43 v)).
Proof.
 have old_found : VM.find 43 old = Some (Gval (Fuint 65) (word_43 v)).
 { rewrite (agree 43); [exact (target_43_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_43 old old = Some (Gval (Fuint 65) (next_raw_word_43 v)).
 { rewrite (scalar_eval_empty_memory next_expr_43 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_43 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_43_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_43 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_43|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 65) (next_raw_word_43 v)) (source:=44) (target:=43) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_45 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 50)).
Definition next_closed_45 v : VM.t hvalue := (VM.add 50 (Gval (Fuint 1) (word_50 v)) (VM.empty hvalue)).
Definition next_raw_word_45 v := word_of_eval (eval_hfexpr next_expr_45 (next_closed_45 v) (next_closed_45 v)).
Definition next_word_45 v := zext_to 1 (take 1 (next_raw_word_45 v)).
Lemma next_closed_45_value v : eval_hfexpr next_expr_45 (next_closed_45 v) (next_closed_45 v) = Some (Gval (Fuint 1) (next_raw_word_45 v)).
Proof. unfold next_raw_word_45, next_closed_45, next_expr_45, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_45.
Lemma next_expr_45_value v : eval_hfexpr next_expr_45 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_45 v)).
Proof. change (eval_hfexpr next_expr_45 (next_closed_45 v) (next_closed_45 v) = Some (Gval (Fuint 1) (next_raw_word_45 v))). apply next_closed_45_value. Qed.
Lemma register_write_45 : register_write_certificate 45 (@Sfcnct VarOrder.T (@Eid VarOrder.T 45) next_expr_45) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_45 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 45 after = Some (Gval (Fuint 1) (next_word_45 v)).
Proof.
 have old_found : VM.find 45 old = Some (Gval (Fuint 1) (word_45 v)).
 { rewrite (agree 45); [exact (target_45_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_45 old old = Some (Gval (Fuint 1) (next_raw_word_45 v)).
 { rewrite (scalar_eval_empty_memory next_expr_45 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_45 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_45_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_45 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_45|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_45 v)) (source:=50) (target:=45) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_46 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 49)).
Definition next_closed_46 v : VM.t hvalue := (VM.add 49 (Gval (Fuint 1) (word_49 v)) (VM.empty hvalue)).
Definition next_raw_word_46 v := word_of_eval (eval_hfexpr next_expr_46 (next_closed_46 v) (next_closed_46 v)).
Definition next_word_46 v := zext_to 1 (take 1 (next_raw_word_46 v)).
Lemma next_closed_46_value v : eval_hfexpr next_expr_46 (next_closed_46 v) (next_closed_46 v) = Some (Gval (Fuint 1) (next_raw_word_46 v)).
Proof. unfold next_raw_word_46, next_closed_46, next_expr_46, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_46.
Lemma next_expr_46_value v : eval_hfexpr next_expr_46 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_46 v)).
Proof. change (eval_hfexpr next_expr_46 (next_closed_46 v) (next_closed_46 v) = Some (Gval (Fuint 1) (next_raw_word_46 v))). apply next_closed_46_value. Qed.
Lemma register_write_46 : register_write_certificate 46 (@Sfcnct VarOrder.T (@Eid VarOrder.T 46) next_expr_46) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_46 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 46 after = Some (Gval (Fuint 1) (next_word_46 v)).
Proof.
 have old_found : VM.find 46 old = Some (Gval (Fuint 1) (word_46 v)).
 { rewrite (agree 46); [exact (target_46_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_46 old old = Some (Gval (Fuint 1) (next_raw_word_46 v)).
 { rewrite (scalar_eval_empty_memory next_expr_46 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_46 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_46_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_46 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_46|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_46 v)) (source:=49) (target:=46) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_47 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 48)).
Definition next_closed_47 v : VM.t hvalue := (VM.add 48 (Gval (Fuint 1) (word_48 v)) (VM.empty hvalue)).
Definition next_raw_word_47 v := word_of_eval (eval_hfexpr next_expr_47 (next_closed_47 v) (next_closed_47 v)).
Definition next_word_47 v := zext_to 1 (take 1 (next_raw_word_47 v)).
Lemma next_closed_47_value v : eval_hfexpr next_expr_47 (next_closed_47 v) (next_closed_47 v) = Some (Gval (Fuint 1) (next_raw_word_47 v)).
Proof. unfold next_raw_word_47, next_closed_47, next_expr_47, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_47.
Lemma next_expr_47_value v : eval_hfexpr next_expr_47 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_47 v)).
Proof. change (eval_hfexpr next_expr_47 (next_closed_47 v) (next_closed_47 v) = Some (Gval (Fuint 1) (next_raw_word_47 v))). apply next_closed_47_value. Qed.
Lemma register_write_47 : register_write_certificate 47 (@Sfcnct VarOrder.T (@Eid VarOrder.T 47) next_expr_47) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_47 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 47 after = Some (Gval (Fuint 1) (next_word_47 v)).
Proof.
 have old_found : VM.find 47 old = Some (Gval (Fuint 1) (word_47 v)).
 { rewrite (agree 47); [exact (target_47_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_47 old old = Some (Gval (Fuint 1) (next_raw_word_47 v)).
 { rewrite (scalar_eval_empty_memory next_expr_47 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_47 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_47_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_47 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_47|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_47 v)) (source:=48) (target:=47) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_51 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 5 0) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 403)))).
Definition next_closed_51 v : VM.t hvalue := (VM.add 403 (Gval (Fuint 7) (word_403 v)) (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue))).
Definition next_raw_word_51 v := word_of_eval (eval_hfexpr next_expr_51 (next_closed_51 v) (next_closed_51 v)).
Definition next_word_51 v := zext_to 6 (take 6 (next_raw_word_51 v)).
Lemma next_closed_51_value v : eval_hfexpr next_expr_51 (next_closed_51 v) (next_closed_51 v) = Some (Gval (Fuint 6) (next_raw_word_51 v)).
Proof. unfold next_raw_word_51, next_closed_51, next_expr_51, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_51.
Lemma next_expr_51_value v : eval_hfexpr next_expr_51 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (next_raw_word_51 v)).
Proof. change (eval_hfexpr next_expr_51 (next_closed_51 v) (next_closed_51 v) = Some (Gval (Fuint 6) (next_raw_word_51 v))). apply next_closed_51_value. Qed.
Lemma register_write_51 : register_write_certificate 51 (@Sfcnct VarOrder.T (@Eid VarOrder.T 51) next_expr_51) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_51 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 51 after = Some (Gval (Fuint 6) (next_word_51 v)).
Proof.
 have old_found : VM.find 51 old = Some (Gval (Fuint 6) (word_51 v)).
 { rewrite (agree 51); [exact (target_51_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_51 old old = Some (Gval (Fuint 6) (next_raw_word_51 v)).
 { rewrite (scalar_eval_empty_memory next_expr_51 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_51 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_51_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_51 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_51|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply unidirectional_eid_target with (expr:=next_expr_51) (value:=Gval (Fuint 6) (next_raw_word_51 v)) (ground:=Fuint 6) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old) (set_regs:=true).
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - reflexivity.
 - eapply one_statement_nonref; [reflexivity|exact step].
Qed.
Definition next_expr_445 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition next_closed_445 v : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition next_raw_word_445 v := word_of_eval (eval_hfexpr next_expr_445 (next_closed_445 v) (next_closed_445 v)).
Definition next_word_445 v := zext_to 1 (take 1 (next_raw_word_445 v)).
Lemma next_closed_445_value v : eval_hfexpr next_expr_445 (next_closed_445 v) (next_closed_445 v) = Some (Gval (Fuint 1) (next_raw_word_445 v)).
Proof. unfold next_raw_word_445, next_closed_445, next_expr_445, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_445.
Lemma next_expr_445_value v : eval_hfexpr next_expr_445 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_445 v)).
Proof. change (eval_hfexpr next_expr_445 (next_closed_445 v) (next_closed_445 v) = Some (Gval (Fuint 1) (next_raw_word_445 v))). apply next_closed_445_value. Qed.
Lemma register_write_445 : register_write_certificate 445 (@Sfcnct VarOrder.T (@Eid VarOrder.T 445) next_expr_445) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_445 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 445 after = Some (Gval (Fuint 1) (next_word_445 v)).
Proof.
 have old_found : VM.find 445 old = Some (Gval (Fuint 1) (word_445 v)).
 { rewrite (agree 445); [exact (target_445_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_445 old old = Some (Gval (Fuint 1) (next_raw_word_445 v)).
 { rewrite (scalar_eval_empty_memory next_expr_445 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_445 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_445_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_445 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_445|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply unidirectional_eid_target with (expr:=next_expr_445) (value:=Gval (Fuint 1) (next_raw_word_445 v)) (ground:=Fuint 1) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old) (set_regs:=true).
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - reflexivity.
 - eapply one_statement_nonref; [reflexivity|exact step].
Qed.
Definition next_expr_446 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 13)).
Definition next_closed_446 v : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition next_raw_word_446 v := word_of_eval (eval_hfexpr next_expr_446 (next_closed_446 v) (next_closed_446 v)).
Definition next_word_446 v := zext_to 3 (take 3 (next_raw_word_446 v)).
Lemma next_closed_446_value v : eval_hfexpr next_expr_446 (next_closed_446 v) (next_closed_446 v) = Some (Gval (Fuint 3) (next_raw_word_446 v)).
Proof. unfold next_raw_word_446, next_closed_446, next_expr_446, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_446.
Lemma next_expr_446_value v : eval_hfexpr next_expr_446 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (next_raw_word_446 v)).
Proof. change (eval_hfexpr next_expr_446 (next_closed_446 v) (next_closed_446 v) = Some (Gval (Fuint 3) (next_raw_word_446 v))). apply next_closed_446_value. Qed.
Lemma register_write_446 : register_write_certificate 446 (@Sfcnct VarOrder.T (@Eid VarOrder.T 446) next_expr_446) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_446 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 446 after = Some (Gval (Fuint 3) (next_word_446 v)).
Proof.
 have old_found : VM.find 446 old = Some (Gval (Fuint 3) (word_446 v)).
 { rewrite (agree 446); [exact (target_446_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_446 old old = Some (Gval (Fuint 3) (next_raw_word_446 v)).
 { rewrite (scalar_eval_empty_memory next_expr_446 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_446 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_446_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_446 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_446|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 3) (next_raw_word_446 v)) (source:=13) (target:=446) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_447 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 51)).
Definition next_closed_447 v : VM.t hvalue := (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.empty hvalue)).
Definition next_raw_word_447 v := word_of_eval (eval_hfexpr next_expr_447 (next_closed_447 v) (next_closed_447 v)).
Definition next_word_447 v := zext_to 6 (take 6 (next_raw_word_447 v)).
Lemma next_closed_447_value v : eval_hfexpr next_expr_447 (next_closed_447 v) (next_closed_447 v) = Some (Gval (Fuint 6) (next_raw_word_447 v)).
Proof. unfold next_raw_word_447, next_closed_447, next_expr_447, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_447.
Lemma next_expr_447_value v : eval_hfexpr next_expr_447 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (next_raw_word_447 v)).
Proof. change (eval_hfexpr next_expr_447 (next_closed_447 v) (next_closed_447 v) = Some (Gval (Fuint 6) (next_raw_word_447 v))). apply next_closed_447_value. Qed.
Lemma register_write_447 : register_write_certificate 447 (@Sfcnct VarOrder.T (@Eid VarOrder.T 447) next_expr_447) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_447 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 447 after = Some (Gval (Fuint 6) (next_word_447 v)).
Proof.
 have old_found : VM.find 447 old = Some (Gval (Fuint 6) (word_447 v)).
 { rewrite (agree 447); [exact (target_447_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_447 old old = Some (Gval (Fuint 6) (next_raw_word_447 v)).
 { rewrite (scalar_eval_empty_memory next_expr_447 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_447 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_447_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_447 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_447|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 6) (next_raw_word_447 v)) (source:=51) (target:=447) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_475 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 474))).
Definition next_closed_475 v : VM.t hvalue := (VM.add 474 (Gval (Fuint 1) (word_474 v)) (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue))).
Definition next_raw_word_475 v := word_of_eval (eval_hfexpr next_expr_475 (next_closed_475 v) (next_closed_475 v)).
Definition next_word_475 v := zext_to 1 (take 1 (next_raw_word_475 v)).
Lemma next_closed_475_value v : eval_hfexpr next_expr_475 (next_closed_475 v) (next_closed_475 v) = Some (Gval (Fuint 1) (next_raw_word_475 v)).
Proof. unfold next_raw_word_475, next_closed_475, next_expr_475, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_475.
Lemma next_expr_475_value v : eval_hfexpr next_expr_475 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (next_raw_word_475 v)).
Proof. change (eval_hfexpr next_expr_475 (next_closed_475 v) (next_closed_475 v) = Some (Gval (Fuint 1) (next_raw_word_475 v))). apply next_closed_475_value. Qed.
Lemma register_write_475 : register_write_certificate 475 (@Sfcnct VarOrder.T (@Eid VarOrder.T 475) next_expr_475) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_475 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 475 after = Some (Gval (Fuint 1) (next_word_475 v)).
Proof.
 have old_found : VM.find 475 old = Some (Gval (Fuint 1) (word_475 v)).
 { rewrite (agree 475); [exact (target_475_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_475 old old = Some (Gval (Fuint 1) (next_raw_word_475 v)).
 { rewrite (scalar_eval_empty_memory next_expr_475 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_475 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_475_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_475 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_475|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply unidirectional_eid_target with (expr:=next_expr_475) (value:=Gval (Fuint 1) (next_raw_word_475 v)) (ground:=Fuint 1) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old) (set_regs:=true).
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - reflexivity.
 - eapply one_statement_nonref; [reflexivity|exact step].
Qed.
Definition next_expr_476 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 9)).
Definition next_closed_476 v : VM.t hvalue := (VM.add 9 (Gval (Fuint 64) (word_9 v)) (VM.empty hvalue)).
Definition next_raw_word_476 v := word_of_eval (eval_hfexpr next_expr_476 (next_closed_476 v) (next_closed_476 v)).
Definition next_word_476 v := zext_to 64 (take 64 (next_raw_word_476 v)).
Lemma next_closed_476_value v : eval_hfexpr next_expr_476 (next_closed_476 v) (next_closed_476 v) = Some (Gval (Fuint 64) (next_raw_word_476 v)).
Proof. unfold next_raw_word_476, next_closed_476, next_expr_476, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_476.
Lemma next_expr_476_value v : eval_hfexpr next_expr_476 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (next_raw_word_476 v)).
Proof. change (eval_hfexpr next_expr_476 (next_closed_476 v) (next_closed_476 v) = Some (Gval (Fuint 64) (next_raw_word_476 v))). apply next_closed_476_value. Qed.
Lemma register_write_476 : register_write_certificate 476 (@Sfcnct VarOrder.T (@Eid VarOrder.T 476) next_expr_476) generated_module_0_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_476 invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 VM.find 476 after = Some (Gval (Fuint 64) (next_word_476 v)).
Proof.
 have old_found : VM.find 476 old = Some (Gval (Fuint 64) (word_476 v)).
 { rewrite (agree 476); [exact (target_476_value v)|vm_compute; reflexivity]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_476 old old = Some (Gval (Fuint 64) (next_raw_word_476 v)).
 { rewrite (scalar_eval_empty_memory next_expr_476 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_476 old (stable_env v) old (stable_env v) (Logic.eq_refl true)); [exact (next_expr_476_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_476 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; reflexivity. }
 eapply pass_register_write_value; [exact register_write_476|exact old_found|reflexivity|exact (divider_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 64) (next_raw_word_476 v)) (source:=9) (target:=476) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_register_value v (id:N) : hvalue := match id with
 | 13 => Gval (Fuint 3) (next_word_13 v)
 | 18 => Gval (Fuint 1) (next_word_18 v)
 | 20 => Gval (Fuint 129) (next_word_20 v)
 | 33 => Gval (Fuint 1) (next_word_33 v)
 | 38 => Gval (Fuint 1) (next_word_38 v)
 | 40 => Gval (Fuint 64) (next_word_40 v)
 | 43 => Gval (Fuint 65) (next_word_43 v)
 | 45 => Gval (Fuint 1) (next_word_45 v)
 | 46 => Gval (Fuint 1) (next_word_46 v)
 | 47 => Gval (Fuint 1) (next_word_47 v)
 | 51 => Gval (Fuint 6) (next_word_51 v)
 | 445 => Gval (Fuint 1) (next_word_445 v)
 | 446 => Gval (Fuint 3) (next_word_446 v)
 | 447 => Gval (Fuint 6) (next_word_447 v)
 | 475 => Gval (Fuint 1) (next_word_475 v)
 | 476 => Gval (Fuint 64) (next_word_476 v)
 | _ => Needtobedefined (Gtyp (Fuint 0)) end.
Definition divider_committed v (env:VM.t hvalue) := forall id, List.In id [:: 13; 18; 20; 33; 38; 40; 43; 45; 46; 47; 51; 445; 446; 447; 475; 476] -> VM.find id env = Some (next_register_value v id).
Lemma divider_commit_values invalid v old before after
 (agree : forall dep, divider_domain dep -> VM.find dep old = VM.find dep (stable_env v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_0_stmts_0 = Some after) :
 divider_committed v after.
Proof. intros id inside.
 destruct inside as [same|inside]; [subst id; exact (commit_register_13 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_18 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_20 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_33 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_38 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_40 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_43 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_45 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_46 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_47 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_51 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_445 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_446 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_447 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_475 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_476 invalid v old before after agree ran)|].
 contradiction.
Qed.
Print Assumptions divider_commit_values.

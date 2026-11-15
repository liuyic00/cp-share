From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames ConnectionFacts RegisterCommitFacts
 RegisterWriteFacts ScalarEvaluation ScalarExtensionality.
From SmallMultiplier Require Import Model Stable GlobalStable GlobalLookups.
Definition root_domain (id:N) : Prop := N.lt id 421 /\ (N.lt id 7 \/ N.le 37 id).
Local Open Scope N_scope.
Lemma multiplier_resets_inert old : registers_inert
 (fun expr => eval_hfexpr_with_memory empty_memory_map expr old old) generated_module_3_stmts_0.
Proof. cbn [registers_inert generated_module_3_stmts_0]. repeat split; intro proposed; reflexivity. Qed.
Definition next_expr_201 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 202)).
Definition next_closed_201 v : VM.t hvalue := (VM.add 202 (Gval (Fuint 1) (global_word_226 v)) (VM.empty hvalue)).
Definition next_raw_word_201 v := word_of_eval (eval_hfexpr next_expr_201 (next_closed_201 v) (next_closed_201 v)).
Definition next_word_201 v := zext_to 1 (take 1 (next_raw_word_201 v)).
Lemma next_closed_201_value v : eval_hfexpr next_expr_201 (next_closed_201 v) (next_closed_201 v) = Some (Gval (Fuint 1) (next_raw_word_201 v)).
Proof. unfold next_raw_word_201, next_closed_201, next_expr_201, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_201.
Lemma next_expr_201_value v : eval_hfexpr next_expr_201 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_201 v)).
Proof. change (eval_hfexpr next_expr_201 (next_closed_201 v) (next_closed_201 v) = Some (Gval (Fuint 1) (next_raw_word_201 v))). apply next_closed_201_value. Qed.
Lemma register_write_201 : register_write_certificate 201 (@Sfcnct VarOrder.T (@Eid VarOrder.T 201) next_expr_201) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_201 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 201 after = Some (Gval (Fuint 1) (next_word_201 v)).
Proof.
 have old_found : VM.find 201 old = Some (Gval (Fuint 1) (global_word_3 v)).
 { rewrite (agree 201); [exact (global_lookup_3 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_201 old old = Some (Gval (Fuint 1) (next_raw_word_201 v)).
 { rewrite (scalar_eval_empty_memory next_expr_201 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_201 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_201_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_201 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_201|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_201 v)) (source:=202) (target:=201) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_203 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 204)).
Definition next_closed_203 v : VM.t hvalue := (VM.add 204 (Gval (Fuint 1) (global_word_227 v)) (VM.empty hvalue)).
Definition next_raw_word_203 v := word_of_eval (eval_hfexpr next_expr_203 (next_closed_203 v) (next_closed_203 v)).
Definition next_word_203 v := zext_to 1 (take 1 (next_raw_word_203 v)).
Lemma next_closed_203_value v : eval_hfexpr next_expr_203 (next_closed_203 v) (next_closed_203 v) = Some (Gval (Fuint 1) (next_raw_word_203 v)).
Proof. unfold next_raw_word_203, next_closed_203, next_expr_203, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_203.
Lemma next_expr_203_value v : eval_hfexpr next_expr_203 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_203 v)).
Proof. change (eval_hfexpr next_expr_203 (next_closed_203 v) (next_closed_203 v) = Some (Gval (Fuint 1) (next_raw_word_203 v))). apply next_closed_203_value. Qed.
Lemma register_write_203 : register_write_certificate 203 (@Sfcnct VarOrder.T (@Eid VarOrder.T 203) next_expr_203) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_203 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 203 after = Some (Gval (Fuint 1) (next_word_203 v)).
Proof.
 have old_found : VM.find 203 old = Some (Gval (Fuint 1) (global_word_4 v)).
 { rewrite (agree 203); [exact (global_lookup_4 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_203 old old = Some (Gval (Fuint 1) (next_raw_word_203 v)).
 { rewrite (scalar_eval_empty_memory next_expr_203 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_203 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_203_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_203 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_203|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_203 v)) (source:=204) (target:=203) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_205 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 206)).
Definition next_closed_205 v : VM.t hvalue := (VM.add 206 (Gval (Fuint 1) (global_word_228 v)) (VM.empty hvalue)).
Definition next_raw_word_205 v := word_of_eval (eval_hfexpr next_expr_205 (next_closed_205 v) (next_closed_205 v)).
Definition next_word_205 v := zext_to 1 (take 1 (next_raw_word_205 v)).
Lemma next_closed_205_value v : eval_hfexpr next_expr_205 (next_closed_205 v) (next_closed_205 v) = Some (Gval (Fuint 1) (next_raw_word_205 v)).
Proof. unfold next_raw_word_205, next_closed_205, next_expr_205, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_205.
Lemma next_expr_205_value v : eval_hfexpr next_expr_205 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_205 v)).
Proof. change (eval_hfexpr next_expr_205 (next_closed_205 v) (next_closed_205 v) = Some (Gval (Fuint 1) (next_raw_word_205 v))). apply next_closed_205_value. Qed.
Lemma register_write_205 : register_write_certificate 205 (@Sfcnct VarOrder.T (@Eid VarOrder.T 205) next_expr_205) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_205 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 205 after = Some (Gval (Fuint 1) (next_word_205 v)).
Proof.
 have old_found : VM.find 205 old = Some (Gval (Fuint 1) (global_word_5 v)).
 { rewrite (agree 205); [exact (global_lookup_5 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_205 old old = Some (Gval (Fuint 1) (next_raw_word_205 v)).
 { rewrite (scalar_eval_empty_memory next_expr_205 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_205 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_205_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_205 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_205|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_205 v)) (source:=206) (target:=205) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_207 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 208)).
Definition next_closed_207 v : VM.t hvalue := (VM.add 208 (Gval (Fuint 1) (global_word_229 v)) (VM.empty hvalue)).
Definition next_raw_word_207 v := word_of_eval (eval_hfexpr next_expr_207 (next_closed_207 v) (next_closed_207 v)).
Definition next_word_207 v := zext_to 1 (take 1 (next_raw_word_207 v)).
Lemma next_closed_207_value v : eval_hfexpr next_expr_207 (next_closed_207 v) (next_closed_207 v) = Some (Gval (Fuint 1) (next_raw_word_207 v)).
Proof. unfold next_raw_word_207, next_closed_207, next_expr_207, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_207.
Lemma next_expr_207_value v : eval_hfexpr next_expr_207 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_207 v)).
Proof. change (eval_hfexpr next_expr_207 (next_closed_207 v) (next_closed_207 v) = Some (Gval (Fuint 1) (next_raw_word_207 v))). apply next_closed_207_value. Qed.
Lemma register_write_207 : register_write_certificate 207 (@Sfcnct VarOrder.T (@Eid VarOrder.T 207) next_expr_207) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_207 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 207 after = Some (Gval (Fuint 1) (next_word_207 v)).
Proof.
 have old_found : VM.find 207 old = Some (Gval (Fuint 1) (global_word_6 v)).
 { rewrite (agree 207); [exact (global_lookup_6 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_207 old old = Some (Gval (Fuint 1) (next_raw_word_207 v)).
 { rewrite (scalar_eval_empty_memory next_expr_207 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_207 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_207_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_207 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_207|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_207 v)) (source:=208) (target:=207) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_209 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 210)).
Definition next_closed_209 v : VM.t hvalue := (VM.add 210 (Gval (Fuint 1) (global_word_230 v)) (VM.empty hvalue)).
Definition next_raw_word_209 v := word_of_eval (eval_hfexpr next_expr_209 (next_closed_209 v) (next_closed_209 v)).
Definition next_word_209 v := zext_to 1 (take 1 (next_raw_word_209 v)).
Lemma next_closed_209_value v : eval_hfexpr next_expr_209 (next_closed_209 v) (next_closed_209 v) = Some (Gval (Fuint 1) (next_raw_word_209 v)).
Proof. unfold next_raw_word_209, next_closed_209, next_expr_209, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_209.
Lemma next_expr_209_value v : eval_hfexpr next_expr_209 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_209 v)).
Proof. change (eval_hfexpr next_expr_209 (next_closed_209 v) (next_closed_209 v) = Some (Gval (Fuint 1) (next_raw_word_209 v))). apply next_closed_209_value. Qed.
Lemma register_write_209 : register_write_certificate 209 (@Sfcnct VarOrder.T (@Eid VarOrder.T 209) next_expr_209) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_209 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 209 after = Some (Gval (Fuint 1) (next_word_209 v)).
Proof.
 have old_found : VM.find 209 old = Some (Gval (Fuint 1) (global_word_7 v)).
 { rewrite (agree 209); [exact (global_lookup_7 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_209 old old = Some (Gval (Fuint 1) (next_raw_word_209 v)).
 { rewrite (scalar_eval_empty_memory next_expr_209 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_209 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_209_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_209 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_209|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_209 v)) (source:=210) (target:=209) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_211 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 212)).
Definition next_closed_211 v : VM.t hvalue := (VM.add 212 (Gval (Fuint 1) (global_word_231 v)) (VM.empty hvalue)).
Definition next_raw_word_211 v := word_of_eval (eval_hfexpr next_expr_211 (next_closed_211 v) (next_closed_211 v)).
Definition next_word_211 v := zext_to 1 (take 1 (next_raw_word_211 v)).
Lemma next_closed_211_value v : eval_hfexpr next_expr_211 (next_closed_211 v) (next_closed_211 v) = Some (Gval (Fuint 1) (next_raw_word_211 v)).
Proof. unfold next_raw_word_211, next_closed_211, next_expr_211, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_211.
Lemma next_expr_211_value v : eval_hfexpr next_expr_211 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_211 v)).
Proof. change (eval_hfexpr next_expr_211 (next_closed_211 v) (next_closed_211 v) = Some (Gval (Fuint 1) (next_raw_word_211 v))). apply next_closed_211_value. Qed.
Lemma register_write_211 : register_write_certificate 211 (@Sfcnct VarOrder.T (@Eid VarOrder.T 211) next_expr_211) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_211 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 211 after = Some (Gval (Fuint 1) (next_word_211 v)).
Proof.
 have old_found : VM.find 211 old = Some (Gval (Fuint 1) (global_word_8 v)).
 { rewrite (agree 211); [exact (global_lookup_8 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_211 old old = Some (Gval (Fuint 1) (next_raw_word_211 v)).
 { rewrite (scalar_eval_empty_memory next_expr_211 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_211 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_211_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_211 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_211|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_211 v)) (source:=212) (target:=211) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_213 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 214)).
Definition next_closed_213 v : VM.t hvalue := (VM.add 214 (Gval (Fuint 1) (global_word_232 v)) (VM.empty hvalue)).
Definition next_raw_word_213 v := word_of_eval (eval_hfexpr next_expr_213 (next_closed_213 v) (next_closed_213 v)).
Definition next_word_213 v := zext_to 1 (take 1 (next_raw_word_213 v)).
Lemma next_closed_213_value v : eval_hfexpr next_expr_213 (next_closed_213 v) (next_closed_213 v) = Some (Gval (Fuint 1) (next_raw_word_213 v)).
Proof. unfold next_raw_word_213, next_closed_213, next_expr_213, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_213.
Lemma next_expr_213_value v : eval_hfexpr next_expr_213 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_213 v)).
Proof. change (eval_hfexpr next_expr_213 (next_closed_213 v) (next_closed_213 v) = Some (Gval (Fuint 1) (next_raw_word_213 v))). apply next_closed_213_value. Qed.
Lemma register_write_213 : register_write_certificate 213 (@Sfcnct VarOrder.T (@Eid VarOrder.T 213) next_expr_213) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_213 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 213 after = Some (Gval (Fuint 1) (next_word_213 v)).
Proof.
 have old_found : VM.find 213 old = Some (Gval (Fuint 1) (global_word_9 v)).
 { rewrite (agree 213); [exact (global_lookup_9 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_213 old old = Some (Gval (Fuint 1) (next_raw_word_213 v)).
 { rewrite (scalar_eval_empty_memory next_expr_213 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_213 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_213_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_213 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_213|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_213 v)) (source:=214) (target:=213) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_215 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 216)).
Definition next_closed_215 v : VM.t hvalue := (VM.add 216 (Gval (Fuint 1) (global_word_233 v)) (VM.empty hvalue)).
Definition next_raw_word_215 v := word_of_eval (eval_hfexpr next_expr_215 (next_closed_215 v) (next_closed_215 v)).
Definition next_word_215 v := zext_to 1 (take 1 (next_raw_word_215 v)).
Lemma next_closed_215_value v : eval_hfexpr next_expr_215 (next_closed_215 v) (next_closed_215 v) = Some (Gval (Fuint 1) (next_raw_word_215 v)).
Proof. unfold next_raw_word_215, next_closed_215, next_expr_215, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_215.
Lemma next_expr_215_value v : eval_hfexpr next_expr_215 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_215 v)).
Proof. change (eval_hfexpr next_expr_215 (next_closed_215 v) (next_closed_215 v) = Some (Gval (Fuint 1) (next_raw_word_215 v))). apply next_closed_215_value. Qed.
Lemma register_write_215 : register_write_certificate 215 (@Sfcnct VarOrder.T (@Eid VarOrder.T 215) next_expr_215) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_215 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 215 after = Some (Gval (Fuint 1) (next_word_215 v)).
Proof.
 have old_found : VM.find 215 old = Some (Gval (Fuint 1) (global_word_10 v)).
 { rewrite (agree 215); [exact (global_lookup_10 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_215 old old = Some (Gval (Fuint 1) (next_raw_word_215 v)).
 { rewrite (scalar_eval_empty_memory next_expr_215 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_215 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_215_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_215 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_215|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_215 v)) (source:=216) (target:=215) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_217 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 218)).
Definition next_closed_217 v : VM.t hvalue := (VM.add 218 (Gval (Fuint 1) (global_word_234 v)) (VM.empty hvalue)).
Definition next_raw_word_217 v := word_of_eval (eval_hfexpr next_expr_217 (next_closed_217 v) (next_closed_217 v)).
Definition next_word_217 v := zext_to 1 (take 1 (next_raw_word_217 v)).
Lemma next_closed_217_value v : eval_hfexpr next_expr_217 (next_closed_217 v) (next_closed_217 v) = Some (Gval (Fuint 1) (next_raw_word_217 v)).
Proof. unfold next_raw_word_217, next_closed_217, next_expr_217, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_217.
Lemma next_expr_217_value v : eval_hfexpr next_expr_217 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_217 v)).
Proof. change (eval_hfexpr next_expr_217 (next_closed_217 v) (next_closed_217 v) = Some (Gval (Fuint 1) (next_raw_word_217 v))). apply next_closed_217_value. Qed.
Lemma register_write_217 : register_write_certificate 217 (@Sfcnct VarOrder.T (@Eid VarOrder.T 217) next_expr_217) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_217 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 217 after = Some (Gval (Fuint 1) (next_word_217 v)).
Proof.
 have old_found : VM.find 217 old = Some (Gval (Fuint 1) (global_word_11 v)).
 { rewrite (agree 217); [exact (global_lookup_11 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_217 old old = Some (Gval (Fuint 1) (next_raw_word_217 v)).
 { rewrite (scalar_eval_empty_memory next_expr_217 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_217 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_217_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_217 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_217|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_217 v)) (source:=218) (target:=217) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_219 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 220)).
Definition next_closed_219 v : VM.t hvalue := (VM.add 220 (Gval (Fuint 1) (global_word_235 v)) (VM.empty hvalue)).
Definition next_raw_word_219 v := word_of_eval (eval_hfexpr next_expr_219 (next_closed_219 v) (next_closed_219 v)).
Definition next_word_219 v := zext_to 1 (take 1 (next_raw_word_219 v)).
Lemma next_closed_219_value v : eval_hfexpr next_expr_219 (next_closed_219 v) (next_closed_219 v) = Some (Gval (Fuint 1) (next_raw_word_219 v)).
Proof. unfold next_raw_word_219, next_closed_219, next_expr_219, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_219.
Lemma next_expr_219_value v : eval_hfexpr next_expr_219 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_219 v)).
Proof. change (eval_hfexpr next_expr_219 (next_closed_219 v) (next_closed_219 v) = Some (Gval (Fuint 1) (next_raw_word_219 v))). apply next_closed_219_value. Qed.
Lemma register_write_219 : register_write_certificate 219 (@Sfcnct VarOrder.T (@Eid VarOrder.T 219) next_expr_219) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_219 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 219 after = Some (Gval (Fuint 1) (next_word_219 v)).
Proof.
 have old_found : VM.find 219 old = Some (Gval (Fuint 1) (global_word_12 v)).
 { rewrite (agree 219); [exact (global_lookup_12 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_219 old old = Some (Gval (Fuint 1) (next_raw_word_219 v)).
 { rewrite (scalar_eval_empty_memory next_expr_219 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_219 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_219_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_219 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_219|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_219 v)) (source:=220) (target:=219) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_221 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 222)).
Definition next_closed_221 v : VM.t hvalue := (VM.add 222 (Gval (Fuint 1) (global_word_236 v)) (VM.empty hvalue)).
Definition next_raw_word_221 v := word_of_eval (eval_hfexpr next_expr_221 (next_closed_221 v) (next_closed_221 v)).
Definition next_word_221 v := zext_to 1 (take 1 (next_raw_word_221 v)).
Lemma next_closed_221_value v : eval_hfexpr next_expr_221 (next_closed_221 v) (next_closed_221 v) = Some (Gval (Fuint 1) (next_raw_word_221 v)).
Proof. unfold next_raw_word_221, next_closed_221, next_expr_221, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_221.
Lemma next_expr_221_value v : eval_hfexpr next_expr_221 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_221 v)).
Proof. change (eval_hfexpr next_expr_221 (next_closed_221 v) (next_closed_221 v) = Some (Gval (Fuint 1) (next_raw_word_221 v))). apply next_closed_221_value. Qed.
Lemma register_write_221 : register_write_certificate 221 (@Sfcnct VarOrder.T (@Eid VarOrder.T 221) next_expr_221) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_221 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 221 after = Some (Gval (Fuint 1) (next_word_221 v)).
Proof.
 have old_found : VM.find 221 old = Some (Gval (Fuint 1) (global_word_13 v)).
 { rewrite (agree 221); [exact (global_lookup_13 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_221 old old = Some (Gval (Fuint 1) (next_raw_word_221 v)).
 { rewrite (scalar_eval_empty_memory next_expr_221 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_221 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_221_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_221 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_221|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_221 v)) (source:=222) (target:=221) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_223 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 224)).
Definition next_closed_223 v : VM.t hvalue := (VM.add 224 (Gval (Fuint 1) (global_word_237 v)) (VM.empty hvalue)).
Definition next_raw_word_223 v := word_of_eval (eval_hfexpr next_expr_223 (next_closed_223 v) (next_closed_223 v)).
Definition next_word_223 v := zext_to 1 (take 1 (next_raw_word_223 v)).
Lemma next_closed_223_value v : eval_hfexpr next_expr_223 (next_closed_223 v) (next_closed_223 v) = Some (Gval (Fuint 1) (next_raw_word_223 v)).
Proof. unfold next_raw_word_223, next_closed_223, next_expr_223, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_223.
Lemma next_expr_223_value v : eval_hfexpr next_expr_223 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_223 v)).
Proof. change (eval_hfexpr next_expr_223 (next_closed_223 v) (next_closed_223 v) = Some (Gval (Fuint 1) (next_raw_word_223 v))). apply next_closed_223_value. Qed.
Lemma register_write_223 : register_write_certificate 223 (@Sfcnct VarOrder.T (@Eid VarOrder.T 223) next_expr_223) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_223 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 223 after = Some (Gval (Fuint 1) (next_word_223 v)).
Proof.
 have old_found : VM.find 223 old = Some (Gval (Fuint 1) (global_word_14 v)).
 { rewrite (agree 223); [exact (global_lookup_14 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_223 old old = Some (Gval (Fuint 1) (next_raw_word_223 v)).
 { rewrite (scalar_eval_empty_memory next_expr_223 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_223 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_223_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_223 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_223|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_223 v)) (source:=224) (target:=223) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_225 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 226)).
Definition next_closed_225 v : VM.t hvalue := (VM.add 226 (Gval (Fuint 1) (global_word_238 v)) (VM.empty hvalue)).
Definition next_raw_word_225 v := word_of_eval (eval_hfexpr next_expr_225 (next_closed_225 v) (next_closed_225 v)).
Definition next_word_225 v := zext_to 1 (take 1 (next_raw_word_225 v)).
Lemma next_closed_225_value v : eval_hfexpr next_expr_225 (next_closed_225 v) (next_closed_225 v) = Some (Gval (Fuint 1) (next_raw_word_225 v)).
Proof. unfold next_raw_word_225, next_closed_225, next_expr_225, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_225.
Lemma next_expr_225_value v : eval_hfexpr next_expr_225 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_225 v)).
Proof. change (eval_hfexpr next_expr_225 (next_closed_225 v) (next_closed_225 v) = Some (Gval (Fuint 1) (next_raw_word_225 v))). apply next_closed_225_value. Qed.
Lemma register_write_225 : register_write_certificate 225 (@Sfcnct VarOrder.T (@Eid VarOrder.T 225) next_expr_225) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_225 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 225 after = Some (Gval (Fuint 1) (next_word_225 v)).
Proof.
 have old_found : VM.find 225 old = Some (Gval (Fuint 1) (global_word_15 v)).
 { rewrite (agree 225); [exact (global_lookup_15 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_225 old old = Some (Gval (Fuint 1) (next_raw_word_225 v)).
 { rewrite (scalar_eval_empty_memory next_expr_225 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_225 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_225_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_225 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_225|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_225 v)) (source:=226) (target:=225) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_227 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 228)).
Definition next_closed_227 v : VM.t hvalue := (VM.add 228 (Gval (Fuint 1) (global_word_239 v)) (VM.empty hvalue)).
Definition next_raw_word_227 v := word_of_eval (eval_hfexpr next_expr_227 (next_closed_227 v) (next_closed_227 v)).
Definition next_word_227 v := zext_to 1 (take 1 (next_raw_word_227 v)).
Lemma next_closed_227_value v : eval_hfexpr next_expr_227 (next_closed_227 v) (next_closed_227 v) = Some (Gval (Fuint 1) (next_raw_word_227 v)).
Proof. unfold next_raw_word_227, next_closed_227, next_expr_227, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_227.
Lemma next_expr_227_value v : eval_hfexpr next_expr_227 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_227 v)).
Proof. change (eval_hfexpr next_expr_227 (next_closed_227 v) (next_closed_227 v) = Some (Gval (Fuint 1) (next_raw_word_227 v))). apply next_closed_227_value. Qed.
Lemma register_write_227 : register_write_certificate 227 (@Sfcnct VarOrder.T (@Eid VarOrder.T 227) next_expr_227) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_227 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 227 after = Some (Gval (Fuint 1) (next_word_227 v)).
Proof.
 have old_found : VM.find 227 old = Some (Gval (Fuint 1) (global_word_16 v)).
 { rewrite (agree 227); [exact (global_lookup_16 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_227 old old = Some (Gval (Fuint 1) (next_raw_word_227 v)).
 { rewrite (scalar_eval_empty_memory next_expr_227 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_227 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_227_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_227 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_227|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_227 v)) (source:=228) (target:=227) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_229 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 230)).
Definition next_closed_229 v : VM.t hvalue := (VM.add 230 (Gval (Fuint 1) (global_word_240 v)) (VM.empty hvalue)).
Definition next_raw_word_229 v := word_of_eval (eval_hfexpr next_expr_229 (next_closed_229 v) (next_closed_229 v)).
Definition next_word_229 v := zext_to 1 (take 1 (next_raw_word_229 v)).
Lemma next_closed_229_value v : eval_hfexpr next_expr_229 (next_closed_229 v) (next_closed_229 v) = Some (Gval (Fuint 1) (next_raw_word_229 v)).
Proof. unfold next_raw_word_229, next_closed_229, next_expr_229, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_229.
Lemma next_expr_229_value v : eval_hfexpr next_expr_229 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_229 v)).
Proof. change (eval_hfexpr next_expr_229 (next_closed_229 v) (next_closed_229 v) = Some (Gval (Fuint 1) (next_raw_word_229 v))). apply next_closed_229_value. Qed.
Lemma register_write_229 : register_write_certificate 229 (@Sfcnct VarOrder.T (@Eid VarOrder.T 229) next_expr_229) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_229 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 229 after = Some (Gval (Fuint 1) (next_word_229 v)).
Proof.
 have old_found : VM.find 229 old = Some (Gval (Fuint 1) (global_word_17 v)).
 { rewrite (agree 229); [exact (global_lookup_17 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_229 old old = Some (Gval (Fuint 1) (next_raw_word_229 v)).
 { rewrite (scalar_eval_empty_memory next_expr_229 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_229 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_229_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_229 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_229|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_229 v)) (source:=230) (target:=229) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_231 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 232)).
Definition next_closed_231 v : VM.t hvalue := (VM.add 232 (Gval (Fuint 1) (global_word_241 v)) (VM.empty hvalue)).
Definition next_raw_word_231 v := word_of_eval (eval_hfexpr next_expr_231 (next_closed_231 v) (next_closed_231 v)).
Definition next_word_231 v := zext_to 1 (take 1 (next_raw_word_231 v)).
Lemma next_closed_231_value v : eval_hfexpr next_expr_231 (next_closed_231 v) (next_closed_231 v) = Some (Gval (Fuint 1) (next_raw_word_231 v)).
Proof. unfold next_raw_word_231, next_closed_231, next_expr_231, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_231.
Lemma next_expr_231_value v : eval_hfexpr next_expr_231 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_231 v)).
Proof. change (eval_hfexpr next_expr_231 (next_closed_231 v) (next_closed_231 v) = Some (Gval (Fuint 1) (next_raw_word_231 v))). apply next_closed_231_value. Qed.
Lemma register_write_231 : register_write_certificate 231 (@Sfcnct VarOrder.T (@Eid VarOrder.T 231) next_expr_231) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_231 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 231 after = Some (Gval (Fuint 1) (next_word_231 v)).
Proof.
 have old_found : VM.find 231 old = Some (Gval (Fuint 1) (global_word_18 v)).
 { rewrite (agree 231); [exact (global_lookup_18 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_231 old old = Some (Gval (Fuint 1) (next_raw_word_231 v)).
 { rewrite (scalar_eval_empty_memory next_expr_231 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_231 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_231_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_231 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_231|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_231 v)) (source:=232) (target:=231) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_233 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 234)).
Definition next_closed_233 v : VM.t hvalue := (VM.add 234 (Gval (Fuint 1) (global_word_242 v)) (VM.empty hvalue)).
Definition next_raw_word_233 v := word_of_eval (eval_hfexpr next_expr_233 (next_closed_233 v) (next_closed_233 v)).
Definition next_word_233 v := zext_to 1 (take 1 (next_raw_word_233 v)).
Lemma next_closed_233_value v : eval_hfexpr next_expr_233 (next_closed_233 v) (next_closed_233 v) = Some (Gval (Fuint 1) (next_raw_word_233 v)).
Proof. unfold next_raw_word_233, next_closed_233, next_expr_233, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_233.
Lemma next_expr_233_value v : eval_hfexpr next_expr_233 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_233 v)).
Proof. change (eval_hfexpr next_expr_233 (next_closed_233 v) (next_closed_233 v) = Some (Gval (Fuint 1) (next_raw_word_233 v))). apply next_closed_233_value. Qed.
Lemma register_write_233 : register_write_certificate 233 (@Sfcnct VarOrder.T (@Eid VarOrder.T 233) next_expr_233) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_233 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 233 after = Some (Gval (Fuint 1) (next_word_233 v)).
Proof.
 have old_found : VM.find 233 old = Some (Gval (Fuint 1) (global_word_19 v)).
 { rewrite (agree 233); [exact (global_lookup_19 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_233 old old = Some (Gval (Fuint 1) (next_raw_word_233 v)).
 { rewrite (scalar_eval_empty_memory next_expr_233 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_233 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_233_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_233 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_233|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_233 v)) (source:=234) (target:=233) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_235 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 236)).
Definition next_closed_235 v : VM.t hvalue := (VM.add 236 (Gval (Fuint 1) (global_word_243 v)) (VM.empty hvalue)).
Definition next_raw_word_235 v := word_of_eval (eval_hfexpr next_expr_235 (next_closed_235 v) (next_closed_235 v)).
Definition next_word_235 v := zext_to 1 (take 1 (next_raw_word_235 v)).
Lemma next_closed_235_value v : eval_hfexpr next_expr_235 (next_closed_235 v) (next_closed_235 v) = Some (Gval (Fuint 1) (next_raw_word_235 v)).
Proof. unfold next_raw_word_235, next_closed_235, next_expr_235, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_235.
Lemma next_expr_235_value v : eval_hfexpr next_expr_235 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_235 v)).
Proof. change (eval_hfexpr next_expr_235 (next_closed_235 v) (next_closed_235 v) = Some (Gval (Fuint 1) (next_raw_word_235 v))). apply next_closed_235_value. Qed.
Lemma register_write_235 : register_write_certificate 235 (@Sfcnct VarOrder.T (@Eid VarOrder.T 235) next_expr_235) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_235 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 235 after = Some (Gval (Fuint 1) (next_word_235 v)).
Proof.
 have old_found : VM.find 235 old = Some (Gval (Fuint 1) (global_word_20 v)).
 { rewrite (agree 235); [exact (global_lookup_20 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_235 old old = Some (Gval (Fuint 1) (next_raw_word_235 v)).
 { rewrite (scalar_eval_empty_memory next_expr_235 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_235 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_235_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_235 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_235|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_235 v)) (source:=236) (target:=235) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_237 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 238)).
Definition next_closed_237 v : VM.t hvalue := (VM.add 238 (Gval (Fuint 1) (global_word_244 v)) (VM.empty hvalue)).
Definition next_raw_word_237 v := word_of_eval (eval_hfexpr next_expr_237 (next_closed_237 v) (next_closed_237 v)).
Definition next_word_237 v := zext_to 1 (take 1 (next_raw_word_237 v)).
Lemma next_closed_237_value v : eval_hfexpr next_expr_237 (next_closed_237 v) (next_closed_237 v) = Some (Gval (Fuint 1) (next_raw_word_237 v)).
Proof. unfold next_raw_word_237, next_closed_237, next_expr_237, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_237.
Lemma next_expr_237_value v : eval_hfexpr next_expr_237 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_237 v)).
Proof. change (eval_hfexpr next_expr_237 (next_closed_237 v) (next_closed_237 v) = Some (Gval (Fuint 1) (next_raw_word_237 v))). apply next_closed_237_value. Qed.
Lemma register_write_237 : register_write_certificate 237 (@Sfcnct VarOrder.T (@Eid VarOrder.T 237) next_expr_237) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_237 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 237 after = Some (Gval (Fuint 1) (next_word_237 v)).
Proof.
 have old_found : VM.find 237 old = Some (Gval (Fuint 1) (global_word_21 v)).
 { rewrite (agree 237); [exact (global_lookup_21 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_237 old old = Some (Gval (Fuint 1) (next_raw_word_237 v)).
 { rewrite (scalar_eval_empty_memory next_expr_237 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_237 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_237_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_237 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_237|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_237 v)) (source:=238) (target:=237) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_239 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 240)).
Definition next_closed_239 v : VM.t hvalue := (VM.add 240 (Gval (Fuint 1) (global_word_245 v)) (VM.empty hvalue)).
Definition next_raw_word_239 v := word_of_eval (eval_hfexpr next_expr_239 (next_closed_239 v) (next_closed_239 v)).
Definition next_word_239 v := zext_to 1 (take 1 (next_raw_word_239 v)).
Lemma next_closed_239_value v : eval_hfexpr next_expr_239 (next_closed_239 v) (next_closed_239 v) = Some (Gval (Fuint 1) (next_raw_word_239 v)).
Proof. unfold next_raw_word_239, next_closed_239, next_expr_239, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_239.
Lemma next_expr_239_value v : eval_hfexpr next_expr_239 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_239 v)).
Proof. change (eval_hfexpr next_expr_239 (next_closed_239 v) (next_closed_239 v) = Some (Gval (Fuint 1) (next_raw_word_239 v))). apply next_closed_239_value. Qed.
Lemma register_write_239 : register_write_certificate 239 (@Sfcnct VarOrder.T (@Eid VarOrder.T 239) next_expr_239) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_239 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 239 after = Some (Gval (Fuint 1) (next_word_239 v)).
Proof.
 have old_found : VM.find 239 old = Some (Gval (Fuint 1) (global_word_22 v)).
 { rewrite (agree 239); [exact (global_lookup_22 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_239 old old = Some (Gval (Fuint 1) (next_raw_word_239 v)).
 { rewrite (scalar_eval_empty_memory next_expr_239 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_239 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_239_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_239 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_239|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_239 v)) (source:=240) (target:=239) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_241 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 242)).
Definition next_closed_241 v : VM.t hvalue := (VM.add 242 (Gval (Fuint 1) (global_word_246 v)) (VM.empty hvalue)).
Definition next_raw_word_241 v := word_of_eval (eval_hfexpr next_expr_241 (next_closed_241 v) (next_closed_241 v)).
Definition next_word_241 v := zext_to 1 (take 1 (next_raw_word_241 v)).
Lemma next_closed_241_value v : eval_hfexpr next_expr_241 (next_closed_241 v) (next_closed_241 v) = Some (Gval (Fuint 1) (next_raw_word_241 v)).
Proof. unfold next_raw_word_241, next_closed_241, next_expr_241, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_241.
Lemma next_expr_241_value v : eval_hfexpr next_expr_241 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_241 v)).
Proof. change (eval_hfexpr next_expr_241 (next_closed_241 v) (next_closed_241 v) = Some (Gval (Fuint 1) (next_raw_word_241 v))). apply next_closed_241_value. Qed.
Lemma register_write_241 : register_write_certificate 241 (@Sfcnct VarOrder.T (@Eid VarOrder.T 241) next_expr_241) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_241 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 241 after = Some (Gval (Fuint 1) (next_word_241 v)).
Proof.
 have old_found : VM.find 241 old = Some (Gval (Fuint 1) (global_word_23 v)).
 { rewrite (agree 241); [exact (global_lookup_23 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_241 old old = Some (Gval (Fuint 1) (next_raw_word_241 v)).
 { rewrite (scalar_eval_empty_memory next_expr_241 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_241 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_241_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_241 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_241|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_241 v)) (source:=242) (target:=241) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_243 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 244)).
Definition next_closed_243 v : VM.t hvalue := (VM.add 244 (Gval (Fuint 1) (global_word_247 v)) (VM.empty hvalue)).
Definition next_raw_word_243 v := word_of_eval (eval_hfexpr next_expr_243 (next_closed_243 v) (next_closed_243 v)).
Definition next_word_243 v := zext_to 1 (take 1 (next_raw_word_243 v)).
Lemma next_closed_243_value v : eval_hfexpr next_expr_243 (next_closed_243 v) (next_closed_243 v) = Some (Gval (Fuint 1) (next_raw_word_243 v)).
Proof. unfold next_raw_word_243, next_closed_243, next_expr_243, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_243.
Lemma next_expr_243_value v : eval_hfexpr next_expr_243 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_243 v)).
Proof. change (eval_hfexpr next_expr_243 (next_closed_243 v) (next_closed_243 v) = Some (Gval (Fuint 1) (next_raw_word_243 v))). apply next_closed_243_value. Qed.
Lemma register_write_243 : register_write_certificate 243 (@Sfcnct VarOrder.T (@Eid VarOrder.T 243) next_expr_243) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_243 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 243 after = Some (Gval (Fuint 1) (next_word_243 v)).
Proof.
 have old_found : VM.find 243 old = Some (Gval (Fuint 1) (global_word_24 v)).
 { rewrite (agree 243); [exact (global_lookup_24 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_243 old old = Some (Gval (Fuint 1) (next_raw_word_243 v)).
 { rewrite (scalar_eval_empty_memory next_expr_243 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_243 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_243_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_243 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_243|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_243 v)) (source:=244) (target:=243) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_245 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 246)).
Definition next_closed_245 v : VM.t hvalue := (VM.add 246 (Gval (Fuint 1) (global_word_248 v)) (VM.empty hvalue)).
Definition next_raw_word_245 v := word_of_eval (eval_hfexpr next_expr_245 (next_closed_245 v) (next_closed_245 v)).
Definition next_word_245 v := zext_to 1 (take 1 (next_raw_word_245 v)).
Lemma next_closed_245_value v : eval_hfexpr next_expr_245 (next_closed_245 v) (next_closed_245 v) = Some (Gval (Fuint 1) (next_raw_word_245 v)).
Proof. unfold next_raw_word_245, next_closed_245, next_expr_245, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_245.
Lemma next_expr_245_value v : eval_hfexpr next_expr_245 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_245 v)).
Proof. change (eval_hfexpr next_expr_245 (next_closed_245 v) (next_closed_245 v) = Some (Gval (Fuint 1) (next_raw_word_245 v))). apply next_closed_245_value. Qed.
Lemma register_write_245 : register_write_certificate 245 (@Sfcnct VarOrder.T (@Eid VarOrder.T 245) next_expr_245) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_245 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 245 after = Some (Gval (Fuint 1) (next_word_245 v)).
Proof.
 have old_found : VM.find 245 old = Some (Gval (Fuint 1) (global_word_25 v)).
 { rewrite (agree 245); [exact (global_lookup_25 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_245 old old = Some (Gval (Fuint 1) (next_raw_word_245 v)).
 { rewrite (scalar_eval_empty_memory next_expr_245 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_245 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_245_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_245 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_245|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_245 v)) (source:=246) (target:=245) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_247 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 248)).
Definition next_closed_247 v : VM.t hvalue := (VM.add 248 (Gval (Fuint 1) (global_word_249 v)) (VM.empty hvalue)).
Definition next_raw_word_247 v := word_of_eval (eval_hfexpr next_expr_247 (next_closed_247 v) (next_closed_247 v)).
Definition next_word_247 v := zext_to 1 (take 1 (next_raw_word_247 v)).
Lemma next_closed_247_value v : eval_hfexpr next_expr_247 (next_closed_247 v) (next_closed_247 v) = Some (Gval (Fuint 1) (next_raw_word_247 v)).
Proof. unfold next_raw_word_247, next_closed_247, next_expr_247, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_247.
Lemma next_expr_247_value v : eval_hfexpr next_expr_247 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_247 v)).
Proof. change (eval_hfexpr next_expr_247 (next_closed_247 v) (next_closed_247 v) = Some (Gval (Fuint 1) (next_raw_word_247 v))). apply next_closed_247_value. Qed.
Lemma register_write_247 : register_write_certificate 247 (@Sfcnct VarOrder.T (@Eid VarOrder.T 247) next_expr_247) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_247 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 247 after = Some (Gval (Fuint 1) (next_word_247 v)).
Proof.
 have old_found : VM.find 247 old = Some (Gval (Fuint 1) (global_word_26 v)).
 { rewrite (agree 247); [exact (global_lookup_26 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_247 old old = Some (Gval (Fuint 1) (next_raw_word_247 v)).
 { rewrite (scalar_eval_empty_memory next_expr_247 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_247 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_247_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_247 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_247|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_247 v)) (source:=248) (target:=247) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_249 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 250)).
Definition next_closed_249 v : VM.t hvalue := (VM.add 250 (Gval (Fuint 1) (global_word_250 v)) (VM.empty hvalue)).
Definition next_raw_word_249 v := word_of_eval (eval_hfexpr next_expr_249 (next_closed_249 v) (next_closed_249 v)).
Definition next_word_249 v := zext_to 1 (take 1 (next_raw_word_249 v)).
Lemma next_closed_249_value v : eval_hfexpr next_expr_249 (next_closed_249 v) (next_closed_249 v) = Some (Gval (Fuint 1) (next_raw_word_249 v)).
Proof. unfold next_raw_word_249, next_closed_249, next_expr_249, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_249.
Lemma next_expr_249_value v : eval_hfexpr next_expr_249 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_249 v)).
Proof. change (eval_hfexpr next_expr_249 (next_closed_249 v) (next_closed_249 v) = Some (Gval (Fuint 1) (next_raw_word_249 v))). apply next_closed_249_value. Qed.
Lemma register_write_249 : register_write_certificate 249 (@Sfcnct VarOrder.T (@Eid VarOrder.T 249) next_expr_249) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_249 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 249 after = Some (Gval (Fuint 1) (next_word_249 v)).
Proof.
 have old_found : VM.find 249 old = Some (Gval (Fuint 1) (global_word_27 v)).
 { rewrite (agree 249); [exact (global_lookup_27 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_249 old old = Some (Gval (Fuint 1) (next_raw_word_249 v)).
 { rewrite (scalar_eval_empty_memory next_expr_249 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_249 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_249_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_249 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_249|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_249 v)) (source:=250) (target:=249) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_251 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 252)).
Definition next_closed_251 v : VM.t hvalue := (VM.add 252 (Gval (Fuint 1) (global_word_251 v)) (VM.empty hvalue)).
Definition next_raw_word_251 v := word_of_eval (eval_hfexpr next_expr_251 (next_closed_251 v) (next_closed_251 v)).
Definition next_word_251 v := zext_to 1 (take 1 (next_raw_word_251 v)).
Lemma next_closed_251_value v : eval_hfexpr next_expr_251 (next_closed_251 v) (next_closed_251 v) = Some (Gval (Fuint 1) (next_raw_word_251 v)).
Proof. unfold next_raw_word_251, next_closed_251, next_expr_251, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_251.
Lemma next_expr_251_value v : eval_hfexpr next_expr_251 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_251 v)).
Proof. change (eval_hfexpr next_expr_251 (next_closed_251 v) (next_closed_251 v) = Some (Gval (Fuint 1) (next_raw_word_251 v))). apply next_closed_251_value. Qed.
Lemma register_write_251 : register_write_certificate 251 (@Sfcnct VarOrder.T (@Eid VarOrder.T 251) next_expr_251) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_251 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 251 after = Some (Gval (Fuint 1) (next_word_251 v)).
Proof.
 have old_found : VM.find 251 old = Some (Gval (Fuint 1) (global_word_28 v)).
 { rewrite (agree 251); [exact (global_lookup_28 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_251 old old = Some (Gval (Fuint 1) (next_raw_word_251 v)).
 { rewrite (scalar_eval_empty_memory next_expr_251 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_251 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_251_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_251 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_251|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_251 v)) (source:=252) (target:=251) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_253 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 254)).
Definition next_closed_253 v : VM.t hvalue := (VM.add 254 (Gval (Fuint 1) (global_word_252 v)) (VM.empty hvalue)).
Definition next_raw_word_253 v := word_of_eval (eval_hfexpr next_expr_253 (next_closed_253 v) (next_closed_253 v)).
Definition next_word_253 v := zext_to 1 (take 1 (next_raw_word_253 v)).
Lemma next_closed_253_value v : eval_hfexpr next_expr_253 (next_closed_253 v) (next_closed_253 v) = Some (Gval (Fuint 1) (next_raw_word_253 v)).
Proof. unfold next_raw_word_253, next_closed_253, next_expr_253, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_253.
Lemma next_expr_253_value v : eval_hfexpr next_expr_253 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_253 v)).
Proof. change (eval_hfexpr next_expr_253 (next_closed_253 v) (next_closed_253 v) = Some (Gval (Fuint 1) (next_raw_word_253 v))). apply next_closed_253_value. Qed.
Lemma register_write_253 : register_write_certificate 253 (@Sfcnct VarOrder.T (@Eid VarOrder.T 253) next_expr_253) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_253 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 253 after = Some (Gval (Fuint 1) (next_word_253 v)).
Proof.
 have old_found : VM.find 253 old = Some (Gval (Fuint 1) (global_word_29 v)).
 { rewrite (agree 253); [exact (global_lookup_29 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_253 old old = Some (Gval (Fuint 1) (next_raw_word_253 v)).
 { rewrite (scalar_eval_empty_memory next_expr_253 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_253 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_253_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_253 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_253|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_253 v)) (source:=254) (target:=253) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_255 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 256)).
Definition next_closed_255 v : VM.t hvalue := (VM.add 256 (Gval (Fuint 1) (global_word_253 v)) (VM.empty hvalue)).
Definition next_raw_word_255 v := word_of_eval (eval_hfexpr next_expr_255 (next_closed_255 v) (next_closed_255 v)).
Definition next_word_255 v := zext_to 1 (take 1 (next_raw_word_255 v)).
Lemma next_closed_255_value v : eval_hfexpr next_expr_255 (next_closed_255 v) (next_closed_255 v) = Some (Gval (Fuint 1) (next_raw_word_255 v)).
Proof. unfold next_raw_word_255, next_closed_255, next_expr_255, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_255.
Lemma next_expr_255_value v : eval_hfexpr next_expr_255 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_255 v)).
Proof. change (eval_hfexpr next_expr_255 (next_closed_255 v) (next_closed_255 v) = Some (Gval (Fuint 1) (next_raw_word_255 v))). apply next_closed_255_value. Qed.
Lemma register_write_255 : register_write_certificate 255 (@Sfcnct VarOrder.T (@Eid VarOrder.T 255) next_expr_255) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_255 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 255 after = Some (Gval (Fuint 1) (next_word_255 v)).
Proof.
 have old_found : VM.find 255 old = Some (Gval (Fuint 1) (global_word_30 v)).
 { rewrite (agree 255); [exact (global_lookup_30 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_255 old old = Some (Gval (Fuint 1) (next_raw_word_255 v)).
 { rewrite (scalar_eval_empty_memory next_expr_255 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_255 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_255_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_255 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_255|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_255 v)) (source:=256) (target:=255) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_257 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 258)).
Definition next_closed_257 v : VM.t hvalue := (VM.add 258 (Gval (Fuint 1) (global_word_254 v)) (VM.empty hvalue)).
Definition next_raw_word_257 v := word_of_eval (eval_hfexpr next_expr_257 (next_closed_257 v) (next_closed_257 v)).
Definition next_word_257 v := zext_to 1 (take 1 (next_raw_word_257 v)).
Lemma next_closed_257_value v : eval_hfexpr next_expr_257 (next_closed_257 v) (next_closed_257 v) = Some (Gval (Fuint 1) (next_raw_word_257 v)).
Proof. unfold next_raw_word_257, next_closed_257, next_expr_257, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_257.
Lemma next_expr_257_value v : eval_hfexpr next_expr_257 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_257 v)).
Proof. change (eval_hfexpr next_expr_257 (next_closed_257 v) (next_closed_257 v) = Some (Gval (Fuint 1) (next_raw_word_257 v))). apply next_closed_257_value. Qed.
Lemma register_write_257 : register_write_certificate 257 (@Sfcnct VarOrder.T (@Eid VarOrder.T 257) next_expr_257) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_257 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 257 after = Some (Gval (Fuint 1) (next_word_257 v)).
Proof.
 have old_found : VM.find 257 old = Some (Gval (Fuint 1) (global_word_31 v)).
 { rewrite (agree 257); [exact (global_lookup_31 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_257 old old = Some (Gval (Fuint 1) (next_raw_word_257 v)).
 { rewrite (scalar_eval_empty_memory next_expr_257 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_257 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_257_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_257 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_257|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_257 v)) (source:=258) (target:=257) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_259 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 260)).
Definition next_closed_259 v : VM.t hvalue := (VM.add 260 (Gval (Fuint 1) (global_word_255 v)) (VM.empty hvalue)).
Definition next_raw_word_259 v := word_of_eval (eval_hfexpr next_expr_259 (next_closed_259 v) (next_closed_259 v)).
Definition next_word_259 v := zext_to 1 (take 1 (next_raw_word_259 v)).
Lemma next_closed_259_value v : eval_hfexpr next_expr_259 (next_closed_259 v) (next_closed_259 v) = Some (Gval (Fuint 1) (next_raw_word_259 v)).
Proof. unfold next_raw_word_259, next_closed_259, next_expr_259, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_259.
Lemma next_expr_259_value v : eval_hfexpr next_expr_259 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_259 v)).
Proof. change (eval_hfexpr next_expr_259 (next_closed_259 v) (next_closed_259 v) = Some (Gval (Fuint 1) (next_raw_word_259 v))). apply next_closed_259_value. Qed.
Lemma register_write_259 : register_write_certificate 259 (@Sfcnct VarOrder.T (@Eid VarOrder.T 259) next_expr_259) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_259 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 259 after = Some (Gval (Fuint 1) (next_word_259 v)).
Proof.
 have old_found : VM.find 259 old = Some (Gval (Fuint 1) (global_word_32 v)).
 { rewrite (agree 259); [exact (global_lookup_32 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_259 old old = Some (Gval (Fuint 1) (next_raw_word_259 v)).
 { rewrite (scalar_eval_empty_memory next_expr_259 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_259 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_259_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_259 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_259|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_259 v)) (source:=260) (target:=259) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_261 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 262)).
Definition next_closed_261 v : VM.t hvalue := (VM.add 262 (Gval (Fuint 1) (global_word_256 v)) (VM.empty hvalue)).
Definition next_raw_word_261 v := word_of_eval (eval_hfexpr next_expr_261 (next_closed_261 v) (next_closed_261 v)).
Definition next_word_261 v := zext_to 1 (take 1 (next_raw_word_261 v)).
Lemma next_closed_261_value v : eval_hfexpr next_expr_261 (next_closed_261 v) (next_closed_261 v) = Some (Gval (Fuint 1) (next_raw_word_261 v)).
Proof. unfold next_raw_word_261, next_closed_261, next_expr_261, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_261.
Lemma next_expr_261_value v : eval_hfexpr next_expr_261 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_261 v)).
Proof. change (eval_hfexpr next_expr_261 (next_closed_261 v) (next_closed_261 v) = Some (Gval (Fuint 1) (next_raw_word_261 v))). apply next_closed_261_value. Qed.
Lemma register_write_261 : register_write_certificate 261 (@Sfcnct VarOrder.T (@Eid VarOrder.T 261) next_expr_261) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_261 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 261 after = Some (Gval (Fuint 1) (next_word_261 v)).
Proof.
 have old_found : VM.find 261 old = Some (Gval (Fuint 1) (global_word_33 v)).
 { rewrite (agree 261); [exact (global_lookup_33 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_261 old old = Some (Gval (Fuint 1) (next_raw_word_261 v)).
 { rewrite (scalar_eval_empty_memory next_expr_261 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_261 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_261_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_261 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_261|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_261 v)) (source:=262) (target:=261) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_263 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 264)).
Definition next_closed_263 v : VM.t hvalue := (VM.add 264 (Gval (Fuint 1) (global_word_257 v)) (VM.empty hvalue)).
Definition next_raw_word_263 v := word_of_eval (eval_hfexpr next_expr_263 (next_closed_263 v) (next_closed_263 v)).
Definition next_word_263 v := zext_to 1 (take 1 (next_raw_word_263 v)).
Lemma next_closed_263_value v : eval_hfexpr next_expr_263 (next_closed_263 v) (next_closed_263 v) = Some (Gval (Fuint 1) (next_raw_word_263 v)).
Proof. unfold next_raw_word_263, next_closed_263, next_expr_263, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_263.
Lemma next_expr_263_value v : eval_hfexpr next_expr_263 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_263 v)).
Proof. change (eval_hfexpr next_expr_263 (next_closed_263 v) (next_closed_263 v) = Some (Gval (Fuint 1) (next_raw_word_263 v))). apply next_closed_263_value. Qed.
Lemma register_write_263 : register_write_certificate 263 (@Sfcnct VarOrder.T (@Eid VarOrder.T 263) next_expr_263) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_263 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 263 after = Some (Gval (Fuint 1) (next_word_263 v)).
Proof.
 have old_found : VM.find 263 old = Some (Gval (Fuint 1) (global_word_34 v)).
 { rewrite (agree 263); [exact (global_lookup_34 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_263 old old = Some (Gval (Fuint 1) (next_raw_word_263 v)).
 { rewrite (scalar_eval_empty_memory next_expr_263 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_263 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_263_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_263 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_263|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_263 v)) (source:=264) (target:=263) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_265 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 266)).
Definition next_closed_265 v : VM.t hvalue := (VM.add 266 (Gval (Fuint 1) (global_word_258 v)) (VM.empty hvalue)).
Definition next_raw_word_265 v := word_of_eval (eval_hfexpr next_expr_265 (next_closed_265 v) (next_closed_265 v)).
Definition next_word_265 v := zext_to 1 (take 1 (next_raw_word_265 v)).
Lemma next_closed_265_value v : eval_hfexpr next_expr_265 (next_closed_265 v) (next_closed_265 v) = Some (Gval (Fuint 1) (next_raw_word_265 v)).
Proof. unfold next_raw_word_265, next_closed_265, next_expr_265, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_265.
Lemma next_expr_265_value v : eval_hfexpr next_expr_265 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_265 v)).
Proof. change (eval_hfexpr next_expr_265 (next_closed_265 v) (next_closed_265 v) = Some (Gval (Fuint 1) (next_raw_word_265 v))). apply next_closed_265_value. Qed.
Lemma register_write_265 : register_write_certificate 265 (@Sfcnct VarOrder.T (@Eid VarOrder.T 265) next_expr_265) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_265 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 265 after = Some (Gval (Fuint 1) (next_word_265 v)).
Proof.
 have old_found : VM.find 265 old = Some (Gval (Fuint 1) (global_word_35 v)).
 { rewrite (agree 265); [exact (global_lookup_35 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_265 old old = Some (Gval (Fuint 1) (next_raw_word_265 v)).
 { rewrite (scalar_eval_empty_memory next_expr_265 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_265 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_265_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_265 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_265|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_265 v)) (source:=266) (target:=265) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_267 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 268)).
Definition next_closed_267 v : VM.t hvalue := (VM.add 268 (Gval (Fuint 1) (global_word_259 v)) (VM.empty hvalue)).
Definition next_raw_word_267 v := word_of_eval (eval_hfexpr next_expr_267 (next_closed_267 v) (next_closed_267 v)).
Definition next_word_267 v := zext_to 1 (take 1 (next_raw_word_267 v)).
Lemma next_closed_267_value v : eval_hfexpr next_expr_267 (next_closed_267 v) (next_closed_267 v) = Some (Gval (Fuint 1) (next_raw_word_267 v)).
Proof. unfold next_raw_word_267, next_closed_267, next_expr_267, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_267.
Lemma next_expr_267_value v : eval_hfexpr next_expr_267 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_267 v)).
Proof. change (eval_hfexpr next_expr_267 (next_closed_267 v) (next_closed_267 v) = Some (Gval (Fuint 1) (next_raw_word_267 v))). apply next_closed_267_value. Qed.
Lemma register_write_267 : register_write_certificate 267 (@Sfcnct VarOrder.T (@Eid VarOrder.T 267) next_expr_267) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_267 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 267 after = Some (Gval (Fuint 1) (next_word_267 v)).
Proof.
 have old_found : VM.find 267 old = Some (Gval (Fuint 1) (global_word_36 v)).
 { rewrite (agree 267); [exact (global_lookup_36 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_267 old old = Some (Gval (Fuint 1) (next_raw_word_267 v)).
 { rewrite (scalar_eval_empty_memory next_expr_267 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_267 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_267_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_267 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_267|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_267 v)) (source:=268) (target:=267) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_269 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 270)).
Definition next_closed_269 v : VM.t hvalue := (VM.add 270 (Gval (Fuint 1) (global_word_260 v)) (VM.empty hvalue)).
Definition next_raw_word_269 v := word_of_eval (eval_hfexpr next_expr_269 (next_closed_269 v) (next_closed_269 v)).
Definition next_word_269 v := zext_to 1 (take 1 (next_raw_word_269 v)).
Lemma next_closed_269_value v : eval_hfexpr next_expr_269 (next_closed_269 v) (next_closed_269 v) = Some (Gval (Fuint 1) (next_raw_word_269 v)).
Proof. unfold next_raw_word_269, next_closed_269, next_expr_269, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_269.
Lemma next_expr_269_value v : eval_hfexpr next_expr_269 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_269 v)).
Proof. change (eval_hfexpr next_expr_269 (next_closed_269 v) (next_closed_269 v) = Some (Gval (Fuint 1) (next_raw_word_269 v))). apply next_closed_269_value. Qed.
Lemma register_write_269 : register_write_certificate 269 (@Sfcnct VarOrder.T (@Eid VarOrder.T 269) next_expr_269) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_269 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 269 after = Some (Gval (Fuint 1) (next_word_269 v)).
Proof.
 have old_found : VM.find 269 old = Some (Gval (Fuint 1) (global_word_37 v)).
 { rewrite (agree 269); [exact (global_lookup_37 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_269 old old = Some (Gval (Fuint 1) (next_raw_word_269 v)).
 { rewrite (scalar_eval_empty_memory next_expr_269 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_269 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_269_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_269 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_269|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_269 v)) (source:=270) (target:=269) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_271 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 272)).
Definition next_closed_271 v : VM.t hvalue := (VM.add 272 (Gval (Fuint 1) (global_word_261 v)) (VM.empty hvalue)).
Definition next_raw_word_271 v := word_of_eval (eval_hfexpr next_expr_271 (next_closed_271 v) (next_closed_271 v)).
Definition next_word_271 v := zext_to 1 (take 1 (next_raw_word_271 v)).
Lemma next_closed_271_value v : eval_hfexpr next_expr_271 (next_closed_271 v) (next_closed_271 v) = Some (Gval (Fuint 1) (next_raw_word_271 v)).
Proof. unfold next_raw_word_271, next_closed_271, next_expr_271, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_271.
Lemma next_expr_271_value v : eval_hfexpr next_expr_271 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_271 v)).
Proof. change (eval_hfexpr next_expr_271 (next_closed_271 v) (next_closed_271 v) = Some (Gval (Fuint 1) (next_raw_word_271 v))). apply next_closed_271_value. Qed.
Lemma register_write_271 : register_write_certificate 271 (@Sfcnct VarOrder.T (@Eid VarOrder.T 271) next_expr_271) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_271 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 271 after = Some (Gval (Fuint 1) (next_word_271 v)).
Proof.
 have old_found : VM.find 271 old = Some (Gval (Fuint 1) (global_word_38 v)).
 { rewrite (agree 271); [exact (global_lookup_38 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_271 old old = Some (Gval (Fuint 1) (next_raw_word_271 v)).
 { rewrite (scalar_eval_empty_memory next_expr_271 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_271 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_271_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_271 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_271|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_271 v)) (source:=272) (target:=271) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_273 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 274)).
Definition next_closed_273 v : VM.t hvalue := (VM.add 274 (Gval (Fuint 1) (global_word_262 v)) (VM.empty hvalue)).
Definition next_raw_word_273 v := word_of_eval (eval_hfexpr next_expr_273 (next_closed_273 v) (next_closed_273 v)).
Definition next_word_273 v := zext_to 1 (take 1 (next_raw_word_273 v)).
Lemma next_closed_273_value v : eval_hfexpr next_expr_273 (next_closed_273 v) (next_closed_273 v) = Some (Gval (Fuint 1) (next_raw_word_273 v)).
Proof. unfold next_raw_word_273, next_closed_273, next_expr_273, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_273.
Lemma next_expr_273_value v : eval_hfexpr next_expr_273 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_273 v)).
Proof. change (eval_hfexpr next_expr_273 (next_closed_273 v) (next_closed_273 v) = Some (Gval (Fuint 1) (next_raw_word_273 v))). apply next_closed_273_value. Qed.
Lemma register_write_273 : register_write_certificate 273 (@Sfcnct VarOrder.T (@Eid VarOrder.T 273) next_expr_273) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_273 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 273 after = Some (Gval (Fuint 1) (next_word_273 v)).
Proof.
 have old_found : VM.find 273 old = Some (Gval (Fuint 1) (global_word_39 v)).
 { rewrite (agree 273); [exact (global_lookup_39 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_273 old old = Some (Gval (Fuint 1) (next_raw_word_273 v)).
 { rewrite (scalar_eval_empty_memory next_expr_273 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_273 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_273_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_273 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_273|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_273 v)) (source:=274) (target:=273) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_275 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 276)).
Definition next_closed_275 v : VM.t hvalue := (VM.add 276 (Gval (Fuint 1) (global_word_263 v)) (VM.empty hvalue)).
Definition next_raw_word_275 v := word_of_eval (eval_hfexpr next_expr_275 (next_closed_275 v) (next_closed_275 v)).
Definition next_word_275 v := zext_to 1 (take 1 (next_raw_word_275 v)).
Lemma next_closed_275_value v : eval_hfexpr next_expr_275 (next_closed_275 v) (next_closed_275 v) = Some (Gval (Fuint 1) (next_raw_word_275 v)).
Proof. unfold next_raw_word_275, next_closed_275, next_expr_275, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_275.
Lemma next_expr_275_value v : eval_hfexpr next_expr_275 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_275 v)).
Proof. change (eval_hfexpr next_expr_275 (next_closed_275 v) (next_closed_275 v) = Some (Gval (Fuint 1) (next_raw_word_275 v))). apply next_closed_275_value. Qed.
Lemma register_write_275 : register_write_certificate 275 (@Sfcnct VarOrder.T (@Eid VarOrder.T 275) next_expr_275) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_275 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 275 after = Some (Gval (Fuint 1) (next_word_275 v)).
Proof.
 have old_found : VM.find 275 old = Some (Gval (Fuint 1) (global_word_40 v)).
 { rewrite (agree 275); [exact (global_lookup_40 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_275 old old = Some (Gval (Fuint 1) (next_raw_word_275 v)).
 { rewrite (scalar_eval_empty_memory next_expr_275 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_275 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_275_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_275 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_275|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_275 v)) (source:=276) (target:=275) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_277 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 278)).
Definition next_closed_277 v : VM.t hvalue := (VM.add 278 (Gval (Fuint 1) (global_word_264 v)) (VM.empty hvalue)).
Definition next_raw_word_277 v := word_of_eval (eval_hfexpr next_expr_277 (next_closed_277 v) (next_closed_277 v)).
Definition next_word_277 v := zext_to 1 (take 1 (next_raw_word_277 v)).
Lemma next_closed_277_value v : eval_hfexpr next_expr_277 (next_closed_277 v) (next_closed_277 v) = Some (Gval (Fuint 1) (next_raw_word_277 v)).
Proof. unfold next_raw_word_277, next_closed_277, next_expr_277, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_277.
Lemma next_expr_277_value v : eval_hfexpr next_expr_277 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_277 v)).
Proof. change (eval_hfexpr next_expr_277 (next_closed_277 v) (next_closed_277 v) = Some (Gval (Fuint 1) (next_raw_word_277 v))). apply next_closed_277_value. Qed.
Lemma register_write_277 : register_write_certificate 277 (@Sfcnct VarOrder.T (@Eid VarOrder.T 277) next_expr_277) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_277 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 277 after = Some (Gval (Fuint 1) (next_word_277 v)).
Proof.
 have old_found : VM.find 277 old = Some (Gval (Fuint 1) (global_word_41 v)).
 { rewrite (agree 277); [exact (global_lookup_41 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_277 old old = Some (Gval (Fuint 1) (next_raw_word_277 v)).
 { rewrite (scalar_eval_empty_memory next_expr_277 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_277 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_277_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_277 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_277|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_277 v)) (source:=278) (target:=277) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_279 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 280)).
Definition next_closed_279 v : VM.t hvalue := (VM.add 280 (Gval (Fuint 1) (global_word_265 v)) (VM.empty hvalue)).
Definition next_raw_word_279 v := word_of_eval (eval_hfexpr next_expr_279 (next_closed_279 v) (next_closed_279 v)).
Definition next_word_279 v := zext_to 1 (take 1 (next_raw_word_279 v)).
Lemma next_closed_279_value v : eval_hfexpr next_expr_279 (next_closed_279 v) (next_closed_279 v) = Some (Gval (Fuint 1) (next_raw_word_279 v)).
Proof. unfold next_raw_word_279, next_closed_279, next_expr_279, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_279.
Lemma next_expr_279_value v : eval_hfexpr next_expr_279 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_279 v)).
Proof. change (eval_hfexpr next_expr_279 (next_closed_279 v) (next_closed_279 v) = Some (Gval (Fuint 1) (next_raw_word_279 v))). apply next_closed_279_value. Qed.
Lemma register_write_279 : register_write_certificate 279 (@Sfcnct VarOrder.T (@Eid VarOrder.T 279) next_expr_279) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_279 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 279 after = Some (Gval (Fuint 1) (next_word_279 v)).
Proof.
 have old_found : VM.find 279 old = Some (Gval (Fuint 1) (global_word_42 v)).
 { rewrite (agree 279); [exact (global_lookup_42 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_279 old old = Some (Gval (Fuint 1) (next_raw_word_279 v)).
 { rewrite (scalar_eval_empty_memory next_expr_279 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_279 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_279_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_279 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_279|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_279 v)) (source:=280) (target:=279) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_281 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 282)).
Definition next_closed_281 v : VM.t hvalue := (VM.add 282 (Gval (Fuint 1) (global_word_266 v)) (VM.empty hvalue)).
Definition next_raw_word_281 v := word_of_eval (eval_hfexpr next_expr_281 (next_closed_281 v) (next_closed_281 v)).
Definition next_word_281 v := zext_to 1 (take 1 (next_raw_word_281 v)).
Lemma next_closed_281_value v : eval_hfexpr next_expr_281 (next_closed_281 v) (next_closed_281 v) = Some (Gval (Fuint 1) (next_raw_word_281 v)).
Proof. unfold next_raw_word_281, next_closed_281, next_expr_281, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_281.
Lemma next_expr_281_value v : eval_hfexpr next_expr_281 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_281 v)).
Proof. change (eval_hfexpr next_expr_281 (next_closed_281 v) (next_closed_281 v) = Some (Gval (Fuint 1) (next_raw_word_281 v))). apply next_closed_281_value. Qed.
Lemma register_write_281 : register_write_certificate 281 (@Sfcnct VarOrder.T (@Eid VarOrder.T 281) next_expr_281) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_281 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 281 after = Some (Gval (Fuint 1) (next_word_281 v)).
Proof.
 have old_found : VM.find 281 old = Some (Gval (Fuint 1) (global_word_43 v)).
 { rewrite (agree 281); [exact (global_lookup_43 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_281 old old = Some (Gval (Fuint 1) (next_raw_word_281 v)).
 { rewrite (scalar_eval_empty_memory next_expr_281 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_281 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_281_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_281 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_281|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_281 v)) (source:=282) (target:=281) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_283 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 284)).
Definition next_closed_283 v : VM.t hvalue := (VM.add 284 (Gval (Fuint 1) (global_word_267 v)) (VM.empty hvalue)).
Definition next_raw_word_283 v := word_of_eval (eval_hfexpr next_expr_283 (next_closed_283 v) (next_closed_283 v)).
Definition next_word_283 v := zext_to 1 (take 1 (next_raw_word_283 v)).
Lemma next_closed_283_value v : eval_hfexpr next_expr_283 (next_closed_283 v) (next_closed_283 v) = Some (Gval (Fuint 1) (next_raw_word_283 v)).
Proof. unfold next_raw_word_283, next_closed_283, next_expr_283, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_283.
Lemma next_expr_283_value v : eval_hfexpr next_expr_283 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_283 v)).
Proof. change (eval_hfexpr next_expr_283 (next_closed_283 v) (next_closed_283 v) = Some (Gval (Fuint 1) (next_raw_word_283 v))). apply next_closed_283_value. Qed.
Lemma register_write_283 : register_write_certificate 283 (@Sfcnct VarOrder.T (@Eid VarOrder.T 283) next_expr_283) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_283 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 283 after = Some (Gval (Fuint 1) (next_word_283 v)).
Proof.
 have old_found : VM.find 283 old = Some (Gval (Fuint 1) (global_word_44 v)).
 { rewrite (agree 283); [exact (global_lookup_44 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_283 old old = Some (Gval (Fuint 1) (next_raw_word_283 v)).
 { rewrite (scalar_eval_empty_memory next_expr_283 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_283 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_283_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_283 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_283|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_283 v)) (source:=284) (target:=283) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_285 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 286)).
Definition next_closed_285 v : VM.t hvalue := (VM.add 286 (Gval (Fuint 1) (global_word_268 v)) (VM.empty hvalue)).
Definition next_raw_word_285 v := word_of_eval (eval_hfexpr next_expr_285 (next_closed_285 v) (next_closed_285 v)).
Definition next_word_285 v := zext_to 1 (take 1 (next_raw_word_285 v)).
Lemma next_closed_285_value v : eval_hfexpr next_expr_285 (next_closed_285 v) (next_closed_285 v) = Some (Gval (Fuint 1) (next_raw_word_285 v)).
Proof. unfold next_raw_word_285, next_closed_285, next_expr_285, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_285.
Lemma next_expr_285_value v : eval_hfexpr next_expr_285 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_285 v)).
Proof. change (eval_hfexpr next_expr_285 (next_closed_285 v) (next_closed_285 v) = Some (Gval (Fuint 1) (next_raw_word_285 v))). apply next_closed_285_value. Qed.
Lemma register_write_285 : register_write_certificate 285 (@Sfcnct VarOrder.T (@Eid VarOrder.T 285) next_expr_285) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_285 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 285 after = Some (Gval (Fuint 1) (next_word_285 v)).
Proof.
 have old_found : VM.find 285 old = Some (Gval (Fuint 1) (global_word_45 v)).
 { rewrite (agree 285); [exact (global_lookup_45 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_285 old old = Some (Gval (Fuint 1) (next_raw_word_285 v)).
 { rewrite (scalar_eval_empty_memory next_expr_285 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_285 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_285_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_285 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_285|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_285 v)) (source:=286) (target:=285) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_287 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 288)).
Definition next_closed_287 v : VM.t hvalue := (VM.add 288 (Gval (Fuint 1) (global_word_269 v)) (VM.empty hvalue)).
Definition next_raw_word_287 v := word_of_eval (eval_hfexpr next_expr_287 (next_closed_287 v) (next_closed_287 v)).
Definition next_word_287 v := zext_to 1 (take 1 (next_raw_word_287 v)).
Lemma next_closed_287_value v : eval_hfexpr next_expr_287 (next_closed_287 v) (next_closed_287 v) = Some (Gval (Fuint 1) (next_raw_word_287 v)).
Proof. unfold next_raw_word_287, next_closed_287, next_expr_287, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_287.
Lemma next_expr_287_value v : eval_hfexpr next_expr_287 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_287 v)).
Proof. change (eval_hfexpr next_expr_287 (next_closed_287 v) (next_closed_287 v) = Some (Gval (Fuint 1) (next_raw_word_287 v))). apply next_closed_287_value. Qed.
Lemma register_write_287 : register_write_certificate 287 (@Sfcnct VarOrder.T (@Eid VarOrder.T 287) next_expr_287) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_287 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 287 after = Some (Gval (Fuint 1) (next_word_287 v)).
Proof.
 have old_found : VM.find 287 old = Some (Gval (Fuint 1) (global_word_46 v)).
 { rewrite (agree 287); [exact (global_lookup_46 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_287 old old = Some (Gval (Fuint 1) (next_raw_word_287 v)).
 { rewrite (scalar_eval_empty_memory next_expr_287 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_287 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_287_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_287 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_287|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_287 v)) (source:=288) (target:=287) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_289 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 290)).
Definition next_closed_289 v : VM.t hvalue := (VM.add 290 (Gval (Fuint 1) (global_word_270 v)) (VM.empty hvalue)).
Definition next_raw_word_289 v := word_of_eval (eval_hfexpr next_expr_289 (next_closed_289 v) (next_closed_289 v)).
Definition next_word_289 v := zext_to 1 (take 1 (next_raw_word_289 v)).
Lemma next_closed_289_value v : eval_hfexpr next_expr_289 (next_closed_289 v) (next_closed_289 v) = Some (Gval (Fuint 1) (next_raw_word_289 v)).
Proof. unfold next_raw_word_289, next_closed_289, next_expr_289, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_289.
Lemma next_expr_289_value v : eval_hfexpr next_expr_289 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_289 v)).
Proof. change (eval_hfexpr next_expr_289 (next_closed_289 v) (next_closed_289 v) = Some (Gval (Fuint 1) (next_raw_word_289 v))). apply next_closed_289_value. Qed.
Lemma register_write_289 : register_write_certificate 289 (@Sfcnct VarOrder.T (@Eid VarOrder.T 289) next_expr_289) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_289 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 289 after = Some (Gval (Fuint 1) (next_word_289 v)).
Proof.
 have old_found : VM.find 289 old = Some (Gval (Fuint 1) (global_word_47 v)).
 { rewrite (agree 289); [exact (global_lookup_47 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_289 old old = Some (Gval (Fuint 1) (next_raw_word_289 v)).
 { rewrite (scalar_eval_empty_memory next_expr_289 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_289 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_289_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_289 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_289|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_289 v)) (source:=290) (target:=289) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_291 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 292)).
Definition next_closed_291 v : VM.t hvalue := (VM.add 292 (Gval (Fuint 1) (global_word_271 v)) (VM.empty hvalue)).
Definition next_raw_word_291 v := word_of_eval (eval_hfexpr next_expr_291 (next_closed_291 v) (next_closed_291 v)).
Definition next_word_291 v := zext_to 1 (take 1 (next_raw_word_291 v)).
Lemma next_closed_291_value v : eval_hfexpr next_expr_291 (next_closed_291 v) (next_closed_291 v) = Some (Gval (Fuint 1) (next_raw_word_291 v)).
Proof. unfold next_raw_word_291, next_closed_291, next_expr_291, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_291.
Lemma next_expr_291_value v : eval_hfexpr next_expr_291 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_291 v)).
Proof. change (eval_hfexpr next_expr_291 (next_closed_291 v) (next_closed_291 v) = Some (Gval (Fuint 1) (next_raw_word_291 v))). apply next_closed_291_value. Qed.
Lemma register_write_291 : register_write_certificate 291 (@Sfcnct VarOrder.T (@Eid VarOrder.T 291) next_expr_291) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_291 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 291 after = Some (Gval (Fuint 1) (next_word_291 v)).
Proof.
 have old_found : VM.find 291 old = Some (Gval (Fuint 1) (global_word_48 v)).
 { rewrite (agree 291); [exact (global_lookup_48 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_291 old old = Some (Gval (Fuint 1) (next_raw_word_291 v)).
 { rewrite (scalar_eval_empty_memory next_expr_291 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_291 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_291_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_291 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_291|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_291 v)) (source:=292) (target:=291) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_293 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 294)).
Definition next_closed_293 v : VM.t hvalue := (VM.add 294 (Gval (Fuint 1) (global_word_272 v)) (VM.empty hvalue)).
Definition next_raw_word_293 v := word_of_eval (eval_hfexpr next_expr_293 (next_closed_293 v) (next_closed_293 v)).
Definition next_word_293 v := zext_to 1 (take 1 (next_raw_word_293 v)).
Lemma next_closed_293_value v : eval_hfexpr next_expr_293 (next_closed_293 v) (next_closed_293 v) = Some (Gval (Fuint 1) (next_raw_word_293 v)).
Proof. unfold next_raw_word_293, next_closed_293, next_expr_293, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_293.
Lemma next_expr_293_value v : eval_hfexpr next_expr_293 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_293 v)).
Proof. change (eval_hfexpr next_expr_293 (next_closed_293 v) (next_closed_293 v) = Some (Gval (Fuint 1) (next_raw_word_293 v))). apply next_closed_293_value. Qed.
Lemma register_write_293 : register_write_certificate 293 (@Sfcnct VarOrder.T (@Eid VarOrder.T 293) next_expr_293) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_293 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 293 after = Some (Gval (Fuint 1) (next_word_293 v)).
Proof.
 have old_found : VM.find 293 old = Some (Gval (Fuint 1) (global_word_49 v)).
 { rewrite (agree 293); [exact (global_lookup_49 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_293 old old = Some (Gval (Fuint 1) (next_raw_word_293 v)).
 { rewrite (scalar_eval_empty_memory next_expr_293 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_293 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_293_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_293 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_293|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_293 v)) (source:=294) (target:=293) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_295 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 296)).
Definition next_closed_295 v : VM.t hvalue := (VM.add 296 (Gval (Fuint 1) (global_word_273 v)) (VM.empty hvalue)).
Definition next_raw_word_295 v := word_of_eval (eval_hfexpr next_expr_295 (next_closed_295 v) (next_closed_295 v)).
Definition next_word_295 v := zext_to 1 (take 1 (next_raw_word_295 v)).
Lemma next_closed_295_value v : eval_hfexpr next_expr_295 (next_closed_295 v) (next_closed_295 v) = Some (Gval (Fuint 1) (next_raw_word_295 v)).
Proof. unfold next_raw_word_295, next_closed_295, next_expr_295, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_295.
Lemma next_expr_295_value v : eval_hfexpr next_expr_295 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_295 v)).
Proof. change (eval_hfexpr next_expr_295 (next_closed_295 v) (next_closed_295 v) = Some (Gval (Fuint 1) (next_raw_word_295 v))). apply next_closed_295_value. Qed.
Lemma register_write_295 : register_write_certificate 295 (@Sfcnct VarOrder.T (@Eid VarOrder.T 295) next_expr_295) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_295 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 295 after = Some (Gval (Fuint 1) (next_word_295 v)).
Proof.
 have old_found : VM.find 295 old = Some (Gval (Fuint 1) (global_word_50 v)).
 { rewrite (agree 295); [exact (global_lookup_50 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_295 old old = Some (Gval (Fuint 1) (next_raw_word_295 v)).
 { rewrite (scalar_eval_empty_memory next_expr_295 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_295 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_295_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_295 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_295|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_295 v)) (source:=296) (target:=295) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_297 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 298)).
Definition next_closed_297 v : VM.t hvalue := (VM.add 298 (Gval (Fuint 1) (global_word_274 v)) (VM.empty hvalue)).
Definition next_raw_word_297 v := word_of_eval (eval_hfexpr next_expr_297 (next_closed_297 v) (next_closed_297 v)).
Definition next_word_297 v := zext_to 1 (take 1 (next_raw_word_297 v)).
Lemma next_closed_297_value v : eval_hfexpr next_expr_297 (next_closed_297 v) (next_closed_297 v) = Some (Gval (Fuint 1) (next_raw_word_297 v)).
Proof. unfold next_raw_word_297, next_closed_297, next_expr_297, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_297.
Lemma next_expr_297_value v : eval_hfexpr next_expr_297 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_297 v)).
Proof. change (eval_hfexpr next_expr_297 (next_closed_297 v) (next_closed_297 v) = Some (Gval (Fuint 1) (next_raw_word_297 v))). apply next_closed_297_value. Qed.
Lemma register_write_297 : register_write_certificate 297 (@Sfcnct VarOrder.T (@Eid VarOrder.T 297) next_expr_297) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_297 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 297 after = Some (Gval (Fuint 1) (next_word_297 v)).
Proof.
 have old_found : VM.find 297 old = Some (Gval (Fuint 1) (global_word_51 v)).
 { rewrite (agree 297); [exact (global_lookup_51 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_297 old old = Some (Gval (Fuint 1) (next_raw_word_297 v)).
 { rewrite (scalar_eval_empty_memory next_expr_297 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_297 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_297_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_297 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_297|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_297 v)) (source:=298) (target:=297) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_299 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 300)).
Definition next_closed_299 v : VM.t hvalue := (VM.add 300 (Gval (Fuint 1) (global_word_275 v)) (VM.empty hvalue)).
Definition next_raw_word_299 v := word_of_eval (eval_hfexpr next_expr_299 (next_closed_299 v) (next_closed_299 v)).
Definition next_word_299 v := zext_to 1 (take 1 (next_raw_word_299 v)).
Lemma next_closed_299_value v : eval_hfexpr next_expr_299 (next_closed_299 v) (next_closed_299 v) = Some (Gval (Fuint 1) (next_raw_word_299 v)).
Proof. unfold next_raw_word_299, next_closed_299, next_expr_299, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_299.
Lemma next_expr_299_value v : eval_hfexpr next_expr_299 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_299 v)).
Proof. change (eval_hfexpr next_expr_299 (next_closed_299 v) (next_closed_299 v) = Some (Gval (Fuint 1) (next_raw_word_299 v))). apply next_closed_299_value. Qed.
Lemma register_write_299 : register_write_certificate 299 (@Sfcnct VarOrder.T (@Eid VarOrder.T 299) next_expr_299) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_299 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 299 after = Some (Gval (Fuint 1) (next_word_299 v)).
Proof.
 have old_found : VM.find 299 old = Some (Gval (Fuint 1) (global_word_52 v)).
 { rewrite (agree 299); [exact (global_lookup_52 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_299 old old = Some (Gval (Fuint 1) (next_raw_word_299 v)).
 { rewrite (scalar_eval_empty_memory next_expr_299 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_299 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_299_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_299 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_299|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_299 v)) (source:=300) (target:=299) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_301 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 302)).
Definition next_closed_301 v : VM.t hvalue := (VM.add 302 (Gval (Fuint 1) (global_word_276 v)) (VM.empty hvalue)).
Definition next_raw_word_301 v := word_of_eval (eval_hfexpr next_expr_301 (next_closed_301 v) (next_closed_301 v)).
Definition next_word_301 v := zext_to 1 (take 1 (next_raw_word_301 v)).
Lemma next_closed_301_value v : eval_hfexpr next_expr_301 (next_closed_301 v) (next_closed_301 v) = Some (Gval (Fuint 1) (next_raw_word_301 v)).
Proof. unfold next_raw_word_301, next_closed_301, next_expr_301, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_301.
Lemma next_expr_301_value v : eval_hfexpr next_expr_301 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_301 v)).
Proof. change (eval_hfexpr next_expr_301 (next_closed_301 v) (next_closed_301 v) = Some (Gval (Fuint 1) (next_raw_word_301 v))). apply next_closed_301_value. Qed.
Lemma register_write_301 : register_write_certificate 301 (@Sfcnct VarOrder.T (@Eid VarOrder.T 301) next_expr_301) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_301 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 301 after = Some (Gval (Fuint 1) (next_word_301 v)).
Proof.
 have old_found : VM.find 301 old = Some (Gval (Fuint 1) (global_word_54 v)).
 { rewrite (agree 301); [exact (global_lookup_54 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_301 old old = Some (Gval (Fuint 1) (next_raw_word_301 v)).
 { rewrite (scalar_eval_empty_memory next_expr_301 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_301 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_301_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_301 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_301|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_301 v)) (source:=302) (target:=301) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_303 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 304)).
Definition next_closed_303 v : VM.t hvalue := (VM.add 304 (Gval (Fuint 1) (global_word_277 v)) (VM.empty hvalue)).
Definition next_raw_word_303 v := word_of_eval (eval_hfexpr next_expr_303 (next_closed_303 v) (next_closed_303 v)).
Definition next_word_303 v := zext_to 1 (take 1 (next_raw_word_303 v)).
Lemma next_closed_303_value v : eval_hfexpr next_expr_303 (next_closed_303 v) (next_closed_303 v) = Some (Gval (Fuint 1) (next_raw_word_303 v)).
Proof. unfold next_raw_word_303, next_closed_303, next_expr_303, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_303.
Lemma next_expr_303_value v : eval_hfexpr next_expr_303 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_303 v)).
Proof. change (eval_hfexpr next_expr_303 (next_closed_303 v) (next_closed_303 v) = Some (Gval (Fuint 1) (next_raw_word_303 v))). apply next_closed_303_value. Qed.
Lemma register_write_303 : register_write_certificate 303 (@Sfcnct VarOrder.T (@Eid VarOrder.T 303) next_expr_303) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_303 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 303 after = Some (Gval (Fuint 1) (next_word_303 v)).
Proof.
 have old_found : VM.find 303 old = Some (Gval (Fuint 1) (global_word_55 v)).
 { rewrite (agree 303); [exact (global_lookup_55 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_303 old old = Some (Gval (Fuint 1) (next_raw_word_303 v)).
 { rewrite (scalar_eval_empty_memory next_expr_303 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_303 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_303_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_303 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_303|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 1) (next_raw_word_303 v)) (source:=304) (target:=303) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_408 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 409)).
Definition next_closed_408 v : VM.t hvalue := (VM.add 409 (Gval (Fuint 16) (global_word_1297 v)) (VM.empty hvalue)).
Definition next_raw_word_408 v := word_of_eval (eval_hfexpr next_expr_408 (next_closed_408 v) (next_closed_408 v)).
Definition next_word_408 v := zext_to 16 (take 16 (next_raw_word_408 v)).
Lemma next_closed_408_value v : eval_hfexpr next_expr_408 (next_closed_408 v) (next_closed_408 v) = Some (Gval (Fuint 16) (next_raw_word_408 v)).
Proof. unfold next_raw_word_408, next_closed_408, next_expr_408, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_408.
Lemma next_expr_408_value v : eval_hfexpr next_expr_408 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 16) (next_raw_word_408 v)).
Proof. change (eval_hfexpr next_expr_408 (next_closed_408 v) (next_closed_408 v) = Some (Gval (Fuint 16) (next_raw_word_408 v))). apply next_closed_408_value. Qed.
Lemma register_write_408 : register_write_certificate 408 (@Sfcnct VarOrder.T (@Eid VarOrder.T 408) next_expr_408) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_408 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 408 after = Some (Gval (Fuint 16) (next_word_408 v)).
Proof.
 have old_found : VM.find 408 old = Some (Gval (Fuint 16) (global_word_57 v)).
 { rewrite (agree 408); [exact (global_lookup_57 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_408 old old = Some (Gval (Fuint 16) (next_raw_word_408 v)).
 { rewrite (scalar_eval_empty_memory next_expr_408 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_408 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_408_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_408 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_408|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 16) (next_raw_word_408 v)) (source:=409) (target:=408) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_410 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 411))).
Definition next_closed_410 v : VM.t hvalue := (VM.add 411 (Gval (Fuint 1) (global_word_1298 v)) (VM.add 1 (Gval (Fuint 1) (global_word_1 v)) (VM.empty hvalue))).
Definition next_raw_word_410 v := word_of_eval (eval_hfexpr next_expr_410 (next_closed_410 v) (next_closed_410 v)).
Definition next_word_410 v := zext_to 1 (take 1 (next_raw_word_410 v)).
Lemma next_closed_410_value v : eval_hfexpr next_expr_410 (next_closed_410 v) (next_closed_410 v) = Some (Gval (Fuint 1) (next_raw_word_410 v)).
Proof. unfold next_raw_word_410, next_closed_410, next_expr_410, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_410.
Lemma next_expr_410_value v : eval_hfexpr next_expr_410 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_410 v)).
Proof. change (eval_hfexpr next_expr_410 (next_closed_410 v) (next_closed_410 v) = Some (Gval (Fuint 1) (next_raw_word_410 v))). apply next_closed_410_value. Qed.
Lemma register_write_410 : register_write_certificate 410 (@Sfcnct VarOrder.T (@Eid VarOrder.T 410) next_expr_410) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_410 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 410 after = Some (Gval (Fuint 1) (next_word_410 v)).
Proof.
 have old_found : VM.find 410 old = Some (Gval (Fuint 1) (global_word_58 v)).
 { rewrite (agree 410); [exact (global_lookup_58 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_410 old old = Some (Gval (Fuint 1) (next_raw_word_410 v)).
 { rewrite (scalar_eval_empty_memory next_expr_410 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_410 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_410_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_410 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_410|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply unidirectional_eid_target with (expr:=next_expr_410) (value:=Gval (Fuint 1) (next_raw_word_410 v)) (ground:=Fuint 1) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old) (set_regs:=true).
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - reflexivity.
 - eapply one_statement_nonref; [reflexivity|exact step].
Qed.
Definition next_expr_416 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 6)).
Definition next_closed_416 v : VM.t hvalue := (VM.add 6 (Gval (Fuint 16) (global_word_1299 v)) (VM.empty hvalue)).
Definition next_raw_word_416 v := word_of_eval (eval_hfexpr next_expr_416 (next_closed_416 v) (next_closed_416 v)).
Definition next_word_416 v := zext_to 16 (take 16 (next_raw_word_416 v)).
Lemma next_closed_416_value v : eval_hfexpr next_expr_416 (next_closed_416 v) (next_closed_416 v) = Some (Gval (Fuint 16) (next_raw_word_416 v)).
Proof. unfold next_raw_word_416, next_closed_416, next_expr_416, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_416.
Lemma next_expr_416_value v : eval_hfexpr next_expr_416 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 16) (next_raw_word_416 v)).
Proof. change (eval_hfexpr next_expr_416 (next_closed_416 v) (next_closed_416 v) = Some (Gval (Fuint 16) (next_raw_word_416 v))). apply next_closed_416_value. Qed.
Lemma register_write_416 : register_write_certificate 416 (@Sfcnct VarOrder.T (@Eid VarOrder.T 416) next_expr_416) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_416 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 416 after = Some (Gval (Fuint 16) (next_word_416 v)).
Proof.
 have old_found : VM.find 416 old = Some (Gval (Fuint 16) (global_word_59 v)).
 { rewrite (agree 416); [exact (global_lookup_59 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_416 old old = Some (Gval (Fuint 16) (next_raw_word_416 v)).
 { rewrite (scalar_eval_empty_memory next_expr_416 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_416 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_416_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_416 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_416|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint 16) (next_raw_word_416 v)) (source:=6) (target:=416) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | |reflexivity|].
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Definition next_expr_419 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 418))).
Definition next_closed_419 v : VM.t hvalue := (VM.add 418 (Gval (Fuint 1) (global_word_1305 v)) (VM.add 1 (Gval (Fuint 1) (global_word_1 v)) (VM.empty hvalue))).
Definition next_raw_word_419 v := word_of_eval (eval_hfexpr next_expr_419 (next_closed_419 v) (next_closed_419 v)).
Definition next_word_419 v := zext_to 1 (take 1 (next_raw_word_419 v)).
Lemma next_closed_419_value v : eval_hfexpr next_expr_419 (next_closed_419 v) (next_closed_419 v) = Some (Gval (Fuint 1) (next_raw_word_419 v)).
Proof. unfold next_raw_word_419, next_closed_419, next_expr_419, word_of_eval.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground.
 repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end;
 cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type];
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]];
 cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity.
Qed.
Opaque next_raw_word_419.
Lemma next_expr_419_value v : eval_hfexpr next_expr_419 (global_env_root v) (global_env_root v) = Some (Gval (Fuint 1) (next_raw_word_419 v)).
Proof. change (eval_hfexpr next_expr_419 (next_closed_419 v) (next_closed_419 v) = Some (Gval (Fuint 1) (next_raw_word_419 v))). apply next_closed_419_value. Qed.
Lemma register_write_419 : register_write_certificate 419 (@Sfcnct VarOrder.T (@Eid VarOrder.T 419) next_expr_419) generated_module_3_stmts_0.
Proof. apply checked_register_writer_sound. vm_compute. reflexivity.
Qed.
Lemma commit_register_419 invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 VM.find 419 after = Some (Gval (Fuint 1) (next_word_419 v)).
Proof.
 have old_found : VM.find 419 old = Some (Gval (Fuint 1) (global_word_60 v)).
 { rewrite (agree 419); [exact (global_lookup_60 v)|vm_compute; intuition congruence]. }
 have evaluated : eval_hfexpr_with_memory empty_memory_map next_expr_419 old old = Some (Gval (Fuint 1) (next_raw_word_419 v)).
 { rewrite (scalar_eval_empty_memory next_expr_419 old old (Logic.eq_refl true)).
    rewrite (scalar_eval_extensional next_expr_419 old (global_env_root v) old (global_env_root v) (Logic.eq_refl true)); [exact (next_expr_419_value v)|].
    intros dep occurs. apply agree. cbn [next_expr_419 scalar_refs List.In] in occurs.
    repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; vm_compute; intuition congruence. }
 eapply pass_register_write_value; [exact register_write_419|exact old_found|reflexivity|exact (multiplier_resets_inert old)| |exact ran].
 intros position initial final found step.
 eapply unidirectional_eid_target with (expr:=next_expr_419) (value:=Gval (Fuint 1) (next_raw_word_419 v)) (ground:=Fuint 1) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old) (set_regs:=true).
 - cbn [eval_type_of_ref]. rewrite found. reflexivity.
 - exact evaluated.
 - reflexivity.
 - eapply one_statement_nonref; [reflexivity|exact step].
Qed.
Definition next_register_value v (id:N) : hvalue := match id with
 | 201 => Gval (Fuint 1) (next_word_201 v)
 | 203 => Gval (Fuint 1) (next_word_203 v)
 | 205 => Gval (Fuint 1) (next_word_205 v)
 | 207 => Gval (Fuint 1) (next_word_207 v)
 | 209 => Gval (Fuint 1) (next_word_209 v)
 | 211 => Gval (Fuint 1) (next_word_211 v)
 | 213 => Gval (Fuint 1) (next_word_213 v)
 | 215 => Gval (Fuint 1) (next_word_215 v)
 | 217 => Gval (Fuint 1) (next_word_217 v)
 | 219 => Gval (Fuint 1) (next_word_219 v)
 | 221 => Gval (Fuint 1) (next_word_221 v)
 | 223 => Gval (Fuint 1) (next_word_223 v)
 | 225 => Gval (Fuint 1) (next_word_225 v)
 | 227 => Gval (Fuint 1) (next_word_227 v)
 | 229 => Gval (Fuint 1) (next_word_229 v)
 | 231 => Gval (Fuint 1) (next_word_231 v)
 | 233 => Gval (Fuint 1) (next_word_233 v)
 | 235 => Gval (Fuint 1) (next_word_235 v)
 | 237 => Gval (Fuint 1) (next_word_237 v)
 | 239 => Gval (Fuint 1) (next_word_239 v)
 | 241 => Gval (Fuint 1) (next_word_241 v)
 | 243 => Gval (Fuint 1) (next_word_243 v)
 | 245 => Gval (Fuint 1) (next_word_245 v)
 | 247 => Gval (Fuint 1) (next_word_247 v)
 | 249 => Gval (Fuint 1) (next_word_249 v)
 | 251 => Gval (Fuint 1) (next_word_251 v)
 | 253 => Gval (Fuint 1) (next_word_253 v)
 | 255 => Gval (Fuint 1) (next_word_255 v)
 | 257 => Gval (Fuint 1) (next_word_257 v)
 | 259 => Gval (Fuint 1) (next_word_259 v)
 | 261 => Gval (Fuint 1) (next_word_261 v)
 | 263 => Gval (Fuint 1) (next_word_263 v)
 | 265 => Gval (Fuint 1) (next_word_265 v)
 | 267 => Gval (Fuint 1) (next_word_267 v)
 | 269 => Gval (Fuint 1) (next_word_269 v)
 | 271 => Gval (Fuint 1) (next_word_271 v)
 | 273 => Gval (Fuint 1) (next_word_273 v)
 | 275 => Gval (Fuint 1) (next_word_275 v)
 | 277 => Gval (Fuint 1) (next_word_277 v)
 | 279 => Gval (Fuint 1) (next_word_279 v)
 | 281 => Gval (Fuint 1) (next_word_281 v)
 | 283 => Gval (Fuint 1) (next_word_283 v)
 | 285 => Gval (Fuint 1) (next_word_285 v)
 | 287 => Gval (Fuint 1) (next_word_287 v)
 | 289 => Gval (Fuint 1) (next_word_289 v)
 | 291 => Gval (Fuint 1) (next_word_291 v)
 | 293 => Gval (Fuint 1) (next_word_293 v)
 | 295 => Gval (Fuint 1) (next_word_295 v)
 | 297 => Gval (Fuint 1) (next_word_297 v)
 | 299 => Gval (Fuint 1) (next_word_299 v)
 | 301 => Gval (Fuint 1) (next_word_301 v)
 | 303 => Gval (Fuint 1) (next_word_303 v)
 | 408 => Gval (Fuint 16) (next_word_408 v)
 | 410 => Gval (Fuint 1) (next_word_410 v)
 | 416 => Gval (Fuint 16) (next_word_416 v)
 | 419 => Gval (Fuint 1) (next_word_419 v)
 | _ => Needtobedefined (Gtyp (Fuint 0)) end.
Definition multiplier_committed v (env:VM.t hvalue) := forall id, List.In id [:: 201; 203; 205; 207; 209; 211; 213; 215; 217; 219; 221; 223; 225; 227; 229; 231; 233; 235; 237; 239; 241; 243; 245; 247; 249; 251; 253; 255; 257; 259; 261; 263; 265; 267; 269; 271; 273; 275; 277; 279; 281; 283; 285; 287; 289; 291; 293; 295; 297; 299; 301; 303; 408; 410; 416; 419] -> VM.find id env = Some (next_register_value v id).
Lemma multiplier_commit_values invalid v old before after
 (agree : forall dep, root_domain dep -> VM.find dep old = VM.find dep (global_env_root v))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old true before generated_module_3_stmts_0 = Some after) :
 multiplier_committed v after.
Proof. intros id inside.
 destruct inside as [same|inside]; [subst id; exact (commit_register_201 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_203 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_205 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_207 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_209 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_211 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_213 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_215 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_217 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_219 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_221 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_223 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_225 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_227 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_229 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_231 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_233 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_235 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_237 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_239 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_241 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_243 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_245 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_247 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_249 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_251 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_253 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_255 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_257 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_259 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_261 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_263 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_265 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_267 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_269 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_271 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_273 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_275 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_277 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_279 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_281 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_283 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_285 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_287 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_289 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_291 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_293 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_295 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_297 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_299 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_301 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_303 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_408 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_410 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_416 invalid v old before after agree ran)|].
 destruct inside as [same|inside]; [subst id; exact (commit_register_419 invalid v old before after agree ran)|].
 contradiction.
Qed.
Print Assumptions multiplier_commit_values.

(* Generated local certificates from the unchanged deep AST. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.
Lemma refine_ground known t b : refine_boolean_result known (Some (Gval t b)) = Some (Gval t b).
Proof. destruct known; reflexivity. Qed.
Definition leaf_values := N -> N -> bits.
Definition word_of_eval (v : option hvalue) : bits := match v with Some (Gval _ b) => b | _ => [::] end.

Definition word_0 (v : leaf_values) := v 0 0.
Definition word_1 (v : leaf_values) := v 0 1.
Definition word_2 (v : leaf_values) := v 0 2.
Definition word_3 (v : leaf_values) := v 0 3.
Definition expr_word_6 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_6 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 1) (word_2 v)) (VM.empty hvalue)).
Definition word_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_6 (closed_word_6 v) (closed_word_6 v)).
Definition expr_word_7 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 3))).
Definition closed_word_7 (v : leaf_values) : VM.t hvalue := (VM.add 3 (Gval (Fuint 1) (word_3 v)) (VM.empty hvalue)).
Definition word_7 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_7 (closed_word_7 v) (closed_word_7 v)).
Definition expr_word_8 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6)) (@Eref VarOrder.T (@Eid VarOrder.T 7))).
Definition closed_word_8 (v : leaf_values) : VM.t hvalue := (VM.add 7 (Gval (Fuint 4) (word_7 v)) (VM.add 6 (Gval (Fuint 4) (word_6 v)) (VM.empty hvalue))).
Definition word_8 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_8 (closed_word_8 v) (closed_word_8 v)).
Definition expr_word_9 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 8))).
Definition closed_word_9 (v : leaf_values) : VM.t hvalue := (VM.add 8 (Gval (Fuint 5) (word_8 v)) (VM.empty hvalue)).
Definition word_9 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_9 (closed_word_9 v) (closed_word_9 v)).
Definition expr_word_19 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_19 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 1) (word_2 v)) (VM.empty hvalue)).
Definition word_19 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_19 (closed_word_19 v) (closed_word_19 v)).
Definition expr_word_20 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 3))).
Definition closed_word_20 (v : leaf_values) : VM.t hvalue := (VM.add 3 (Gval (Fuint 1) (word_3 v)) (VM.empty hvalue)).
Definition word_20 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_20 (closed_word_20 v) (closed_word_20 v)).
Definition expr_word_21 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 19)) (@Eref VarOrder.T (@Eid VarOrder.T 20))).
Definition closed_word_21 (v : leaf_values) : VM.t hvalue := (VM.add 20 (Gval (Fuint 1) (word_20 v)) (VM.add 19 (Gval (Fuint 1) (word_19 v)) (VM.empty hvalue))).
Definition word_21 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_21 (closed_word_21 v) (closed_word_21 v)).
Definition expr_word_22 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 19)) (@Eref VarOrder.T (@Eid VarOrder.T 20))).
Definition closed_word_22 (v : leaf_values) : VM.t hvalue := (VM.add 20 (Gval (Fuint 1) (word_20 v)) (VM.add 19 (Gval (Fuint 1) (word_19 v)) (VM.empty hvalue))).
Definition word_22 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_22 (closed_word_22 v) (closed_word_22 v)).
Definition expr_word_23 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 22)) (@Eref VarOrder.T (@Eid VarOrder.T 21))).
Definition closed_word_23 (v : leaf_values) : VM.t hvalue := (VM.add 22 (Gval (Fuint 1) (word_22 v)) (VM.add 21 (Gval (Fuint 1) (word_21 v)) (VM.empty hvalue))).
Definition word_23 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_23 (closed_word_23 v) (closed_word_23 v)).
Definition expr_word_24 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 23)).
Definition closed_word_24 (v : leaf_values) : VM.t hvalue := (VM.add 23 (Gval (Fuint 2) (word_23 v)) (VM.empty hvalue)).
Definition word_24 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_24 (closed_word_24 v) (closed_word_24 v)).
Definition expr_word_25 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 24))).
Definition closed_word_25 (v : leaf_values) : VM.t hvalue := (VM.add 24 (Gval (Fuint 2) (word_24 v)) (VM.empty hvalue)).
Definition word_25 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_25 (closed_word_25 v) (closed_word_25 v)).
Definition expr_word_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 25)).
Definition closed_word_4 (v : leaf_values) : VM.t hvalue := (VM.add 25 (Gval (Fuint 1) (word_25 v)) (VM.empty hvalue)).
Definition word_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_4 (closed_word_4 v) (closed_word_4 v)).
Definition expr_word_10 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 4))).
Definition closed_word_10 (v : leaf_values) : VM.t hvalue := (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)).
Definition word_10 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_10 (closed_word_10 v) (closed_word_10 v)).
Definition expr_word_26 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 24))).
Definition closed_word_26 (v : leaf_values) : VM.t hvalue := (VM.add 24 (Gval (Fuint 2) (word_24 v)) (VM.empty hvalue)).
Definition word_26 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_26 (closed_word_26 v) (closed_word_26 v)).
Definition expr_word_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 26)).
Definition closed_word_5 (v : leaf_values) : VM.t hvalue := (VM.add 26 (Gval (Fuint 1) (word_26 v)) (VM.empty hvalue)).
Definition word_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_5 (closed_word_5 v) (closed_word_5 v)).
Definition expr_word_11 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 5))).
Definition closed_word_11 (v : leaf_values) : VM.t hvalue := (VM.add 5 (Gval (Fuint 1) (word_5 v)) (VM.empty hvalue)).
Definition word_11 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_11 (closed_word_11 v) (closed_word_11 v)).
Definition expr_word_12 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 11))).
Definition closed_word_12 (v : leaf_values) : VM.t hvalue := (VM.add 11 (Gval (Fuint 4) (word_11 v)) (VM.empty hvalue)).
Definition word_12 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_12 (closed_word_12 v) (closed_word_12 v)).
Definition expr_word_13 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 10)) (@Eref VarOrder.T (@Eid VarOrder.T 12))).
Definition closed_word_13 (v : leaf_values) : VM.t hvalue := (VM.add 12 (Gval (Fuint 5) (word_12 v)) (VM.add 10 (Gval (Fuint 4) (word_10 v)) (VM.empty hvalue))).
Definition word_13 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_13 (closed_word_13 v) (closed_word_13 v)).
Definition expr_word_14 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 13))).
Definition closed_word_14 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 6) (word_13 v)) (VM.empty hvalue)).
Definition word_14 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_14 (closed_word_14 v) (closed_word_14 v)).
Definition expr_word_15 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 9)) (@Eref VarOrder.T (@Eid VarOrder.T 14))).
Definition closed_word_15 (v : leaf_values) : VM.t hvalue := (VM.add 14 (Gval (Fuint 5) (word_14 v)) (VM.add 9 (Gval (Fuint 4) (word_9 v)) (VM.empty hvalue))).
Definition word_15 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_15 (closed_word_15 v) (closed_word_15 v)).
Definition expr_word_16 : @hfexpr VarOrder.T := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_word_16 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_16 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_16 (closed_word_16 v) (closed_word_16 v)).
Definition expr_word_17 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_17 (v : leaf_values) : VM.t hvalue := (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)).
Definition word_17 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_17 (closed_word_17 v) (closed_word_17 v)).
Definition expr_word_18 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 15)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_18 (v : leaf_values) : VM.t hvalue := (VM.add 15 (Gval (Fuint 1) (word_15 v)) (VM.empty hvalue)).
Definition word_18 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_18 (closed_word_18 v) (closed_word_18 v)).
Opaque word_0 word_1 word_2 word_3 word_4 word_5 word_6 word_7 word_8 word_9 word_10 word_11 word_12 word_13 word_14 word_15 word_16 word_17 word_18 word_19 word_20 word_21 word_22 word_23 word_24 word_25 word_26.
Definition stable_shape (values : N -> hvalue) : VM.t hvalue := Eval vm_compute in
 (VM.add 26 (values 26) (VM.add 25 (values 25) (VM.add 24 (values 24) (VM.add 23 (values 23) (VM.add 22 (values 22) (VM.add 21 (values 21) (VM.add 20 (values 20) (VM.add 19 (values 19) (VM.add 18 (values 18) (VM.add 17 (values 17) (VM.add 16 (values 16) (VM.add 15 (values 15) (VM.add 14 (values 14) (VM.add 13 (values 13) (VM.add 12 (values 12) (VM.add 11 (values 11) (VM.add 10 (values 10) (VM.add 9 (values 9) (VM.add 8 (values 8) (VM.add 7 (values 7) (VM.add 6 (values 6) (VM.add 5 (values 5) (VM.add 4 (values 4) (VM.add 3 (values 3) (VM.add 2 (values 2) (VM.add 1 (values 1) (VM.add 0 (values 0) (VM.empty hvalue)))))))))))))))))))))))))))).
Definition stable_values (v : leaf_values) (id : N) : hvalue := match id with
| 0 => (Gval Fclock (word_0 v))
| 1 => (Gval (Fuint 1) (word_1 v))
| 2 => (Gval (Fuint 1) (word_2 v))
| 3 => (Gval (Fuint 1) (word_3 v))
| 4 => (Gval (Fuint 1) (word_4 v))
| 5 => (Gval (Fuint 1) (word_5 v))
| 6 => (Gval (Fuint 4) (word_6 v))
| 7 => (Gval (Fuint 4) (word_7 v))
| 8 => (Gval (Fuint 5) (word_8 v))
| 9 => (Gval (Fuint 4) (word_9 v))
| 10 => (Gval (Fuint 4) (word_10 v))
| 11 => (Gval (Fuint 4) (word_11 v))
| 12 => (Gval (Fuint 5) (word_12 v))
| 13 => (Gval (Fuint 6) (word_13 v))
| 14 => (Gval (Fuint 5) (word_14 v))
| 15 => (Gval (Fuint 1) (word_15 v))
| 16 => (Gval (Fuint 1) (word_16 v))
| 17 => (Gval (Fuint 1) (word_17 v))
| 18 => (Gval (Fuint 1) (word_18 v))
| 19 => (Gval (Fuint 1) (word_19 v))
| 20 => (Gval (Fuint 1) (word_20 v))
| 21 => (Gval (Fuint 1) (word_21 v))
| 22 => (Gval (Fuint 1) (word_22 v))
| 23 => (Gval (Fuint 2) (word_23 v))
| 24 => (Gval (Fuint 2) (word_24 v))
| 25 => (Gval (Fuint 1) (word_25 v))
| 26 => (Gval (Fuint 1) (word_26 v))
| _ => Needtobedefined (Gtyp (Fuint 0)) end.
Definition stable_env v := stable_shape (stable_values v).
Transparent word_6.
Lemma closed_word_6_value v : eval_hfexpr expr_word_6 (closed_word_6 v) (closed_word_6 v) = Some (Gval (Fuint 4) (word_6 v)).
Proof. unfold word_6, closed_word_6, expr_word_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_6.
Lemma node_word_6_value v : eval_hfexpr expr_word_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_6 v)).
Proof. change (eval_hfexpr expr_word_6 (closed_word_6 v) (closed_word_6 v) = Some (Gval (Fuint 4) (word_6 v))). apply closed_word_6_value. Qed.
Transparent word_7.
Lemma closed_word_7_value v : eval_hfexpr expr_word_7 (closed_word_7 v) (closed_word_7 v) = Some (Gval (Fuint 4) (word_7 v)).
Proof. unfold word_7, closed_word_7, expr_word_7, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_7.
Lemma node_word_7_value v : eval_hfexpr expr_word_7 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_7 v)).
Proof. change (eval_hfexpr expr_word_7 (closed_word_7 v) (closed_word_7 v) = Some (Gval (Fuint 4) (word_7 v))). apply closed_word_7_value. Qed.
Transparent word_8.
Lemma closed_word_8_value v : eval_hfexpr expr_word_8 (closed_word_8 v) (closed_word_8 v) = Some (Gval (Fuint 5) (word_8 v)).
Proof. unfold word_8, closed_word_8, expr_word_8, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_8.
Lemma node_word_8_value v : eval_hfexpr expr_word_8 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_8 v)).
Proof. change (eval_hfexpr expr_word_8 (closed_word_8 v) (closed_word_8 v) = Some (Gval (Fuint 5) (word_8 v))). apply closed_word_8_value. Qed.
Transparent word_9.
Lemma closed_word_9_value v : eval_hfexpr expr_word_9 (closed_word_9 v) (closed_word_9 v) = Some (Gval (Fuint 4) (word_9 v)).
Proof. unfold word_9, closed_word_9, expr_word_9, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_9.
Lemma node_word_9_value v : eval_hfexpr expr_word_9 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_9 v)).
Proof. change (eval_hfexpr expr_word_9 (closed_word_9 v) (closed_word_9 v) = Some (Gval (Fuint 4) (word_9 v))). apply closed_word_9_value. Qed.
Transparent word_19.
Lemma closed_word_19_value v : eval_hfexpr expr_word_19 (closed_word_19 v) (closed_word_19 v) = Some (Gval (Fuint 1) (word_19 v)).
Proof. unfold word_19, closed_word_19, expr_word_19, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_19.
Lemma node_word_19_value v : eval_hfexpr expr_word_19 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_19 v)).
Proof. change (eval_hfexpr expr_word_19 (closed_word_19 v) (closed_word_19 v) = Some (Gval (Fuint 1) (word_19 v))). apply closed_word_19_value. Qed.
Transparent word_20.
Lemma closed_word_20_value v : eval_hfexpr expr_word_20 (closed_word_20 v) (closed_word_20 v) = Some (Gval (Fuint 1) (word_20 v)).
Proof. unfold word_20, closed_word_20, expr_word_20, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_20.
Lemma node_word_20_value v : eval_hfexpr expr_word_20 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_20 v)).
Proof. change (eval_hfexpr expr_word_20 (closed_word_20 v) (closed_word_20 v) = Some (Gval (Fuint 1) (word_20 v))). apply closed_word_20_value. Qed.
Transparent word_21.
Lemma closed_word_21_value v : eval_hfexpr expr_word_21 (closed_word_21 v) (closed_word_21 v) = Some (Gval (Fuint 1) (word_21 v)).
Proof. unfold word_21, closed_word_21, expr_word_21, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_21.
Lemma node_word_21_value v : eval_hfexpr expr_word_21 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_21 v)).
Proof. change (eval_hfexpr expr_word_21 (closed_word_21 v) (closed_word_21 v) = Some (Gval (Fuint 1) (word_21 v))). apply closed_word_21_value. Qed.
Transparent word_22.
Lemma closed_word_22_value v : eval_hfexpr expr_word_22 (closed_word_22 v) (closed_word_22 v) = Some (Gval (Fuint 1) (word_22 v)).
Proof. unfold word_22, closed_word_22, expr_word_22, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_22.
Lemma node_word_22_value v : eval_hfexpr expr_word_22 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_22 v)).
Proof. change (eval_hfexpr expr_word_22 (closed_word_22 v) (closed_word_22 v) = Some (Gval (Fuint 1) (word_22 v))). apply closed_word_22_value. Qed.
Transparent word_23.
Lemma closed_word_23_value v : eval_hfexpr expr_word_23 (closed_word_23 v) (closed_word_23 v) = Some (Gval (Fuint 2) (word_23 v)).
Proof. unfold word_23, closed_word_23, expr_word_23, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_23.
Lemma node_word_23_value v : eval_hfexpr expr_word_23 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_23 v)).
Proof. change (eval_hfexpr expr_word_23 (closed_word_23 v) (closed_word_23 v) = Some (Gval (Fuint 2) (word_23 v))). apply closed_word_23_value. Qed.
Transparent word_24.
Lemma closed_word_24_value v : eval_hfexpr expr_word_24 (closed_word_24 v) (closed_word_24 v) = Some (Gval (Fuint 2) (word_24 v)).
Proof. unfold word_24, closed_word_24, expr_word_24, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_24.
Lemma node_word_24_value v : eval_hfexpr expr_word_24 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_24 v)).
Proof. change (eval_hfexpr expr_word_24 (closed_word_24 v) (closed_word_24 v) = Some (Gval (Fuint 2) (word_24 v))). apply closed_word_24_value. Qed.
Transparent word_25.
Lemma closed_word_25_value v : eval_hfexpr expr_word_25 (closed_word_25 v) (closed_word_25 v) = Some (Gval (Fuint 1) (word_25 v)).
Proof. unfold word_25, closed_word_25, expr_word_25, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_25.
Lemma node_word_25_value v : eval_hfexpr expr_word_25 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_25 v)).
Proof. change (eval_hfexpr expr_word_25 (closed_word_25 v) (closed_word_25 v) = Some (Gval (Fuint 1) (word_25 v))). apply closed_word_25_value. Qed.
Transparent word_4.
Lemma closed_word_4_value v : eval_hfexpr expr_word_4 (closed_word_4 v) (closed_word_4 v) = Some (Gval (Fuint 1) (word_4 v)).
Proof. unfold word_4, closed_word_4, expr_word_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_4.
Lemma node_word_4_value v : eval_hfexpr expr_word_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_4 v)).
Proof. change (eval_hfexpr expr_word_4 (closed_word_4 v) (closed_word_4 v) = Some (Gval (Fuint 1) (word_4 v))). apply closed_word_4_value. Qed.
Transparent word_10.
Lemma closed_word_10_value v : eval_hfexpr expr_word_10 (closed_word_10 v) (closed_word_10 v) = Some (Gval (Fuint 4) (word_10 v)).
Proof. unfold word_10, closed_word_10, expr_word_10, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_10.
Lemma node_word_10_value v : eval_hfexpr expr_word_10 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_10 v)).
Proof. change (eval_hfexpr expr_word_10 (closed_word_10 v) (closed_word_10 v) = Some (Gval (Fuint 4) (word_10 v))). apply closed_word_10_value. Qed.
Transparent word_26.
Lemma closed_word_26_value v : eval_hfexpr expr_word_26 (closed_word_26 v) (closed_word_26 v) = Some (Gval (Fuint 1) (word_26 v)).
Proof. unfold word_26, closed_word_26, expr_word_26, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_26.
Lemma node_word_26_value v : eval_hfexpr expr_word_26 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_26 v)).
Proof. change (eval_hfexpr expr_word_26 (closed_word_26 v) (closed_word_26 v) = Some (Gval (Fuint 1) (word_26 v))). apply closed_word_26_value. Qed.
Transparent word_5.
Lemma closed_word_5_value v : eval_hfexpr expr_word_5 (closed_word_5 v) (closed_word_5 v) = Some (Gval (Fuint 1) (word_5 v)).
Proof. unfold word_5, closed_word_5, expr_word_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_5.
Lemma node_word_5_value v : eval_hfexpr expr_word_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_5 v)).
Proof. change (eval_hfexpr expr_word_5 (closed_word_5 v) (closed_word_5 v) = Some (Gval (Fuint 1) (word_5 v))). apply closed_word_5_value. Qed.
Transparent word_11.
Lemma closed_word_11_value v : eval_hfexpr expr_word_11 (closed_word_11 v) (closed_word_11 v) = Some (Gval (Fuint 4) (word_11 v)).
Proof. unfold word_11, closed_word_11, expr_word_11, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_11.
Lemma node_word_11_value v : eval_hfexpr expr_word_11 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_11 v)).
Proof. change (eval_hfexpr expr_word_11 (closed_word_11 v) (closed_word_11 v) = Some (Gval (Fuint 4) (word_11 v))). apply closed_word_11_value. Qed.
Transparent word_12.
Lemma closed_word_12_value v : eval_hfexpr expr_word_12 (closed_word_12 v) (closed_word_12 v) = Some (Gval (Fuint 5) (word_12 v)).
Proof. unfold word_12, closed_word_12, expr_word_12, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_12.
Lemma node_word_12_value v : eval_hfexpr expr_word_12 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_12 v)).
Proof. change (eval_hfexpr expr_word_12 (closed_word_12 v) (closed_word_12 v) = Some (Gval (Fuint 5) (word_12 v))). apply closed_word_12_value. Qed.
Transparent word_13.
Lemma closed_word_13_value v : eval_hfexpr expr_word_13 (closed_word_13 v) (closed_word_13 v) = Some (Gval (Fuint 6) (word_13 v)).
Proof. unfold word_13, closed_word_13, expr_word_13, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_13.
Lemma node_word_13_value v : eval_hfexpr expr_word_13 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_13 v)).
Proof. change (eval_hfexpr expr_word_13 (closed_word_13 v) (closed_word_13 v) = Some (Gval (Fuint 6) (word_13 v))). apply closed_word_13_value. Qed.
Transparent word_14.
Lemma closed_word_14_value v : eval_hfexpr expr_word_14 (closed_word_14 v) (closed_word_14 v) = Some (Gval (Fuint 5) (word_14 v)).
Proof. unfold word_14, closed_word_14, expr_word_14, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_14.
Lemma node_word_14_value v : eval_hfexpr expr_word_14 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_14 v)).
Proof. change (eval_hfexpr expr_word_14 (closed_word_14 v) (closed_word_14 v) = Some (Gval (Fuint 5) (word_14 v))). apply closed_word_14_value. Qed.
Transparent word_15.
Lemma closed_word_15_value v : eval_hfexpr expr_word_15 (closed_word_15 v) (closed_word_15 v) = Some (Gval (Fuint 1) (word_15 v)).
Proof. unfold word_15, closed_word_15, expr_word_15, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_15.
Lemma node_word_15_value v : eval_hfexpr expr_word_15 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_15 v)).
Proof. change (eval_hfexpr expr_word_15 (closed_word_15 v) (closed_word_15 v) = Some (Gval (Fuint 1) (word_15 v))). apply closed_word_15_value. Qed.
Transparent word_16.
Lemma closed_word_16_value v : eval_hfexpr expr_word_16 (closed_word_16 v) (closed_word_16 v) = Some (Gval (Fuint 1) (word_16 v)).
Proof. unfold word_16, closed_word_16, expr_word_16, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_16.
Lemma node_word_16_value v : eval_hfexpr expr_word_16 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_16 v)).
Proof. change (eval_hfexpr expr_word_16 (closed_word_16 v) (closed_word_16 v) = Some (Gval (Fuint 1) (word_16 v))). apply closed_word_16_value. Qed.
Transparent word_17.
Lemma closed_word_17_value v : eval_hfexpr expr_word_17 (closed_word_17 v) (closed_word_17 v) = Some (Gval (Fuint 1) (word_17 v)).
Proof. unfold word_17, closed_word_17, expr_word_17, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_17.
Lemma node_word_17_value v : eval_hfexpr expr_word_17 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_17 v)).
Proof. change (eval_hfexpr expr_word_17 (closed_word_17 v) (closed_word_17 v) = Some (Gval (Fuint 1) (word_17 v))). apply closed_word_17_value. Qed.
Transparent word_18.
Lemma closed_word_18_value v : eval_hfexpr expr_word_18 (closed_word_18 v) (closed_word_18 v) = Some (Gval (Fuint 1) (word_18 v)).
Proof. unfold word_18, closed_word_18, expr_word_18, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_18.
Lemma node_word_18_value v : eval_hfexpr expr_word_18 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_18 v)).
Proof. change (eval_hfexpr expr_word_18 (closed_word_18 v) (closed_word_18 v) = Some (Gval (Fuint 1) (word_18 v))). apply closed_word_18_value. Qed.

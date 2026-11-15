From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Child2Stable.
Local Open Scope N_scope.
Lemma local_word_12_value v env
 (H0 : VM.find 2 env = Some (Gval (Fuint 1) (word_2 v)))
 : eval_hfexpr expr_word_12 env env = Some (Gval (Fuint 4) (word_12 v)).
Proof. rewrite - (closed_word_12_value v). unfold expr_word_12, closed_word_12.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_13_value v env
 (H0 : VM.find 3 env = Some (Gval (Fuint 1) (word_3 v)))
 : eval_hfexpr expr_word_13 env env = Some (Gval (Fuint 4) (word_13 v)).
Proof. rewrite - (closed_word_13_value v). unfold expr_word_13, closed_word_13.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_14_value v env
 (H0 : VM.find 4 env = Some (Gval (Fuint 1) (word_4 v)))
 : eval_hfexpr expr_word_14 env env = Some (Gval (Fuint 4) (word_14 v)).
Proof. rewrite - (closed_word_14_value v). unfold expr_word_14, closed_word_14.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_15_value v env
 (H0 : VM.find 5 env = Some (Gval (Fuint 1) (word_5 v)))
 : eval_hfexpr expr_word_15 env env = Some (Gval (Fuint 4) (word_15 v)).
Proof. rewrite - (closed_word_15_value v). unfold expr_word_15, closed_word_15.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_16_value v env
 (H0 : VM.find 6 env = Some (Gval (Fuint 1) (word_6 v)))
 : eval_hfexpr expr_word_16 env env = Some (Gval (Fuint 4) (word_16 v)).
Proof. rewrite - (closed_word_16_value v). unfold expr_word_16, closed_word_16.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_17_value v env
 (H0 : VM.find 12 env = Some (Gval (Fuint 4) (word_12 v)))
 (H1 : VM.find 13 env = Some (Gval (Fuint 4) (word_13 v)))
 : eval_hfexpr expr_word_17 env env = Some (Gval (Fuint 5) (word_17 v)).
Proof. rewrite - (closed_word_17_value v). unfold expr_word_17, closed_word_17.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_18_value v env
 (H0 : VM.find 17 env = Some (Gval (Fuint 5) (word_17 v)))
 : eval_hfexpr expr_word_18 env env = Some (Gval (Fuint 4) (word_18 v)).
Proof. rewrite - (closed_word_18_value v). unfold expr_word_18, closed_word_18.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_19_value v env
 (H0 : VM.find 14 env = Some (Gval (Fuint 4) (word_14 v)))
 (H1 : VM.find 18 env = Some (Gval (Fuint 4) (word_18 v)))
 : eval_hfexpr expr_word_19 env env = Some (Gval (Fuint 5) (word_19 v)).
Proof. rewrite - (closed_word_19_value v). unfold expr_word_19, closed_word_19.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_20_value v env
 (H0 : VM.find 19 env = Some (Gval (Fuint 5) (word_19 v)))
 : eval_hfexpr expr_word_20 env env = Some (Gval (Fuint 4) (word_20 v)).
Proof. rewrite - (closed_word_20_value v). unfold expr_word_20, closed_word_20.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_21_value v env
 (H0 : VM.find 15 env = Some (Gval (Fuint 4) (word_15 v)))
 (H1 : VM.find 20 env = Some (Gval (Fuint 4) (word_20 v)))
 : eval_hfexpr expr_word_21 env env = Some (Gval (Fuint 5) (word_21 v)).
Proof. rewrite - (closed_word_21_value v). unfold expr_word_21, closed_word_21.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_22_value v env
 (H0 : VM.find 21 env = Some (Gval (Fuint 5) (word_21 v)))
 : eval_hfexpr expr_word_22 env env = Some (Gval (Fuint 4) (word_22 v)).
Proof. rewrite - (closed_word_22_value v). unfold expr_word_22, closed_word_22.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_23_value v env
 (H0 : VM.find 16 env = Some (Gval (Fuint 4) (word_16 v)))
 (H1 : VM.find 22 env = Some (Gval (Fuint 4) (word_22 v)))
 : eval_hfexpr expr_word_23 env env = Some (Gval (Fuint 5) (word_23 v)).
Proof. rewrite - (closed_word_23_value v). unfold expr_word_23, closed_word_23.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_24_value v env
 (H0 : VM.find 23 env = Some (Gval (Fuint 5) (word_23 v)))
 : eval_hfexpr expr_word_24 env env = Some (Gval (Fuint 4) (word_24 v)).
Proof. rewrite - (closed_word_24_value v). unfold expr_word_24, closed_word_24.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_41_value v env
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 5) env env = Some (Gval (Fuint 1) (port_11_5 v)))
 : eval_hfexpr expr_word_41 env env = Some (Gval (Fuint 1) (word_41 v)).
Proof. rewrite - (closed_word_41_value v). unfold expr_word_41, closed_word_41.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_7_value v env
 (H0 : VM.find 41 env = Some (Gval (Fuint 1) (word_41 v)))
 : eval_hfexpr expr_word_7 env env = Some (Gval (Fuint 1) (word_7 v)).
Proof. rewrite - (closed_word_7_value v). unfold expr_word_7, closed_word_7.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_25_value v env
 (H0 : VM.find 7 env = Some (Gval (Fuint 1) (word_7 v)))
 : eval_hfexpr expr_word_25 env env = Some (Gval (Fuint 4) (word_25 v)).
Proof. rewrite - (closed_word_25_value v). unfold expr_word_25, closed_word_25.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_42_value v env
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 6) env env = Some (Gval (Fuint 1) (port_10_6 v)))
 : eval_hfexpr expr_word_42 env env = Some (Gval (Fuint 1) (word_42 v)).
Proof. rewrite - (closed_word_42_value v). unfold expr_word_42, closed_word_42.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_8_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 1) (word_42 v)))
 : eval_hfexpr expr_word_8 env env = Some (Gval (Fuint 1) (word_8 v)).
Proof. rewrite - (closed_word_8_value v). unfold expr_word_8, closed_word_8.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_26_value v env
 (H0 : VM.find 8 env = Some (Gval (Fuint 1) (word_8 v)))
 : eval_hfexpr expr_word_26 env env = Some (Gval (Fuint 4) (word_26 v)).
Proof. rewrite - (closed_word_26_value v). unfold expr_word_26, closed_word_26.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_27_value v env
 (H0 : VM.find 26 env = Some (Gval (Fuint 4) (word_26 v)))
 : eval_hfexpr expr_word_27 env env = Some (Gval (Fuint 5) (word_27 v)).
Proof. rewrite - (closed_word_27_value v). unfold expr_word_27, closed_word_27.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_43_value v env
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 6) env env = Some (Gval (Fuint 1) (port_11_6 v)))
 : eval_hfexpr expr_word_43 env env = Some (Gval (Fuint 1) (word_43 v)).
Proof. rewrite - (closed_word_43_value v). unfold expr_word_43, closed_word_43.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_9_value v env
 (H0 : VM.find 43 env = Some (Gval (Fuint 1) (word_43 v)))
 : eval_hfexpr expr_word_9 env env = Some (Gval (Fuint 1) (word_9 v)).
Proof. rewrite - (closed_word_9_value v). unfold expr_word_9, closed_word_9.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_28_value v env
 (H0 : VM.find 9 env = Some (Gval (Fuint 1) (word_9 v)))
 : eval_hfexpr expr_word_28 env env = Some (Gval (Fuint 4) (word_28 v)).
Proof. rewrite - (closed_word_28_value v). unfold expr_word_28, closed_word_28.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_29_value v env
 (H0 : VM.find 28 env = Some (Gval (Fuint 4) (word_28 v)))
 : eval_hfexpr expr_word_29 env env = Some (Gval (Fuint 5) (word_29 v)).
Proof. rewrite - (closed_word_29_value v). unfold expr_word_29, closed_word_29.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_30_value v env
 (H0 : VM.find 25 env = Some (Gval (Fuint 4) (word_25 v)))
 (H1 : VM.find 27 env = Some (Gval (Fuint 5) (word_27 v)))
 : eval_hfexpr expr_word_30 env env = Some (Gval (Fuint 6) (word_30 v)).
Proof. rewrite - (closed_word_30_value v). unfold expr_word_30, closed_word_30.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_31_value v env
 (H0 : VM.find 30 env = Some (Gval (Fuint 6) (word_30 v)))
 : eval_hfexpr expr_word_31 env env = Some (Gval (Fuint 5) (word_31 v)).
Proof. rewrite - (closed_word_31_value v). unfold expr_word_31, closed_word_31.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_32_value v env
 (H0 : VM.find 29 env = Some (Gval (Fuint 5) (word_29 v)))
 (H1 : VM.find 31 env = Some (Gval (Fuint 5) (word_31 v)))
 : eval_hfexpr expr_word_32 env env = Some (Gval (Fuint 6) (word_32 v)).
Proof. rewrite - (closed_word_32_value v). unfold expr_word_32, closed_word_32.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_33_value v env
 (H0 : VM.find 32 env = Some (Gval (Fuint 6) (word_32 v)))
 : eval_hfexpr expr_word_33 env env = Some (Gval (Fuint 5) (word_33 v)).
Proof. rewrite - (closed_word_33_value v). unfold expr_word_33, closed_word_33.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_34_value v env
 (H0 : VM.find 24 env = Some (Gval (Fuint 4) (word_24 v)))
 (H1 : VM.find 33 env = Some (Gval (Fuint 5) (word_33 v)))
 : eval_hfexpr expr_word_34 env env = Some (Gval (Fuint 1) (word_34 v)).
Proof. rewrite - (closed_word_34_value v). unfold expr_word_34, closed_word_34.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_35_value v env
 (H0 : VM.find 1 env = Some (Gval (Fuint 1) (word_1 v)))
 : eval_hfexpr expr_word_35 env env = Some (Gval (Fuint 1) (word_35 v)).
Proof. rewrite - (closed_word_35_value v). unfold expr_word_35, closed_word_35.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_36_value v env
 (H0 : VM.find 35 env = Some (Gval (Fuint 1) (word_35 v)))
 : eval_hfexpr expr_word_36 env env = Some (Gval (Fuint 1) (word_36 v)).
Proof. rewrite - (closed_word_36_value v). unfold expr_word_36, closed_word_36.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_37_value v env
 (H0 : VM.find 34 env = Some (Gval (Fuint 1) (word_34 v)))
 : eval_hfexpr expr_word_37 env env = Some (Gval (Fuint 1) (word_37 v)).
Proof. rewrite - (closed_word_37_value v). unfold expr_word_37, closed_word_37.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_38_value v env
 (H0 : eval_href (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 5) env env = Some (Gval (Fuint 1) (port_10_5 v)))
 : eval_hfexpr expr_word_38 env env = Some (Gval (Fuint 1) (word_38 v)).
Proof. rewrite - (closed_word_38_value v). unfold expr_word_38, closed_word_38.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_39_value v env
 (H0 : VM.find 5 env = Some (Gval (Fuint 1) (word_5 v)))
 : eval_hfexpr expr_word_39 env env = Some (Gval (Fuint 1) (word_39 v)).
Proof. rewrite - (closed_word_39_value v). unfold expr_word_39, closed_word_39.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_40_value v env
 (H0 : VM.find 6 env = Some (Gval (Fuint 1) (word_6 v)))
 : eval_hfexpr expr_word_40 env env = Some (Gval (Fuint 1) (word_40 v)).
Proof. rewrite - (closed_word_40_value v). unfold expr_word_40, closed_word_40.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_10_0_value v env
 (H0 : VM.find 0 env = Some (Gval Fclock (word_0 v)))
 : eval_hfexpr expr_port_10_0 env env = Some (Gval Fclock (port_10_0 v)).
Proof. rewrite - (closed_port_10_0_value v). unfold expr_port_10_0, closed_port_10_0.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_10_1_value v env
 (H0 : VM.find 1 env = Some (Gval (Fuint 1) (word_1 v)))
 : eval_hfexpr expr_port_10_1 env env = Some (Gval (Fuint 1) (port_10_1 v)).
Proof. rewrite - (closed_port_10_1_value v). unfold expr_port_10_1, closed_port_10_1.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_10_2_value v env
 (H0 : VM.find 2 env = Some (Gval (Fuint 1) (word_2 v)))
 : eval_hfexpr expr_port_10_2 env env = Some (Gval (Fuint 1) (port_10_2 v)).
Proof. rewrite - (closed_port_10_2_value v). unfold expr_port_10_2, closed_port_10_2.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_10_3_value v env
 (H0 : VM.find 3 env = Some (Gval (Fuint 1) (word_3 v)))
 : eval_hfexpr expr_port_10_3 env env = Some (Gval (Fuint 1) (port_10_3 v)).
Proof. rewrite - (closed_port_10_3_value v). unfold expr_port_10_3, closed_port_10_3.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_10_4_value v env
 (H0 : VM.find 4 env = Some (Gval (Fuint 1) (word_4 v)))
 : eval_hfexpr expr_port_10_4 env env = Some (Gval (Fuint 1) (port_10_4 v)).
Proof. rewrite - (closed_port_10_4_value v). unfold expr_port_10_4, closed_port_10_4.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_11_0_value v env
 (H0 : VM.find 0 env = Some (Gval Fclock (word_0 v)))
 : eval_hfexpr expr_port_11_0 env env = Some (Gval Fclock (port_11_0 v)).
Proof. rewrite - (closed_port_11_0_value v). unfold expr_port_11_0, closed_port_11_0.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_11_1_value v env
 (H0 : VM.find 1 env = Some (Gval (Fuint 1) (word_1 v)))
 : eval_hfexpr expr_port_11_1 env env = Some (Gval (Fuint 1) (port_11_1 v)).
Proof. rewrite - (closed_port_11_1_value v). unfold expr_port_11_1, closed_port_11_1.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_11_2_value v env
 (H0 : VM.find 38 env = Some (Gval (Fuint 1) (word_38 v)))
 : eval_hfexpr expr_port_11_2 env env = Some (Gval (Fuint 1) (port_11_2 v)).
Proof. rewrite - (closed_port_11_2_value v). unfold expr_port_11_2, closed_port_11_2.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_11_3_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 1) (word_39 v)))
 : eval_hfexpr expr_port_11_3 env env = Some (Gval (Fuint 1) (port_11_3 v)).
Proof. rewrite - (closed_port_11_3_value v). unfold expr_port_11_3, closed_port_11_3.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_port_11_4_value v env
 (H0 : VM.find 40 env = Some (Gval (Fuint 1) (word_40 v)))
 : eval_hfexpr expr_port_11_4 env env = Some (Gval (Fuint 1) (port_11_4 v)).
Proof. rewrite - (closed_port_11_4_value v). unfold expr_port_11_4, closed_port_11_4.
 cbn [eval_hfexpr eval_type_of_expr type_of_expr' eval_type_of_ref].
 cbn [eval_href].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.

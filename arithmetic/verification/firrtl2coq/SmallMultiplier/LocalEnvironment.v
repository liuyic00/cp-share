From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Stable.
Local Open Scope N_scope.
Lemma local_word_37_value v env
 (H0 : VM.find 3 env = Some (Gval (Fuint 8) (word_3 v)))
 : eval_hfexpr expr_word_37 env env = Some (Gval (Fuint 1) (word_37 v)).
Proof. rewrite - (closed_word_37_value v). unfold expr_word_37, closed_word_37.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_38_value v env
 (H0 : VM.find 3 env = Some (Gval (Fuint 8) (word_3 v)))
 (H1 : VM.find 37 env = Some (Gval (Fuint 1) (word_37 v)))
 : eval_hfexpr expr_word_38 env env = Some (Gval (Fuint 9) (word_38 v)).
Proof. rewrite - (closed_word_38_value v). unfold expr_word_38, closed_word_38.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_39_value v env
 (H0 : VM.find 38 env = Some (Gval (Fuint 9) (word_38 v)))
 : eval_hfexpr expr_word_39 env env = Some (Gval (Fuint 9) (word_39 v)).
Proof. rewrite - (closed_word_39_value v). unfold expr_word_39, closed_word_39.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_40_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 : eval_hfexpr expr_word_40 env env = Some (Gval (Fuint 10) (word_40 v)).
Proof. rewrite - (closed_word_40_value v). unfold expr_word_40, closed_word_40.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_41_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 : eval_hfexpr expr_word_41 env env = Some (Gval (Fuint 9) (word_41 v)).
Proof. rewrite - (closed_word_41_value v). unfold expr_word_41, closed_word_41.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_42_value v env
 (H0 : VM.find 41 env = Some (Gval (Fuint 9) (word_41 v)))
 : eval_hfexpr expr_word_42 env env = Some (Gval (Fuint 9) (word_42 v)).
Proof. rewrite - (closed_word_42_value v). unfold expr_word_42, closed_word_42.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_43_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 : eval_hfexpr expr_word_43 env env = Some (Gval (Fuint 10) (word_43 v)).
Proof. rewrite - (closed_word_43_value v). unfold expr_word_43, closed_word_43.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_44_value v env
 (H0 : VM.find 2 env = Some (Gval (Fuint 8) (word_2 v)))
 : eval_hfexpr expr_word_44 env env = Some (Gval (Fuint 2) (word_44 v)).
Proof. rewrite - (closed_word_44_value v). unfold expr_word_44, closed_word_44.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_45_value v env
 (H0 : VM.find 44 env = Some (Gval (Fuint 2) (word_44 v)))
 : eval_hfexpr expr_word_45 env env = Some (Gval (Fuint 3) (word_45 v)).
Proof. rewrite - (closed_word_45_value v). unfold expr_word_45, closed_word_45.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_46_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_46 env env = Some (Gval (Fuint 1) (word_46 v)).
Proof. rewrite - (closed_word_46_value v). unfold expr_word_46, closed_word_46.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_47_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 46 env = Some (Gval (Fuint 1) (word_46 v)))
 : eval_hfexpr expr_word_47 env env = Some (Gval (Fuint 9) (word_47 v)).
Proof. rewrite - (closed_word_47_value v). unfold expr_word_47, closed_word_47.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_48_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_48 env env = Some (Gval (Fuint 1) (word_48 v)).
Proof. rewrite - (closed_word_48_value v). unfold expr_word_48, closed_word_48.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_49_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 47 env = Some (Gval (Fuint 9) (word_47 v)))
 (H2 : VM.find 48 env = Some (Gval (Fuint 1) (word_48 v)))
 : eval_hfexpr expr_word_49 env env = Some (Gval (Fuint 9) (word_49 v)).
Proof. rewrite - (closed_word_49_value v). unfold expr_word_49, closed_word_49.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_50_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_50 env env = Some (Gval (Fuint 1) (word_50 v)).
Proof. rewrite - (closed_word_50_value v). unfold expr_word_50, closed_word_50.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_51_value v env
 (H0 : VM.find 40 env = Some (Gval (Fuint 10) (word_40 v)))
 : eval_hfexpr expr_word_51 env env = Some (Gval (Fuint 9) (word_51 v)).
Proof. rewrite - (closed_word_51_value v). unfold expr_word_51, closed_word_51.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_52_value v env
 (H0 : VM.find 49 env = Some (Gval (Fuint 9) (word_49 v)))
 (H1 : VM.find 50 env = Some (Gval (Fuint 1) (word_50 v)))
 (H2 : VM.find 51 env = Some (Gval (Fuint 9) (word_51 v)))
 : eval_hfexpr expr_word_52 env env = Some (Gval (Fuint 9) (word_52 v)).
Proof. rewrite - (closed_word_52_value v). unfold expr_word_52, closed_word_52.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_53_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_53 env env = Some (Gval (Fuint 1) (word_53 v)).
Proof. rewrite - (closed_word_53_value v). unfold expr_word_53, closed_word_53.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_54_value v env
 (H0 : VM.find 43 env = Some (Gval (Fuint 10) (word_43 v)))
 : eval_hfexpr expr_word_54 env env = Some (Gval (Fuint 9) (word_54 v)).
Proof. rewrite - (closed_word_54_value v). unfold expr_word_54, closed_word_54.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_55_value v env
 (H0 : VM.find 52 env = Some (Gval (Fuint 9) (word_52 v)))
 (H1 : VM.find 53 env = Some (Gval (Fuint 1) (word_53 v)))
 (H2 : VM.find 54 env = Some (Gval (Fuint 9) (word_54 v)))
 : eval_hfexpr expr_word_55 env env = Some (Gval (Fuint 9) (word_55 v)).
Proof. rewrite - (closed_word_55_value v). unfold expr_word_55, closed_word_55.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_56_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_56 env env = Some (Gval (Fuint 1) (word_56 v)).
Proof. rewrite - (closed_word_56_value v). unfold expr_word_56, closed_word_56.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_57_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 55 env = Some (Gval (Fuint 9) (word_55 v)))
 (H2 : VM.find 56 env = Some (Gval (Fuint 1) (word_56 v)))
 : eval_hfexpr expr_word_57 env env = Some (Gval (Fuint 9) (word_57 v)).
Proof. rewrite - (closed_word_57_value v). unfold expr_word_57, closed_word_57.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_58_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_58 env env = Some (Gval (Fuint 1) (word_58 v)).
Proof. rewrite - (closed_word_58_value v). unfold expr_word_58, closed_word_58.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_59_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 57 env = Some (Gval (Fuint 9) (word_57 v)))
 (H2 : VM.find 58 env = Some (Gval (Fuint 1) (word_58 v)))
 : eval_hfexpr expr_word_59 env env = Some (Gval (Fuint 9) (word_59 v)).
Proof. rewrite - (closed_word_59_value v). unfold expr_word_59, closed_word_59.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_60_value v env
 (H0 : VM.find 59 env = Some (Gval (Fuint 9) (word_59 v)))
 : eval_hfexpr expr_word_60 env env = Some (Gval (Fuint 1) (word_60 v)).
Proof. rewrite - (closed_word_60_value v). unfold expr_word_60, closed_word_60.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_61_value v env
 : eval_hfexpr expr_word_61 env env = Some (Gval (Fuint 3) (word_61 v)).
Proof. rewrite - (closed_word_61_value v). unfold expr_word_61, closed_word_61.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].

 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].

 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_62_value v env
 (H0 : VM.find 61 env = Some (Gval (Fuint 3) (word_61 v)))
 : eval_hfexpr expr_word_62 env env = Some (Gval (Fuint 1) (word_62 v)).
Proof. rewrite - (closed_word_62_value v). unfold expr_word_62, closed_word_62.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_63_value v env
 (H0 : VM.find 62 env = Some (Gval (Fuint 1) (word_62 v)))
 : eval_hfexpr expr_word_63 env env = Some (Gval (Fuint 2) (word_63 v)).
Proof. rewrite - (closed_word_63_value v). unfold expr_word_63, closed_word_63.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_64_value v env
 (H0 : VM.find 61 env = Some (Gval (Fuint 3) (word_61 v)))
 : eval_hfexpr expr_word_64 env env = Some (Gval (Fuint 1) (word_64 v)).
Proof. rewrite - (closed_word_64_value v). unfold expr_word_64, closed_word_64.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_65_value v env
 (H0 : VM.find 63 env = Some (Gval (Fuint 2) (word_63 v)))
 (H1 : VM.find 64 env = Some (Gval (Fuint 1) (word_64 v)))
 : eval_hfexpr expr_word_65 env env = Some (Gval (Fuint 2) (word_65 v)).
Proof. rewrite - (closed_word_65_value v). unfold expr_word_65, closed_word_65.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_66_value v env
 (H0 : VM.find 61 env = Some (Gval (Fuint 3) (word_61 v)))
 : eval_hfexpr expr_word_66 env env = Some (Gval (Fuint 1) (word_66 v)).
Proof. rewrite - (closed_word_66_value v). unfold expr_word_66, closed_word_66.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_67_value v env
 (H0 : VM.find 65 env = Some (Gval (Fuint 2) (word_65 v)))
 (H1 : VM.find 66 env = Some (Gval (Fuint 1) (word_66 v)))
 : eval_hfexpr expr_word_67 env env = Some (Gval (Fuint 2) (word_67 v)).
Proof. rewrite - (closed_word_67_value v). unfold expr_word_67, closed_word_67.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_68_value v env
 (H0 : VM.find 60 env = Some (Gval (Fuint 1) (word_60 v)))
 : eval_hfexpr expr_word_68 env env = Some (Gval (Fuint 1) (word_68 v)).
Proof. rewrite - (closed_word_68_value v). unfold expr_word_68, closed_word_68.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_69_value v env
 (H0 : VM.find 59 env = Some (Gval (Fuint 9) (word_59 v)))
 (H1 : VM.find 60 env = Some (Gval (Fuint 1) (word_60 v)))
 : eval_hfexpr expr_word_69 env env = Some (Gval (Fuint 10) (word_69 v)).
Proof. rewrite - (closed_word_69_value v). unfold expr_word_69, closed_word_69.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_70_value v env
 (H0 : VM.find 60 env = Some (Gval (Fuint 1) (word_60 v)))
 (H1 : VM.find 68 env = Some (Gval (Fuint 1) (word_68 v)))
 : eval_hfexpr expr_word_70 env env = Some (Gval (Fuint 2) (word_70 v)).
Proof. rewrite - (closed_word_70_value v). unfold expr_word_70, closed_word_70.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_71_value v env
 (H0 : VM.find 69 env = Some (Gval (Fuint 10) (word_69 v)))
 (H1 : VM.find 70 env = Some (Gval (Fuint 2) (word_70 v)))
 : eval_hfexpr expr_word_71 env env = Some (Gval (Fuint 12) (word_71 v)).
Proof. rewrite - (closed_word_71_value v). unfold expr_word_71, closed_word_71.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_72_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_72 env env = Some (Gval (Fuint 1) (word_72 v)).
Proof. rewrite - (closed_word_72_value v). unfold expr_word_72, closed_word_72.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_73_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_73 env env = Some (Gval (Fuint 1) (word_73 v)).
Proof. rewrite - (closed_word_73_value v). unfold expr_word_73, closed_word_73.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_74_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_74 env env = Some (Gval (Fuint 1) (word_74 v)).
Proof. rewrite - (closed_word_74_value v). unfold expr_word_74, closed_word_74.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_75_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_75 env env = Some (Gval (Fuint 1) (word_75 v)).
Proof. rewrite - (closed_word_75_value v). unfold expr_word_75, closed_word_75.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_76_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_76 env env = Some (Gval (Fuint 1) (word_76 v)).
Proof. rewrite - (closed_word_76_value v). unfold expr_word_76, closed_word_76.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_77_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_77 env env = Some (Gval (Fuint 1) (word_77 v)).
Proof. rewrite - (closed_word_77_value v). unfold expr_word_77, closed_word_77.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_78_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_78 env env = Some (Gval (Fuint 1) (word_78 v)).
Proof. rewrite - (closed_word_78_value v). unfold expr_word_78, closed_word_78.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_79_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_79 env env = Some (Gval (Fuint 1) (word_79 v)).
Proof. rewrite - (closed_word_79_value v). unfold expr_word_79, closed_word_79.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_80_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_80 env env = Some (Gval (Fuint 1) (word_80 v)).
Proof. rewrite - (closed_word_80_value v). unfold expr_word_80, closed_word_80.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_81_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_81 env env = Some (Gval (Fuint 1) (word_81 v)).
Proof. rewrite - (closed_word_81_value v). unfold expr_word_81, closed_word_81.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_82_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_82 env env = Some (Gval (Fuint 1) (word_82 v)).
Proof. rewrite - (closed_word_82_value v). unfold expr_word_82, closed_word_82.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_83_value v env
 (H0 : VM.find 71 env = Some (Gval (Fuint 12) (word_71 v)))
 : eval_hfexpr expr_word_83 env env = Some (Gval (Fuint 1) (word_83 v)).
Proof. rewrite - (closed_word_83_value v). unfold expr_word_83, closed_word_83.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_84_value v env
 (H0 : VM.find 2 env = Some (Gval (Fuint 8) (word_2 v)))
 : eval_hfexpr expr_word_84 env env = Some (Gval (Fuint 3) (word_84 v)).
Proof. rewrite - (closed_word_84_value v). unfold expr_word_84, closed_word_84.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_85_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_85 env env = Some (Gval (Fuint 1) (word_85 v)).
Proof. rewrite - (closed_word_85_value v). unfold expr_word_85, closed_word_85.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_86_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 85 env = Some (Gval (Fuint 1) (word_85 v)))
 : eval_hfexpr expr_word_86 env env = Some (Gval (Fuint 9) (word_86 v)).
Proof. rewrite - (closed_word_86_value v). unfold expr_word_86, closed_word_86.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_87_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_87 env env = Some (Gval (Fuint 1) (word_87 v)).
Proof. rewrite - (closed_word_87_value v). unfold expr_word_87, closed_word_87.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_88_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 86 env = Some (Gval (Fuint 9) (word_86 v)))
 (H2 : VM.find 87 env = Some (Gval (Fuint 1) (word_87 v)))
 : eval_hfexpr expr_word_88 env env = Some (Gval (Fuint 9) (word_88 v)).
Proof. rewrite - (closed_word_88_value v). unfold expr_word_88, closed_word_88.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_89_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_89 env env = Some (Gval (Fuint 1) (word_89 v)).
Proof. rewrite - (closed_word_89_value v). unfold expr_word_89, closed_word_89.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_90_value v env
 (H0 : VM.find 51 env = Some (Gval (Fuint 9) (word_51 v)))
 (H1 : VM.find 88 env = Some (Gval (Fuint 9) (word_88 v)))
 (H2 : VM.find 89 env = Some (Gval (Fuint 1) (word_89 v)))
 : eval_hfexpr expr_word_90 env env = Some (Gval (Fuint 9) (word_90 v)).
Proof. rewrite - (closed_word_90_value v). unfold expr_word_90, closed_word_90.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_91_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_91 env env = Some (Gval (Fuint 1) (word_91 v)).
Proof. rewrite - (closed_word_91_value v). unfold expr_word_91, closed_word_91.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_92_value v env
 (H0 : VM.find 54 env = Some (Gval (Fuint 9) (word_54 v)))
 (H1 : VM.find 90 env = Some (Gval (Fuint 9) (word_90 v)))
 (H2 : VM.find 91 env = Some (Gval (Fuint 1) (word_91 v)))
 : eval_hfexpr expr_word_92 env env = Some (Gval (Fuint 9) (word_92 v)).
Proof. rewrite - (closed_word_92_value v). unfold expr_word_92, closed_word_92.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_93_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_93 env env = Some (Gval (Fuint 1) (word_93 v)).
Proof. rewrite - (closed_word_93_value v). unfold expr_word_93, closed_word_93.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_94_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 92 env = Some (Gval (Fuint 9) (word_92 v)))
 (H2 : VM.find 93 env = Some (Gval (Fuint 1) (word_93 v)))
 : eval_hfexpr expr_word_94 env env = Some (Gval (Fuint 9) (word_94 v)).
Proof. rewrite - (closed_word_94_value v). unfold expr_word_94, closed_word_94.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_95_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_95 env env = Some (Gval (Fuint 1) (word_95 v)).
Proof. rewrite - (closed_word_95_value v). unfold expr_word_95, closed_word_95.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_96_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 94 env = Some (Gval (Fuint 9) (word_94 v)))
 (H2 : VM.find 95 env = Some (Gval (Fuint 1) (word_95 v)))
 : eval_hfexpr expr_word_96 env env = Some (Gval (Fuint 9) (word_96 v)).
Proof. rewrite - (closed_word_96_value v). unfold expr_word_96, closed_word_96.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_97_value v env
 (H0 : VM.find 96 env = Some (Gval (Fuint 9) (word_96 v)))
 : eval_hfexpr expr_word_97 env env = Some (Gval (Fuint 1) (word_97 v)).
Proof. rewrite - (closed_word_97_value v). unfold expr_word_97, closed_word_97.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_98_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_98 env env = Some (Gval (Fuint 1) (word_98 v)).
Proof. rewrite - (closed_word_98_value v). unfold expr_word_98, closed_word_98.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_99_value v env
 (H0 : VM.find 98 env = Some (Gval (Fuint 1) (word_98 v)))
 : eval_hfexpr expr_word_99 env env = Some (Gval (Fuint 2) (word_99 v)).
Proof. rewrite - (closed_word_99_value v). unfold expr_word_99, closed_word_99.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_100_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_100 env env = Some (Gval (Fuint 1) (word_100 v)).
Proof. rewrite - (closed_word_100_value v). unfold expr_word_100, closed_word_100.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_101_value v env
 (H0 : VM.find 99 env = Some (Gval (Fuint 2) (word_99 v)))
 (H1 : VM.find 100 env = Some (Gval (Fuint 1) (word_100 v)))
 : eval_hfexpr expr_word_101 env env = Some (Gval (Fuint 2) (word_101 v)).
Proof. rewrite - (closed_word_101_value v). unfold expr_word_101, closed_word_101.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_102_value v env
 (H0 : VM.find 45 env = Some (Gval (Fuint 3) (word_45 v)))
 : eval_hfexpr expr_word_102 env env = Some (Gval (Fuint 1) (word_102 v)).
Proof. rewrite - (closed_word_102_value v). unfold expr_word_102, closed_word_102.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_103_value v env
 (H0 : VM.find 101 env = Some (Gval (Fuint 2) (word_101 v)))
 (H1 : VM.find 102 env = Some (Gval (Fuint 1) (word_102 v)))
 : eval_hfexpr expr_word_103 env env = Some (Gval (Fuint 2) (word_103 v)).
Proof. rewrite - (closed_word_103_value v). unfold expr_word_103, closed_word_103.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_104_value v env
 (H0 : VM.find 97 env = Some (Gval (Fuint 1) (word_97 v)))
 : eval_hfexpr expr_word_104 env env = Some (Gval (Fuint 1) (word_104 v)).
Proof. rewrite - (closed_word_104_value v). unfold expr_word_104, closed_word_104.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_105_value v env
 (H0 : VM.find 96 env = Some (Gval (Fuint 9) (word_96 v)))
 (H1 : VM.find 103 env = Some (Gval (Fuint 2) (word_103 v)))
 : eval_hfexpr expr_word_105 env env = Some (Gval (Fuint 11) (word_105 v)).
Proof. rewrite - (closed_word_105_value v). unfold expr_word_105, closed_word_105.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_106_value v env
 (H0 : VM.find 104 env = Some (Gval (Fuint 1) (word_104 v)))
 : eval_hfexpr expr_word_106 env env = Some (Gval (Fuint 2) (word_106 v)).
Proof. rewrite - (closed_word_106_value v). unfold expr_word_106, closed_word_106.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_107_value v env
 (H0 : VM.find 105 env = Some (Gval (Fuint 11) (word_105 v)))
 (H1 : VM.find 106 env = Some (Gval (Fuint 2) (word_106 v)))
 : eval_hfexpr expr_word_107 env env = Some (Gval (Fuint 13) (word_107 v)).
Proof. rewrite - (closed_word_107_value v). unfold expr_word_107, closed_word_107.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_108_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_108 env env = Some (Gval (Fuint 1) (word_108 v)).
Proof. rewrite - (closed_word_108_value v). unfold expr_word_108, closed_word_108.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_109_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_109 env env = Some (Gval (Fuint 1) (word_109 v)).
Proof. rewrite - (closed_word_109_value v). unfold expr_word_109, closed_word_109.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_110_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_110 env env = Some (Gval (Fuint 1) (word_110 v)).
Proof. rewrite - (closed_word_110_value v). unfold expr_word_110, closed_word_110.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_111_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_111 env env = Some (Gval (Fuint 1) (word_111 v)).
Proof. rewrite - (closed_word_111_value v). unfold expr_word_111, closed_word_111.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_112_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_112 env env = Some (Gval (Fuint 1) (word_112 v)).
Proof. rewrite - (closed_word_112_value v). unfold expr_word_112, closed_word_112.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_113_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_113 env env = Some (Gval (Fuint 1) (word_113 v)).
Proof. rewrite - (closed_word_113_value v). unfold expr_word_113, closed_word_113.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_114_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_114 env env = Some (Gval (Fuint 1) (word_114 v)).
Proof. rewrite - (closed_word_114_value v). unfold expr_word_114, closed_word_114.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_115_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_115 env env = Some (Gval (Fuint 1) (word_115 v)).
Proof. rewrite - (closed_word_115_value v). unfold expr_word_115, closed_word_115.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_116_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_116 env env = Some (Gval (Fuint 1) (word_116 v)).
Proof. rewrite - (closed_word_116_value v). unfold expr_word_116, closed_word_116.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_117_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_117 env env = Some (Gval (Fuint 1) (word_117 v)).
Proof. rewrite - (closed_word_117_value v). unfold expr_word_117, closed_word_117.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_118_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_118 env env = Some (Gval (Fuint 1) (word_118 v)).
Proof. rewrite - (closed_word_118_value v). unfold expr_word_118, closed_word_118.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_119_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_119 env env = Some (Gval (Fuint 1) (word_119 v)).
Proof. rewrite - (closed_word_119_value v). unfold expr_word_119, closed_word_119.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_120_value v env
 (H0 : VM.find 107 env = Some (Gval (Fuint 13) (word_107 v)))
 : eval_hfexpr expr_word_120 env env = Some (Gval (Fuint 1) (word_120 v)).
Proof. rewrite - (closed_word_120_value v). unfold expr_word_120, closed_word_120.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_121_value v env
 (H0 : VM.find 2 env = Some (Gval (Fuint 8) (word_2 v)))
 : eval_hfexpr expr_word_121 env env = Some (Gval (Fuint 3) (word_121 v)).
Proof. rewrite - (closed_word_121_value v). unfold expr_word_121, closed_word_121.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_122_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_122 env env = Some (Gval (Fuint 1) (word_122 v)).
Proof. rewrite - (closed_word_122_value v). unfold expr_word_122, closed_word_122.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_123_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 122 env = Some (Gval (Fuint 1) (word_122 v)))
 : eval_hfexpr expr_word_123 env env = Some (Gval (Fuint 9) (word_123 v)).
Proof. rewrite - (closed_word_123_value v). unfold expr_word_123, closed_word_123.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_124_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_124 env env = Some (Gval (Fuint 1) (word_124 v)).
Proof. rewrite - (closed_word_124_value v). unfold expr_word_124, closed_word_124.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_125_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 123 env = Some (Gval (Fuint 9) (word_123 v)))
 (H2 : VM.find 124 env = Some (Gval (Fuint 1) (word_124 v)))
 : eval_hfexpr expr_word_125 env env = Some (Gval (Fuint 9) (word_125 v)).
Proof. rewrite - (closed_word_125_value v). unfold expr_word_125, closed_word_125.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_126_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_126 env env = Some (Gval (Fuint 1) (word_126 v)).
Proof. rewrite - (closed_word_126_value v). unfold expr_word_126, closed_word_126.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_127_value v env
 (H0 : VM.find 51 env = Some (Gval (Fuint 9) (word_51 v)))
 (H1 : VM.find 125 env = Some (Gval (Fuint 9) (word_125 v)))
 (H2 : VM.find 126 env = Some (Gval (Fuint 1) (word_126 v)))
 : eval_hfexpr expr_word_127 env env = Some (Gval (Fuint 9) (word_127 v)).
Proof. rewrite - (closed_word_127_value v). unfold expr_word_127, closed_word_127.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_128_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_128 env env = Some (Gval (Fuint 1) (word_128 v)).
Proof. rewrite - (closed_word_128_value v). unfold expr_word_128, closed_word_128.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_129_value v env
 (H0 : VM.find 54 env = Some (Gval (Fuint 9) (word_54 v)))
 (H1 : VM.find 127 env = Some (Gval (Fuint 9) (word_127 v)))
 (H2 : VM.find 128 env = Some (Gval (Fuint 1) (word_128 v)))
 : eval_hfexpr expr_word_129 env env = Some (Gval (Fuint 9) (word_129 v)).
Proof. rewrite - (closed_word_129_value v). unfold expr_word_129, closed_word_129.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_130_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_130 env env = Some (Gval (Fuint 1) (word_130 v)).
Proof. rewrite - (closed_word_130_value v). unfold expr_word_130, closed_word_130.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_131_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 129 env = Some (Gval (Fuint 9) (word_129 v)))
 (H2 : VM.find 130 env = Some (Gval (Fuint 1) (word_130 v)))
 : eval_hfexpr expr_word_131 env env = Some (Gval (Fuint 9) (word_131 v)).
Proof. rewrite - (closed_word_131_value v). unfold expr_word_131, closed_word_131.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_132_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_132 env env = Some (Gval (Fuint 1) (word_132 v)).
Proof. rewrite - (closed_word_132_value v). unfold expr_word_132, closed_word_132.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_133_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 131 env = Some (Gval (Fuint 9) (word_131 v)))
 (H2 : VM.find 132 env = Some (Gval (Fuint 1) (word_132 v)))
 : eval_hfexpr expr_word_133 env env = Some (Gval (Fuint 9) (word_133 v)).
Proof. rewrite - (closed_word_133_value v). unfold expr_word_133, closed_word_133.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_134_value v env
 (H0 : VM.find 133 env = Some (Gval (Fuint 9) (word_133 v)))
 : eval_hfexpr expr_word_134 env env = Some (Gval (Fuint 1) (word_134 v)).
Proof. rewrite - (closed_word_134_value v). unfold expr_word_134, closed_word_134.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_135_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_135 env env = Some (Gval (Fuint 1) (word_135 v)).
Proof. rewrite - (closed_word_135_value v). unfold expr_word_135, closed_word_135.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_136_value v env
 (H0 : VM.find 135 env = Some (Gval (Fuint 1) (word_135 v)))
 : eval_hfexpr expr_word_136 env env = Some (Gval (Fuint 2) (word_136 v)).
Proof. rewrite - (closed_word_136_value v). unfold expr_word_136, closed_word_136.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_137_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_137 env env = Some (Gval (Fuint 1) (word_137 v)).
Proof. rewrite - (closed_word_137_value v). unfold expr_word_137, closed_word_137.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_138_value v env
 (H0 : VM.find 136 env = Some (Gval (Fuint 2) (word_136 v)))
 (H1 : VM.find 137 env = Some (Gval (Fuint 1) (word_137 v)))
 : eval_hfexpr expr_word_138 env env = Some (Gval (Fuint 2) (word_138 v)).
Proof. rewrite - (closed_word_138_value v). unfold expr_word_138, closed_word_138.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_139_value v env
 (H0 : VM.find 84 env = Some (Gval (Fuint 3) (word_84 v)))
 : eval_hfexpr expr_word_139 env env = Some (Gval (Fuint 1) (word_139 v)).
Proof. rewrite - (closed_word_139_value v). unfold expr_word_139, closed_word_139.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_140_value v env
 (H0 : VM.find 138 env = Some (Gval (Fuint 2) (word_138 v)))
 (H1 : VM.find 139 env = Some (Gval (Fuint 1) (word_139 v)))
 : eval_hfexpr expr_word_140 env env = Some (Gval (Fuint 2) (word_140 v)).
Proof. rewrite - (closed_word_140_value v). unfold expr_word_140, closed_word_140.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_141_value v env
 (H0 : VM.find 134 env = Some (Gval (Fuint 1) (word_134 v)))
 : eval_hfexpr expr_word_141 env env = Some (Gval (Fuint 1) (word_141 v)).
Proof. rewrite - (closed_word_141_value v). unfold expr_word_141, closed_word_141.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_142_value v env
 (H0 : VM.find 133 env = Some (Gval (Fuint 9) (word_133 v)))
 (H1 : VM.find 140 env = Some (Gval (Fuint 2) (word_140 v)))
 : eval_hfexpr expr_word_142 env env = Some (Gval (Fuint 11) (word_142 v)).
Proof. rewrite - (closed_word_142_value v). unfold expr_word_142, closed_word_142.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_143_value v env
 (H0 : VM.find 141 env = Some (Gval (Fuint 1) (word_141 v)))
 : eval_hfexpr expr_word_143 env env = Some (Gval (Fuint 2) (word_143 v)).
Proof. rewrite - (closed_word_143_value v). unfold expr_word_143, closed_word_143.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_144_value v env
 (H0 : VM.find 142 env = Some (Gval (Fuint 11) (word_142 v)))
 (H1 : VM.find 143 env = Some (Gval (Fuint 2) (word_143 v)))
 : eval_hfexpr expr_word_144 env env = Some (Gval (Fuint 13) (word_144 v)).
Proof. rewrite - (closed_word_144_value v). unfold expr_word_144, closed_word_144.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_145_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_145 env env = Some (Gval (Fuint 1) (word_145 v)).
Proof. rewrite - (closed_word_145_value v). unfold expr_word_145, closed_word_145.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_146_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_146 env env = Some (Gval (Fuint 1) (word_146 v)).
Proof. rewrite - (closed_word_146_value v). unfold expr_word_146, closed_word_146.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_147_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_147 env env = Some (Gval (Fuint 1) (word_147 v)).
Proof. rewrite - (closed_word_147_value v). unfold expr_word_147, closed_word_147.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_148_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_148 env env = Some (Gval (Fuint 1) (word_148 v)).
Proof. rewrite - (closed_word_148_value v). unfold expr_word_148, closed_word_148.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_149_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_149 env env = Some (Gval (Fuint 1) (word_149 v)).
Proof. rewrite - (closed_word_149_value v). unfold expr_word_149, closed_word_149.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_150_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_150 env env = Some (Gval (Fuint 1) (word_150 v)).
Proof. rewrite - (closed_word_150_value v). unfold expr_word_150, closed_word_150.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_151_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_151 env env = Some (Gval (Fuint 1) (word_151 v)).
Proof. rewrite - (closed_word_151_value v). unfold expr_word_151, closed_word_151.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_152_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_152 env env = Some (Gval (Fuint 1) (word_152 v)).
Proof. rewrite - (closed_word_152_value v). unfold expr_word_152, closed_word_152.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_153_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_153 env env = Some (Gval (Fuint 1) (word_153 v)).
Proof. rewrite - (closed_word_153_value v). unfold expr_word_153, closed_word_153.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_154_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_154 env env = Some (Gval (Fuint 1) (word_154 v)).
Proof. rewrite - (closed_word_154_value v). unfold expr_word_154, closed_word_154.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_155_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_155 env env = Some (Gval (Fuint 1) (word_155 v)).
Proof. rewrite - (closed_word_155_value v). unfold expr_word_155, closed_word_155.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_156_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_156 env env = Some (Gval (Fuint 1) (word_156 v)).
Proof. rewrite - (closed_word_156_value v). unfold expr_word_156, closed_word_156.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_157_value v env
 (H0 : VM.find 144 env = Some (Gval (Fuint 13) (word_144 v)))
 : eval_hfexpr expr_word_157 env env = Some (Gval (Fuint 1) (word_157 v)).
Proof. rewrite - (closed_word_157_value v). unfold expr_word_157, closed_word_157.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_158_value v env
 (H0 : VM.find 2 env = Some (Gval (Fuint 8) (word_2 v)))
 : eval_hfexpr expr_word_158 env env = Some (Gval (Fuint 3) (word_158 v)).
Proof. rewrite - (closed_word_158_value v). unfold expr_word_158, closed_word_158.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_159_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_159 env env = Some (Gval (Fuint 1) (word_159 v)).
Proof. rewrite - (closed_word_159_value v). unfold expr_word_159, closed_word_159.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_160_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 159 env = Some (Gval (Fuint 1) (word_159 v)))
 : eval_hfexpr expr_word_160 env env = Some (Gval (Fuint 9) (word_160 v)).
Proof. rewrite - (closed_word_160_value v). unfold expr_word_160, closed_word_160.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_161_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_161 env env = Some (Gval (Fuint 1) (word_161 v)).
Proof. rewrite - (closed_word_161_value v). unfold expr_word_161, closed_word_161.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_162_value v env
 (H0 : VM.find 39 env = Some (Gval (Fuint 9) (word_39 v)))
 (H1 : VM.find 160 env = Some (Gval (Fuint 9) (word_160 v)))
 (H2 : VM.find 161 env = Some (Gval (Fuint 1) (word_161 v)))
 : eval_hfexpr expr_word_162 env env = Some (Gval (Fuint 9) (word_162 v)).
Proof. rewrite - (closed_word_162_value v). unfold expr_word_162, closed_word_162.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_163_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_163 env env = Some (Gval (Fuint 1) (word_163 v)).
Proof. rewrite - (closed_word_163_value v). unfold expr_word_163, closed_word_163.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_164_value v env
 (H0 : VM.find 51 env = Some (Gval (Fuint 9) (word_51 v)))
 (H1 : VM.find 162 env = Some (Gval (Fuint 9) (word_162 v)))
 (H2 : VM.find 163 env = Some (Gval (Fuint 1) (word_163 v)))
 : eval_hfexpr expr_word_164 env env = Some (Gval (Fuint 9) (word_164 v)).
Proof. rewrite - (closed_word_164_value v). unfold expr_word_164, closed_word_164.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_165_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_165 env env = Some (Gval (Fuint 1) (word_165 v)).
Proof. rewrite - (closed_word_165_value v). unfold expr_word_165, closed_word_165.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_166_value v env
 (H0 : VM.find 54 env = Some (Gval (Fuint 9) (word_54 v)))
 (H1 : VM.find 164 env = Some (Gval (Fuint 9) (word_164 v)))
 (H2 : VM.find 165 env = Some (Gval (Fuint 1) (word_165 v)))
 : eval_hfexpr expr_word_166 env env = Some (Gval (Fuint 9) (word_166 v)).
Proof. rewrite - (closed_word_166_value v). unfold expr_word_166, closed_word_166.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_167_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_167 env env = Some (Gval (Fuint 1) (word_167 v)).
Proof. rewrite - (closed_word_167_value v). unfold expr_word_167, closed_word_167.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_168_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 166 env = Some (Gval (Fuint 9) (word_166 v)))
 (H2 : VM.find 167 env = Some (Gval (Fuint 1) (word_167 v)))
 : eval_hfexpr expr_word_168 env env = Some (Gval (Fuint 9) (word_168 v)).
Proof. rewrite - (closed_word_168_value v). unfold expr_word_168, closed_word_168.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_169_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_169 env env = Some (Gval (Fuint 1) (word_169 v)).
Proof. rewrite - (closed_word_169_value v). unfold expr_word_169, closed_word_169.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_170_value v env
 (H0 : VM.find 42 env = Some (Gval (Fuint 9) (word_42 v)))
 (H1 : VM.find 168 env = Some (Gval (Fuint 9) (word_168 v)))
 (H2 : VM.find 169 env = Some (Gval (Fuint 1) (word_169 v)))
 : eval_hfexpr expr_word_170 env env = Some (Gval (Fuint 9) (word_170 v)).
Proof. rewrite - (closed_word_170_value v). unfold expr_word_170, closed_word_170.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1 ?H2.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_171_value v env
 (H0 : VM.find 170 env = Some (Gval (Fuint 9) (word_170 v)))
 : eval_hfexpr expr_word_171 env env = Some (Gval (Fuint 1) (word_171 v)).
Proof. rewrite - (closed_word_171_value v). unfold expr_word_171, closed_word_171.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_172_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_172 env env = Some (Gval (Fuint 1) (word_172 v)).
Proof. rewrite - (closed_word_172_value v). unfold expr_word_172, closed_word_172.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_173_value v env
 (H0 : VM.find 172 env = Some (Gval (Fuint 1) (word_172 v)))
 : eval_hfexpr expr_word_173 env env = Some (Gval (Fuint 2) (word_173 v)).
Proof. rewrite - (closed_word_173_value v). unfold expr_word_173, closed_word_173.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_174_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_174 env env = Some (Gval (Fuint 1) (word_174 v)).
Proof. rewrite - (closed_word_174_value v). unfold expr_word_174, closed_word_174.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_175_value v env
 (H0 : VM.find 173 env = Some (Gval (Fuint 2) (word_173 v)))
 (H1 : VM.find 174 env = Some (Gval (Fuint 1) (word_174 v)))
 : eval_hfexpr expr_word_175 env env = Some (Gval (Fuint 2) (word_175 v)).
Proof. rewrite - (closed_word_175_value v). unfold expr_word_175, closed_word_175.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_176_value v env
 (H0 : VM.find 121 env = Some (Gval (Fuint 3) (word_121 v)))
 : eval_hfexpr expr_word_176 env env = Some (Gval (Fuint 1) (word_176 v)).
Proof. rewrite - (closed_word_176_value v). unfold expr_word_176, closed_word_176.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_177_value v env
 (H0 : VM.find 175 env = Some (Gval (Fuint 2) (word_175 v)))
 (H1 : VM.find 176 env = Some (Gval (Fuint 1) (word_176 v)))
 : eval_hfexpr expr_word_177 env env = Some (Gval (Fuint 2) (word_177 v)).
Proof. rewrite - (closed_word_177_value v). unfold expr_word_177, closed_word_177.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_178_value v env
 (H0 : VM.find 171 env = Some (Gval (Fuint 1) (word_171 v)))
 : eval_hfexpr expr_word_178 env env = Some (Gval (Fuint 1) (word_178 v)).
Proof. rewrite - (closed_word_178_value v). unfold expr_word_178, closed_word_178.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_179_value v env
 (H0 : VM.find 170 env = Some (Gval (Fuint 9) (word_170 v)))
 (H1 : VM.find 178 env = Some (Gval (Fuint 1) (word_178 v)))
 : eval_hfexpr expr_word_179 env env = Some (Gval (Fuint 10) (word_179 v)).
Proof. rewrite - (closed_word_179_value v). unfold expr_word_179, closed_word_179.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_180_value v env
 (H0 : VM.find 177 env = Some (Gval (Fuint 2) (word_177 v)))
 (H1 : VM.find 179 env = Some (Gval (Fuint 10) (word_179 v)))
 : eval_hfexpr expr_word_180 env env = Some (Gval (Fuint 12) (word_180 v)).
Proof. rewrite - (closed_word_180_value v). unfold expr_word_180, closed_word_180.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_181_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_181 env env = Some (Gval (Fuint 1) (word_181 v)).
Proof. rewrite - (closed_word_181_value v). unfold expr_word_181, closed_word_181.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_182_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_182 env env = Some (Gval (Fuint 1) (word_182 v)).
Proof. rewrite - (closed_word_182_value v). unfold expr_word_182, closed_word_182.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_183_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_183 env env = Some (Gval (Fuint 1) (word_183 v)).
Proof. rewrite - (closed_word_183_value v). unfold expr_word_183, closed_word_183.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_184_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_184 env env = Some (Gval (Fuint 1) (word_184 v)).
Proof. rewrite - (closed_word_184_value v). unfold expr_word_184, closed_word_184.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_185_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_185 env env = Some (Gval (Fuint 1) (word_185 v)).
Proof. rewrite - (closed_word_185_value v). unfold expr_word_185, closed_word_185.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_186_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_186 env env = Some (Gval (Fuint 1) (word_186 v)).
Proof. rewrite - (closed_word_186_value v). unfold expr_word_186, closed_word_186.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_187_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_187 env env = Some (Gval (Fuint 1) (word_187 v)).
Proof. rewrite - (closed_word_187_value v). unfold expr_word_187, closed_word_187.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_188_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_188 env env = Some (Gval (Fuint 1) (word_188 v)).
Proof. rewrite - (closed_word_188_value v). unfold expr_word_188, closed_word_188.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_189_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_189 env env = Some (Gval (Fuint 1) (word_189 v)).
Proof. rewrite - (closed_word_189_value v). unfold expr_word_189, closed_word_189.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_190_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_190 env env = Some (Gval (Fuint 1) (word_190 v)).
Proof. rewrite - (closed_word_190_value v). unfold expr_word_190, closed_word_190.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_191_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_191 env env = Some (Gval (Fuint 1) (word_191 v)).
Proof. rewrite - (closed_word_191_value v). unfold expr_word_191, closed_word_191.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_192_value v env
 (H0 : VM.find 180 env = Some (Gval (Fuint 12) (word_180 v)))
 : eval_hfexpr expr_word_192 env env = Some (Gval (Fuint 1) (word_192 v)).
Proof. rewrite - (closed_word_192_value v). unfold expr_word_192, closed_word_192.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_193_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_193 env env = Some (Gval (Fuint 1) (word_193 v)).
Proof. rewrite - (closed_word_193_value v). unfold expr_word_193, closed_word_193.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_194_value v env
 (H0 : VM.find 193 env = Some (Gval (Fuint 1) (word_193 v)))
 : eval_hfexpr expr_word_194 env env = Some (Gval (Fuint 2) (word_194 v)).
Proof. rewrite - (closed_word_194_value v). unfold expr_word_194, closed_word_194.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_195_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_195 env env = Some (Gval (Fuint 1) (word_195 v)).
Proof. rewrite - (closed_word_195_value v). unfold expr_word_195, closed_word_195.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_196_value v env
 (H0 : VM.find 194 env = Some (Gval (Fuint 2) (word_194 v)))
 (H1 : VM.find 195 env = Some (Gval (Fuint 1) (word_195 v)))
 : eval_hfexpr expr_word_196 env env = Some (Gval (Fuint 2) (word_196 v)).
Proof. rewrite - (closed_word_196_value v). unfold expr_word_196, closed_word_196.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_197_value v env
 (H0 : VM.find 158 env = Some (Gval (Fuint 3) (word_158 v)))
 : eval_hfexpr expr_word_197 env env = Some (Gval (Fuint 1) (word_197 v)).
Proof. rewrite - (closed_word_197_value v). unfold expr_word_197, closed_word_197.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.
Lemma local_word_198_value v env
 (H0 : VM.find 196 env = Some (Gval (Fuint 2) (word_196 v)))
 (H1 : VM.find 197 env = Some (Gval (Fuint 1) (word_197 v)))
 : eval_hfexpr expr_word_198 env env = Some (Gval (Fuint 2) (word_198 v)).
Proof. rewrite - (closed_word_198_value v). unfold expr_word_198, closed_word_198.
 cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_type_of_expr, eval_type_of_ref; cbn [type_of_expr'].
 rewrite ?H0 ?H1.
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity. Qed.

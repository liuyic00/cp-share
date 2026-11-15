From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing ReferenceNodes.
Local Open Scope Z_scope.
Lemma binary_lt_unsigned a b : N.ltb (to_N a) (to_N b) = Z.ltb (to_Zpos a) (to_Zpos b).
Proof.
 rewrite !to_Zpos_N. destruct (N.ltb_spec0 (to_N a) (to_N b)) as [lt|ge].
 - symmetry. apply Z.ltb_lt. apply N2Z.inj_lt. exact lt.
 - symmetry. apply Z.ltb_ge. apply N2Z.inj_le. apply N.nlt_ge. exact ge.
Qed.
Lemma binary_le_unsigned a b : N.leb (to_N a) (to_N b) = Z.leb (to_Zpos a) (to_Zpos b).
Proof.
 rewrite !to_Zpos_N. destruct (N.leb_spec0 (to_N a) (to_N b)) as [le|gt].
 - symmetry. apply Z.leb_le. apply N2Z.inj_le. exact le.
 - symmetry. apply Z.leb_gt. apply N2Z.inj_lt. apply N.nle_gt. exact gt.
Qed.

Transparent word_14.
Lemma scalar_shape_14 v : word_14 v = [:: to_N (word_13 v) == to_N ([::false; false; false])].
Proof. unfold word_14, closed_14, expr_14, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_14.
Lemma scalar_integer_14 s i ghost : to_Zpos (word_14 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::false; false; false])) then 1 else 0.
Proof. rewrite scalar_shape_14. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_420.
Lemma scalar_shape_420 v : word_420 v = [:: to_N (word_13 v) == to_N ([::false; false; false])].
Proof. unfold word_420, closed_420, expr_420, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_420.
Lemma scalar_integer_420 s i ghost : to_Zpos (word_420 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::false; false; false])) then 1 else 0.
Proof. rewrite scalar_shape_420. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_15.
Lemma scalar_shape_15 v : word_15 v = andB (word_2 v) (word_3 v).
Proof. unfold word_15, closed_15, expr_15, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_15.
Lemma scalar_integer_15 s i ghost : to_Zpos (word_15 (encoded_leaves s i ghost)) = Z.land (to_Zpos (word_2 (encoded_leaves s i ghost))) (to_Zpos (word_3 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_15. apply unsigned_and. rewrite encoded_word_2_size. rewrite encoded_word_3_size. reflexivity. Qed.
Transparent word_16.
Lemma scalar_shape_16 v : word_16 v = andB (word_14 v) (word_15 v).
Proof. unfold word_16, closed_16, expr_16, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_16.
Lemma scalar_integer_16 s i ghost : to_Zpos (word_16 (encoded_leaves s i ghost)) = Z.land (to_Zpos (word_14 (encoded_leaves s i ghost))) (to_Zpos (word_15 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_16. apply unsigned_and. rewrite encoded_word_14_size. rewrite encoded_word_15_size. reflexivity. Qed.
Transparent word_17.
Lemma scalar_shape_17 v : word_17 v = [:: to_N (word_5 v) == to_N ([::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])].
Proof. unfold word_17, closed_17, expr_17, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_17.
Lemma scalar_integer_17 s i ghost : to_Zpos (word_17 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_5 (encoded_leaves s i ghost))) (to_Zpos ([::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])) then 1 else 0.
Proof. rewrite scalar_shape_17. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_24.
Lemma scalar_shape_24 v : word_24 v = andB (word_23 v) (word_10 v).
Proof. unfold word_24, closed_24, expr_24, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_24.
Lemma scalar_integer_24 s i ghost : to_Zpos (word_24 (encoded_leaves s i ghost)) = Z.land (to_Zpos (word_23 (encoded_leaves s i ghost))) (to_Zpos (word_10 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_24. apply unsigned_and. rewrite encoded_word_23_size. rewrite encoded_word_10_size. reflexivity. Qed.
Transparent word_25.
Lemma scalar_shape_25 v : word_25 v = from_Z 65 (to_Zpos ([::false]) - to_Zpos (word_4 v)).
Proof. unfold word_25, closed_25, expr_25, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_25.
Lemma scalar_integer_25 s i ghost : to_Zpos (word_25 (encoded_leaves s i ghost)) = normalize 65 (to_Zpos ([::false]) - to_Zpos (word_4 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_25. apply unsigned_from_Z. Qed.
Transparent word_29.
Lemma scalar_shape_29 v : word_29 v = andB (word_28 v) (word_10 v).
Proof. unfold word_29, closed_29, expr_29, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_29.
Lemma scalar_integer_29 s i ghost : to_Zpos (word_29 (encoded_leaves s i ghost)) = Z.land (to_Zpos (word_28 (encoded_leaves s i ghost))) (to_Zpos (word_10 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_29. apply unsigned_and. rewrite encoded_word_28_size. rewrite encoded_word_10_size. reflexivity. Qed.
Transparent word_30.
Lemma scalar_shape_30 v : word_30 v = from_Z 65 (to_Zpos ([::false]) - to_Zpos (word_5 v)).
Proof. unfold word_30, closed_30, expr_30, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_30.
Lemma scalar_integer_30 s i ghost : to_Zpos (word_30 (encoded_leaves s i ghost)) = normalize 65 (to_Zpos ([::false]) - to_Zpos (word_5 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_30. apply unsigned_from_Z. Qed.
Transparent word_35.
Lemma scalar_shape_35 v : word_35 v = xorB (word_24 v) (word_29 v).
Proof. unfold word_35, closed_35, expr_35, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_35.
Lemma scalar_integer_35 s i ghost : to_Zpos (word_35 (encoded_leaves s i ghost)) = Z.lxor (to_Zpos (word_24 (encoded_leaves s i ghost))) (to_Zpos (word_29 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_35. apply unsigned_xor. rewrite encoded_word_24_size. rewrite encoded_word_29_size. reflexivity. Qed.
Transparent word_36.
Lemma scalar_shape_36 v : word_36 v = [:: to_N (word_17 v) == to_N ([::false])].
Proof. unfold word_36, closed_36, expr_36, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_36.
Lemma scalar_integer_36 s i ghost : to_Zpos (word_36 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_17 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_36. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_37.
Lemma scalar_shape_37 v : word_37 v = andB (word_35 v) (word_36 v).
Proof. unfold word_37, closed_37, expr_37, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_37.
Lemma scalar_integer_37 s i ghost : to_Zpos (word_37 (encoded_leaves s i ghost)) = Z.land (to_Zpos (word_35 (encoded_leaves s i ghost))) (to_Zpos (word_36 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_37. apply unsigned_and. rewrite encoded_word_35_size. rewrite encoded_word_36_size. reflexivity. Qed.
Transparent word_52.
Lemma scalar_shape_52 v : word_52 v = [:: to_N (word_13 v) == to_N ([::true; false; false])].
Proof. unfold word_52, closed_52, expr_52, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_52.
Lemma scalar_integer_52 s i ghost : to_Zpos (word_52 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::true; false; false])) then 1 else 0.
Proof. rewrite scalar_shape_52. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_208.
Lemma scalar_shape_208 v : word_208 v = from_N 8 ((to_N ([::false; false; false; false; false; false; true]) + to_N (word_207 v))%num).
Proof. unfold word_208, closed_208, expr_208, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_208.
Lemma scalar_integer_208 s i ghost : to_Zpos (word_208 (encoded_leaves s i ghost)) = normalize 8 (to_Zpos ([::false; false; false; false; false; false; true]) + to_Zpos (word_207 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_208. apply unsigned_from_N_add. Qed.
Transparent word_370.
Lemma scalar_shape_370 v : word_370 v = from_Z 8 (to_Zpos (word_209 v) - to_Zpos (word_369 v)).
Proof. unfold word_370, closed_370, expr_370, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_370.
Lemma scalar_integer_370 s i ghost : to_Zpos (word_370 (encoded_leaves s i ghost)) = normalize 8 (to_Zpos (word_209 (encoded_leaves s i ghost)) - to_Zpos (word_369 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_370. apply unsigned_from_Z. Qed.
Transparent word_372.
Lemma scalar_shape_372 v : word_372 v = [:: N.leb (to_N ([::true; true; true; true; true; true])) (to_N (word_371 v))].
Proof. unfold word_372, closed_372, expr_372, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_372.
Lemma scalar_integer_372 s i ghost : to_Zpos (word_372 (encoded_leaves s i ghost)) = if Z.leb (to_Zpos ([::true; true; true; true; true; true])) (to_Zpos (word_371 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_372. rewrite unsigned_singleton binary_le_unsigned. reflexivity. Qed.
Transparent word_375.
Lemma scalar_shape_375 v : word_375 v = [:: to_N (word_13 v) == to_N ([::false; true; false])].
Proof. unfold word_375, closed_375, expr_375, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_375.
Lemma scalar_integer_375 s i ghost : to_Zpos (word_375 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::false; true; false])) then 1 else 0.
Proof. rewrite scalar_shape_375. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_377.
Lemma scalar_shape_377 v : word_377 v = [:: to_N (word_13 v) == to_N ([::true; true; false])].
Proof. unfold word_377, closed_377, expr_377, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_377.
Lemma scalar_integer_377 s i ghost : to_Zpos (word_377 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; false])) then 1 else 0.
Proof. rewrite scalar_shape_377. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_378.
Lemma scalar_shape_378 v : word_378 v = [:: N.leb (to_N (word_40 v)) (to_N (word_21 v))].
Proof. unfold word_378, closed_378, expr_378, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_378.
Lemma scalar_integer_378 s i ghost : to_Zpos (word_378 (encoded_leaves s i ghost)) = if Z.leb (to_Zpos (word_40 (encoded_leaves s i ghost))) (to_Zpos (word_21 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_378. rewrite unsigned_singleton binary_le_unsigned. reflexivity. Qed.
Transparent word_379.
Lemma scalar_shape_379 v : word_379 v = from_Z 66 (to_Zpos (word_21 v) - to_Zpos (word_40 v)).
Proof. unfold word_379, closed_379, expr_379, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_379.
Lemma scalar_integer_379 s i ghost : to_Zpos (word_379 (encoded_leaves s i ghost)) = normalize 66 (to_Zpos (word_21 (encoded_leaves s i ghost)) - to_Zpos (word_40 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_379. apply unsigned_from_Z. Qed.
Transparent word_385.
Lemma scalar_shape_385 v : word_385 v = [:: to_N (word_51 v) == to_N ([::true; true; true; true; true; true])].
Proof. unfold word_385, closed_385, expr_385, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_385.
Lemma scalar_integer_385 s i ghost : to_Zpos (word_385 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_51 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; true; true; true; true])) then 1 else 0.
Proof. rewrite scalar_shape_385. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_386.
Lemma scalar_shape_386 v : word_386 v = from_N 7 ((to_N (word_51 v) + to_N ([::true]))%num).
Proof. unfold word_386, closed_386, expr_386, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_386.
Lemma scalar_integer_386 s i ghost : to_Zpos (word_386 (encoded_leaves s i ghost)) = normalize 7 (to_Zpos (word_51 (encoded_leaves s i ghost)) + to_Zpos ([::true])).
Proof. rewrite scalar_shape_386. apply unsigned_from_N_add. Qed.
Transparent word_388.
Lemma scalar_shape_388 v : word_388 v = [:: to_N (word_51 v) == to_N ([::true; true; true; true; true; true])].
Proof. unfold word_388, closed_388, expr_388, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_388.
Lemma scalar_integer_388 s i ghost : to_Zpos (word_388 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_51 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; true; true; true; true])) then 1 else 0.
Proof. rewrite scalar_shape_388. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_390.
Lemma scalar_shape_390 v : word_390 v = [:: to_N (word_13 v) == to_N ([::false; false; true])].
Proof. unfold word_390, closed_390, expr_390, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_390.
Lemma scalar_integer_390 s i ghost : to_Zpos (word_390 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::false; false; true])) then 1 else 0.
Proof. rewrite scalar_shape_390. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_406.
Lemma scalar_shape_406 v : word_406 v = from_Z 65 (to_Zpos ([::false]) - to_Zpos (word_22 v)).
Proof. unfold word_406, closed_406, expr_406, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_406.
Lemma scalar_integer_406 s i ghost : to_Zpos (word_406 (encoded_leaves s i ghost)) = normalize 65 (to_Zpos ([::false]) - to_Zpos (word_22 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_406. apply unsigned_from_Z. Qed.
Transparent word_409.
Lemma scalar_shape_409 v : word_409 v = from_Z 65 (to_Zpos ([::false]) - to_Zpos (word_405 v)).
Proof. unfold word_409, closed_409, expr_409, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_409.
Lemma scalar_integer_409 s i ghost : to_Zpos (word_409 (encoded_leaves s i ghost)) = normalize 65 (to_Zpos ([::false]) - to_Zpos (word_405 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_409. apply unsigned_from_Z. Qed.
Transparent word_419.
Lemma scalar_shape_419 v : word_419 v = [:: to_N (word_13 v) == to_N ([::false; false; true])].
Proof. unfold word_419, closed_419, expr_419, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_419.
Lemma scalar_integer_419 s i ghost : to_Zpos (word_419 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::false; false; true])) then 1 else 0.
Proof. rewrite scalar_shape_419. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_421.
Lemma scalar_shape_421 v : word_421 v = [:: to_N (word_22 v) == to_N ([::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])].
Proof. unfold word_421, closed_421, expr_421, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_421.
Lemma scalar_integer_421 s i ghost : to_Zpos (word_421 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_22 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])) then 1 else 0.
Proof. rewrite scalar_shape_421. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_423.
Lemma scalar_shape_423 v : word_423 v = [:: to_N (word_422 v) == to_N ([::false])].
Proof. unfold word_423, closed_423, expr_423, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_423.
Lemma scalar_integer_423 s i ghost : to_Zpos (word_423 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_422 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_423. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_424.
Lemma scalar_shape_424 v : word_424 v = [:: to_N (word_421 v) == to_N ([::false])].
Proof. unfold word_424, closed_424, expr_424, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_424.
Lemma scalar_integer_424 s i ghost : to_Zpos (word_424 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_421 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_424. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_426.
Lemma scalar_shape_426 v : word_426 v = [:: to_N (word_405 v) == to_N (word_425 v)].
Proof. unfold word_426, closed_426, expr_426, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_426.
Lemma scalar_integer_426 s i ghost : to_Zpos (word_426 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_405 (encoded_leaves s i ghost))) (to_Zpos (word_425 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_426. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_428.
Lemma scalar_shape_428 v : word_428 v = [:: to_N (word_427 v) == to_N ([::false])].
Proof. unfold word_428, closed_428, expr_428, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_428.
Lemma scalar_integer_428 s i ghost : to_Zpos (word_428 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_427 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_428. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_429.
Lemma scalar_shape_429 v : word_429 v = [:: to_N (word_426 v) == to_N ([::false])].
Proof. unfold word_429, closed_429, expr_429, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_429.
Lemma scalar_integer_429 s i ghost : to_Zpos (word_429 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_426 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_429. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_430.
Lemma scalar_shape_430 v : word_430 v = [:: to_N (word_40 v) != to_N ([::false])].
Proof. unfold word_430, closed_430, expr_430, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_430.
Lemma scalar_integer_430 s i ghost : to_Zpos (word_430 (encoded_leaves s i ghost)) = if negb (Z.eqb (to_Zpos (word_40 (encoded_leaves s i ghost))) (to_Zpos ([::false]))) then 1 else 0.
Proof. rewrite scalar_shape_430. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_432.
Lemma scalar_shape_432 v : word_432 v = [:: to_N (word_431 v) == to_N ([::false])].
Proof. unfold word_432, closed_432, expr_432, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_432.
Lemma scalar_integer_432 s i ghost : to_Zpos (word_432 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_431 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_432. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_433.
Lemma scalar_shape_433 v : word_433 v = [:: to_N (word_430 v) == to_N ([::false])].
Proof. unfold word_433, closed_433, expr_433, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_433.
Lemma scalar_integer_433 s i ghost : to_Zpos (word_433 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_430 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_433. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_434.
Lemma scalar_shape_434 v : word_434 v = from_N 128 ((to_N (word_22 v) * to_N (word_40 v))%num).
Proof. unfold word_434, closed_434, expr_434, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_434.
Lemma scalar_integer_434 s i ghost : to_Zpos (word_434 (encoded_leaves s i ghost)) = normalize 128 (to_Zpos (word_22 (encoded_leaves s i ghost)) * to_Zpos (word_40 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_434. apply unsigned_from_N_mul. Qed.
Transparent word_435.
Lemma scalar_shape_435 v : word_435 v = from_N 129 ((to_N (word_434 v) + to_N (word_405 v))%num).
Proof. unfold word_435, closed_435, expr_435, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_435.
Lemma scalar_integer_435 s i ghost : to_Zpos (word_435 (encoded_leaves s i ghost)) = normalize 129 (to_Zpos (word_434 (encoded_leaves s i ghost)) + to_Zpos (word_405 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_435. apply unsigned_from_N_add. Qed.
Transparent word_437.
Lemma scalar_shape_437 v : word_437 v = [:: to_N (word_435 v) == to_N (word_436 v)].
Proof. unfold word_437, closed_437, expr_437, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_437.
Lemma scalar_integer_437 s i ghost : to_Zpos (word_437 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_435 (encoded_leaves s i ghost))) (to_Zpos (word_436 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_437. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_439.
Lemma scalar_shape_439 v : word_439 v = [:: to_N (word_438 v) == to_N ([::false])].
Proof. unfold word_439, closed_439, expr_439, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_439.
Lemma scalar_integer_439 s i ghost : to_Zpos (word_439 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_438 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_439. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_440.
Lemma scalar_shape_440 v : word_440 v = [:: to_N (word_437 v) == to_N ([::false])].
Proof. unfold word_440, closed_440, expr_440, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_440.
Lemma scalar_integer_440 s i ghost : to_Zpos (word_440 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_437 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_440. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_441.
Lemma scalar_shape_441 v : word_441 v = [:: N.ltb (to_N (word_405 v)) (to_N (word_40 v))].
Proof. unfold word_441, closed_441, expr_441, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_441.
Lemma scalar_integer_441 s i ghost : to_Zpos (word_441 (encoded_leaves s i ghost)) = if Z.ltb (to_Zpos (word_405 (encoded_leaves s i ghost))) (to_Zpos (word_40 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_441. rewrite unsigned_singleton binary_lt_unsigned. reflexivity. Qed.
Transparent word_443.
Lemma scalar_shape_443 v : word_443 v = [:: to_N (word_442 v) == to_N ([::false])].
Proof. unfold word_443, closed_443, expr_443, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_443.
Lemma scalar_integer_443 s i ghost : to_Zpos (word_443 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_442 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_443. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_444.
Lemma scalar_shape_444 v : word_444 v = [:: to_N (word_441 v) == to_N ([::false])].
Proof. unfold word_444, closed_444, expr_444, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_444.
Lemma scalar_integer_444 s i ghost : to_Zpos (word_444 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_441 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_444. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_448.
Lemma scalar_shape_448 v : word_448 v = [:: to_N (word_446 v) == to_N ([::true; false; false])].
Proof. unfold word_448, closed_448, expr_448, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_448.
Lemma scalar_integer_448 s i ghost : to_Zpos (word_448 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_446 (encoded_leaves s i ghost))) (to_Zpos ([::true; false; false])) then 1 else 0.
Proof. rewrite scalar_shape_448. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_449.
Lemma scalar_shape_449 v : word_449 v = [:: to_N (word_13 v) == to_N ([::false; true; false])].
Proof. unfold word_449, closed_449, expr_449, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_449.
Lemma scalar_integer_449 s i ghost : to_Zpos (word_449 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::false; true; false])) then 1 else 0.
Proof. rewrite scalar_shape_449. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_451.
Lemma scalar_shape_451 v : word_451 v = [:: to_N (word_450 v) == to_N ([::false])].
Proof. unfold word_451, closed_451, expr_451, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_451.
Lemma scalar_integer_451 s i ghost : to_Zpos (word_451 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_450 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_451. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_452.
Lemma scalar_shape_452 v : word_452 v = [:: to_N (word_449 v) == to_N ([::false])].
Proof. unfold word_452, closed_452, expr_452, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_452.
Lemma scalar_integer_452 s i ghost : to_Zpos (word_452 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_449 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_452. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_453.
Lemma scalar_shape_453 v : word_453 v = [:: to_N (word_446 v) == to_N ([::false; true; false])].
Proof. unfold word_453, closed_453, expr_453, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_453.
Lemma scalar_integer_453 s i ghost : to_Zpos (word_453 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_446 (encoded_leaves s i ghost))) (to_Zpos ([::false; true; false])) then 1 else 0.
Proof. rewrite scalar_shape_453. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_454.
Lemma scalar_shape_454 v : word_454 v = [:: to_N (word_13 v) == to_N ([::true; true; false])].
Proof. unfold word_454, closed_454, expr_454, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_454.
Lemma scalar_integer_454 s i ghost : to_Zpos (word_454 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; false])) then 1 else 0.
Proof. rewrite scalar_shape_454. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_456.
Lemma scalar_shape_456 v : word_456 v = [:: to_N (word_455 v) == to_N ([::false])].
Proof. unfold word_456, closed_456, expr_456, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_456.
Lemma scalar_integer_456 s i ghost : to_Zpos (word_456 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_455 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_456. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_457.
Lemma scalar_shape_457 v : word_457 v = [:: to_N (word_454 v) == to_N ([::false])].
Proof. unfold word_457, closed_457, expr_457, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_457.
Lemma scalar_integer_457 s i ghost : to_Zpos (word_457 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_454 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_457. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_458.
Lemma scalar_shape_458 v : word_458 v = [:: to_N (word_446 v) == to_N ([::true; true; false])].
Proof. unfold word_458, closed_458, expr_458, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_458.
Lemma scalar_integer_458 s i ghost : to_Zpos (word_458 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_446 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; false])) then 1 else 0.
Proof. rewrite scalar_shape_458. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_459.
Lemma scalar_shape_459 v : word_459 v = [:: to_N (word_447 v) == to_N ([::true; true; true; true; true; true])].
Proof. unfold word_459, closed_459, expr_459, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_459.
Lemma scalar_integer_459 s i ghost : to_Zpos (word_459 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_447 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; true; true; true; true])) then 1 else 0.
Proof. rewrite scalar_shape_459. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_461.
Lemma scalar_shape_461 v : word_461 v = [:: to_N (word_13 v) == to_N (word_460 v)].
Proof. unfold word_461, closed_461, expr_461, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_461.
Lemma scalar_integer_461 s i ghost : to_Zpos (word_461 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_13 (encoded_leaves s i ghost))) (to_Zpos (word_460 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_461. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_463.
Lemma scalar_shape_463 v : word_463 v = [:: to_N (word_462 v) == to_N ([::false])].
Proof. unfold word_463, closed_463, expr_463, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_463.
Lemma scalar_integer_463 s i ghost : to_Zpos (word_463 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_462 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_463. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_464.
Lemma scalar_shape_464 v : word_464 v = [:: to_N (word_461 v) == to_N ([::false])].
Proof. unfold word_464, closed_464, expr_464, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_464.
Lemma scalar_integer_464 s i ghost : to_Zpos (word_464 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_461 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_464. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_465.
Lemma scalar_shape_465 v : word_465 v = [:: to_N (word_447 v) == to_N ([::true; true; true; true; true; true])].
Proof. unfold word_465, closed_465, expr_465, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_465.
Lemma scalar_integer_465 s i ghost : to_Zpos (word_465 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_447 (encoded_leaves s i ghost))) (to_Zpos ([::true; true; true; true; true; true])) then 1 else 0.
Proof. rewrite scalar_shape_465. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_466.
Lemma scalar_shape_466 v : word_466 v = from_N 7 ((to_N (word_447 v) + to_N ([::true]))%num).
Proof. unfold word_466, closed_466, expr_466, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_466.
Lemma scalar_integer_466 s i ghost : to_Zpos (word_466 (encoded_leaves s i ghost)) = normalize 7 (to_Zpos (word_447 (encoded_leaves s i ghost)) + to_Zpos ([::true])).
Proof. rewrite scalar_shape_466. apply unsigned_from_N_add. Qed.
Transparent word_469.
Lemma scalar_shape_469 v : word_469 v = [:: to_N (word_51 v) == to_N (word_468 v)].
Proof. unfold word_469, closed_469, expr_469, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_469.
Lemma scalar_integer_469 s i ghost : to_Zpos (word_469 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_51 (encoded_leaves s i ghost))) (to_Zpos (word_468 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_469. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_471.
Lemma scalar_shape_471 v : word_471 v = [:: to_N (word_470 v) == to_N ([::false])].
Proof. unfold word_471, closed_471, expr_471, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_471.
Lemma scalar_integer_471 s i ghost : to_Zpos (word_471 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_470 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_471. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_472.
Lemma scalar_shape_472 v : word_472 v = [:: to_N (word_469 v) == to_N ([::false])].
Proof. unfold word_472, closed_472, expr_472, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_472.
Lemma scalar_integer_472 s i ghost : to_Zpos (word_472 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_469 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_472. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_473.
Lemma scalar_shape_473 v : word_473 v = [:: to_N (word_7 v) == to_N ([::false])].
Proof. unfold word_473, closed_473, expr_473, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_473.
Lemma scalar_integer_473 s i ghost : to_Zpos (word_473 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_7 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_473. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_474.
Lemma scalar_shape_474 v : word_474 v = andB (word_8 v) (word_473 v).
Proof. unfold word_474, closed_474, expr_474, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_474.
Lemma scalar_integer_474 s i ghost : to_Zpos (word_474 (encoded_leaves s i ghost)) = Z.land (to_Zpos (word_8 (encoded_leaves s i ghost))) (to_Zpos (word_473 (encoded_leaves s i ghost))).
Proof. rewrite scalar_shape_474. apply unsigned_and. rewrite encoded_word_8_size. rewrite encoded_word_473_size. reflexivity. Qed.
Transparent word_478.
Lemma scalar_shape_478 v : word_478 v = [:: to_N (word_477 v) == to_N ([::false])].
Proof. unfold word_478, closed_478, expr_478, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_478.
Lemma scalar_integer_478 s i ghost : to_Zpos (word_478 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_477 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_478. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_479.
Lemma scalar_shape_479 v : word_479 v = [:: to_N (word_8 v) == to_N ([::false])].
Proof. unfold word_479, closed_479, expr_479, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_479.
Lemma scalar_integer_479 s i ghost : to_Zpos (word_479 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_8 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_479. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_480.
Lemma scalar_shape_480 v : word_480 v = [:: to_N (word_9 v) == to_N (word_476 v)].
Proof. unfold word_480, closed_480, expr_480, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_480.
Lemma scalar_integer_480 s i ghost : to_Zpos (word_480 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_9 (encoded_leaves s i ghost))) (to_Zpos (word_476 (encoded_leaves s i ghost))) then 1 else 0.
Proof. rewrite scalar_shape_480. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_482.
Lemma scalar_shape_482 v : word_482 v = [:: to_N (word_481 v) == to_N ([::false])].
Proof. unfold word_482, closed_482, expr_482, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_482.
Lemma scalar_integer_482 s i ghost : to_Zpos (word_482 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_481 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_482. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Transparent word_483.
Lemma scalar_shape_483 v : word_483 v = [:: to_N (word_480 v) == to_N ([::false])].
Proof. unfold word_483, closed_483, expr_483, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_483.
Lemma scalar_integer_483 s i ghost : to_Zpos (word_483 (encoded_leaves s i ghost)) = if Z.eqb (to_Zpos (word_480 (encoded_leaves s i ghost))) (to_Zpos ([::false])) then 1 else 0.
Proof. rewrite scalar_shape_483. rewrite unsigned_singleton numeric_equality_unsigned. reflexivity. Qed.
Print Assumptions scalar_integer_483.

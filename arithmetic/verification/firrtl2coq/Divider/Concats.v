From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Typing.
Local Open Scope Z_scope.

Transparent word_42.
Lemma concat_shape_42 v : word_42 v = ([::false]) ++ (word_27 v).
Proof. unfold word_42, closed_42, expr_42, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_42.
Lemma concat_integer_42 s i ghost : to_Zpos (word_42 (encoded_leaves s i ghost)) = to_Zpos ([::false]) + to_Zpos (word_27 (encoded_leaves s i ghost)) * modulus 1.
Proof. rewrite concat_shape_42 unsigned_cat.
 reflexivity. Qed.
Transparent word_76.
Lemma concat_shape_76 v : word_76 v = (word_75 v) ++ (word_64 v).
Proof. unfold word_76, closed_76, expr_76, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_76.
Lemma concat_integer_76 s i ghost : to_Zpos (word_76 (encoded_leaves s i ghost)) = to_Zpos (word_75 (encoded_leaves s i ghost)) + to_Zpos (word_64 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_76 unsigned_cat.
 rewrite encoded_word_75_size.
 reflexivity. Qed.
Transparent word_91.
Lemma concat_shape_91 v : word_91 v = (word_90 v) ++ (word_79 v).
Proof. unfold word_91, closed_91, expr_91, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_91.
Lemma concat_integer_91 s i ghost : to_Zpos (word_91 (encoded_leaves s i ghost)) = to_Zpos (word_90 (encoded_leaves s i ghost)) + to_Zpos (word_79 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_91 unsigned_cat.
 rewrite encoded_word_90_size.
 reflexivity. Qed.
Transparent word_93.
Lemma concat_shape_93 v : word_93 v = (word_92 v) ++ (word_61 v).
Proof. unfold word_93, closed_93, expr_93, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_93.
Lemma concat_integer_93 s i ghost : to_Zpos (word_93 (encoded_leaves s i ghost)) = to_Zpos (word_92 (encoded_leaves s i ghost)) + to_Zpos (word_61 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_93 unsigned_cat.
 rewrite encoded_word_92_size.
 reflexivity. Qed.
Transparent word_111.
Lemma concat_shape_111 v : word_111 v = (word_110 v) ++ (word_99 v).
Proof. unfold word_111, closed_111, expr_111, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_111.
Lemma concat_integer_111 s i ghost : to_Zpos (word_111 (encoded_leaves s i ghost)) = to_Zpos (word_110 (encoded_leaves s i ghost)) + to_Zpos (word_99 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_111 unsigned_cat.
 rewrite encoded_word_110_size.
 reflexivity. Qed.
Transparent word_126.
Lemma concat_shape_126 v : word_126 v = (word_125 v) ++ (word_114 v).
Proof. unfold word_126, closed_126, expr_126, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_126.
Lemma concat_integer_126 s i ghost : to_Zpos (word_126 (encoded_leaves s i ghost)) = to_Zpos (word_125 (encoded_leaves s i ghost)) + to_Zpos (word_114 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_126 unsigned_cat.
 rewrite encoded_word_125_size.
 reflexivity. Qed.
Transparent word_128.
Lemma concat_shape_128 v : word_128 v = (word_127 v) ++ (word_96 v).
Proof. unfold word_128, closed_128, expr_128, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_128.
Lemma concat_integer_128 s i ghost : to_Zpos (word_128 (encoded_leaves s i ghost)) = to_Zpos (word_127 (encoded_leaves s i ghost)) + to_Zpos (word_96 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_128 unsigned_cat.
 rewrite encoded_word_127_size.
 reflexivity. Qed.
Transparent word_130.
Lemma concat_shape_130 v : word_130 v = (word_129 v) ++ (word_58 v).
Proof. unfold word_130, closed_130, expr_130, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_130.
Lemma concat_integer_130 s i ghost : to_Zpos (word_130 (encoded_leaves s i ghost)) = to_Zpos (word_129 (encoded_leaves s i ghost)) + to_Zpos (word_58 (encoded_leaves s i ghost)) * modulus 4.
Proof. rewrite concat_shape_130 unsigned_cat.
 rewrite encoded_word_129_size.
 reflexivity. Qed.
Transparent word_151.
Lemma concat_shape_151 v : word_151 v = (word_150 v) ++ (word_139 v).
Proof. unfold word_151, closed_151, expr_151, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_151.
Lemma concat_integer_151 s i ghost : to_Zpos (word_151 (encoded_leaves s i ghost)) = to_Zpos (word_150 (encoded_leaves s i ghost)) + to_Zpos (word_139 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_151 unsigned_cat.
 rewrite encoded_word_150_size.
 reflexivity. Qed.
Transparent word_166.
Lemma concat_shape_166 v : word_166 v = (word_165 v) ++ (word_154 v).
Proof. unfold word_166, closed_166, expr_166, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_166.
Lemma concat_integer_166 s i ghost : to_Zpos (word_166 (encoded_leaves s i ghost)) = to_Zpos (word_165 (encoded_leaves s i ghost)) + to_Zpos (word_154 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_166 unsigned_cat.
 rewrite encoded_word_165_size.
 reflexivity. Qed.
Transparent word_168.
Lemma concat_shape_168 v : word_168 v = (word_167 v) ++ (word_136 v).
Proof. unfold word_168, closed_168, expr_168, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_168.
Lemma concat_integer_168 s i ghost : to_Zpos (word_168 (encoded_leaves s i ghost)) = to_Zpos (word_167 (encoded_leaves s i ghost)) + to_Zpos (word_136 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_168 unsigned_cat.
 rewrite encoded_word_167_size.
 reflexivity. Qed.
Transparent word_186.
Lemma concat_shape_186 v : word_186 v = (word_185 v) ++ (word_174 v).
Proof. unfold word_186, closed_186, expr_186, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_186.
Lemma concat_integer_186 s i ghost : to_Zpos (word_186 (encoded_leaves s i ghost)) = to_Zpos (word_185 (encoded_leaves s i ghost)) + to_Zpos (word_174 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_186 unsigned_cat.
 rewrite encoded_word_185_size.
 reflexivity. Qed.
Transparent word_201.
Lemma concat_shape_201 v : word_201 v = (word_200 v) ++ (word_189 v).
Proof. unfold word_201, closed_201, expr_201, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_201.
Lemma concat_integer_201 s i ghost : to_Zpos (word_201 (encoded_leaves s i ghost)) = to_Zpos (word_200 (encoded_leaves s i ghost)) + to_Zpos (word_189 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_201 unsigned_cat.
 rewrite encoded_word_200_size.
 reflexivity. Qed.
Transparent word_203.
Lemma concat_shape_203 v : word_203 v = (word_202 v) ++ (word_171 v).
Proof. unfold word_203, closed_203, expr_203, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_203.
Lemma concat_integer_203 s i ghost : to_Zpos (word_203 (encoded_leaves s i ghost)) = to_Zpos (word_202 (encoded_leaves s i ghost)) + to_Zpos (word_171 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_203 unsigned_cat.
 rewrite encoded_word_202_size.
 reflexivity. Qed.
Transparent word_205.
Lemma concat_shape_205 v : word_205 v = (word_204 v) ++ (word_133 v).
Proof. unfold word_205, closed_205, expr_205, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_205.
Lemma concat_integer_205 s i ghost : to_Zpos (word_205 (encoded_leaves s i ghost)) = to_Zpos (word_204 (encoded_leaves s i ghost)) + to_Zpos (word_133 (encoded_leaves s i ghost)) * modulus 4.
Proof. rewrite concat_shape_205 unsigned_cat.
 rewrite encoded_word_204_size.
 reflexivity. Qed.
Transparent word_207.
Lemma concat_shape_207 v : word_207 v = (word_206 v) ++ (word_55 v).
Proof. unfold word_207, closed_207, expr_207, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_207.
Lemma concat_integer_207 s i ghost : to_Zpos (word_207 (encoded_leaves s i ghost)) = to_Zpos (word_206 (encoded_leaves s i ghost)) + to_Zpos (word_55 (encoded_leaves s i ghost)) * modulus 5.
Proof. rewrite concat_shape_207 unsigned_cat.
 rewrite encoded_word_206_size.
 reflexivity. Qed.
Transparent word_236.
Lemma concat_shape_236 v : word_236 v = (word_235 v) ++ (word_224 v).
Proof. unfold word_236, closed_236, expr_236, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_236.
Lemma concat_integer_236 s i ghost : to_Zpos (word_236 (encoded_leaves s i ghost)) = to_Zpos (word_235 (encoded_leaves s i ghost)) + to_Zpos (word_224 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_236 unsigned_cat.
 rewrite encoded_word_235_size.
 reflexivity. Qed.
Transparent word_251.
Lemma concat_shape_251 v : word_251 v = (word_250 v) ++ (word_239 v).
Proof. unfold word_251, closed_251, expr_251, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_251.
Lemma concat_integer_251 s i ghost : to_Zpos (word_251 (encoded_leaves s i ghost)) = to_Zpos (word_250 (encoded_leaves s i ghost)) + to_Zpos (word_239 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_251 unsigned_cat.
 rewrite encoded_word_250_size.
 reflexivity. Qed.
Transparent word_253.
Lemma concat_shape_253 v : word_253 v = (word_252 v) ++ (word_221 v).
Proof. unfold word_253, closed_253, expr_253, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_253.
Lemma concat_integer_253 s i ghost : to_Zpos (word_253 (encoded_leaves s i ghost)) = to_Zpos (word_252 (encoded_leaves s i ghost)) + to_Zpos (word_221 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_253 unsigned_cat.
 rewrite encoded_word_252_size.
 reflexivity. Qed.
Transparent word_271.
Lemma concat_shape_271 v : word_271 v = (word_270 v) ++ (word_259 v).
Proof. unfold word_271, closed_271, expr_271, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_271.
Lemma concat_integer_271 s i ghost : to_Zpos (word_271 (encoded_leaves s i ghost)) = to_Zpos (word_270 (encoded_leaves s i ghost)) + to_Zpos (word_259 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_271 unsigned_cat.
 rewrite encoded_word_270_size.
 reflexivity. Qed.
Transparent word_286.
Lemma concat_shape_286 v : word_286 v = (word_285 v) ++ (word_274 v).
Proof. unfold word_286, closed_286, expr_286, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_286.
Lemma concat_integer_286 s i ghost : to_Zpos (word_286 (encoded_leaves s i ghost)) = to_Zpos (word_285 (encoded_leaves s i ghost)) + to_Zpos (word_274 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_286 unsigned_cat.
 rewrite encoded_word_285_size.
 reflexivity. Qed.
Transparent word_288.
Lemma concat_shape_288 v : word_288 v = (word_287 v) ++ (word_256 v).
Proof. unfold word_288, closed_288, expr_288, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_288.
Lemma concat_integer_288 s i ghost : to_Zpos (word_288 (encoded_leaves s i ghost)) = to_Zpos (word_287 (encoded_leaves s i ghost)) + to_Zpos (word_256 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_288 unsigned_cat.
 rewrite encoded_word_287_size.
 reflexivity. Qed.
Transparent word_290.
Lemma concat_shape_290 v : word_290 v = (word_289 v) ++ (word_218 v).
Proof. unfold word_290, closed_290, expr_290, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_290.
Lemma concat_integer_290 s i ghost : to_Zpos (word_290 (encoded_leaves s i ghost)) = to_Zpos (word_289 (encoded_leaves s i ghost)) + to_Zpos (word_218 (encoded_leaves s i ghost)) * modulus 4.
Proof. rewrite concat_shape_290 unsigned_cat.
 rewrite encoded_word_289_size.
 reflexivity. Qed.
Transparent word_311.
Lemma concat_shape_311 v : word_311 v = (word_310 v) ++ (word_299 v).
Proof. unfold word_311, closed_311, expr_311, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_311.
Lemma concat_integer_311 s i ghost : to_Zpos (word_311 (encoded_leaves s i ghost)) = to_Zpos (word_310 (encoded_leaves s i ghost)) + to_Zpos (word_299 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_311 unsigned_cat.
 rewrite encoded_word_310_size.
 reflexivity. Qed.
Transparent word_326.
Lemma concat_shape_326 v : word_326 v = (word_325 v) ++ (word_314 v).
Proof. unfold word_326, closed_326, expr_326, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_326.
Lemma concat_integer_326 s i ghost : to_Zpos (word_326 (encoded_leaves s i ghost)) = to_Zpos (word_325 (encoded_leaves s i ghost)) + to_Zpos (word_314 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_326 unsigned_cat.
 rewrite encoded_word_325_size.
 reflexivity. Qed.
Transparent word_328.
Lemma concat_shape_328 v : word_328 v = (word_327 v) ++ (word_296 v).
Proof. unfold word_328, closed_328, expr_328, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_328.
Lemma concat_integer_328 s i ghost : to_Zpos (word_328 (encoded_leaves s i ghost)) = to_Zpos (word_327 (encoded_leaves s i ghost)) + to_Zpos (word_296 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_328 unsigned_cat.
 rewrite encoded_word_327_size.
 reflexivity. Qed.
Transparent word_346.
Lemma concat_shape_346 v : word_346 v = (word_345 v) ++ (word_334 v).
Proof. unfold word_346, closed_346, expr_346, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_346.
Lemma concat_integer_346 s i ghost : to_Zpos (word_346 (encoded_leaves s i ghost)) = to_Zpos (word_345 (encoded_leaves s i ghost)) + to_Zpos (word_334 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_346 unsigned_cat.
 rewrite encoded_word_345_size.
 reflexivity. Qed.
Transparent word_361.
Lemma concat_shape_361 v : word_361 v = (word_360 v) ++ (word_349 v).
Proof. unfold word_361, closed_361, expr_361, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_361.
Lemma concat_integer_361 s i ghost : to_Zpos (word_361 (encoded_leaves s i ghost)) = to_Zpos (word_360 (encoded_leaves s i ghost)) + to_Zpos (word_349 (encoded_leaves s i ghost)) * modulus 2.
Proof. rewrite concat_shape_361 unsigned_cat.
 rewrite encoded_word_360_size.
 reflexivity. Qed.
Transparent word_363.
Lemma concat_shape_363 v : word_363 v = (word_362 v) ++ (word_331 v).
Proof. unfold word_363, closed_363, expr_363, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_363.
Lemma concat_integer_363 s i ghost : to_Zpos (word_363 (encoded_leaves s i ghost)) = to_Zpos (word_362 (encoded_leaves s i ghost)) + to_Zpos (word_331 (encoded_leaves s i ghost)) * modulus 3.
Proof. rewrite concat_shape_363 unsigned_cat.
 rewrite encoded_word_362_size.
 reflexivity. Qed.
Transparent word_365.
Lemma concat_shape_365 v : word_365 v = (word_364 v) ++ (word_293 v).
Proof. unfold word_365, closed_365, expr_365, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_365.
Lemma concat_integer_365 s i ghost : to_Zpos (word_365 (encoded_leaves s i ghost)) = to_Zpos (word_364 (encoded_leaves s i ghost)) + to_Zpos (word_293 (encoded_leaves s i ghost)) * modulus 4.
Proof. rewrite concat_shape_365 unsigned_cat.
 rewrite encoded_word_364_size.
 reflexivity. Qed.
Transparent word_367.
Lemma concat_shape_367 v : word_367 v = (word_366 v) ++ (word_215 v).
Proof. unfold word_367, closed_367, expr_367, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_367.
Lemma concat_integer_367 s i ghost : to_Zpos (word_367 (encoded_leaves s i ghost)) = to_Zpos (word_366 (encoded_leaves s i ghost)) + to_Zpos (word_215 (encoded_leaves s i ghost)) * modulus 5.
Proof. rewrite concat_shape_367 unsigned_cat.
 rewrite encoded_word_366_size.
 reflexivity. Qed.
Transparent word_369.
Lemma concat_shape_369 v : word_369 v = (word_368 v) ++ (word_212 v).
Proof. unfold word_369, closed_369, expr_369, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_369.
Lemma concat_integer_369 s i ghost : to_Zpos (word_369 (encoded_leaves s i ghost)) = to_Zpos (word_368 (encoded_leaves s i ghost)) + to_Zpos (word_212 (encoded_leaves s i ghost)) * modulus 6.
Proof. rewrite concat_shape_369 unsigned_cat.
 rewrite encoded_word_368_size.
 reflexivity. Qed.
Transparent word_383.
Lemma concat_shape_383 v : word_383 v = (word_22 v) ++ (word_382 v).
Proof. unfold word_383, closed_383, expr_383, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_383.
Lemma concat_integer_383 s i ghost : to_Zpos (word_383 (encoded_leaves s i ghost)) = to_Zpos (word_22 (encoded_leaves s i ghost)) + to_Zpos (word_382 (encoded_leaves s i ghost)) * modulus 64.
Proof. rewrite concat_shape_383 unsigned_cat.
 rewrite encoded_word_22_size.
 reflexivity. Qed.
Transparent word_384.
Lemma concat_shape_384 v : word_384 v = (word_378 v) ++ (word_383 v).
Proof. unfold word_384, closed_384, expr_384, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_384.
Lemma concat_integer_384 s i ghost : to_Zpos (word_384 (encoded_leaves s i ghost)) = to_Zpos (word_378 (encoded_leaves s i ghost)) + to_Zpos (word_383 (encoded_leaves s i ghost)) * modulus 1.
Proof. rewrite concat_shape_384 unsigned_cat.
 rewrite encoded_word_378_size.
 reflexivity. Qed.
Transparent word_417.
Lemma concat_shape_417 v : word_417 v = (word_413 v) ++ (word_416 v).
Proof. unfold word_417, closed_417, expr_417, word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 unfold eval_binop. cbn [eval_binop_basic]. rewrite ?refine_ground. reflexivity. Qed.
Opaque word_417.
Lemma concat_integer_417 s i ghost : to_Zpos (word_417 (encoded_leaves s i ghost)) = to_Zpos (word_413 (encoded_leaves s i ghost)) + to_Zpos (word_416 (encoded_leaves s i ghost)) * modulus 32.
Proof. rewrite concat_shape_417 unsigned_cat.
 rewrite encoded_word_413_size.
 reflexivity. Qed.
Print Assumptions concat_integer_76.

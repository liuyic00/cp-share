From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import BitvectorFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalAliases GlobalBitWires GlobalContracts Compression8 NodeFacts.
Local Open Scope Z_scope.
Transparent global_word_1262.
Lemma output_cat_1262 v : global_word_1262 v = (global_word_291 v) ++ global_word_987 v.
Proof.
 unfold global_word_1262, global_closed_1262, global_expr_1262, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1262.
Lemma output_cat_integer_1262 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1262 v) = to_Zpos (global_word_291 v) + to_Zpos (global_word_987 v) * 2.
Proof. rewrite output_cat_1262 unsigned_cat. rewrite (global_size_291 v sizes). reflexivity. Qed.
Transparent global_word_1263.
Lemma output_cat_1263 v : global_word_1263 v = (global_word_1005 v) ++ global_word_1023 v.
Proof.
 unfold global_word_1263, global_closed_1263, global_expr_1263, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1263.
Lemma output_cat_integer_1263 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1263 v) = to_Zpos (global_word_1005 v) + to_Zpos (global_word_1023 v) * 2.
Proof. rewrite output_cat_1263 unsigned_cat. rewrite (global_size_1005 v sizes). reflexivity. Qed.
Transparent global_word_1264.
Lemma output_cat_1264 v : global_word_1264 v = (global_word_1262 v) ++ global_word_1263 v.
Proof.
 unfold global_word_1264, global_closed_1264, global_expr_1264, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1264.
Lemma output_cat_integer_1264 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1264 v) = to_Zpos (global_word_1262 v) + to_Zpos (global_word_1263 v) * 4.
Proof. rewrite output_cat_1264 unsigned_cat. rewrite (global_size_1262 v sizes). reflexivity. Qed.
Transparent global_word_1265.
Lemma output_cat_1265 v : global_word_1265 v = (global_word_1041 v) ++ global_word_1059 v.
Proof.
 unfold global_word_1265, global_closed_1265, global_expr_1265, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1265.
Lemma output_cat_integer_1265 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1265 v) = to_Zpos (global_word_1041 v) + to_Zpos (global_word_1059 v) * 2.
Proof. rewrite output_cat_1265 unsigned_cat. rewrite (global_size_1041 v sizes). reflexivity. Qed.
Transparent global_word_1266.
Lemma output_cat_1266 v : global_word_1266 v = (global_word_1083 v) ++ global_word_1107 v.
Proof.
 unfold global_word_1266, global_closed_1266, global_expr_1266, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1266.
Lemma output_cat_integer_1266 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1266 v) = to_Zpos (global_word_1083 v) + to_Zpos (global_word_1107 v) * 2.
Proof. rewrite output_cat_1266 unsigned_cat. rewrite (global_size_1083 v sizes). reflexivity. Qed.
Transparent global_word_1267.
Lemma output_cat_1267 v : global_word_1267 v = (global_word_1265 v) ++ global_word_1266 v.
Proof.
 unfold global_word_1267, global_closed_1267, global_expr_1267, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1267.
Lemma output_cat_integer_1267 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1267 v) = to_Zpos (global_word_1265 v) + to_Zpos (global_word_1266 v) * 4.
Proof. rewrite output_cat_1267 unsigned_cat. rewrite (global_size_1265 v sizes). reflexivity. Qed.
Transparent global_word_1268.
Lemma output_cat_1268 v : global_word_1268 v = (global_word_1264 v) ++ global_word_1267 v.
Proof.
 unfold global_word_1268, global_closed_1268, global_expr_1268, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1268.
Lemma output_cat_integer_1268 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1268 v) = to_Zpos (global_word_1264 v) + to_Zpos (global_word_1267 v) * 16.
Proof. rewrite output_cat_1268 unsigned_cat. rewrite (global_size_1264 v sizes). reflexivity. Qed.
Transparent global_word_1269.
Lemma output_cat_1269 v : global_word_1269 v = (global_word_1125 v) ++ global_word_1143 v.
Proof.
 unfold global_word_1269, global_closed_1269, global_expr_1269, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1269.
Lemma output_cat_integer_1269 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1269 v) = to_Zpos (global_word_1125 v) + to_Zpos (global_word_1143 v) * 2.
Proof. rewrite output_cat_1269 unsigned_cat. rewrite (global_size_1125 v sizes). reflexivity. Qed.
Transparent global_word_1270.
Lemma output_cat_1270 v : global_word_1270 v = (global_word_1161 v) ++ global_word_1179 v.
Proof.
 unfold global_word_1270, global_closed_1270, global_expr_1270, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1270.
Lemma output_cat_integer_1270 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1270 v) = to_Zpos (global_word_1161 v) + to_Zpos (global_word_1179 v) * 2.
Proof. rewrite output_cat_1270 unsigned_cat. rewrite (global_size_1161 v sizes). reflexivity. Qed.
Transparent global_word_1271.
Lemma output_cat_1271 v : global_word_1271 v = (global_word_1269 v) ++ global_word_1270 v.
Proof.
 unfold global_word_1271, global_closed_1271, global_expr_1271, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1271.
Lemma output_cat_integer_1271 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1271 v) = to_Zpos (global_word_1269 v) + to_Zpos (global_word_1270 v) * 4.
Proof. rewrite output_cat_1271 unsigned_cat. rewrite (global_size_1269 v sizes). reflexivity. Qed.
Transparent global_word_1272.
Lemma output_cat_1272 v : global_word_1272 v = (global_word_1203 v) ++ global_word_1221 v.
Proof.
 unfold global_word_1272, global_closed_1272, global_expr_1272, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1272.
Lemma output_cat_integer_1272 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1272 v) = to_Zpos (global_word_1203 v) + to_Zpos (global_word_1221 v) * 2.
Proof. rewrite output_cat_1272 unsigned_cat. rewrite (global_size_1203 v sizes). reflexivity. Qed.
Transparent global_word_1273.
Lemma output_cat_1273 v : global_word_1273 v = (global_word_1239 v) ++ global_word_1257 v.
Proof.
 unfold global_word_1273, global_closed_1273, global_expr_1273, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1273.
Lemma output_cat_integer_1273 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1273 v) = to_Zpos (global_word_1239 v) + to_Zpos (global_word_1257 v) * 2.
Proof. rewrite output_cat_1273 unsigned_cat. rewrite (global_size_1239 v sizes). reflexivity. Qed.
Transparent global_word_1274.
Lemma output_cat_1274 v : global_word_1274 v = (global_word_1272 v) ++ global_word_1273 v.
Proof.
 unfold global_word_1274, global_closed_1274, global_expr_1274, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1274.
Lemma output_cat_integer_1274 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1274 v) = to_Zpos (global_word_1272 v) + to_Zpos (global_word_1273 v) * 4.
Proof. rewrite output_cat_1274 unsigned_cat. rewrite (global_size_1272 v sizes). reflexivity. Qed.
Transparent global_word_1275.
Lemma output_cat_1275 v : global_word_1275 v = (global_word_1271 v) ++ global_word_1274 v.
Proof.
 unfold global_word_1275, global_closed_1275, global_expr_1275, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1275.
Lemma output_cat_integer_1275 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1275 v) = to_Zpos (global_word_1271 v) + to_Zpos (global_word_1274 v) * 16.
Proof. rewrite output_cat_1275 unsigned_cat. rewrite (global_size_1271 v sizes). reflexivity. Qed.
Transparent global_word_1276.
Lemma output_cat_1276 v : global_word_1276 v = (global_word_1268 v) ++ global_word_1275 v.
Proof.
 unfold global_word_1276, global_closed_1276, global_expr_1276, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1276.
Lemma output_cat_integer_1276 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1276 v) = to_Zpos (global_word_1268 v) + to_Zpos (global_word_1275 v) * 256.
Proof. rewrite output_cat_1276 unsigned_cat. rewrite (global_size_1268 v sizes). reflexivity. Qed.
Transparent global_word_1277.
Lemma output_cat_1277 v : global_word_1277 v = (global_word_1009 v) ++ global_word_1027 v.
Proof.
 unfold global_word_1277, global_closed_1277, global_expr_1277, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1277.
Lemma output_cat_integer_1277 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1277 v) = to_Zpos (global_word_1009 v) + to_Zpos (global_word_1027 v) * 2.
Proof. rewrite output_cat_1277 unsigned_cat. rewrite (global_size_1009 v sizes). reflexivity. Qed.
Transparent global_word_1278.
Lemma output_cat_1278 v : global_word_1278 v = (global_word_991 v) ++ global_word_1277 v.
Proof.
 unfold global_word_1278, global_closed_1278, global_expr_1278, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1278.
Lemma output_cat_integer_1278 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1278 v) = to_Zpos (global_word_991 v) + to_Zpos (global_word_1277 v) * 2.
Proof. rewrite output_cat_1278 unsigned_cat. rewrite (global_size_991 v sizes). reflexivity. Qed.
Transparent global_word_1279.
Lemma output_cat_1279 v : global_word_1279 v = (global_word_1045 v) ++ global_word_1063 v.
Proof.
 unfold global_word_1279, global_closed_1279, global_expr_1279, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1279.
Lemma output_cat_integer_1279 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1279 v) = to_Zpos (global_word_1045 v) + to_Zpos (global_word_1063 v) * 2.
Proof. rewrite output_cat_1279 unsigned_cat. rewrite (global_size_1045 v sizes). reflexivity. Qed.
Transparent global_word_1280.
Lemma output_cat_1280 v : global_word_1280 v = (global_word_1087 v) ++ global_word_1111 v.
Proof.
 unfold global_word_1280, global_closed_1280, global_expr_1280, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1280.
Lemma output_cat_integer_1280 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1280 v) = to_Zpos (global_word_1087 v) + to_Zpos (global_word_1111 v) * 2.
Proof. rewrite output_cat_1280 unsigned_cat. rewrite (global_size_1087 v sizes). reflexivity. Qed.
Transparent global_word_1281.
Lemma output_cat_1281 v : global_word_1281 v = (global_word_1279 v) ++ global_word_1280 v.
Proof.
 unfold global_word_1281, global_closed_1281, global_expr_1281, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1281.
Lemma output_cat_integer_1281 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1281 v) = to_Zpos (global_word_1279 v) + to_Zpos (global_word_1280 v) * 4.
Proof. rewrite output_cat_1281 unsigned_cat. rewrite (global_size_1279 v sizes). reflexivity. Qed.
Transparent global_word_1282.
Lemma output_cat_1282 v : global_word_1282 v = (global_word_1278 v) ++ global_word_1281 v.
Proof.
 unfold global_word_1282, global_closed_1282, global_expr_1282, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1282.
Lemma output_cat_integer_1282 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1282 v) = to_Zpos (global_word_1278 v) + to_Zpos (global_word_1281 v) * 8.
Proof. rewrite output_cat_1282 unsigned_cat. rewrite (global_size_1278 v sizes). reflexivity. Qed.
Transparent global_word_1283.
Lemma output_cat_1283 v : global_word_1283 v = (global_word_1147 v) ++ global_word_1165 v.
Proof.
 unfold global_word_1283, global_closed_1283, global_expr_1283, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1283.
Lemma output_cat_integer_1283 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1283 v) = to_Zpos (global_word_1147 v) + to_Zpos (global_word_1165 v) * 2.
Proof. rewrite output_cat_1283 unsigned_cat. rewrite (global_size_1147 v sizes). reflexivity. Qed.
Transparent global_word_1284.
Lemma output_cat_1284 v : global_word_1284 v = (global_word_1129 v) ++ global_word_1283 v.
Proof.
 unfold global_word_1284, global_closed_1284, global_expr_1284, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1284.
Lemma output_cat_integer_1284 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1284 v) = to_Zpos (global_word_1129 v) + to_Zpos (global_word_1283 v) * 2.
Proof. rewrite output_cat_1284 unsigned_cat. rewrite (global_size_1129 v sizes). reflexivity. Qed.
Transparent global_word_1285.
Lemma output_cat_1285 v : global_word_1285 v = (global_word_1183 v) ++ global_word_1207 v.
Proof.
 unfold global_word_1285, global_closed_1285, global_expr_1285, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1285.
Lemma output_cat_integer_1285 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1285 v) = to_Zpos (global_word_1183 v) + to_Zpos (global_word_1207 v) * 2.
Proof. rewrite output_cat_1285 unsigned_cat. rewrite (global_size_1183 v sizes). reflexivity. Qed.
Transparent global_word_1286.
Lemma output_cat_1286 v : global_word_1286 v = (global_word_1225 v) ++ global_word_1243 v.
Proof.
 unfold global_word_1286, global_closed_1286, global_expr_1286, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1286.
Lemma output_cat_integer_1286 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1286 v) = to_Zpos (global_word_1225 v) + to_Zpos (global_word_1243 v) * 2.
Proof. rewrite output_cat_1286 unsigned_cat. rewrite (global_size_1225 v sizes). reflexivity. Qed.
Transparent global_word_1287.
Lemma output_cat_1287 v : global_word_1287 v = (global_word_1285 v) ++ global_word_1286 v.
Proof.
 unfold global_word_1287, global_closed_1287, global_expr_1287, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1287.
Lemma output_cat_integer_1287 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1287 v) = to_Zpos (global_word_1285 v) + to_Zpos (global_word_1286 v) * 4.
Proof. rewrite output_cat_1287 unsigned_cat. rewrite (global_size_1285 v sizes). reflexivity. Qed.
Transparent global_word_1288.
Lemma output_cat_1288 v : global_word_1288 v = (global_word_1284 v) ++ global_word_1287 v.
Proof.
 unfold global_word_1288, global_closed_1288, global_expr_1288, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1288.
Lemma output_cat_integer_1288 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1288 v) = to_Zpos (global_word_1284 v) + to_Zpos (global_word_1287 v) * 8.
Proof. rewrite output_cat_1288 unsigned_cat. rewrite (global_size_1284 v sizes). reflexivity. Qed.
Transparent global_word_1289.
Lemma output_cat_1289 v : global_word_1289 v = (global_word_1282 v) ++ global_word_1288 v.
Proof.
 unfold global_word_1289, global_closed_1289, global_expr_1289, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1289.
Lemma output_cat_integer_1289 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1289 v) = to_Zpos (global_word_1282 v) + to_Zpos (global_word_1288 v) * 128.
Proof. rewrite output_cat_1289 unsigned_cat. rewrite (global_size_1282 v sizes). reflexivity. Qed.
Transparent global_word_1290.
Lemma output_cat_1290 v : global_word_1290 v = ([::false;false]) ++ global_word_1289 v.
Proof.
 unfold global_word_1290, global_closed_1290, global_expr_1290, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 reflexivity.
Qed.
Opaque global_word_1290.
Lemma output_cat_integer_1290 v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1290 v) = 0 + to_Zpos (global_word_1289 v) * 4.
Proof. rewrite output_cat_1290 unsigned_cat. reflexivity. Qed.
Lemma output_rows_match v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1276 v) + to_Zpos (global_word_1290 v) = output_rows (global_compressor_outputs v).
Proof.
 rewrite (output_cat_integer_1290 v sizes) (output_cat_integer_1289 v sizes) (output_cat_integer_1288 v sizes) (output_cat_integer_1287 v sizes) (output_cat_integer_1286 v sizes) (output_cat_integer_1285 v sizes) (output_cat_integer_1284 v sizes) (output_cat_integer_1283 v sizes) (output_cat_integer_1282 v sizes) (output_cat_integer_1281 v sizes) (output_cat_integer_1280 v sizes) (output_cat_integer_1279 v sizes) (output_cat_integer_1278 v sizes) (output_cat_integer_1277 v sizes) (output_cat_integer_1276 v sizes) (output_cat_integer_1275 v sizes) (output_cat_integer_1274 v sizes) (output_cat_integer_1273 v sizes) (output_cat_integer_1272 v sizes) (output_cat_integer_1271 v sizes) (output_cat_integer_1270 v sizes) (output_cat_integer_1269 v sizes) (output_cat_integer_1268 v sizes) (output_cat_integer_1267 v sizes) (output_cat_integer_1266 v sizes) (output_cat_integer_1265 v sizes) (output_cat_integer_1264 v sizes) (output_cat_integer_1263 v sizes) (output_cat_integer_1262 v sizes).
 rewrite ?(bit_wire_991 v sizes) ?wire_alias_990 ?(bit_wire_1059 v sizes) ?wire_alias_1058 ?(bit_wire_1083 v sizes) ?wire_alias_1082 ?(bit_wire_1257 v sizes) ?wire_alias_1256 ?(bit_wire_291 v sizes) ?wire_alias_290 ?(bit_wire_1207 v sizes) ?wire_alias_1206 ?(bit_wire_1161 v sizes) ?wire_alias_1160 ?(bit_wire_1239 v sizes) ?wire_alias_1238 ?(bit_wire_1005 v sizes) ?wire_alias_1004 ?(bit_wire_1183 v sizes) ?wire_alias_1182 ?(bit_wire_1179 v sizes) ?wire_alias_1178 ?(bit_wire_1063 v sizes) ?wire_alias_1062 ?(bit_wire_1009 v sizes) ?wire_alias_1008 ?(bit_wire_1045 v sizes) ?wire_alias_1044 ?(bit_wire_1147 v sizes) ?wire_alias_1146 ?(bit_wire_1165 v sizes) ?wire_alias_1164 ?(bit_wire_1027 v sizes) ?wire_alias_1026 ?(bit_wire_1041 v sizes) ?wire_alias_1040 ?(bit_wire_987 v sizes) ?wire_alias_986 ?(bit_wire_1225 v sizes) ?wire_alias_1224 ?(bit_wire_1023 v sizes) ?wire_alias_1022 ?(bit_wire_1203 v sizes) ?wire_alias_1202 ?(bit_wire_1221 v sizes) ?wire_alias_1220 ?(bit_wire_1143 v sizes) ?wire_alias_1142 ?(bit_wire_1125 v sizes) ?wire_alias_1124 ?(bit_wire_1243 v sizes) ?wire_alias_1242 ?(bit_wire_1087 v sizes) ?wire_alias_1086 ?(bit_wire_1107 v sizes) ?wire_alias_1106 ?(bit_wire_1111 v sizes) ?wire_alias_1110 ?(bit_wire_1129 v sizes) ?wire_alias_1128.
 unfold output_rows. cbn [global_compressor_outputs nth]. ring.
Qed.
Transparent global_word_1291 global_word_1292.
Lemma output_add_bits v : global_word_1291 v = from_N 17 (to_N (global_word_1276 v) + to_N (global_word_1290 v)).
Proof.
 unfold global_word_1291, global_closed_1291, global_expr_1291, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
Qed.
Lemma output_truncate_bits v : global_word_1292 v = take 16 (global_word_1291 v).
Proof.
 unfold global_word_1292, global_closed_1292, global_expr_1292, Stable.word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity].
Qed.
Opaque global_word_1291 global_word_1292.
Theorem global_output_weight v (sizes:global_leaf_sizes v) :
 to_Zpos (global_word_1299 v) = weighted_registers (global_register_numbers v) mod 65536.
Proof.
 rewrite wire_alias_1299 output_truncate_bits output_add_bits final_add_value.
 rewrite (output_rows_match v sizes). exact (global_compression_mod v sizes).
Qed.

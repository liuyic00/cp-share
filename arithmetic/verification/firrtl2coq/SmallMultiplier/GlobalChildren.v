From Coq Require Import NArith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import GlobalStable Child0Stable Child1Stable Child2Stable.
Local Open Scope N_scope.
Definition instance_1_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1384 v
| 0, 1 => global_word_1380 v
| 0, 2 => global_word_279 v
| 0, 3 => global_word_282 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_1384.
Lemma instance_1_word_0 v : Child0Stable.word_0 (instance_1_leaves v) = global_word_1384 v.
Proof. unfold Child0Stable.word_0, instance_1_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_1384.
Transparent Child0Stable.word_1 global_word_1380.
Lemma instance_1_word_1 v : Child0Stable.word_1 (instance_1_leaves v) = global_word_1380 v.
Proof. unfold Child0Stable.word_1, instance_1_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_1380.
Transparent Child0Stable.word_2 global_word_279.
Lemma instance_1_word_2 v : Child0Stable.word_2 (instance_1_leaves v) = global_word_279 v.
Proof. unfold Child0Stable.word_2, instance_1_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_279.
Transparent Child0Stable.word_3 global_word_282.
Lemma instance_1_word_3 v : Child0Stable.word_3 (instance_1_leaves v) = global_word_282 v.
Proof. unfold Child0Stable.word_3, instance_1_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_282.
Transparent Child0Stable.word_6 global_word_1370.
Lemma instance_1_word_6 v : Child0Stable.word_6 (instance_1_leaves v) = global_word_1370 v.
Proof. unfold Child0Stable.word_6, global_word_1370, Child0Stable.closed_word_6, global_closed_1370, Child0Stable.expr_word_6, global_expr_1370.
 rewrite instance_1_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_1370.
Transparent Child0Stable.word_7 global_word_1371.
Lemma instance_1_word_7 v : Child0Stable.word_7 (instance_1_leaves v) = global_word_1371 v.
Proof. unfold Child0Stable.word_7, global_word_1371, Child0Stable.closed_word_7, global_closed_1371, Child0Stable.expr_word_7, global_expr_1371.
 rewrite instance_1_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_1371.
Transparent Child0Stable.word_8 global_word_1372.
Lemma instance_1_word_8 v : Child0Stable.word_8 (instance_1_leaves v) = global_word_1372 v.
Proof. unfold Child0Stable.word_8, global_word_1372, Child0Stable.closed_word_8, global_closed_1372, Child0Stable.expr_word_8, global_expr_1372.
 rewrite instance_1_word_6 instance_1_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_1372.
Transparent Child0Stable.word_9 global_word_1373.
Lemma instance_1_word_9 v : Child0Stable.word_9 (instance_1_leaves v) = global_word_1373 v.
Proof. unfold Child0Stable.word_9, global_word_1373, Child0Stable.closed_word_9, global_closed_1373, Child0Stable.expr_word_9, global_expr_1373.
 rewrite instance_1_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_1373.
Transparent Child0Stable.word_19 global_word_280.
Lemma instance_1_word_19 v : Child0Stable.word_19 (instance_1_leaves v) = global_word_280 v.
Proof. unfold Child0Stable.word_19, global_word_280, Child0Stable.closed_word_19, global_closed_280, Child0Stable.expr_word_19, global_expr_280.
 rewrite instance_1_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_280.
Transparent Child0Stable.word_20 global_word_283.
Lemma instance_1_word_20 v : Child0Stable.word_20 (instance_1_leaves v) = global_word_283 v.
Proof. unfold Child0Stable.word_20, global_word_283, Child0Stable.closed_word_20, global_closed_283, Child0Stable.expr_word_20, global_expr_283.
 rewrite instance_1_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_283.
Transparent Child0Stable.word_21 global_word_284.
Lemma instance_1_word_21 v : Child0Stable.word_21 (instance_1_leaves v) = global_word_284 v.
Proof. unfold Child0Stable.word_21, global_word_284, Child0Stable.closed_word_21, global_closed_284, Child0Stable.expr_word_21, global_expr_284.
 rewrite instance_1_word_19 instance_1_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_284.
Transparent Child0Stable.word_22 global_word_285.
Lemma instance_1_word_22 v : Child0Stable.word_22 (instance_1_leaves v) = global_word_285 v.
Proof. unfold Child0Stable.word_22, global_word_285, Child0Stable.closed_word_22, global_closed_285, Child0Stable.expr_word_22, global_expr_285.
 rewrite instance_1_word_19 instance_1_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_285.
Transparent Child0Stable.word_23 global_word_286.
Lemma instance_1_word_23 v : Child0Stable.word_23 (instance_1_leaves v) = global_word_286 v.
Proof. unfold Child0Stable.word_23, global_word_286, Child0Stable.closed_word_23, global_closed_286, Child0Stable.expr_word_23, global_expr_286.
 rewrite instance_1_word_21 instance_1_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_286.
Transparent Child0Stable.word_24 global_word_287.
Lemma instance_1_word_24 v : Child0Stable.word_24 (instance_1_leaves v) = global_word_287 v.
Proof. unfold Child0Stable.word_24, global_word_287, Child0Stable.closed_word_24, global_closed_287, Child0Stable.expr_word_24, global_expr_287.
 rewrite instance_1_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_287.
Transparent Child0Stable.word_25 global_word_288.
Lemma instance_1_word_25 v : Child0Stable.word_25 (instance_1_leaves v) = global_word_288 v.
Proof. unfold Child0Stable.word_25, global_word_288, Child0Stable.closed_word_25, global_closed_288, Child0Stable.expr_word_25, global_expr_288.
 rewrite instance_1_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_288.
Transparent Child0Stable.word_4 global_word_289.
Lemma instance_1_word_4 v : Child0Stable.word_4 (instance_1_leaves v) = global_word_289 v.
Proof. unfold Child0Stable.word_4, global_word_289, Child0Stable.closed_word_4, global_closed_289, Child0Stable.expr_word_4, global_expr_289.
 rewrite instance_1_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_289.
Transparent Child0Stable.word_10 global_word_1374.
Lemma instance_1_word_10 v : Child0Stable.word_10 (instance_1_leaves v) = global_word_1374 v.
Proof. unfold Child0Stable.word_10, global_word_1374, Child0Stable.closed_word_10, global_closed_1374, Child0Stable.expr_word_10, global_expr_1374.
 rewrite instance_1_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_1374.
Transparent Child0Stable.word_26 global_word_292.
Lemma instance_1_word_26 v : Child0Stable.word_26 (instance_1_leaves v) = global_word_292 v.
Proof. unfold Child0Stable.word_26, global_word_292, Child0Stable.closed_word_26, global_closed_292, Child0Stable.expr_word_26, global_expr_292.
 rewrite instance_1_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_292.
Transparent Child0Stable.word_5 global_word_293.
Lemma instance_1_word_5 v : Child0Stable.word_5 (instance_1_leaves v) = global_word_293 v.
Proof. unfold Child0Stable.word_5, global_word_293, Child0Stable.closed_word_5, global_closed_293, Child0Stable.expr_word_5, global_expr_293.
 rewrite instance_1_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_293.
Transparent Child0Stable.word_11 global_word_1375.
Lemma instance_1_word_11 v : Child0Stable.word_11 (instance_1_leaves v) = global_word_1375 v.
Proof. unfold Child0Stable.word_11, global_word_1375, Child0Stable.closed_word_11, global_closed_1375, Child0Stable.expr_word_11, global_expr_1375.
 rewrite instance_1_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_1375.
Transparent Child0Stable.word_12 global_word_1376.
Lemma instance_1_word_12 v : Child0Stable.word_12 (instance_1_leaves v) = global_word_1376 v.
Proof. unfold Child0Stable.word_12, global_word_1376, Child0Stable.closed_word_12, global_closed_1376, Child0Stable.expr_word_12, global_expr_1376.
 rewrite instance_1_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_1376.
Transparent Child0Stable.word_13 global_word_1377.
Lemma instance_1_word_13 v : Child0Stable.word_13 (instance_1_leaves v) = global_word_1377 v.
Proof. unfold Child0Stable.word_13, global_word_1377, Child0Stable.closed_word_13, global_closed_1377, Child0Stable.expr_word_13, global_expr_1377.
 rewrite instance_1_word_10 instance_1_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_1377.
Transparent Child0Stable.word_14 global_word_1378.
Lemma instance_1_word_14 v : Child0Stable.word_14 (instance_1_leaves v) = global_word_1378 v.
Proof. unfold Child0Stable.word_14, global_word_1378, Child0Stable.closed_word_14, global_closed_1378, Child0Stable.expr_word_14, global_expr_1378.
 rewrite instance_1_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_1378.
Transparent Child0Stable.word_15 global_word_1379.
Lemma instance_1_word_15 v : Child0Stable.word_15 (instance_1_leaves v) = global_word_1379 v.
Proof. unfold Child0Stable.word_15, global_word_1379, Child0Stable.closed_word_15, global_closed_1379, Child0Stable.expr_word_15, global_expr_1379.
 rewrite instance_1_word_9 instance_1_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_1379.
Transparent Child0Stable.word_16 global_word_1381.
Lemma instance_1_word_16 v : Child0Stable.word_16 (instance_1_leaves v) = global_word_1381 v.
Proof. unfold Child0Stable.word_16, global_word_1381, Child0Stable.closed_word_16, global_closed_1381, Child0Stable.expr_word_16, global_expr_1381.
 rewrite instance_1_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_1381.
Transparent Child0Stable.word_17 global_word_1382.
Lemma instance_1_word_17 v : Child0Stable.word_17 (instance_1_leaves v) = global_word_1382 v.
Proof. unfold Child0Stable.word_17, global_word_1382, Child0Stable.closed_word_17, global_closed_1382, Child0Stable.expr_word_17, global_expr_1382.
 rewrite instance_1_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_1382.
Transparent Child0Stable.word_18 global_word_1383.
Lemma instance_1_word_18 v : Child0Stable.word_18 (instance_1_leaves v) = global_word_1383 v.
Proof. unfold Child0Stable.word_18, global_word_1383, Child0Stable.closed_word_18, global_closed_1383, Child0Stable.expr_word_18, global_expr_1383.
 rewrite instance_1_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_1383.
Definition instance_2_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1399 v
| 0, 1 => global_word_1395 v
| 0, 2 => global_word_297 v
| 0, 3 => global_word_300 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_1399.
Lemma instance_2_word_0 v : Child0Stable.word_0 (instance_2_leaves v) = global_word_1399 v.
Proof. unfold Child0Stable.word_0, instance_2_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_1399.
Transparent Child0Stable.word_1 global_word_1395.
Lemma instance_2_word_1 v : Child0Stable.word_1 (instance_2_leaves v) = global_word_1395 v.
Proof. unfold Child0Stable.word_1, instance_2_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_1395.
Transparent Child0Stable.word_2 global_word_297.
Lemma instance_2_word_2 v : Child0Stable.word_2 (instance_2_leaves v) = global_word_297 v.
Proof. unfold Child0Stable.word_2, instance_2_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_297.
Transparent Child0Stable.word_3 global_word_300.
Lemma instance_2_word_3 v : Child0Stable.word_3 (instance_2_leaves v) = global_word_300 v.
Proof. unfold Child0Stable.word_3, instance_2_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_300.
Transparent Child0Stable.word_6 global_word_1385.
Lemma instance_2_word_6 v : Child0Stable.word_6 (instance_2_leaves v) = global_word_1385 v.
Proof. unfold Child0Stable.word_6, global_word_1385, Child0Stable.closed_word_6, global_closed_1385, Child0Stable.expr_word_6, global_expr_1385.
 rewrite instance_2_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_1385.
Transparent Child0Stable.word_7 global_word_1386.
Lemma instance_2_word_7 v : Child0Stable.word_7 (instance_2_leaves v) = global_word_1386 v.
Proof. unfold Child0Stable.word_7, global_word_1386, Child0Stable.closed_word_7, global_closed_1386, Child0Stable.expr_word_7, global_expr_1386.
 rewrite instance_2_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_1386.
Transparent Child0Stable.word_8 global_word_1387.
Lemma instance_2_word_8 v : Child0Stable.word_8 (instance_2_leaves v) = global_word_1387 v.
Proof. unfold Child0Stable.word_8, global_word_1387, Child0Stable.closed_word_8, global_closed_1387, Child0Stable.expr_word_8, global_expr_1387.
 rewrite instance_2_word_6 instance_2_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_1387.
Transparent Child0Stable.word_9 global_word_1388.
Lemma instance_2_word_9 v : Child0Stable.word_9 (instance_2_leaves v) = global_word_1388 v.
Proof. unfold Child0Stable.word_9, global_word_1388, Child0Stable.closed_word_9, global_closed_1388, Child0Stable.expr_word_9, global_expr_1388.
 rewrite instance_2_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_1388.
Transparent Child0Stable.word_19 global_word_298.
Lemma instance_2_word_19 v : Child0Stable.word_19 (instance_2_leaves v) = global_word_298 v.
Proof. unfold Child0Stable.word_19, global_word_298, Child0Stable.closed_word_19, global_closed_298, Child0Stable.expr_word_19, global_expr_298.
 rewrite instance_2_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_298.
Transparent Child0Stable.word_20 global_word_301.
Lemma instance_2_word_20 v : Child0Stable.word_20 (instance_2_leaves v) = global_word_301 v.
Proof. unfold Child0Stable.word_20, global_word_301, Child0Stable.closed_word_20, global_closed_301, Child0Stable.expr_word_20, global_expr_301.
 rewrite instance_2_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_301.
Transparent Child0Stable.word_21 global_word_302.
Lemma instance_2_word_21 v : Child0Stable.word_21 (instance_2_leaves v) = global_word_302 v.
Proof. unfold Child0Stable.word_21, global_word_302, Child0Stable.closed_word_21, global_closed_302, Child0Stable.expr_word_21, global_expr_302.
 rewrite instance_2_word_19 instance_2_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_302.
Transparent Child0Stable.word_22 global_word_303.
Lemma instance_2_word_22 v : Child0Stable.word_22 (instance_2_leaves v) = global_word_303 v.
Proof. unfold Child0Stable.word_22, global_word_303, Child0Stable.closed_word_22, global_closed_303, Child0Stable.expr_word_22, global_expr_303.
 rewrite instance_2_word_19 instance_2_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_303.
Transparent Child0Stable.word_23 global_word_304.
Lemma instance_2_word_23 v : Child0Stable.word_23 (instance_2_leaves v) = global_word_304 v.
Proof. unfold Child0Stable.word_23, global_word_304, Child0Stable.closed_word_23, global_closed_304, Child0Stable.expr_word_23, global_expr_304.
 rewrite instance_2_word_21 instance_2_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_304.
Transparent Child0Stable.word_24 global_word_305.
Lemma instance_2_word_24 v : Child0Stable.word_24 (instance_2_leaves v) = global_word_305 v.
Proof. unfold Child0Stable.word_24, global_word_305, Child0Stable.closed_word_24, global_closed_305, Child0Stable.expr_word_24, global_expr_305.
 rewrite instance_2_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_305.
Transparent Child0Stable.word_25 global_word_306.
Lemma instance_2_word_25 v : Child0Stable.word_25 (instance_2_leaves v) = global_word_306 v.
Proof. unfold Child0Stable.word_25, global_word_306, Child0Stable.closed_word_25, global_closed_306, Child0Stable.expr_word_25, global_expr_306.
 rewrite instance_2_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_306.
Transparent Child0Stable.word_4 global_word_307.
Lemma instance_2_word_4 v : Child0Stable.word_4 (instance_2_leaves v) = global_word_307 v.
Proof. unfold Child0Stable.word_4, global_word_307, Child0Stable.closed_word_4, global_closed_307, Child0Stable.expr_word_4, global_expr_307.
 rewrite instance_2_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_307.
Transparent Child0Stable.word_10 global_word_1389.
Lemma instance_2_word_10 v : Child0Stable.word_10 (instance_2_leaves v) = global_word_1389 v.
Proof. unfold Child0Stable.word_10, global_word_1389, Child0Stable.closed_word_10, global_closed_1389, Child0Stable.expr_word_10, global_expr_1389.
 rewrite instance_2_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_1389.
Transparent Child0Stable.word_26 global_word_310.
Lemma instance_2_word_26 v : Child0Stable.word_26 (instance_2_leaves v) = global_word_310 v.
Proof. unfold Child0Stable.word_26, global_word_310, Child0Stable.closed_word_26, global_closed_310, Child0Stable.expr_word_26, global_expr_310.
 rewrite instance_2_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_310.
Transparent Child0Stable.word_5 global_word_311.
Lemma instance_2_word_5 v : Child0Stable.word_5 (instance_2_leaves v) = global_word_311 v.
Proof. unfold Child0Stable.word_5, global_word_311, Child0Stable.closed_word_5, global_closed_311, Child0Stable.expr_word_5, global_expr_311.
 rewrite instance_2_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_311.
Transparent Child0Stable.word_11 global_word_1390.
Lemma instance_2_word_11 v : Child0Stable.word_11 (instance_2_leaves v) = global_word_1390 v.
Proof. unfold Child0Stable.word_11, global_word_1390, Child0Stable.closed_word_11, global_closed_1390, Child0Stable.expr_word_11, global_expr_1390.
 rewrite instance_2_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_1390.
Transparent Child0Stable.word_12 global_word_1391.
Lemma instance_2_word_12 v : Child0Stable.word_12 (instance_2_leaves v) = global_word_1391 v.
Proof. unfold Child0Stable.word_12, global_word_1391, Child0Stable.closed_word_12, global_closed_1391, Child0Stable.expr_word_12, global_expr_1391.
 rewrite instance_2_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_1391.
Transparent Child0Stable.word_13 global_word_1392.
Lemma instance_2_word_13 v : Child0Stable.word_13 (instance_2_leaves v) = global_word_1392 v.
Proof. unfold Child0Stable.word_13, global_word_1392, Child0Stable.closed_word_13, global_closed_1392, Child0Stable.expr_word_13, global_expr_1392.
 rewrite instance_2_word_10 instance_2_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_1392.
Transparent Child0Stable.word_14 global_word_1393.
Lemma instance_2_word_14 v : Child0Stable.word_14 (instance_2_leaves v) = global_word_1393 v.
Proof. unfold Child0Stable.word_14, global_word_1393, Child0Stable.closed_word_14, global_closed_1393, Child0Stable.expr_word_14, global_expr_1393.
 rewrite instance_2_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_1393.
Transparent Child0Stable.word_15 global_word_1394.
Lemma instance_2_word_15 v : Child0Stable.word_15 (instance_2_leaves v) = global_word_1394 v.
Proof. unfold Child0Stable.word_15, global_word_1394, Child0Stable.closed_word_15, global_closed_1394, Child0Stable.expr_word_15, global_expr_1394.
 rewrite instance_2_word_9 instance_2_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_1394.
Transparent Child0Stable.word_16 global_word_1396.
Lemma instance_2_word_16 v : Child0Stable.word_16 (instance_2_leaves v) = global_word_1396 v.
Proof. unfold Child0Stable.word_16, global_word_1396, Child0Stable.closed_word_16, global_closed_1396, Child0Stable.expr_word_16, global_expr_1396.
 rewrite instance_2_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_1396.
Transparent Child0Stable.word_17 global_word_1397.
Lemma instance_2_word_17 v : Child0Stable.word_17 (instance_2_leaves v) = global_word_1397 v.
Proof. unfold Child0Stable.word_17, global_word_1397, Child0Stable.closed_word_17, global_closed_1397, Child0Stable.expr_word_17, global_expr_1397.
 rewrite instance_2_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_1397.
Transparent Child0Stable.word_18 global_word_1398.
Lemma instance_2_word_18 v : Child0Stable.word_18 (instance_2_leaves v) = global_word_1398 v.
Proof. unfold Child0Stable.word_18, global_word_1398, Child0Stable.closed_word_18, global_closed_1398, Child0Stable.expr_word_18, global_expr_1398.
 rewrite instance_2_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_1398.
Definition instance_3_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1417 v
| 0, 1 => global_word_1413 v
| 0, 2 => global_word_318 v
| 0, 3 => global_word_321 v
| 0, 4 => global_word_315 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1417.
Lemma instance_3_word_0 v : Child1Stable.word_0 (instance_3_leaves v) = global_word_1417 v.
Proof. unfold Child1Stable.word_0, instance_3_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1417.
Transparent Child1Stable.word_1 global_word_1413.
Lemma instance_3_word_1 v : Child1Stable.word_1 (instance_3_leaves v) = global_word_1413 v.
Proof. unfold Child1Stable.word_1, instance_3_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1413.
Transparent Child1Stable.word_2 global_word_318.
Lemma instance_3_word_2 v : Child1Stable.word_2 (instance_3_leaves v) = global_word_318 v.
Proof. unfold Child1Stable.word_2, instance_3_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_318.
Transparent Child1Stable.word_3 global_word_321.
Lemma instance_3_word_3 v : Child1Stable.word_3 (instance_3_leaves v) = global_word_321 v.
Proof. unfold Child1Stable.word_3, instance_3_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_321.
Transparent Child1Stable.word_4 global_word_315.
Lemma instance_3_word_4 v : Child1Stable.word_4 (instance_3_leaves v) = global_word_315 v.
Proof. unfold Child1Stable.word_4, instance_3_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_315.
Transparent Child1Stable.word_7 global_word_1400.
Lemma instance_3_word_7 v : Child1Stable.word_7 (instance_3_leaves v) = global_word_1400 v.
Proof. unfold Child1Stable.word_7, global_word_1400, Child1Stable.closed_word_7, global_closed_1400, Child1Stable.expr_word_7, global_expr_1400.
 rewrite instance_3_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1400.
Transparent Child1Stable.word_8 global_word_1401.
Lemma instance_3_word_8 v : Child1Stable.word_8 (instance_3_leaves v) = global_word_1401 v.
Proof. unfold Child1Stable.word_8, global_word_1401, Child1Stable.closed_word_8, global_closed_1401, Child1Stable.expr_word_8, global_expr_1401.
 rewrite instance_3_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1401.
Transparent Child1Stable.word_9 global_word_1402.
Lemma instance_3_word_9 v : Child1Stable.word_9 (instance_3_leaves v) = global_word_1402 v.
Proof. unfold Child1Stable.word_9, global_word_1402, Child1Stable.closed_word_9, global_closed_1402, Child1Stable.expr_word_9, global_expr_1402.
 rewrite instance_3_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1402.
Transparent Child1Stable.word_10 global_word_1403.
Lemma instance_3_word_10 v : Child1Stable.word_10 (instance_3_leaves v) = global_word_1403 v.
Proof. unfold Child1Stable.word_10, global_word_1403, Child1Stable.closed_word_10, global_closed_1403, Child1Stable.expr_word_10, global_expr_1403.
 rewrite instance_3_word_7 instance_3_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1403.
Transparent Child1Stable.word_11 global_word_1404.
Lemma instance_3_word_11 v : Child1Stable.word_11 (instance_3_leaves v) = global_word_1404 v.
Proof. unfold Child1Stable.word_11, global_word_1404, Child1Stable.closed_word_11, global_closed_1404, Child1Stable.expr_word_11, global_expr_1404.
 rewrite instance_3_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1404.
Transparent Child1Stable.word_12 global_word_1405.
Lemma instance_3_word_12 v : Child1Stable.word_12 (instance_3_leaves v) = global_word_1405 v.
Proof. unfold Child1Stable.word_12, global_word_1405, Child1Stable.closed_word_12, global_closed_1405, Child1Stable.expr_word_12, global_expr_1405.
 rewrite instance_3_word_9 instance_3_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1405.
Transparent Child1Stable.word_13 global_word_1406.
Lemma instance_3_word_13 v : Child1Stable.word_13 (instance_3_leaves v) = global_word_1406 v.
Proof. unfold Child1Stable.word_13, global_word_1406, Child1Stable.closed_word_13, global_closed_1406, Child1Stable.expr_word_13, global_expr_1406.
 rewrite instance_3_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1406.
Transparent Child1Stable.word_25 global_word_316.
Lemma instance_3_word_25 v : Child1Stable.word_25 (instance_3_leaves v) = global_word_316 v.
Proof. unfold Child1Stable.word_25, global_word_316, Child1Stable.closed_word_25, global_closed_316, Child1Stable.expr_word_25, global_expr_316.
 rewrite instance_3_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_316.
Transparent Child1Stable.word_23 global_word_319.
Lemma instance_3_word_23 v : Child1Stable.word_23 (instance_3_leaves v) = global_word_319 v.
Proof. unfold Child1Stable.word_23, global_word_319, Child1Stable.closed_word_23, global_closed_319, Child1Stable.expr_word_23, global_expr_319.
 rewrite instance_3_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_319.
Transparent Child1Stable.word_24 global_word_322.
Lemma instance_3_word_24 v : Child1Stable.word_24 (instance_3_leaves v) = global_word_322 v.
Proof. unfold Child1Stable.word_24, global_word_322, Child1Stable.closed_word_24, global_closed_322, Child1Stable.expr_word_24, global_expr_322.
 rewrite instance_3_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_322.
Transparent Child1Stable.word_26 global_word_323.
Lemma instance_3_word_26 v : Child1Stable.word_26 (instance_3_leaves v) = global_word_323 v.
Proof. unfold Child1Stable.word_26, global_word_323, Child1Stable.closed_word_26, global_closed_323, Child1Stable.expr_word_26, global_expr_323.
 rewrite instance_3_word_23 instance_3_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_323.
Transparent Child1Stable.word_28 global_word_324.
Lemma instance_3_word_28 v : Child1Stable.word_28 (instance_3_leaves v) = global_word_324 v.
Proof. unfold Child1Stable.word_28, global_word_324, Child1Stable.closed_word_28, global_closed_324, Child1Stable.expr_word_28, global_expr_324.
 rewrite instance_3_word_25 instance_3_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_324.
Transparent Child1Stable.word_27 global_word_325.
Lemma instance_3_word_27 v : Child1Stable.word_27 (instance_3_leaves v) = global_word_325 v.
Proof. unfold Child1Stable.word_27, global_word_325, Child1Stable.closed_word_27, global_closed_325, Child1Stable.expr_word_27, global_expr_325.
 rewrite instance_3_word_23 instance_3_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_325.
Transparent Child1Stable.word_29 global_word_326.
Lemma instance_3_word_29 v : Child1Stable.word_29 (instance_3_leaves v) = global_word_326 v.
Proof. unfold Child1Stable.word_29, global_word_326, Child1Stable.closed_word_29, global_closed_326, Child1Stable.expr_word_29, global_expr_326.
 rewrite instance_3_word_25 instance_3_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_326.
Transparent Child1Stable.word_30 global_word_327.
Lemma instance_3_word_30 v : Child1Stable.word_30 (instance_3_leaves v) = global_word_327 v.
Proof. unfold Child1Stable.word_30, global_word_327, Child1Stable.closed_word_30, global_closed_327, Child1Stable.expr_word_30, global_expr_327.
 rewrite instance_3_word_27 instance_3_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_327.
Transparent Child1Stable.word_31 global_word_328.
Lemma instance_3_word_31 v : Child1Stable.word_31 (instance_3_leaves v) = global_word_328 v.
Proof. unfold Child1Stable.word_31, global_word_328, Child1Stable.closed_word_31, global_closed_328, Child1Stable.expr_word_31, global_expr_328.
 rewrite instance_3_word_28 instance_3_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_328.
Transparent Child1Stable.word_32 global_word_329.
Lemma instance_3_word_32 v : Child1Stable.word_32 (instance_3_leaves v) = global_word_329 v.
Proof. unfold Child1Stable.word_32, global_word_329, Child1Stable.closed_word_32, global_closed_329, Child1Stable.expr_word_32, global_expr_329.
 rewrite instance_3_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_329.
Transparent Child1Stable.word_33 global_word_330.
Lemma instance_3_word_33 v : Child1Stable.word_33 (instance_3_leaves v) = global_word_330 v.
Proof. unfold Child1Stable.word_33, global_word_330, Child1Stable.closed_word_33, global_closed_330, Child1Stable.expr_word_33, global_expr_330.
 rewrite instance_3_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_330.
Transparent Child1Stable.word_5 global_word_331.
Lemma instance_3_word_5 v : Child1Stable.word_5 (instance_3_leaves v) = global_word_331 v.
Proof. unfold Child1Stable.word_5, global_word_331, Child1Stable.closed_word_5, global_closed_331, Child1Stable.expr_word_5, global_expr_331.
 rewrite instance_3_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_331.
Transparent Child1Stable.word_14 global_word_1407.
Lemma instance_3_word_14 v : Child1Stable.word_14 (instance_3_leaves v) = global_word_1407 v.
Proof. unfold Child1Stable.word_14, global_word_1407, Child1Stable.closed_word_14, global_closed_1407, Child1Stable.expr_word_14, global_expr_1407.
 rewrite instance_3_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1407.
Transparent Child1Stable.word_34 global_word_334.
Lemma instance_3_word_34 v : Child1Stable.word_34 (instance_3_leaves v) = global_word_334 v.
Proof. unfold Child1Stable.word_34, global_word_334, Child1Stable.closed_word_34, global_closed_334, Child1Stable.expr_word_34, global_expr_334.
 rewrite instance_3_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_334.
Transparent Child1Stable.word_6 global_word_335.
Lemma instance_3_word_6 v : Child1Stable.word_6 (instance_3_leaves v) = global_word_335 v.
Proof. unfold Child1Stable.word_6, global_word_335, Child1Stable.closed_word_6, global_closed_335, Child1Stable.expr_word_6, global_expr_335.
 rewrite instance_3_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_335.
Transparent Child1Stable.word_15 global_word_1408.
Lemma instance_3_word_15 v : Child1Stable.word_15 (instance_3_leaves v) = global_word_1408 v.
Proof. unfold Child1Stable.word_15, global_word_1408, Child1Stable.closed_word_15, global_closed_1408, Child1Stable.expr_word_15, global_expr_1408.
 rewrite instance_3_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1408.
Transparent Child1Stable.word_16 global_word_1409.
Lemma instance_3_word_16 v : Child1Stable.word_16 (instance_3_leaves v) = global_word_1409 v.
Proof. unfold Child1Stable.word_16, global_word_1409, Child1Stable.closed_word_16, global_closed_1409, Child1Stable.expr_word_16, global_expr_1409.
 rewrite instance_3_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1409.
Transparent Child1Stable.word_17 global_word_1410.
Lemma instance_3_word_17 v : Child1Stable.word_17 (instance_3_leaves v) = global_word_1410 v.
Proof. unfold Child1Stable.word_17, global_word_1410, Child1Stable.closed_word_17, global_closed_1410, Child1Stable.expr_word_17, global_expr_1410.
 rewrite instance_3_word_14 instance_3_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1410.
Transparent Child1Stable.word_18 global_word_1411.
Lemma instance_3_word_18 v : Child1Stable.word_18 (instance_3_leaves v) = global_word_1411 v.
Proof. unfold Child1Stable.word_18, global_word_1411, Child1Stable.closed_word_18, global_closed_1411, Child1Stable.expr_word_18, global_expr_1411.
 rewrite instance_3_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1411.
Transparent Child1Stable.word_19 global_word_1412.
Lemma instance_3_word_19 v : Child1Stable.word_19 (instance_3_leaves v) = global_word_1412 v.
Proof. unfold Child1Stable.word_19, global_word_1412, Child1Stable.closed_word_19, global_closed_1412, Child1Stable.expr_word_19, global_expr_1412.
 rewrite instance_3_word_13 instance_3_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1412.
Transparent Child1Stable.word_20 global_word_1414.
Lemma instance_3_word_20 v : Child1Stable.word_20 (instance_3_leaves v) = global_word_1414 v.
Proof. unfold Child1Stable.word_20, global_word_1414, Child1Stable.closed_word_20, global_closed_1414, Child1Stable.expr_word_20, global_expr_1414.
 rewrite instance_3_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1414.
Transparent Child1Stable.word_21 global_word_1415.
Lemma instance_3_word_21 v : Child1Stable.word_21 (instance_3_leaves v) = global_word_1415 v.
Proof. unfold Child1Stable.word_21, global_word_1415, Child1Stable.closed_word_21, global_closed_1415, Child1Stable.expr_word_21, global_expr_1415.
 rewrite instance_3_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1415.
Transparent Child1Stable.word_22 global_word_1416.
Lemma instance_3_word_22 v : Child1Stable.word_22 (instance_3_leaves v) = global_word_1416 v.
Proof. unfold Child1Stable.word_22, global_word_1416, Child1Stable.closed_word_22, global_closed_1416, Child1Stable.expr_word_22, global_expr_1416.
 rewrite instance_3_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1416.
Definition instance_4_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1435 v
| 0, 1 => global_word_1431 v
| 0, 2 => global_word_342 v
| 0, 3 => global_word_345 v
| 0, 4 => global_word_339 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1435.
Lemma instance_4_word_0 v : Child1Stable.word_0 (instance_4_leaves v) = global_word_1435 v.
Proof. unfold Child1Stable.word_0, instance_4_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1435.
Transparent Child1Stable.word_1 global_word_1431.
Lemma instance_4_word_1 v : Child1Stable.word_1 (instance_4_leaves v) = global_word_1431 v.
Proof. unfold Child1Stable.word_1, instance_4_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1431.
Transparent Child1Stable.word_2 global_word_342.
Lemma instance_4_word_2 v : Child1Stable.word_2 (instance_4_leaves v) = global_word_342 v.
Proof. unfold Child1Stable.word_2, instance_4_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_342.
Transparent Child1Stable.word_3 global_word_345.
Lemma instance_4_word_3 v : Child1Stable.word_3 (instance_4_leaves v) = global_word_345 v.
Proof. unfold Child1Stable.word_3, instance_4_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_345.
Transparent Child1Stable.word_4 global_word_339.
Lemma instance_4_word_4 v : Child1Stable.word_4 (instance_4_leaves v) = global_word_339 v.
Proof. unfold Child1Stable.word_4, instance_4_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_339.
Transparent Child1Stable.word_7 global_word_1418.
Lemma instance_4_word_7 v : Child1Stable.word_7 (instance_4_leaves v) = global_word_1418 v.
Proof. unfold Child1Stable.word_7, global_word_1418, Child1Stable.closed_word_7, global_closed_1418, Child1Stable.expr_word_7, global_expr_1418.
 rewrite instance_4_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1418.
Transparent Child1Stable.word_8 global_word_1419.
Lemma instance_4_word_8 v : Child1Stable.word_8 (instance_4_leaves v) = global_word_1419 v.
Proof. unfold Child1Stable.word_8, global_word_1419, Child1Stable.closed_word_8, global_closed_1419, Child1Stable.expr_word_8, global_expr_1419.
 rewrite instance_4_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1419.
Transparent Child1Stable.word_9 global_word_1420.
Lemma instance_4_word_9 v : Child1Stable.word_9 (instance_4_leaves v) = global_word_1420 v.
Proof. unfold Child1Stable.word_9, global_word_1420, Child1Stable.closed_word_9, global_closed_1420, Child1Stable.expr_word_9, global_expr_1420.
 rewrite instance_4_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1420.
Transparent Child1Stable.word_10 global_word_1421.
Lemma instance_4_word_10 v : Child1Stable.word_10 (instance_4_leaves v) = global_word_1421 v.
Proof. unfold Child1Stable.word_10, global_word_1421, Child1Stable.closed_word_10, global_closed_1421, Child1Stable.expr_word_10, global_expr_1421.
 rewrite instance_4_word_7 instance_4_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1421.
Transparent Child1Stable.word_11 global_word_1422.
Lemma instance_4_word_11 v : Child1Stable.word_11 (instance_4_leaves v) = global_word_1422 v.
Proof. unfold Child1Stable.word_11, global_word_1422, Child1Stable.closed_word_11, global_closed_1422, Child1Stable.expr_word_11, global_expr_1422.
 rewrite instance_4_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1422.
Transparent Child1Stable.word_12 global_word_1423.
Lemma instance_4_word_12 v : Child1Stable.word_12 (instance_4_leaves v) = global_word_1423 v.
Proof. unfold Child1Stable.word_12, global_word_1423, Child1Stable.closed_word_12, global_closed_1423, Child1Stable.expr_word_12, global_expr_1423.
 rewrite instance_4_word_9 instance_4_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1423.
Transparent Child1Stable.word_13 global_word_1424.
Lemma instance_4_word_13 v : Child1Stable.word_13 (instance_4_leaves v) = global_word_1424 v.
Proof. unfold Child1Stable.word_13, global_word_1424, Child1Stable.closed_word_13, global_closed_1424, Child1Stable.expr_word_13, global_expr_1424.
 rewrite instance_4_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1424.
Transparent Child1Stable.word_25 global_word_340.
Lemma instance_4_word_25 v : Child1Stable.word_25 (instance_4_leaves v) = global_word_340 v.
Proof. unfold Child1Stable.word_25, global_word_340, Child1Stable.closed_word_25, global_closed_340, Child1Stable.expr_word_25, global_expr_340.
 rewrite instance_4_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_340.
Transparent Child1Stable.word_23 global_word_343.
Lemma instance_4_word_23 v : Child1Stable.word_23 (instance_4_leaves v) = global_word_343 v.
Proof. unfold Child1Stable.word_23, global_word_343, Child1Stable.closed_word_23, global_closed_343, Child1Stable.expr_word_23, global_expr_343.
 rewrite instance_4_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_343.
Transparent Child1Stable.word_24 global_word_346.
Lemma instance_4_word_24 v : Child1Stable.word_24 (instance_4_leaves v) = global_word_346 v.
Proof. unfold Child1Stable.word_24, global_word_346, Child1Stable.closed_word_24, global_closed_346, Child1Stable.expr_word_24, global_expr_346.
 rewrite instance_4_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_346.
Transparent Child1Stable.word_26 global_word_347.
Lemma instance_4_word_26 v : Child1Stable.word_26 (instance_4_leaves v) = global_word_347 v.
Proof. unfold Child1Stable.word_26, global_word_347, Child1Stable.closed_word_26, global_closed_347, Child1Stable.expr_word_26, global_expr_347.
 rewrite instance_4_word_23 instance_4_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_347.
Transparent Child1Stable.word_28 global_word_348.
Lemma instance_4_word_28 v : Child1Stable.word_28 (instance_4_leaves v) = global_word_348 v.
Proof. unfold Child1Stable.word_28, global_word_348, Child1Stable.closed_word_28, global_closed_348, Child1Stable.expr_word_28, global_expr_348.
 rewrite instance_4_word_25 instance_4_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_348.
Transparent Child1Stable.word_27 global_word_349.
Lemma instance_4_word_27 v : Child1Stable.word_27 (instance_4_leaves v) = global_word_349 v.
Proof. unfold Child1Stable.word_27, global_word_349, Child1Stable.closed_word_27, global_closed_349, Child1Stable.expr_word_27, global_expr_349.
 rewrite instance_4_word_23 instance_4_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_349.
Transparent Child1Stable.word_29 global_word_350.
Lemma instance_4_word_29 v : Child1Stable.word_29 (instance_4_leaves v) = global_word_350 v.
Proof. unfold Child1Stable.word_29, global_word_350, Child1Stable.closed_word_29, global_closed_350, Child1Stable.expr_word_29, global_expr_350.
 rewrite instance_4_word_25 instance_4_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_350.
Transparent Child1Stable.word_30 global_word_351.
Lemma instance_4_word_30 v : Child1Stable.word_30 (instance_4_leaves v) = global_word_351 v.
Proof. unfold Child1Stable.word_30, global_word_351, Child1Stable.closed_word_30, global_closed_351, Child1Stable.expr_word_30, global_expr_351.
 rewrite instance_4_word_27 instance_4_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_351.
Transparent Child1Stable.word_31 global_word_352.
Lemma instance_4_word_31 v : Child1Stable.word_31 (instance_4_leaves v) = global_word_352 v.
Proof. unfold Child1Stable.word_31, global_word_352, Child1Stable.closed_word_31, global_closed_352, Child1Stable.expr_word_31, global_expr_352.
 rewrite instance_4_word_28 instance_4_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_352.
Transparent Child1Stable.word_32 global_word_353.
Lemma instance_4_word_32 v : Child1Stable.word_32 (instance_4_leaves v) = global_word_353 v.
Proof. unfold Child1Stable.word_32, global_word_353, Child1Stable.closed_word_32, global_closed_353, Child1Stable.expr_word_32, global_expr_353.
 rewrite instance_4_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_353.
Transparent Child1Stable.word_33 global_word_354.
Lemma instance_4_word_33 v : Child1Stable.word_33 (instance_4_leaves v) = global_word_354 v.
Proof. unfold Child1Stable.word_33, global_word_354, Child1Stable.closed_word_33, global_closed_354, Child1Stable.expr_word_33, global_expr_354.
 rewrite instance_4_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_354.
Transparent Child1Stable.word_5 global_word_355.
Lemma instance_4_word_5 v : Child1Stable.word_5 (instance_4_leaves v) = global_word_355 v.
Proof. unfold Child1Stable.word_5, global_word_355, Child1Stable.closed_word_5, global_closed_355, Child1Stable.expr_word_5, global_expr_355.
 rewrite instance_4_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_355.
Transparent Child1Stable.word_14 global_word_1425.
Lemma instance_4_word_14 v : Child1Stable.word_14 (instance_4_leaves v) = global_word_1425 v.
Proof. unfold Child1Stable.word_14, global_word_1425, Child1Stable.closed_word_14, global_closed_1425, Child1Stable.expr_word_14, global_expr_1425.
 rewrite instance_4_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1425.
Transparent Child1Stable.word_34 global_word_358.
Lemma instance_4_word_34 v : Child1Stable.word_34 (instance_4_leaves v) = global_word_358 v.
Proof. unfold Child1Stable.word_34, global_word_358, Child1Stable.closed_word_34, global_closed_358, Child1Stable.expr_word_34, global_expr_358.
 rewrite instance_4_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_358.
Transparent Child1Stable.word_6 global_word_359.
Lemma instance_4_word_6 v : Child1Stable.word_6 (instance_4_leaves v) = global_word_359 v.
Proof. unfold Child1Stable.word_6, global_word_359, Child1Stable.closed_word_6, global_closed_359, Child1Stable.expr_word_6, global_expr_359.
 rewrite instance_4_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_359.
Transparent Child1Stable.word_15 global_word_1426.
Lemma instance_4_word_15 v : Child1Stable.word_15 (instance_4_leaves v) = global_word_1426 v.
Proof. unfold Child1Stable.word_15, global_word_1426, Child1Stable.closed_word_15, global_closed_1426, Child1Stable.expr_word_15, global_expr_1426.
 rewrite instance_4_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1426.
Transparent Child1Stable.word_16 global_word_1427.
Lemma instance_4_word_16 v : Child1Stable.word_16 (instance_4_leaves v) = global_word_1427 v.
Proof. unfold Child1Stable.word_16, global_word_1427, Child1Stable.closed_word_16, global_closed_1427, Child1Stable.expr_word_16, global_expr_1427.
 rewrite instance_4_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1427.
Transparent Child1Stable.word_17 global_word_1428.
Lemma instance_4_word_17 v : Child1Stable.word_17 (instance_4_leaves v) = global_word_1428 v.
Proof. unfold Child1Stable.word_17, global_word_1428, Child1Stable.closed_word_17, global_closed_1428, Child1Stable.expr_word_17, global_expr_1428.
 rewrite instance_4_word_14 instance_4_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1428.
Transparent Child1Stable.word_18 global_word_1429.
Lemma instance_4_word_18 v : Child1Stable.word_18 (instance_4_leaves v) = global_word_1429 v.
Proof. unfold Child1Stable.word_18, global_word_1429, Child1Stable.closed_word_18, global_closed_1429, Child1Stable.expr_word_18, global_expr_1429.
 rewrite instance_4_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1429.
Transparent Child1Stable.word_19 global_word_1430.
Lemma instance_4_word_19 v : Child1Stable.word_19 (instance_4_leaves v) = global_word_1430 v.
Proof. unfold Child1Stable.word_19, global_word_1430, Child1Stable.closed_word_19, global_closed_1430, Child1Stable.expr_word_19, global_expr_1430.
 rewrite instance_4_word_13 instance_4_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1430.
Transparent Child1Stable.word_20 global_word_1432.
Lemma instance_4_word_20 v : Child1Stable.word_20 (instance_4_leaves v) = global_word_1432 v.
Proof. unfold Child1Stable.word_20, global_word_1432, Child1Stable.closed_word_20, global_closed_1432, Child1Stable.expr_word_20, global_expr_1432.
 rewrite instance_4_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1432.
Transparent Child1Stable.word_21 global_word_1433.
Lemma instance_4_word_21 v : Child1Stable.word_21 (instance_4_leaves v) = global_word_1433 v.
Proof. unfold Child1Stable.word_21, global_word_1433, Child1Stable.closed_word_21, global_closed_1433, Child1Stable.expr_word_21, global_expr_1433.
 rewrite instance_4_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1433.
Transparent Child1Stable.word_22 global_word_1434.
Lemma instance_4_word_22 v : Child1Stable.word_22 (instance_4_leaves v) = global_word_1434 v.
Proof. unfold Child1Stable.word_22, global_word_1434, Child1Stable.closed_word_22, global_closed_1434, Child1Stable.expr_word_22, global_expr_1434.
 rewrite instance_4_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1434.
Definition instance_5_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1463 v
| 0, 1 => global_word_1459 v
| 0, 2 => global_word_374 v
| 0, 3 => global_word_379 v
| 0, 4 => global_word_369 v
| 0, 5 => global_word_398 v
| 0, 6 => global_word_363 v
| 10, 5 => global_word_392 v
| 10, 6 => global_word_419 v
| 11, 5 => global_word_412 v
| 11, 6 => global_word_426 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1463.
Lemma instance_5_word_0 v : Child2Stable.word_0 (instance_5_leaves v) = global_word_1463 v.
Proof. unfold Child2Stable.word_0, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1463.
Transparent Child2Stable.word_1 global_word_1459.
Lemma instance_5_word_1 v : Child2Stable.word_1 (instance_5_leaves v) = global_word_1459 v.
Proof. unfold Child2Stable.word_1, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1459.
Transparent Child2Stable.word_2 global_word_374.
Lemma instance_5_word_2 v : Child2Stable.word_2 (instance_5_leaves v) = global_word_374 v.
Proof. unfold Child2Stable.word_2, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_374.
Transparent Child2Stable.word_3 global_word_379.
Lemma instance_5_word_3 v : Child2Stable.word_3 (instance_5_leaves v) = global_word_379 v.
Proof. unfold Child2Stable.word_3, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_379.
Transparent Child2Stable.word_4 global_word_369.
Lemma instance_5_word_4 v : Child2Stable.word_4 (instance_5_leaves v) = global_word_369 v.
Proof. unfold Child2Stable.word_4, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_369.
Transparent Child2Stable.word_5 global_word_398.
Lemma instance_5_word_5 v : Child2Stable.word_5 (instance_5_leaves v) = global_word_398 v.
Proof. unfold Child2Stable.word_5, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_398.
Transparent Child2Stable.word_6 global_word_363.
Lemma instance_5_word_6 v : Child2Stable.word_6 (instance_5_leaves v) = global_word_363 v.
Proof. unfold Child2Stable.word_6, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_363.
Transparent Child2Stable.port_10_5 global_word_392.
Lemma instance_5_port_10_5 v : Child2Stable.port_10_5 (instance_5_leaves v) = global_word_392 v.
Proof. unfold Child2Stable.port_10_5, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_392.
Transparent Child2Stable.port_10_6 global_word_419.
Lemma instance_5_port_10_6 v : Child2Stable.port_10_6 (instance_5_leaves v) = global_word_419 v.
Proof. unfold Child2Stable.port_10_6, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_419.
Transparent Child2Stable.port_11_5 global_word_412.
Lemma instance_5_port_11_5 v : Child2Stable.port_11_5 (instance_5_leaves v) = global_word_412 v.
Proof. unfold Child2Stable.port_11_5, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_412.
Transparent Child2Stable.port_11_6 global_word_426.
Lemma instance_5_port_11_6 v : Child2Stable.port_11_6 (instance_5_leaves v) = global_word_426 v.
Proof. unfold Child2Stable.port_11_6, instance_5_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_426.
Transparent Child2Stable.word_12 global_word_1436.
Lemma instance_5_word_12 v : Child2Stable.word_12 (instance_5_leaves v) = global_word_1436 v.
Proof. unfold Child2Stable.word_12, global_word_1436, Child2Stable.closed_word_12, global_closed_1436, Child2Stable.expr_word_12, global_expr_1436.
 rewrite instance_5_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1436.
Transparent Child2Stable.word_13 global_word_1437.
Lemma instance_5_word_13 v : Child2Stable.word_13 (instance_5_leaves v) = global_word_1437 v.
Proof. unfold Child2Stable.word_13, global_word_1437, Child2Stable.closed_word_13, global_closed_1437, Child2Stable.expr_word_13, global_expr_1437.
 rewrite instance_5_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1437.
Transparent Child2Stable.word_14 global_word_1438.
Lemma instance_5_word_14 v : Child2Stable.word_14 (instance_5_leaves v) = global_word_1438 v.
Proof. unfold Child2Stable.word_14, global_word_1438, Child2Stable.closed_word_14, global_closed_1438, Child2Stable.expr_word_14, global_expr_1438.
 rewrite instance_5_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1438.
Transparent Child2Stable.word_15 global_word_1439.
Lemma instance_5_word_15 v : Child2Stable.word_15 (instance_5_leaves v) = global_word_1439 v.
Proof. unfold Child2Stable.word_15, global_word_1439, Child2Stable.closed_word_15, global_closed_1439, Child2Stable.expr_word_15, global_expr_1439.
 rewrite instance_5_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1439.
Transparent Child2Stable.word_16 global_word_1440.
Lemma instance_5_word_16 v : Child2Stable.word_16 (instance_5_leaves v) = global_word_1440 v.
Proof. unfold Child2Stable.word_16, global_word_1440, Child2Stable.closed_word_16, global_closed_1440, Child2Stable.expr_word_16, global_expr_1440.
 rewrite instance_5_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1440.
Transparent Child2Stable.word_17 global_word_1441.
Lemma instance_5_word_17 v : Child2Stable.word_17 (instance_5_leaves v) = global_word_1441 v.
Proof. unfold Child2Stable.word_17, global_word_1441, Child2Stable.closed_word_17, global_closed_1441, Child2Stable.expr_word_17, global_expr_1441.
 rewrite instance_5_word_12 instance_5_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1441.
Transparent Child2Stable.word_18 global_word_1442.
Lemma instance_5_word_18 v : Child2Stable.word_18 (instance_5_leaves v) = global_word_1442 v.
Proof. unfold Child2Stable.word_18, global_word_1442, Child2Stable.closed_word_18, global_closed_1442, Child2Stable.expr_word_18, global_expr_1442.
 rewrite instance_5_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1442.
Transparent Child2Stable.word_19 global_word_1443.
Lemma instance_5_word_19 v : Child2Stable.word_19 (instance_5_leaves v) = global_word_1443 v.
Proof. unfold Child2Stable.word_19, global_word_1443, Child2Stable.closed_word_19, global_closed_1443, Child2Stable.expr_word_19, global_expr_1443.
 rewrite instance_5_word_14 instance_5_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1443.
Transparent Child2Stable.word_20 global_word_1444.
Lemma instance_5_word_20 v : Child2Stable.word_20 (instance_5_leaves v) = global_word_1444 v.
Proof. unfold Child2Stable.word_20, global_word_1444, Child2Stable.closed_word_20, global_closed_1444, Child2Stable.expr_word_20, global_expr_1444.
 rewrite instance_5_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1444.
Transparent Child2Stable.word_21 global_word_1445.
Lemma instance_5_word_21 v : Child2Stable.word_21 (instance_5_leaves v) = global_word_1445 v.
Proof. unfold Child2Stable.word_21, global_word_1445, Child2Stable.closed_word_21, global_closed_1445, Child2Stable.expr_word_21, global_expr_1445.
 rewrite instance_5_word_15 instance_5_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1445.
Transparent Child2Stable.word_22 global_word_1446.
Lemma instance_5_word_22 v : Child2Stable.word_22 (instance_5_leaves v) = global_word_1446 v.
Proof. unfold Child2Stable.word_22, global_word_1446, Child2Stable.closed_word_22, global_closed_1446, Child2Stable.expr_word_22, global_expr_1446.
 rewrite instance_5_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1446.
Transparent Child2Stable.word_23 global_word_1447.
Lemma instance_5_word_23 v : Child2Stable.word_23 (instance_5_leaves v) = global_word_1447 v.
Proof. unfold Child2Stable.word_23, global_word_1447, Child2Stable.closed_word_23, global_closed_1447, Child2Stable.expr_word_23, global_expr_1447.
 rewrite instance_5_word_16 instance_5_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1447.
Transparent Child2Stable.word_24 global_word_1448.
Lemma instance_5_word_24 v : Child2Stable.word_24 (instance_5_leaves v) = global_word_1448 v.
Proof. unfold Child2Stable.word_24, global_word_1448, Child2Stable.closed_word_24, global_closed_1448, Child2Stable.expr_word_24, global_expr_1448.
 rewrite instance_5_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1448.
Transparent Child2Stable.word_41 global_word_413.
Lemma instance_5_word_41 v : Child2Stable.word_41 (instance_5_leaves v) = global_word_413 v.
Proof. unfold Child2Stable.word_41, global_word_413, Child2Stable.closed_word_41, global_closed_413, Child2Stable.expr_word_41, global_expr_413.
 rewrite instance_5_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_413.
Transparent Child2Stable.word_7 global_word_414.
Lemma instance_5_word_7 v : Child2Stable.word_7 (instance_5_leaves v) = global_word_414 v.
Proof. unfold Child2Stable.word_7, global_word_414, Child2Stable.closed_word_7, global_closed_414, Child2Stable.expr_word_7, global_expr_414.
 rewrite instance_5_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_414.
Transparent Child2Stable.word_25 global_word_1449.
Lemma instance_5_word_25 v : Child2Stable.word_25 (instance_5_leaves v) = global_word_1449 v.
Proof. unfold Child2Stable.word_25, global_word_1449, Child2Stable.closed_word_25, global_closed_1449, Child2Stable.expr_word_25, global_expr_1449.
 rewrite instance_5_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1449.
Transparent Child2Stable.word_42 global_word_420.
Lemma instance_5_word_42 v : Child2Stable.word_42 (instance_5_leaves v) = global_word_420 v.
Proof. unfold Child2Stable.word_42, global_word_420, Child2Stable.closed_word_42, global_closed_420, Child2Stable.expr_word_42, global_expr_420.
 rewrite instance_5_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_420.
Transparent Child2Stable.word_8 global_word_421.
Lemma instance_5_word_8 v : Child2Stable.word_8 (instance_5_leaves v) = global_word_421 v.
Proof. unfold Child2Stable.word_8, global_word_421, Child2Stable.closed_word_8, global_closed_421, Child2Stable.expr_word_8, global_expr_421.
 rewrite instance_5_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_421.
Transparent Child2Stable.word_26 global_word_1450.
Lemma instance_5_word_26 v : Child2Stable.word_26 (instance_5_leaves v) = global_word_1450 v.
Proof. unfold Child2Stable.word_26, global_word_1450, Child2Stable.closed_word_26, global_closed_1450, Child2Stable.expr_word_26, global_expr_1450.
 rewrite instance_5_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1450.
Transparent Child2Stable.word_27 global_word_1451.
Lemma instance_5_word_27 v : Child2Stable.word_27 (instance_5_leaves v) = global_word_1451 v.
Proof. unfold Child2Stable.word_27, global_word_1451, Child2Stable.closed_word_27, global_closed_1451, Child2Stable.expr_word_27, global_expr_1451.
 rewrite instance_5_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1451.
Transparent Child2Stable.word_43 global_word_427.
Lemma instance_5_word_43 v : Child2Stable.word_43 (instance_5_leaves v) = global_word_427 v.
Proof. unfold Child2Stable.word_43, global_word_427, Child2Stable.closed_word_43, global_closed_427, Child2Stable.expr_word_43, global_expr_427.
 rewrite instance_5_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_427.
Transparent Child2Stable.word_9 global_word_428.
Lemma instance_5_word_9 v : Child2Stable.word_9 (instance_5_leaves v) = global_word_428 v.
Proof. unfold Child2Stable.word_9, global_word_428, Child2Stable.closed_word_9, global_closed_428, Child2Stable.expr_word_9, global_expr_428.
 rewrite instance_5_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_428.
Transparent Child2Stable.word_28 global_word_1452.
Lemma instance_5_word_28 v : Child2Stable.word_28 (instance_5_leaves v) = global_word_1452 v.
Proof. unfold Child2Stable.word_28, global_word_1452, Child2Stable.closed_word_28, global_closed_1452, Child2Stable.expr_word_28, global_expr_1452.
 rewrite instance_5_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1452.
Transparent Child2Stable.word_29 global_word_1453.
Lemma instance_5_word_29 v : Child2Stable.word_29 (instance_5_leaves v) = global_word_1453 v.
Proof. unfold Child2Stable.word_29, global_word_1453, Child2Stable.closed_word_29, global_closed_1453, Child2Stable.expr_word_29, global_expr_1453.
 rewrite instance_5_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1453.
Transparent Child2Stable.word_30 global_word_1454.
Lemma instance_5_word_30 v : Child2Stable.word_30 (instance_5_leaves v) = global_word_1454 v.
Proof. unfold Child2Stable.word_30, global_word_1454, Child2Stable.closed_word_30, global_closed_1454, Child2Stable.expr_word_30, global_expr_1454.
 rewrite instance_5_word_25 instance_5_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1454.
Transparent Child2Stable.word_31 global_word_1455.
Lemma instance_5_word_31 v : Child2Stable.word_31 (instance_5_leaves v) = global_word_1455 v.
Proof. unfold Child2Stable.word_31, global_word_1455, Child2Stable.closed_word_31, global_closed_1455, Child2Stable.expr_word_31, global_expr_1455.
 rewrite instance_5_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1455.
Transparent Child2Stable.word_32 global_word_1456.
Lemma instance_5_word_32 v : Child2Stable.word_32 (instance_5_leaves v) = global_word_1456 v.
Proof. unfold Child2Stable.word_32, global_word_1456, Child2Stable.closed_word_32, global_closed_1456, Child2Stable.expr_word_32, global_expr_1456.
 rewrite instance_5_word_29 instance_5_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1456.
Transparent Child2Stable.word_33 global_word_1457.
Lemma instance_5_word_33 v : Child2Stable.word_33 (instance_5_leaves v) = global_word_1457 v.
Proof. unfold Child2Stable.word_33, global_word_1457, Child2Stable.closed_word_33, global_closed_1457, Child2Stable.expr_word_33, global_expr_1457.
 rewrite instance_5_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1457.
Transparent Child2Stable.word_34 global_word_1458.
Lemma instance_5_word_34 v : Child2Stable.word_34 (instance_5_leaves v) = global_word_1458 v.
Proof. unfold Child2Stable.word_34, global_word_1458, Child2Stable.closed_word_34, global_closed_1458, Child2Stable.expr_word_34, global_expr_1458.
 rewrite instance_5_word_24 instance_5_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1458.
Transparent Child2Stable.word_35 global_word_1460.
Lemma instance_5_word_35 v : Child2Stable.word_35 (instance_5_leaves v) = global_word_1460 v.
Proof. unfold Child2Stable.word_35, global_word_1460, Child2Stable.closed_word_35, global_closed_1460, Child2Stable.expr_word_35, global_expr_1460.
 rewrite instance_5_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1460.
Transparent Child2Stable.word_36 global_word_1461.
Lemma instance_5_word_36 v : Child2Stable.word_36 (instance_5_leaves v) = global_word_1461 v.
Proof. unfold Child2Stable.word_36, global_word_1461, Child2Stable.closed_word_36, global_closed_1461, Child2Stable.expr_word_36, global_expr_1461.
 rewrite instance_5_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1461.
Transparent Child2Stable.word_37 global_word_1462.
Lemma instance_5_word_37 v : Child2Stable.word_37 (instance_5_leaves v) = global_word_1462 v.
Proof. unfold Child2Stable.word_37, global_word_1462, Child2Stable.closed_word_37, global_closed_1462, Child2Stable.expr_word_37, global_expr_1462.
 rewrite instance_5_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1462.
Transparent Child2Stable.word_38 global_word_393.
Lemma instance_5_word_38 v : Child2Stable.word_38 (instance_5_leaves v) = global_word_393 v.
Proof. unfold Child2Stable.word_38, global_word_393, Child2Stable.closed_word_38, global_closed_393, Child2Stable.expr_word_38, global_expr_393.
 rewrite instance_5_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_393.
Transparent Child2Stable.word_39 global_word_399.
Lemma instance_5_word_39 v : Child2Stable.word_39 (instance_5_leaves v) = global_word_399 v.
Proof. unfold Child2Stable.word_39, global_word_399, Child2Stable.closed_word_39, global_closed_399, Child2Stable.expr_word_39, global_expr_399.
 rewrite instance_5_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_399.
Transparent Child2Stable.word_40 global_word_364.
Lemma instance_5_word_40 v : Child2Stable.word_40 (instance_5_leaves v) = global_word_364 v.
Proof. unfold Child2Stable.word_40, global_word_364, Child2Stable.closed_word_40, global_closed_364, Child2Stable.expr_word_40, global_expr_364.
 rewrite instance_5_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_364.
Transparent Child2Stable.port_10_0 global_word_1464.
Lemma instance_5_port_10_0 v : Child2Stable.port_10_0 (instance_5_leaves v) = global_word_1464 v.
Proof. unfold Child2Stable.port_10_0, global_word_1464, Child2Stable.closed_port_10_0, global_closed_1464, Child2Stable.expr_port_10_0, global_expr_1464.
 rewrite instance_5_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1464.
Transparent Child2Stable.port_10_1 global_word_1465.
Lemma instance_5_port_10_1 v : Child2Stable.port_10_1 (instance_5_leaves v) = global_word_1465 v.
Proof. unfold Child2Stable.port_10_1, global_word_1465, Child2Stable.closed_port_10_1, global_closed_1465, Child2Stable.expr_port_10_1, global_expr_1465.
 rewrite instance_5_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1465.
Transparent Child2Stable.port_10_2 global_word_375.
Lemma instance_5_port_10_2 v : Child2Stable.port_10_2 (instance_5_leaves v) = global_word_375 v.
Proof. unfold Child2Stable.port_10_2, global_word_375, Child2Stable.closed_port_10_2, global_closed_375, Child2Stable.expr_port_10_2, global_expr_375.
 rewrite instance_5_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_375.
Transparent Child2Stable.port_10_3 global_word_380.
Lemma instance_5_port_10_3 v : Child2Stable.port_10_3 (instance_5_leaves v) = global_word_380 v.
Proof. unfold Child2Stable.port_10_3, global_word_380, Child2Stable.closed_port_10_3, global_closed_380, Child2Stable.expr_port_10_3, global_expr_380.
 rewrite instance_5_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_380.
Transparent Child2Stable.port_10_4 global_word_370.
Lemma instance_5_port_10_4 v : Child2Stable.port_10_4 (instance_5_leaves v) = global_word_370 v.
Proof. unfold Child2Stable.port_10_4, global_word_370, Child2Stable.closed_port_10_4, global_closed_370, Child2Stable.expr_port_10_4, global_expr_370.
 rewrite instance_5_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_370.
Transparent Child2Stable.port_11_0 global_word_1466.
Lemma instance_5_port_11_0 v : Child2Stable.port_11_0 (instance_5_leaves v) = global_word_1466 v.
Proof. unfold Child2Stable.port_11_0, global_word_1466, Child2Stable.closed_port_11_0, global_closed_1466, Child2Stable.expr_port_11_0, global_expr_1466.
 rewrite instance_5_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1466.
Transparent Child2Stable.port_11_1 global_word_1467.
Lemma instance_5_port_11_1 v : Child2Stable.port_11_1 (instance_5_leaves v) = global_word_1467 v.
Proof. unfold Child2Stable.port_11_1, global_word_1467, Child2Stable.closed_port_11_1, global_closed_1467, Child2Stable.expr_port_11_1, global_expr_1467.
 rewrite instance_5_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1467.
Transparent Child2Stable.port_11_2 global_word_394.
Lemma instance_5_port_11_2 v : Child2Stable.port_11_2 (instance_5_leaves v) = global_word_394 v.
Proof. unfold Child2Stable.port_11_2, global_word_394, Child2Stable.closed_port_11_2, global_closed_394, Child2Stable.expr_port_11_2, global_expr_394.
 rewrite instance_5_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_394.
Transparent Child2Stable.port_11_3 global_word_400.
Lemma instance_5_port_11_3 v : Child2Stable.port_11_3 (instance_5_leaves v) = global_word_400 v.
Proof. unfold Child2Stable.port_11_3, global_word_400, Child2Stable.closed_port_11_3, global_closed_400, Child2Stable.expr_port_11_3, global_expr_400.
 rewrite instance_5_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_400.
Transparent Child2Stable.port_11_4 global_word_365.
Lemma instance_5_port_11_4 v : Child2Stable.port_11_4 (instance_5_leaves v) = global_word_365 v.
Proof. unfold Child2Stable.port_11_4, global_word_365, Child2Stable.closed_port_11_4, global_closed_365, Child2Stable.expr_port_11_4, global_expr_365.
 rewrite instance_5_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_365.
Definition instance_6_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1485 v
| 0, 1 => global_word_1481 v
| 0, 2 => global_word_376 v
| 0, 3 => global_word_381 v
| 0, 4 => global_word_371 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1485.
Lemma instance_6_word_0 v : Child1Stable.word_0 (instance_6_leaves v) = global_word_1485 v.
Proof. unfold Child1Stable.word_0, instance_6_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1485.
Transparent Child1Stable.word_1 global_word_1481.
Lemma instance_6_word_1 v : Child1Stable.word_1 (instance_6_leaves v) = global_word_1481 v.
Proof. unfold Child1Stable.word_1, instance_6_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1481.
Transparent Child1Stable.word_2 global_word_376.
Lemma instance_6_word_2 v : Child1Stable.word_2 (instance_6_leaves v) = global_word_376 v.
Proof. unfold Child1Stable.word_2, instance_6_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_376.
Transparent Child1Stable.word_3 global_word_381.
Lemma instance_6_word_3 v : Child1Stable.word_3 (instance_6_leaves v) = global_word_381 v.
Proof. unfold Child1Stable.word_3, instance_6_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_381.
Transparent Child1Stable.word_4 global_word_371.
Lemma instance_6_word_4 v : Child1Stable.word_4 (instance_6_leaves v) = global_word_371 v.
Proof. unfold Child1Stable.word_4, instance_6_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_371.
Transparent Child1Stable.word_7 global_word_1468.
Lemma instance_6_word_7 v : Child1Stable.word_7 (instance_6_leaves v) = global_word_1468 v.
Proof. unfold Child1Stable.word_7, global_word_1468, Child1Stable.closed_word_7, global_closed_1468, Child1Stable.expr_word_7, global_expr_1468.
 rewrite instance_6_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1468.
Transparent Child1Stable.word_8 global_word_1469.
Lemma instance_6_word_8 v : Child1Stable.word_8 (instance_6_leaves v) = global_word_1469 v.
Proof. unfold Child1Stable.word_8, global_word_1469, Child1Stable.closed_word_8, global_closed_1469, Child1Stable.expr_word_8, global_expr_1469.
 rewrite instance_6_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1469.
Transparent Child1Stable.word_9 global_word_1470.
Lemma instance_6_word_9 v : Child1Stable.word_9 (instance_6_leaves v) = global_word_1470 v.
Proof. unfold Child1Stable.word_9, global_word_1470, Child1Stable.closed_word_9, global_closed_1470, Child1Stable.expr_word_9, global_expr_1470.
 rewrite instance_6_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1470.
Transparent Child1Stable.word_10 global_word_1471.
Lemma instance_6_word_10 v : Child1Stable.word_10 (instance_6_leaves v) = global_word_1471 v.
Proof. unfold Child1Stable.word_10, global_word_1471, Child1Stable.closed_word_10, global_closed_1471, Child1Stable.expr_word_10, global_expr_1471.
 rewrite instance_6_word_7 instance_6_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1471.
Transparent Child1Stable.word_11 global_word_1472.
Lemma instance_6_word_11 v : Child1Stable.word_11 (instance_6_leaves v) = global_word_1472 v.
Proof. unfold Child1Stable.word_11, global_word_1472, Child1Stable.closed_word_11, global_closed_1472, Child1Stable.expr_word_11, global_expr_1472.
 rewrite instance_6_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1472.
Transparent Child1Stable.word_12 global_word_1473.
Lemma instance_6_word_12 v : Child1Stable.word_12 (instance_6_leaves v) = global_word_1473 v.
Proof. unfold Child1Stable.word_12, global_word_1473, Child1Stable.closed_word_12, global_closed_1473, Child1Stable.expr_word_12, global_expr_1473.
 rewrite instance_6_word_9 instance_6_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1473.
Transparent Child1Stable.word_13 global_word_1474.
Lemma instance_6_word_13 v : Child1Stable.word_13 (instance_6_leaves v) = global_word_1474 v.
Proof. unfold Child1Stable.word_13, global_word_1474, Child1Stable.closed_word_13, global_closed_1474, Child1Stable.expr_word_13, global_expr_1474.
 rewrite instance_6_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1474.
Transparent Child1Stable.word_25 global_word_372.
Lemma instance_6_word_25 v : Child1Stable.word_25 (instance_6_leaves v) = global_word_372 v.
Proof. unfold Child1Stable.word_25, global_word_372, Child1Stable.closed_word_25, global_closed_372, Child1Stable.expr_word_25, global_expr_372.
 rewrite instance_6_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_372.
Transparent Child1Stable.word_23 global_word_377.
Lemma instance_6_word_23 v : Child1Stable.word_23 (instance_6_leaves v) = global_word_377 v.
Proof. unfold Child1Stable.word_23, global_word_377, Child1Stable.closed_word_23, global_closed_377, Child1Stable.expr_word_23, global_expr_377.
 rewrite instance_6_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_377.
Transparent Child1Stable.word_24 global_word_382.
Lemma instance_6_word_24 v : Child1Stable.word_24 (instance_6_leaves v) = global_word_382 v.
Proof. unfold Child1Stable.word_24, global_word_382, Child1Stable.closed_word_24, global_closed_382, Child1Stable.expr_word_24, global_expr_382.
 rewrite instance_6_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_382.
Transparent Child1Stable.word_26 global_word_383.
Lemma instance_6_word_26 v : Child1Stable.word_26 (instance_6_leaves v) = global_word_383 v.
Proof. unfold Child1Stable.word_26, global_word_383, Child1Stable.closed_word_26, global_closed_383, Child1Stable.expr_word_26, global_expr_383.
 rewrite instance_6_word_23 instance_6_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_383.
Transparent Child1Stable.word_28 global_word_384.
Lemma instance_6_word_28 v : Child1Stable.word_28 (instance_6_leaves v) = global_word_384 v.
Proof. unfold Child1Stable.word_28, global_word_384, Child1Stable.closed_word_28, global_closed_384, Child1Stable.expr_word_28, global_expr_384.
 rewrite instance_6_word_25 instance_6_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_384.
Transparent Child1Stable.word_27 global_word_385.
Lemma instance_6_word_27 v : Child1Stable.word_27 (instance_6_leaves v) = global_word_385 v.
Proof. unfold Child1Stable.word_27, global_word_385, Child1Stable.closed_word_27, global_closed_385, Child1Stable.expr_word_27, global_expr_385.
 rewrite instance_6_word_23 instance_6_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_385.
Transparent Child1Stable.word_29 global_word_386.
Lemma instance_6_word_29 v : Child1Stable.word_29 (instance_6_leaves v) = global_word_386 v.
Proof. unfold Child1Stable.word_29, global_word_386, Child1Stable.closed_word_29, global_closed_386, Child1Stable.expr_word_29, global_expr_386.
 rewrite instance_6_word_25 instance_6_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_386.
Transparent Child1Stable.word_30 global_word_387.
Lemma instance_6_word_30 v : Child1Stable.word_30 (instance_6_leaves v) = global_word_387 v.
Proof. unfold Child1Stable.word_30, global_word_387, Child1Stable.closed_word_30, global_closed_387, Child1Stable.expr_word_30, global_expr_387.
 rewrite instance_6_word_27 instance_6_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_387.
Transparent Child1Stable.word_31 global_word_388.
Lemma instance_6_word_31 v : Child1Stable.word_31 (instance_6_leaves v) = global_word_388 v.
Proof. unfold Child1Stable.word_31, global_word_388, Child1Stable.closed_word_31, global_closed_388, Child1Stable.expr_word_31, global_expr_388.
 rewrite instance_6_word_28 instance_6_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_388.
Transparent Child1Stable.word_32 global_word_389.
Lemma instance_6_word_32 v : Child1Stable.word_32 (instance_6_leaves v) = global_word_389 v.
Proof. unfold Child1Stable.word_32, global_word_389, Child1Stable.closed_word_32, global_closed_389, Child1Stable.expr_word_32, global_expr_389.
 rewrite instance_6_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_389.
Transparent Child1Stable.word_33 global_word_390.
Lemma instance_6_word_33 v : Child1Stable.word_33 (instance_6_leaves v) = global_word_390 v.
Proof. unfold Child1Stable.word_33, global_word_390, Child1Stable.closed_word_33, global_closed_390, Child1Stable.expr_word_33, global_expr_390.
 rewrite instance_6_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_390.
Transparent Child1Stable.word_5 global_word_391.
Lemma instance_6_word_5 v : Child1Stable.word_5 (instance_6_leaves v) = global_word_391 v.
Proof. unfold Child1Stable.word_5, global_word_391, Child1Stable.closed_word_5, global_closed_391, Child1Stable.expr_word_5, global_expr_391.
 rewrite instance_6_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_391.
Transparent Child1Stable.word_14 global_word_1475.
Lemma instance_6_word_14 v : Child1Stable.word_14 (instance_6_leaves v) = global_word_1475 v.
Proof. unfold Child1Stable.word_14, global_word_1475, Child1Stable.closed_word_14, global_closed_1475, Child1Stable.expr_word_14, global_expr_1475.
 rewrite instance_6_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1475.
Transparent Child1Stable.word_34 global_word_417.
Lemma instance_6_word_34 v : Child1Stable.word_34 (instance_6_leaves v) = global_word_417 v.
Proof. unfold Child1Stable.word_34, global_word_417, Child1Stable.closed_word_34, global_closed_417, Child1Stable.expr_word_34, global_expr_417.
 rewrite instance_6_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_417.
Transparent Child1Stable.word_6 global_word_418.
Lemma instance_6_word_6 v : Child1Stable.word_6 (instance_6_leaves v) = global_word_418 v.
Proof. unfold Child1Stable.word_6, global_word_418, Child1Stable.closed_word_6, global_closed_418, Child1Stable.expr_word_6, global_expr_418.
 rewrite instance_6_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_418.
Transparent Child1Stable.word_15 global_word_1476.
Lemma instance_6_word_15 v : Child1Stable.word_15 (instance_6_leaves v) = global_word_1476 v.
Proof. unfold Child1Stable.word_15, global_word_1476, Child1Stable.closed_word_15, global_closed_1476, Child1Stable.expr_word_15, global_expr_1476.
 rewrite instance_6_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1476.
Transparent Child1Stable.word_16 global_word_1477.
Lemma instance_6_word_16 v : Child1Stable.word_16 (instance_6_leaves v) = global_word_1477 v.
Proof. unfold Child1Stable.word_16, global_word_1477, Child1Stable.closed_word_16, global_closed_1477, Child1Stable.expr_word_16, global_expr_1477.
 rewrite instance_6_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1477.
Transparent Child1Stable.word_17 global_word_1478.
Lemma instance_6_word_17 v : Child1Stable.word_17 (instance_6_leaves v) = global_word_1478 v.
Proof. unfold Child1Stable.word_17, global_word_1478, Child1Stable.closed_word_17, global_closed_1478, Child1Stable.expr_word_17, global_expr_1478.
 rewrite instance_6_word_14 instance_6_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1478.
Transparent Child1Stable.word_18 global_word_1479.
Lemma instance_6_word_18 v : Child1Stable.word_18 (instance_6_leaves v) = global_word_1479 v.
Proof. unfold Child1Stable.word_18, global_word_1479, Child1Stable.closed_word_18, global_closed_1479, Child1Stable.expr_word_18, global_expr_1479.
 rewrite instance_6_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1479.
Transparent Child1Stable.word_19 global_word_1480.
Lemma instance_6_word_19 v : Child1Stable.word_19 (instance_6_leaves v) = global_word_1480 v.
Proof. unfold Child1Stable.word_19, global_word_1480, Child1Stable.closed_word_19, global_closed_1480, Child1Stable.expr_word_19, global_expr_1480.
 rewrite instance_6_word_13 instance_6_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1480.
Transparent Child1Stable.word_20 global_word_1482.
Lemma instance_6_word_20 v : Child1Stable.word_20 (instance_6_leaves v) = global_word_1482 v.
Proof. unfold Child1Stable.word_20, global_word_1482, Child1Stable.closed_word_20, global_closed_1482, Child1Stable.expr_word_20, global_expr_1482.
 rewrite instance_6_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1482.
Transparent Child1Stable.word_21 global_word_1483.
Lemma instance_6_word_21 v : Child1Stable.word_21 (instance_6_leaves v) = global_word_1483 v.
Proof. unfold Child1Stable.word_21, global_word_1483, Child1Stable.closed_word_21, global_closed_1483, Child1Stable.expr_word_21, global_expr_1483.
 rewrite instance_6_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1483.
Transparent Child1Stable.word_22 global_word_1484.
Lemma instance_6_word_22 v : Child1Stable.word_22 (instance_6_leaves v) = global_word_1484 v.
Proof. unfold Child1Stable.word_22, global_word_1484, Child1Stable.closed_word_22, global_closed_1484, Child1Stable.expr_word_22, global_expr_1484.
 rewrite instance_6_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1484.
Definition instance_7_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1503 v
| 0, 1 => global_word_1499 v
| 0, 2 => global_word_395 v
| 0, 3 => global_word_401 v
| 0, 4 => global_word_366 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1503.
Lemma instance_7_word_0 v : Child1Stable.word_0 (instance_7_leaves v) = global_word_1503 v.
Proof. unfold Child1Stable.word_0, instance_7_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1503.
Transparent Child1Stable.word_1 global_word_1499.
Lemma instance_7_word_1 v : Child1Stable.word_1 (instance_7_leaves v) = global_word_1499 v.
Proof. unfold Child1Stable.word_1, instance_7_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1499.
Transparent Child1Stable.word_2 global_word_395.
Lemma instance_7_word_2 v : Child1Stable.word_2 (instance_7_leaves v) = global_word_395 v.
Proof. unfold Child1Stable.word_2, instance_7_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_395.
Transparent Child1Stable.word_3 global_word_401.
Lemma instance_7_word_3 v : Child1Stable.word_3 (instance_7_leaves v) = global_word_401 v.
Proof. unfold Child1Stable.word_3, instance_7_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_401.
Transparent Child1Stable.word_4 global_word_366.
Lemma instance_7_word_4 v : Child1Stable.word_4 (instance_7_leaves v) = global_word_366 v.
Proof. unfold Child1Stable.word_4, instance_7_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_366.
Transparent Child1Stable.word_7 global_word_1486.
Lemma instance_7_word_7 v : Child1Stable.word_7 (instance_7_leaves v) = global_word_1486 v.
Proof. unfold Child1Stable.word_7, global_word_1486, Child1Stable.closed_word_7, global_closed_1486, Child1Stable.expr_word_7, global_expr_1486.
 rewrite instance_7_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1486.
Transparent Child1Stable.word_8 global_word_1487.
Lemma instance_7_word_8 v : Child1Stable.word_8 (instance_7_leaves v) = global_word_1487 v.
Proof. unfold Child1Stable.word_8, global_word_1487, Child1Stable.closed_word_8, global_closed_1487, Child1Stable.expr_word_8, global_expr_1487.
 rewrite instance_7_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1487.
Transparent Child1Stable.word_9 global_word_1488.
Lemma instance_7_word_9 v : Child1Stable.word_9 (instance_7_leaves v) = global_word_1488 v.
Proof. unfold Child1Stable.word_9, global_word_1488, Child1Stable.closed_word_9, global_closed_1488, Child1Stable.expr_word_9, global_expr_1488.
 rewrite instance_7_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1488.
Transparent Child1Stable.word_10 global_word_1489.
Lemma instance_7_word_10 v : Child1Stable.word_10 (instance_7_leaves v) = global_word_1489 v.
Proof. unfold Child1Stable.word_10, global_word_1489, Child1Stable.closed_word_10, global_closed_1489, Child1Stable.expr_word_10, global_expr_1489.
 rewrite instance_7_word_7 instance_7_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1489.
Transparent Child1Stable.word_11 global_word_1490.
Lemma instance_7_word_11 v : Child1Stable.word_11 (instance_7_leaves v) = global_word_1490 v.
Proof. unfold Child1Stable.word_11, global_word_1490, Child1Stable.closed_word_11, global_closed_1490, Child1Stable.expr_word_11, global_expr_1490.
 rewrite instance_7_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1490.
Transparent Child1Stable.word_12 global_word_1491.
Lemma instance_7_word_12 v : Child1Stable.word_12 (instance_7_leaves v) = global_word_1491 v.
Proof. unfold Child1Stable.word_12, global_word_1491, Child1Stable.closed_word_12, global_closed_1491, Child1Stable.expr_word_12, global_expr_1491.
 rewrite instance_7_word_9 instance_7_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1491.
Transparent Child1Stable.word_13 global_word_1492.
Lemma instance_7_word_13 v : Child1Stable.word_13 (instance_7_leaves v) = global_word_1492 v.
Proof. unfold Child1Stable.word_13, global_word_1492, Child1Stable.closed_word_13, global_closed_1492, Child1Stable.expr_word_13, global_expr_1492.
 rewrite instance_7_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1492.
Transparent Child1Stable.word_25 global_word_367.
Lemma instance_7_word_25 v : Child1Stable.word_25 (instance_7_leaves v) = global_word_367 v.
Proof. unfold Child1Stable.word_25, global_word_367, Child1Stable.closed_word_25, global_closed_367, Child1Stable.expr_word_25, global_expr_367.
 rewrite instance_7_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_367.
Transparent Child1Stable.word_23 global_word_396.
Lemma instance_7_word_23 v : Child1Stable.word_23 (instance_7_leaves v) = global_word_396 v.
Proof. unfold Child1Stable.word_23, global_word_396, Child1Stable.closed_word_23, global_closed_396, Child1Stable.expr_word_23, global_expr_396.
 rewrite instance_7_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_396.
Transparent Child1Stable.word_24 global_word_402.
Lemma instance_7_word_24 v : Child1Stable.word_24 (instance_7_leaves v) = global_word_402 v.
Proof. unfold Child1Stable.word_24, global_word_402, Child1Stable.closed_word_24, global_closed_402, Child1Stable.expr_word_24, global_expr_402.
 rewrite instance_7_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_402.
Transparent Child1Stable.word_26 global_word_403.
Lemma instance_7_word_26 v : Child1Stable.word_26 (instance_7_leaves v) = global_word_403 v.
Proof. unfold Child1Stable.word_26, global_word_403, Child1Stable.closed_word_26, global_closed_403, Child1Stable.expr_word_26, global_expr_403.
 rewrite instance_7_word_23 instance_7_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_403.
Transparent Child1Stable.word_28 global_word_404.
Lemma instance_7_word_28 v : Child1Stable.word_28 (instance_7_leaves v) = global_word_404 v.
Proof. unfold Child1Stable.word_28, global_word_404, Child1Stable.closed_word_28, global_closed_404, Child1Stable.expr_word_28, global_expr_404.
 rewrite instance_7_word_25 instance_7_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_404.
Transparent Child1Stable.word_27 global_word_405.
Lemma instance_7_word_27 v : Child1Stable.word_27 (instance_7_leaves v) = global_word_405 v.
Proof. unfold Child1Stable.word_27, global_word_405, Child1Stable.closed_word_27, global_closed_405, Child1Stable.expr_word_27, global_expr_405.
 rewrite instance_7_word_23 instance_7_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_405.
Transparent Child1Stable.word_29 global_word_406.
Lemma instance_7_word_29 v : Child1Stable.word_29 (instance_7_leaves v) = global_word_406 v.
Proof. unfold Child1Stable.word_29, global_word_406, Child1Stable.closed_word_29, global_closed_406, Child1Stable.expr_word_29, global_expr_406.
 rewrite instance_7_word_25 instance_7_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_406.
Transparent Child1Stable.word_30 global_word_407.
Lemma instance_7_word_30 v : Child1Stable.word_30 (instance_7_leaves v) = global_word_407 v.
Proof. unfold Child1Stable.word_30, global_word_407, Child1Stable.closed_word_30, global_closed_407, Child1Stable.expr_word_30, global_expr_407.
 rewrite instance_7_word_27 instance_7_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_407.
Transparent Child1Stable.word_31 global_word_408.
Lemma instance_7_word_31 v : Child1Stable.word_31 (instance_7_leaves v) = global_word_408 v.
Proof. unfold Child1Stable.word_31, global_word_408, Child1Stable.closed_word_31, global_closed_408, Child1Stable.expr_word_31, global_expr_408.
 rewrite instance_7_word_28 instance_7_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_408.
Transparent Child1Stable.word_32 global_word_409.
Lemma instance_7_word_32 v : Child1Stable.word_32 (instance_7_leaves v) = global_word_409 v.
Proof. unfold Child1Stable.word_32, global_word_409, Child1Stable.closed_word_32, global_closed_409, Child1Stable.expr_word_32, global_expr_409.
 rewrite instance_7_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_409.
Transparent Child1Stable.word_33 global_word_410.
Lemma instance_7_word_33 v : Child1Stable.word_33 (instance_7_leaves v) = global_word_410 v.
Proof. unfold Child1Stable.word_33, global_word_410, Child1Stable.closed_word_33, global_closed_410, Child1Stable.expr_word_33, global_expr_410.
 rewrite instance_7_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_410.
Transparent Child1Stable.word_5 global_word_411.
Lemma instance_7_word_5 v : Child1Stable.word_5 (instance_7_leaves v) = global_word_411 v.
Proof. unfold Child1Stable.word_5, global_word_411, Child1Stable.closed_word_5, global_closed_411, Child1Stable.expr_word_5, global_expr_411.
 rewrite instance_7_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_411.
Transparent Child1Stable.word_14 global_word_1493.
Lemma instance_7_word_14 v : Child1Stable.word_14 (instance_7_leaves v) = global_word_1493 v.
Proof. unfold Child1Stable.word_14, global_word_1493, Child1Stable.closed_word_14, global_closed_1493, Child1Stable.expr_word_14, global_expr_1493.
 rewrite instance_7_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1493.
Transparent Child1Stable.word_34 global_word_424.
Lemma instance_7_word_34 v : Child1Stable.word_34 (instance_7_leaves v) = global_word_424 v.
Proof. unfold Child1Stable.word_34, global_word_424, Child1Stable.closed_word_34, global_closed_424, Child1Stable.expr_word_34, global_expr_424.
 rewrite instance_7_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_424.
Transparent Child1Stable.word_6 global_word_425.
Lemma instance_7_word_6 v : Child1Stable.word_6 (instance_7_leaves v) = global_word_425 v.
Proof. unfold Child1Stable.word_6, global_word_425, Child1Stable.closed_word_6, global_closed_425, Child1Stable.expr_word_6, global_expr_425.
 rewrite instance_7_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_425.
Transparent Child1Stable.word_15 global_word_1494.
Lemma instance_7_word_15 v : Child1Stable.word_15 (instance_7_leaves v) = global_word_1494 v.
Proof. unfold Child1Stable.word_15, global_word_1494, Child1Stable.closed_word_15, global_closed_1494, Child1Stable.expr_word_15, global_expr_1494.
 rewrite instance_7_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1494.
Transparent Child1Stable.word_16 global_word_1495.
Lemma instance_7_word_16 v : Child1Stable.word_16 (instance_7_leaves v) = global_word_1495 v.
Proof. unfold Child1Stable.word_16, global_word_1495, Child1Stable.closed_word_16, global_closed_1495, Child1Stable.expr_word_16, global_expr_1495.
 rewrite instance_7_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1495.
Transparent Child1Stable.word_17 global_word_1496.
Lemma instance_7_word_17 v : Child1Stable.word_17 (instance_7_leaves v) = global_word_1496 v.
Proof. unfold Child1Stable.word_17, global_word_1496, Child1Stable.closed_word_17, global_closed_1496, Child1Stable.expr_word_17, global_expr_1496.
 rewrite instance_7_word_14 instance_7_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1496.
Transparent Child1Stable.word_18 global_word_1497.
Lemma instance_7_word_18 v : Child1Stable.word_18 (instance_7_leaves v) = global_word_1497 v.
Proof. unfold Child1Stable.word_18, global_word_1497, Child1Stable.closed_word_18, global_closed_1497, Child1Stable.expr_word_18, global_expr_1497.
 rewrite instance_7_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1497.
Transparent Child1Stable.word_19 global_word_1498.
Lemma instance_7_word_19 v : Child1Stable.word_19 (instance_7_leaves v) = global_word_1498 v.
Proof. unfold Child1Stable.word_19, global_word_1498, Child1Stable.closed_word_19, global_closed_1498, Child1Stable.expr_word_19, global_expr_1498.
 rewrite instance_7_word_13 instance_7_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1498.
Transparent Child1Stable.word_20 global_word_1500.
Lemma instance_7_word_20 v : Child1Stable.word_20 (instance_7_leaves v) = global_word_1500 v.
Proof. unfold Child1Stable.word_20, global_word_1500, Child1Stable.closed_word_20, global_closed_1500, Child1Stable.expr_word_20, global_expr_1500.
 rewrite instance_7_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1500.
Transparent Child1Stable.word_21 global_word_1501.
Lemma instance_7_word_21 v : Child1Stable.word_21 (instance_7_leaves v) = global_word_1501 v.
Proof. unfold Child1Stable.word_21, global_word_1501, Child1Stable.closed_word_21, global_closed_1501, Child1Stable.expr_word_21, global_expr_1501.
 rewrite instance_7_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1501.
Transparent Child1Stable.word_22 global_word_1502.
Lemma instance_7_word_22 v : Child1Stable.word_22 (instance_7_leaves v) = global_word_1502 v.
Proof. unfold Child1Stable.word_22, global_word_1502, Child1Stable.closed_word_22, global_closed_1502, Child1Stable.expr_word_22, global_expr_1502.
 rewrite instance_7_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1502.
Definition instance_8_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1531 v
| 0, 1 => global_word_1527 v
| 0, 2 => global_word_443 v
| 0, 3 => global_word_448 v
| 0, 4 => global_word_438 v
| 0, 5 => global_word_467 v
| 0, 6 => global_word_432 v
| 10, 5 => global_word_461 v
| 10, 6 => global_word_488 v
| 11, 5 => global_word_481 v
| 11, 6 => global_word_495 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1531.
Lemma instance_8_word_0 v : Child2Stable.word_0 (instance_8_leaves v) = global_word_1531 v.
Proof. unfold Child2Stable.word_0, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1531.
Transparent Child2Stable.word_1 global_word_1527.
Lemma instance_8_word_1 v : Child2Stable.word_1 (instance_8_leaves v) = global_word_1527 v.
Proof. unfold Child2Stable.word_1, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1527.
Transparent Child2Stable.word_2 global_word_443.
Lemma instance_8_word_2 v : Child2Stable.word_2 (instance_8_leaves v) = global_word_443 v.
Proof. unfold Child2Stable.word_2, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_443.
Transparent Child2Stable.word_3 global_word_448.
Lemma instance_8_word_3 v : Child2Stable.word_3 (instance_8_leaves v) = global_word_448 v.
Proof. unfold Child2Stable.word_3, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_448.
Transparent Child2Stable.word_4 global_word_438.
Lemma instance_8_word_4 v : Child2Stable.word_4 (instance_8_leaves v) = global_word_438 v.
Proof. unfold Child2Stable.word_4, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_438.
Transparent Child2Stable.word_5 global_word_467.
Lemma instance_8_word_5 v : Child2Stable.word_5 (instance_8_leaves v) = global_word_467 v.
Proof. unfold Child2Stable.word_5, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_467.
Transparent Child2Stable.word_6 global_word_432.
Lemma instance_8_word_6 v : Child2Stable.word_6 (instance_8_leaves v) = global_word_432 v.
Proof. unfold Child2Stable.word_6, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_432.
Transparent Child2Stable.port_10_5 global_word_461.
Lemma instance_8_port_10_5 v : Child2Stable.port_10_5 (instance_8_leaves v) = global_word_461 v.
Proof. unfold Child2Stable.port_10_5, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_461.
Transparent Child2Stable.port_10_6 global_word_488.
Lemma instance_8_port_10_6 v : Child2Stable.port_10_6 (instance_8_leaves v) = global_word_488 v.
Proof. unfold Child2Stable.port_10_6, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_488.
Transparent Child2Stable.port_11_5 global_word_481.
Lemma instance_8_port_11_5 v : Child2Stable.port_11_5 (instance_8_leaves v) = global_word_481 v.
Proof. unfold Child2Stable.port_11_5, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_481.
Transparent Child2Stable.port_11_6 global_word_495.
Lemma instance_8_port_11_6 v : Child2Stable.port_11_6 (instance_8_leaves v) = global_word_495 v.
Proof. unfold Child2Stable.port_11_6, instance_8_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_495.
Transparent Child2Stable.word_12 global_word_1504.
Lemma instance_8_word_12 v : Child2Stable.word_12 (instance_8_leaves v) = global_word_1504 v.
Proof. unfold Child2Stable.word_12, global_word_1504, Child2Stable.closed_word_12, global_closed_1504, Child2Stable.expr_word_12, global_expr_1504.
 rewrite instance_8_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1504.
Transparent Child2Stable.word_13 global_word_1505.
Lemma instance_8_word_13 v : Child2Stable.word_13 (instance_8_leaves v) = global_word_1505 v.
Proof. unfold Child2Stable.word_13, global_word_1505, Child2Stable.closed_word_13, global_closed_1505, Child2Stable.expr_word_13, global_expr_1505.
 rewrite instance_8_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1505.
Transparent Child2Stable.word_14 global_word_1506.
Lemma instance_8_word_14 v : Child2Stable.word_14 (instance_8_leaves v) = global_word_1506 v.
Proof. unfold Child2Stable.word_14, global_word_1506, Child2Stable.closed_word_14, global_closed_1506, Child2Stable.expr_word_14, global_expr_1506.
 rewrite instance_8_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1506.
Transparent Child2Stable.word_15 global_word_1507.
Lemma instance_8_word_15 v : Child2Stable.word_15 (instance_8_leaves v) = global_word_1507 v.
Proof. unfold Child2Stable.word_15, global_word_1507, Child2Stable.closed_word_15, global_closed_1507, Child2Stable.expr_word_15, global_expr_1507.
 rewrite instance_8_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1507.
Transparent Child2Stable.word_16 global_word_1508.
Lemma instance_8_word_16 v : Child2Stable.word_16 (instance_8_leaves v) = global_word_1508 v.
Proof. unfold Child2Stable.word_16, global_word_1508, Child2Stable.closed_word_16, global_closed_1508, Child2Stable.expr_word_16, global_expr_1508.
 rewrite instance_8_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1508.
Transparent Child2Stable.word_17 global_word_1509.
Lemma instance_8_word_17 v : Child2Stable.word_17 (instance_8_leaves v) = global_word_1509 v.
Proof. unfold Child2Stable.word_17, global_word_1509, Child2Stable.closed_word_17, global_closed_1509, Child2Stable.expr_word_17, global_expr_1509.
 rewrite instance_8_word_12 instance_8_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1509.
Transparent Child2Stable.word_18 global_word_1510.
Lemma instance_8_word_18 v : Child2Stable.word_18 (instance_8_leaves v) = global_word_1510 v.
Proof. unfold Child2Stable.word_18, global_word_1510, Child2Stable.closed_word_18, global_closed_1510, Child2Stable.expr_word_18, global_expr_1510.
 rewrite instance_8_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1510.
Transparent Child2Stable.word_19 global_word_1511.
Lemma instance_8_word_19 v : Child2Stable.word_19 (instance_8_leaves v) = global_word_1511 v.
Proof. unfold Child2Stable.word_19, global_word_1511, Child2Stable.closed_word_19, global_closed_1511, Child2Stable.expr_word_19, global_expr_1511.
 rewrite instance_8_word_14 instance_8_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1511.
Transparent Child2Stable.word_20 global_word_1512.
Lemma instance_8_word_20 v : Child2Stable.word_20 (instance_8_leaves v) = global_word_1512 v.
Proof. unfold Child2Stable.word_20, global_word_1512, Child2Stable.closed_word_20, global_closed_1512, Child2Stable.expr_word_20, global_expr_1512.
 rewrite instance_8_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1512.
Transparent Child2Stable.word_21 global_word_1513.
Lemma instance_8_word_21 v : Child2Stable.word_21 (instance_8_leaves v) = global_word_1513 v.
Proof. unfold Child2Stable.word_21, global_word_1513, Child2Stable.closed_word_21, global_closed_1513, Child2Stable.expr_word_21, global_expr_1513.
 rewrite instance_8_word_15 instance_8_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1513.
Transparent Child2Stable.word_22 global_word_1514.
Lemma instance_8_word_22 v : Child2Stable.word_22 (instance_8_leaves v) = global_word_1514 v.
Proof. unfold Child2Stable.word_22, global_word_1514, Child2Stable.closed_word_22, global_closed_1514, Child2Stable.expr_word_22, global_expr_1514.
 rewrite instance_8_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1514.
Transparent Child2Stable.word_23 global_word_1515.
Lemma instance_8_word_23 v : Child2Stable.word_23 (instance_8_leaves v) = global_word_1515 v.
Proof. unfold Child2Stable.word_23, global_word_1515, Child2Stable.closed_word_23, global_closed_1515, Child2Stable.expr_word_23, global_expr_1515.
 rewrite instance_8_word_16 instance_8_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1515.
Transparent Child2Stable.word_24 global_word_1516.
Lemma instance_8_word_24 v : Child2Stable.word_24 (instance_8_leaves v) = global_word_1516 v.
Proof. unfold Child2Stable.word_24, global_word_1516, Child2Stable.closed_word_24, global_closed_1516, Child2Stable.expr_word_24, global_expr_1516.
 rewrite instance_8_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1516.
Transparent Child2Stable.word_41 global_word_482.
Lemma instance_8_word_41 v : Child2Stable.word_41 (instance_8_leaves v) = global_word_482 v.
Proof. unfold Child2Stable.word_41, global_word_482, Child2Stable.closed_word_41, global_closed_482, Child2Stable.expr_word_41, global_expr_482.
 rewrite instance_8_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_482.
Transparent Child2Stable.word_7 global_word_483.
Lemma instance_8_word_7 v : Child2Stable.word_7 (instance_8_leaves v) = global_word_483 v.
Proof. unfold Child2Stable.word_7, global_word_483, Child2Stable.closed_word_7, global_closed_483, Child2Stable.expr_word_7, global_expr_483.
 rewrite instance_8_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_483.
Transparent Child2Stable.word_25 global_word_1517.
Lemma instance_8_word_25 v : Child2Stable.word_25 (instance_8_leaves v) = global_word_1517 v.
Proof. unfold Child2Stable.word_25, global_word_1517, Child2Stable.closed_word_25, global_closed_1517, Child2Stable.expr_word_25, global_expr_1517.
 rewrite instance_8_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1517.
Transparent Child2Stable.word_42 global_word_489.
Lemma instance_8_word_42 v : Child2Stable.word_42 (instance_8_leaves v) = global_word_489 v.
Proof. unfold Child2Stable.word_42, global_word_489, Child2Stable.closed_word_42, global_closed_489, Child2Stable.expr_word_42, global_expr_489.
 rewrite instance_8_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_489.
Transparent Child2Stable.word_8 global_word_490.
Lemma instance_8_word_8 v : Child2Stable.word_8 (instance_8_leaves v) = global_word_490 v.
Proof. unfold Child2Stable.word_8, global_word_490, Child2Stable.closed_word_8, global_closed_490, Child2Stable.expr_word_8, global_expr_490.
 rewrite instance_8_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_490.
Transparent Child2Stable.word_26 global_word_1518.
Lemma instance_8_word_26 v : Child2Stable.word_26 (instance_8_leaves v) = global_word_1518 v.
Proof. unfold Child2Stable.word_26, global_word_1518, Child2Stable.closed_word_26, global_closed_1518, Child2Stable.expr_word_26, global_expr_1518.
 rewrite instance_8_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1518.
Transparent Child2Stable.word_27 global_word_1519.
Lemma instance_8_word_27 v : Child2Stable.word_27 (instance_8_leaves v) = global_word_1519 v.
Proof. unfold Child2Stable.word_27, global_word_1519, Child2Stable.closed_word_27, global_closed_1519, Child2Stable.expr_word_27, global_expr_1519.
 rewrite instance_8_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1519.
Transparent Child2Stable.word_43 global_word_496.
Lemma instance_8_word_43 v : Child2Stable.word_43 (instance_8_leaves v) = global_word_496 v.
Proof. unfold Child2Stable.word_43, global_word_496, Child2Stable.closed_word_43, global_closed_496, Child2Stable.expr_word_43, global_expr_496.
 rewrite instance_8_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_496.
Transparent Child2Stable.word_9 global_word_497.
Lemma instance_8_word_9 v : Child2Stable.word_9 (instance_8_leaves v) = global_word_497 v.
Proof. unfold Child2Stable.word_9, global_word_497, Child2Stable.closed_word_9, global_closed_497, Child2Stable.expr_word_9, global_expr_497.
 rewrite instance_8_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_497.
Transparent Child2Stable.word_28 global_word_1520.
Lemma instance_8_word_28 v : Child2Stable.word_28 (instance_8_leaves v) = global_word_1520 v.
Proof. unfold Child2Stable.word_28, global_word_1520, Child2Stable.closed_word_28, global_closed_1520, Child2Stable.expr_word_28, global_expr_1520.
 rewrite instance_8_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1520.
Transparent Child2Stable.word_29 global_word_1521.
Lemma instance_8_word_29 v : Child2Stable.word_29 (instance_8_leaves v) = global_word_1521 v.
Proof. unfold Child2Stable.word_29, global_word_1521, Child2Stable.closed_word_29, global_closed_1521, Child2Stable.expr_word_29, global_expr_1521.
 rewrite instance_8_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1521.
Transparent Child2Stable.word_30 global_word_1522.
Lemma instance_8_word_30 v : Child2Stable.word_30 (instance_8_leaves v) = global_word_1522 v.
Proof. unfold Child2Stable.word_30, global_word_1522, Child2Stable.closed_word_30, global_closed_1522, Child2Stable.expr_word_30, global_expr_1522.
 rewrite instance_8_word_25 instance_8_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1522.
Transparent Child2Stable.word_31 global_word_1523.
Lemma instance_8_word_31 v : Child2Stable.word_31 (instance_8_leaves v) = global_word_1523 v.
Proof. unfold Child2Stable.word_31, global_word_1523, Child2Stable.closed_word_31, global_closed_1523, Child2Stable.expr_word_31, global_expr_1523.
 rewrite instance_8_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1523.
Transparent Child2Stable.word_32 global_word_1524.
Lemma instance_8_word_32 v : Child2Stable.word_32 (instance_8_leaves v) = global_word_1524 v.
Proof. unfold Child2Stable.word_32, global_word_1524, Child2Stable.closed_word_32, global_closed_1524, Child2Stable.expr_word_32, global_expr_1524.
 rewrite instance_8_word_29 instance_8_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1524.
Transparent Child2Stable.word_33 global_word_1525.
Lemma instance_8_word_33 v : Child2Stable.word_33 (instance_8_leaves v) = global_word_1525 v.
Proof. unfold Child2Stable.word_33, global_word_1525, Child2Stable.closed_word_33, global_closed_1525, Child2Stable.expr_word_33, global_expr_1525.
 rewrite instance_8_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1525.
Transparent Child2Stable.word_34 global_word_1526.
Lemma instance_8_word_34 v : Child2Stable.word_34 (instance_8_leaves v) = global_word_1526 v.
Proof. unfold Child2Stable.word_34, global_word_1526, Child2Stable.closed_word_34, global_closed_1526, Child2Stable.expr_word_34, global_expr_1526.
 rewrite instance_8_word_24 instance_8_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1526.
Transparent Child2Stable.word_35 global_word_1528.
Lemma instance_8_word_35 v : Child2Stable.word_35 (instance_8_leaves v) = global_word_1528 v.
Proof. unfold Child2Stable.word_35, global_word_1528, Child2Stable.closed_word_35, global_closed_1528, Child2Stable.expr_word_35, global_expr_1528.
 rewrite instance_8_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1528.
Transparent Child2Stable.word_36 global_word_1529.
Lemma instance_8_word_36 v : Child2Stable.word_36 (instance_8_leaves v) = global_word_1529 v.
Proof. unfold Child2Stable.word_36, global_word_1529, Child2Stable.closed_word_36, global_closed_1529, Child2Stable.expr_word_36, global_expr_1529.
 rewrite instance_8_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1529.
Transparent Child2Stable.word_37 global_word_1530.
Lemma instance_8_word_37 v : Child2Stable.word_37 (instance_8_leaves v) = global_word_1530 v.
Proof. unfold Child2Stable.word_37, global_word_1530, Child2Stable.closed_word_37, global_closed_1530, Child2Stable.expr_word_37, global_expr_1530.
 rewrite instance_8_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1530.
Transparent Child2Stable.word_38 global_word_462.
Lemma instance_8_word_38 v : Child2Stable.word_38 (instance_8_leaves v) = global_word_462 v.
Proof. unfold Child2Stable.word_38, global_word_462, Child2Stable.closed_word_38, global_closed_462, Child2Stable.expr_word_38, global_expr_462.
 rewrite instance_8_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_462.
Transparent Child2Stable.word_39 global_word_468.
Lemma instance_8_word_39 v : Child2Stable.word_39 (instance_8_leaves v) = global_word_468 v.
Proof. unfold Child2Stable.word_39, global_word_468, Child2Stable.closed_word_39, global_closed_468, Child2Stable.expr_word_39, global_expr_468.
 rewrite instance_8_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_468.
Transparent Child2Stable.word_40 global_word_433.
Lemma instance_8_word_40 v : Child2Stable.word_40 (instance_8_leaves v) = global_word_433 v.
Proof. unfold Child2Stable.word_40, global_word_433, Child2Stable.closed_word_40, global_closed_433, Child2Stable.expr_word_40, global_expr_433.
 rewrite instance_8_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_433.
Transparent Child2Stable.port_10_0 global_word_1532.
Lemma instance_8_port_10_0 v : Child2Stable.port_10_0 (instance_8_leaves v) = global_word_1532 v.
Proof. unfold Child2Stable.port_10_0, global_word_1532, Child2Stable.closed_port_10_0, global_closed_1532, Child2Stable.expr_port_10_0, global_expr_1532.
 rewrite instance_8_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1532.
Transparent Child2Stable.port_10_1 global_word_1533.
Lemma instance_8_port_10_1 v : Child2Stable.port_10_1 (instance_8_leaves v) = global_word_1533 v.
Proof. unfold Child2Stable.port_10_1, global_word_1533, Child2Stable.closed_port_10_1, global_closed_1533, Child2Stable.expr_port_10_1, global_expr_1533.
 rewrite instance_8_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1533.
Transparent Child2Stable.port_10_2 global_word_444.
Lemma instance_8_port_10_2 v : Child2Stable.port_10_2 (instance_8_leaves v) = global_word_444 v.
Proof. unfold Child2Stable.port_10_2, global_word_444, Child2Stable.closed_port_10_2, global_closed_444, Child2Stable.expr_port_10_2, global_expr_444.
 rewrite instance_8_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_444.
Transparent Child2Stable.port_10_3 global_word_449.
Lemma instance_8_port_10_3 v : Child2Stable.port_10_3 (instance_8_leaves v) = global_word_449 v.
Proof. unfold Child2Stable.port_10_3, global_word_449, Child2Stable.closed_port_10_3, global_closed_449, Child2Stable.expr_port_10_3, global_expr_449.
 rewrite instance_8_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_449.
Transparent Child2Stable.port_10_4 global_word_439.
Lemma instance_8_port_10_4 v : Child2Stable.port_10_4 (instance_8_leaves v) = global_word_439 v.
Proof. unfold Child2Stable.port_10_4, global_word_439, Child2Stable.closed_port_10_4, global_closed_439, Child2Stable.expr_port_10_4, global_expr_439.
 rewrite instance_8_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_439.
Transparent Child2Stable.port_11_0 global_word_1534.
Lemma instance_8_port_11_0 v : Child2Stable.port_11_0 (instance_8_leaves v) = global_word_1534 v.
Proof. unfold Child2Stable.port_11_0, global_word_1534, Child2Stable.closed_port_11_0, global_closed_1534, Child2Stable.expr_port_11_0, global_expr_1534.
 rewrite instance_8_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1534.
Transparent Child2Stable.port_11_1 global_word_1535.
Lemma instance_8_port_11_1 v : Child2Stable.port_11_1 (instance_8_leaves v) = global_word_1535 v.
Proof. unfold Child2Stable.port_11_1, global_word_1535, Child2Stable.closed_port_11_1, global_closed_1535, Child2Stable.expr_port_11_1, global_expr_1535.
 rewrite instance_8_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1535.
Transparent Child2Stable.port_11_2 global_word_463.
Lemma instance_8_port_11_2 v : Child2Stable.port_11_2 (instance_8_leaves v) = global_word_463 v.
Proof. unfold Child2Stable.port_11_2, global_word_463, Child2Stable.closed_port_11_2, global_closed_463, Child2Stable.expr_port_11_2, global_expr_463.
 rewrite instance_8_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_463.
Transparent Child2Stable.port_11_3 global_word_469.
Lemma instance_8_port_11_3 v : Child2Stable.port_11_3 (instance_8_leaves v) = global_word_469 v.
Proof. unfold Child2Stable.port_11_3, global_word_469, Child2Stable.closed_port_11_3, global_closed_469, Child2Stable.expr_port_11_3, global_expr_469.
 rewrite instance_8_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_469.
Transparent Child2Stable.port_11_4 global_word_434.
Lemma instance_8_port_11_4 v : Child2Stable.port_11_4 (instance_8_leaves v) = global_word_434 v.
Proof. unfold Child2Stable.port_11_4, global_word_434, Child2Stable.closed_port_11_4, global_closed_434, Child2Stable.expr_port_11_4, global_expr_434.
 rewrite instance_8_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_434.
Definition instance_9_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1553 v
| 0, 1 => global_word_1549 v
| 0, 2 => global_word_445 v
| 0, 3 => global_word_450 v
| 0, 4 => global_word_440 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1553.
Lemma instance_9_word_0 v : Child1Stable.word_0 (instance_9_leaves v) = global_word_1553 v.
Proof. unfold Child1Stable.word_0, instance_9_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1553.
Transparent Child1Stable.word_1 global_word_1549.
Lemma instance_9_word_1 v : Child1Stable.word_1 (instance_9_leaves v) = global_word_1549 v.
Proof. unfold Child1Stable.word_1, instance_9_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1549.
Transparent Child1Stable.word_2 global_word_445.
Lemma instance_9_word_2 v : Child1Stable.word_2 (instance_9_leaves v) = global_word_445 v.
Proof. unfold Child1Stable.word_2, instance_9_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_445.
Transparent Child1Stable.word_3 global_word_450.
Lemma instance_9_word_3 v : Child1Stable.word_3 (instance_9_leaves v) = global_word_450 v.
Proof. unfold Child1Stable.word_3, instance_9_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_450.
Transparent Child1Stable.word_4 global_word_440.
Lemma instance_9_word_4 v : Child1Stable.word_4 (instance_9_leaves v) = global_word_440 v.
Proof. unfold Child1Stable.word_4, instance_9_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_440.
Transparent Child1Stable.word_7 global_word_1536.
Lemma instance_9_word_7 v : Child1Stable.word_7 (instance_9_leaves v) = global_word_1536 v.
Proof. unfold Child1Stable.word_7, global_word_1536, Child1Stable.closed_word_7, global_closed_1536, Child1Stable.expr_word_7, global_expr_1536.
 rewrite instance_9_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1536.
Transparent Child1Stable.word_8 global_word_1537.
Lemma instance_9_word_8 v : Child1Stable.word_8 (instance_9_leaves v) = global_word_1537 v.
Proof. unfold Child1Stable.word_8, global_word_1537, Child1Stable.closed_word_8, global_closed_1537, Child1Stable.expr_word_8, global_expr_1537.
 rewrite instance_9_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1537.
Transparent Child1Stable.word_9 global_word_1538.
Lemma instance_9_word_9 v : Child1Stable.word_9 (instance_9_leaves v) = global_word_1538 v.
Proof. unfold Child1Stable.word_9, global_word_1538, Child1Stable.closed_word_9, global_closed_1538, Child1Stable.expr_word_9, global_expr_1538.
 rewrite instance_9_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1538.
Transparent Child1Stable.word_10 global_word_1539.
Lemma instance_9_word_10 v : Child1Stable.word_10 (instance_9_leaves v) = global_word_1539 v.
Proof. unfold Child1Stable.word_10, global_word_1539, Child1Stable.closed_word_10, global_closed_1539, Child1Stable.expr_word_10, global_expr_1539.
 rewrite instance_9_word_7 instance_9_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1539.
Transparent Child1Stable.word_11 global_word_1540.
Lemma instance_9_word_11 v : Child1Stable.word_11 (instance_9_leaves v) = global_word_1540 v.
Proof. unfold Child1Stable.word_11, global_word_1540, Child1Stable.closed_word_11, global_closed_1540, Child1Stable.expr_word_11, global_expr_1540.
 rewrite instance_9_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1540.
Transparent Child1Stable.word_12 global_word_1541.
Lemma instance_9_word_12 v : Child1Stable.word_12 (instance_9_leaves v) = global_word_1541 v.
Proof. unfold Child1Stable.word_12, global_word_1541, Child1Stable.closed_word_12, global_closed_1541, Child1Stable.expr_word_12, global_expr_1541.
 rewrite instance_9_word_9 instance_9_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1541.
Transparent Child1Stable.word_13 global_word_1542.
Lemma instance_9_word_13 v : Child1Stable.word_13 (instance_9_leaves v) = global_word_1542 v.
Proof. unfold Child1Stable.word_13, global_word_1542, Child1Stable.closed_word_13, global_closed_1542, Child1Stable.expr_word_13, global_expr_1542.
 rewrite instance_9_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1542.
Transparent Child1Stable.word_25 global_word_441.
Lemma instance_9_word_25 v : Child1Stable.word_25 (instance_9_leaves v) = global_word_441 v.
Proof. unfold Child1Stable.word_25, global_word_441, Child1Stable.closed_word_25, global_closed_441, Child1Stable.expr_word_25, global_expr_441.
 rewrite instance_9_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_441.
Transparent Child1Stable.word_23 global_word_446.
Lemma instance_9_word_23 v : Child1Stable.word_23 (instance_9_leaves v) = global_word_446 v.
Proof. unfold Child1Stable.word_23, global_word_446, Child1Stable.closed_word_23, global_closed_446, Child1Stable.expr_word_23, global_expr_446.
 rewrite instance_9_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_446.
Transparent Child1Stable.word_24 global_word_451.
Lemma instance_9_word_24 v : Child1Stable.word_24 (instance_9_leaves v) = global_word_451 v.
Proof. unfold Child1Stable.word_24, global_word_451, Child1Stable.closed_word_24, global_closed_451, Child1Stable.expr_word_24, global_expr_451.
 rewrite instance_9_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_451.
Transparent Child1Stable.word_26 global_word_452.
Lemma instance_9_word_26 v : Child1Stable.word_26 (instance_9_leaves v) = global_word_452 v.
Proof. unfold Child1Stable.word_26, global_word_452, Child1Stable.closed_word_26, global_closed_452, Child1Stable.expr_word_26, global_expr_452.
 rewrite instance_9_word_23 instance_9_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_452.
Transparent Child1Stable.word_28 global_word_453.
Lemma instance_9_word_28 v : Child1Stable.word_28 (instance_9_leaves v) = global_word_453 v.
Proof. unfold Child1Stable.word_28, global_word_453, Child1Stable.closed_word_28, global_closed_453, Child1Stable.expr_word_28, global_expr_453.
 rewrite instance_9_word_25 instance_9_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_453.
Transparent Child1Stable.word_27 global_word_454.
Lemma instance_9_word_27 v : Child1Stable.word_27 (instance_9_leaves v) = global_word_454 v.
Proof. unfold Child1Stable.word_27, global_word_454, Child1Stable.closed_word_27, global_closed_454, Child1Stable.expr_word_27, global_expr_454.
 rewrite instance_9_word_23 instance_9_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_454.
Transparent Child1Stable.word_29 global_word_455.
Lemma instance_9_word_29 v : Child1Stable.word_29 (instance_9_leaves v) = global_word_455 v.
Proof. unfold Child1Stable.word_29, global_word_455, Child1Stable.closed_word_29, global_closed_455, Child1Stable.expr_word_29, global_expr_455.
 rewrite instance_9_word_25 instance_9_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_455.
Transparent Child1Stable.word_30 global_word_456.
Lemma instance_9_word_30 v : Child1Stable.word_30 (instance_9_leaves v) = global_word_456 v.
Proof. unfold Child1Stable.word_30, global_word_456, Child1Stable.closed_word_30, global_closed_456, Child1Stable.expr_word_30, global_expr_456.
 rewrite instance_9_word_27 instance_9_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_456.
Transparent Child1Stable.word_31 global_word_457.
Lemma instance_9_word_31 v : Child1Stable.word_31 (instance_9_leaves v) = global_word_457 v.
Proof. unfold Child1Stable.word_31, global_word_457, Child1Stable.closed_word_31, global_closed_457, Child1Stable.expr_word_31, global_expr_457.
 rewrite instance_9_word_28 instance_9_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_457.
Transparent Child1Stable.word_32 global_word_458.
Lemma instance_9_word_32 v : Child1Stable.word_32 (instance_9_leaves v) = global_word_458 v.
Proof. unfold Child1Stable.word_32, global_word_458, Child1Stable.closed_word_32, global_closed_458, Child1Stable.expr_word_32, global_expr_458.
 rewrite instance_9_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_458.
Transparent Child1Stable.word_33 global_word_459.
Lemma instance_9_word_33 v : Child1Stable.word_33 (instance_9_leaves v) = global_word_459 v.
Proof. unfold Child1Stable.word_33, global_word_459, Child1Stable.closed_word_33, global_closed_459, Child1Stable.expr_word_33, global_expr_459.
 rewrite instance_9_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_459.
Transparent Child1Stable.word_5 global_word_460.
Lemma instance_9_word_5 v : Child1Stable.word_5 (instance_9_leaves v) = global_word_460 v.
Proof. unfold Child1Stable.word_5, global_word_460, Child1Stable.closed_word_5, global_closed_460, Child1Stable.expr_word_5, global_expr_460.
 rewrite instance_9_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_460.
Transparent Child1Stable.word_14 global_word_1543.
Lemma instance_9_word_14 v : Child1Stable.word_14 (instance_9_leaves v) = global_word_1543 v.
Proof. unfold Child1Stable.word_14, global_word_1543, Child1Stable.closed_word_14, global_closed_1543, Child1Stable.expr_word_14, global_expr_1543.
 rewrite instance_9_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1543.
Transparent Child1Stable.word_34 global_word_486.
Lemma instance_9_word_34 v : Child1Stable.word_34 (instance_9_leaves v) = global_word_486 v.
Proof. unfold Child1Stable.word_34, global_word_486, Child1Stable.closed_word_34, global_closed_486, Child1Stable.expr_word_34, global_expr_486.
 rewrite instance_9_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_486.
Transparent Child1Stable.word_6 global_word_487.
Lemma instance_9_word_6 v : Child1Stable.word_6 (instance_9_leaves v) = global_word_487 v.
Proof. unfold Child1Stable.word_6, global_word_487, Child1Stable.closed_word_6, global_closed_487, Child1Stable.expr_word_6, global_expr_487.
 rewrite instance_9_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_487.
Transparent Child1Stable.word_15 global_word_1544.
Lemma instance_9_word_15 v : Child1Stable.word_15 (instance_9_leaves v) = global_word_1544 v.
Proof. unfold Child1Stable.word_15, global_word_1544, Child1Stable.closed_word_15, global_closed_1544, Child1Stable.expr_word_15, global_expr_1544.
 rewrite instance_9_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1544.
Transparent Child1Stable.word_16 global_word_1545.
Lemma instance_9_word_16 v : Child1Stable.word_16 (instance_9_leaves v) = global_word_1545 v.
Proof. unfold Child1Stable.word_16, global_word_1545, Child1Stable.closed_word_16, global_closed_1545, Child1Stable.expr_word_16, global_expr_1545.
 rewrite instance_9_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1545.
Transparent Child1Stable.word_17 global_word_1546.
Lemma instance_9_word_17 v : Child1Stable.word_17 (instance_9_leaves v) = global_word_1546 v.
Proof. unfold Child1Stable.word_17, global_word_1546, Child1Stable.closed_word_17, global_closed_1546, Child1Stable.expr_word_17, global_expr_1546.
 rewrite instance_9_word_14 instance_9_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1546.
Transparent Child1Stable.word_18 global_word_1547.
Lemma instance_9_word_18 v : Child1Stable.word_18 (instance_9_leaves v) = global_word_1547 v.
Proof. unfold Child1Stable.word_18, global_word_1547, Child1Stable.closed_word_18, global_closed_1547, Child1Stable.expr_word_18, global_expr_1547.
 rewrite instance_9_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1547.
Transparent Child1Stable.word_19 global_word_1548.
Lemma instance_9_word_19 v : Child1Stable.word_19 (instance_9_leaves v) = global_word_1548 v.
Proof. unfold Child1Stable.word_19, global_word_1548, Child1Stable.closed_word_19, global_closed_1548, Child1Stable.expr_word_19, global_expr_1548.
 rewrite instance_9_word_13 instance_9_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1548.
Transparent Child1Stable.word_20 global_word_1550.
Lemma instance_9_word_20 v : Child1Stable.word_20 (instance_9_leaves v) = global_word_1550 v.
Proof. unfold Child1Stable.word_20, global_word_1550, Child1Stable.closed_word_20, global_closed_1550, Child1Stable.expr_word_20, global_expr_1550.
 rewrite instance_9_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1550.
Transparent Child1Stable.word_21 global_word_1551.
Lemma instance_9_word_21 v : Child1Stable.word_21 (instance_9_leaves v) = global_word_1551 v.
Proof. unfold Child1Stable.word_21, global_word_1551, Child1Stable.closed_word_21, global_closed_1551, Child1Stable.expr_word_21, global_expr_1551.
 rewrite instance_9_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1551.
Transparent Child1Stable.word_22 global_word_1552.
Lemma instance_9_word_22 v : Child1Stable.word_22 (instance_9_leaves v) = global_word_1552 v.
Proof. unfold Child1Stable.word_22, global_word_1552, Child1Stable.closed_word_22, global_closed_1552, Child1Stable.expr_word_22, global_expr_1552.
 rewrite instance_9_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1552.
Definition instance_10_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1571 v
| 0, 1 => global_word_1567 v
| 0, 2 => global_word_464 v
| 0, 3 => global_word_470 v
| 0, 4 => global_word_435 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1571.
Lemma instance_10_word_0 v : Child1Stable.word_0 (instance_10_leaves v) = global_word_1571 v.
Proof. unfold Child1Stable.word_0, instance_10_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1571.
Transparent Child1Stable.word_1 global_word_1567.
Lemma instance_10_word_1 v : Child1Stable.word_1 (instance_10_leaves v) = global_word_1567 v.
Proof. unfold Child1Stable.word_1, instance_10_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1567.
Transparent Child1Stable.word_2 global_word_464.
Lemma instance_10_word_2 v : Child1Stable.word_2 (instance_10_leaves v) = global_word_464 v.
Proof. unfold Child1Stable.word_2, instance_10_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_464.
Transparent Child1Stable.word_3 global_word_470.
Lemma instance_10_word_3 v : Child1Stable.word_3 (instance_10_leaves v) = global_word_470 v.
Proof. unfold Child1Stable.word_3, instance_10_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_470.
Transparent Child1Stable.word_4 global_word_435.
Lemma instance_10_word_4 v : Child1Stable.word_4 (instance_10_leaves v) = global_word_435 v.
Proof. unfold Child1Stable.word_4, instance_10_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_435.
Transparent Child1Stable.word_7 global_word_1554.
Lemma instance_10_word_7 v : Child1Stable.word_7 (instance_10_leaves v) = global_word_1554 v.
Proof. unfold Child1Stable.word_7, global_word_1554, Child1Stable.closed_word_7, global_closed_1554, Child1Stable.expr_word_7, global_expr_1554.
 rewrite instance_10_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1554.
Transparent Child1Stable.word_8 global_word_1555.
Lemma instance_10_word_8 v : Child1Stable.word_8 (instance_10_leaves v) = global_word_1555 v.
Proof. unfold Child1Stable.word_8, global_word_1555, Child1Stable.closed_word_8, global_closed_1555, Child1Stable.expr_word_8, global_expr_1555.
 rewrite instance_10_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1555.
Transparent Child1Stable.word_9 global_word_1556.
Lemma instance_10_word_9 v : Child1Stable.word_9 (instance_10_leaves v) = global_word_1556 v.
Proof. unfold Child1Stable.word_9, global_word_1556, Child1Stable.closed_word_9, global_closed_1556, Child1Stable.expr_word_9, global_expr_1556.
 rewrite instance_10_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1556.
Transparent Child1Stable.word_10 global_word_1557.
Lemma instance_10_word_10 v : Child1Stable.word_10 (instance_10_leaves v) = global_word_1557 v.
Proof. unfold Child1Stable.word_10, global_word_1557, Child1Stable.closed_word_10, global_closed_1557, Child1Stable.expr_word_10, global_expr_1557.
 rewrite instance_10_word_7 instance_10_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1557.
Transparent Child1Stable.word_11 global_word_1558.
Lemma instance_10_word_11 v : Child1Stable.word_11 (instance_10_leaves v) = global_word_1558 v.
Proof. unfold Child1Stable.word_11, global_word_1558, Child1Stable.closed_word_11, global_closed_1558, Child1Stable.expr_word_11, global_expr_1558.
 rewrite instance_10_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1558.
Transparent Child1Stable.word_12 global_word_1559.
Lemma instance_10_word_12 v : Child1Stable.word_12 (instance_10_leaves v) = global_word_1559 v.
Proof. unfold Child1Stable.word_12, global_word_1559, Child1Stable.closed_word_12, global_closed_1559, Child1Stable.expr_word_12, global_expr_1559.
 rewrite instance_10_word_9 instance_10_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1559.
Transparent Child1Stable.word_13 global_word_1560.
Lemma instance_10_word_13 v : Child1Stable.word_13 (instance_10_leaves v) = global_word_1560 v.
Proof. unfold Child1Stable.word_13, global_word_1560, Child1Stable.closed_word_13, global_closed_1560, Child1Stable.expr_word_13, global_expr_1560.
 rewrite instance_10_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1560.
Transparent Child1Stable.word_25 global_word_436.
Lemma instance_10_word_25 v : Child1Stable.word_25 (instance_10_leaves v) = global_word_436 v.
Proof. unfold Child1Stable.word_25, global_word_436, Child1Stable.closed_word_25, global_closed_436, Child1Stable.expr_word_25, global_expr_436.
 rewrite instance_10_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_436.
Transparent Child1Stable.word_23 global_word_465.
Lemma instance_10_word_23 v : Child1Stable.word_23 (instance_10_leaves v) = global_word_465 v.
Proof. unfold Child1Stable.word_23, global_word_465, Child1Stable.closed_word_23, global_closed_465, Child1Stable.expr_word_23, global_expr_465.
 rewrite instance_10_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_465.
Transparent Child1Stable.word_24 global_word_471.
Lemma instance_10_word_24 v : Child1Stable.word_24 (instance_10_leaves v) = global_word_471 v.
Proof. unfold Child1Stable.word_24, global_word_471, Child1Stable.closed_word_24, global_closed_471, Child1Stable.expr_word_24, global_expr_471.
 rewrite instance_10_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_471.
Transparent Child1Stable.word_26 global_word_472.
Lemma instance_10_word_26 v : Child1Stable.word_26 (instance_10_leaves v) = global_word_472 v.
Proof. unfold Child1Stable.word_26, global_word_472, Child1Stable.closed_word_26, global_closed_472, Child1Stable.expr_word_26, global_expr_472.
 rewrite instance_10_word_23 instance_10_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_472.
Transparent Child1Stable.word_28 global_word_473.
Lemma instance_10_word_28 v : Child1Stable.word_28 (instance_10_leaves v) = global_word_473 v.
Proof. unfold Child1Stable.word_28, global_word_473, Child1Stable.closed_word_28, global_closed_473, Child1Stable.expr_word_28, global_expr_473.
 rewrite instance_10_word_25 instance_10_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_473.
Transparent Child1Stable.word_27 global_word_474.
Lemma instance_10_word_27 v : Child1Stable.word_27 (instance_10_leaves v) = global_word_474 v.
Proof. unfold Child1Stable.word_27, global_word_474, Child1Stable.closed_word_27, global_closed_474, Child1Stable.expr_word_27, global_expr_474.
 rewrite instance_10_word_23 instance_10_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_474.
Transparent Child1Stable.word_29 global_word_475.
Lemma instance_10_word_29 v : Child1Stable.word_29 (instance_10_leaves v) = global_word_475 v.
Proof. unfold Child1Stable.word_29, global_word_475, Child1Stable.closed_word_29, global_closed_475, Child1Stable.expr_word_29, global_expr_475.
 rewrite instance_10_word_25 instance_10_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_475.
Transparent Child1Stable.word_30 global_word_476.
Lemma instance_10_word_30 v : Child1Stable.word_30 (instance_10_leaves v) = global_word_476 v.
Proof. unfold Child1Stable.word_30, global_word_476, Child1Stable.closed_word_30, global_closed_476, Child1Stable.expr_word_30, global_expr_476.
 rewrite instance_10_word_27 instance_10_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_476.
Transparent Child1Stable.word_31 global_word_477.
Lemma instance_10_word_31 v : Child1Stable.word_31 (instance_10_leaves v) = global_word_477 v.
Proof. unfold Child1Stable.word_31, global_word_477, Child1Stable.closed_word_31, global_closed_477, Child1Stable.expr_word_31, global_expr_477.
 rewrite instance_10_word_28 instance_10_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_477.
Transparent Child1Stable.word_32 global_word_478.
Lemma instance_10_word_32 v : Child1Stable.word_32 (instance_10_leaves v) = global_word_478 v.
Proof. unfold Child1Stable.word_32, global_word_478, Child1Stable.closed_word_32, global_closed_478, Child1Stable.expr_word_32, global_expr_478.
 rewrite instance_10_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_478.
Transparent Child1Stable.word_33 global_word_479.
Lemma instance_10_word_33 v : Child1Stable.word_33 (instance_10_leaves v) = global_word_479 v.
Proof. unfold Child1Stable.word_33, global_word_479, Child1Stable.closed_word_33, global_closed_479, Child1Stable.expr_word_33, global_expr_479.
 rewrite instance_10_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_479.
Transparent Child1Stable.word_5 global_word_480.
Lemma instance_10_word_5 v : Child1Stable.word_5 (instance_10_leaves v) = global_word_480 v.
Proof. unfold Child1Stable.word_5, global_word_480, Child1Stable.closed_word_5, global_closed_480, Child1Stable.expr_word_5, global_expr_480.
 rewrite instance_10_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_480.
Transparent Child1Stable.word_14 global_word_1561.
Lemma instance_10_word_14 v : Child1Stable.word_14 (instance_10_leaves v) = global_word_1561 v.
Proof. unfold Child1Stable.word_14, global_word_1561, Child1Stable.closed_word_14, global_closed_1561, Child1Stable.expr_word_14, global_expr_1561.
 rewrite instance_10_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1561.
Transparent Child1Stable.word_34 global_word_493.
Lemma instance_10_word_34 v : Child1Stable.word_34 (instance_10_leaves v) = global_word_493 v.
Proof. unfold Child1Stable.word_34, global_word_493, Child1Stable.closed_word_34, global_closed_493, Child1Stable.expr_word_34, global_expr_493.
 rewrite instance_10_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_493.
Transparent Child1Stable.word_6 global_word_494.
Lemma instance_10_word_6 v : Child1Stable.word_6 (instance_10_leaves v) = global_word_494 v.
Proof. unfold Child1Stable.word_6, global_word_494, Child1Stable.closed_word_6, global_closed_494, Child1Stable.expr_word_6, global_expr_494.
 rewrite instance_10_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_494.
Transparent Child1Stable.word_15 global_word_1562.
Lemma instance_10_word_15 v : Child1Stable.word_15 (instance_10_leaves v) = global_word_1562 v.
Proof. unfold Child1Stable.word_15, global_word_1562, Child1Stable.closed_word_15, global_closed_1562, Child1Stable.expr_word_15, global_expr_1562.
 rewrite instance_10_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1562.
Transparent Child1Stable.word_16 global_word_1563.
Lemma instance_10_word_16 v : Child1Stable.word_16 (instance_10_leaves v) = global_word_1563 v.
Proof. unfold Child1Stable.word_16, global_word_1563, Child1Stable.closed_word_16, global_closed_1563, Child1Stable.expr_word_16, global_expr_1563.
 rewrite instance_10_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1563.
Transparent Child1Stable.word_17 global_word_1564.
Lemma instance_10_word_17 v : Child1Stable.word_17 (instance_10_leaves v) = global_word_1564 v.
Proof. unfold Child1Stable.word_17, global_word_1564, Child1Stable.closed_word_17, global_closed_1564, Child1Stable.expr_word_17, global_expr_1564.
 rewrite instance_10_word_14 instance_10_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1564.
Transparent Child1Stable.word_18 global_word_1565.
Lemma instance_10_word_18 v : Child1Stable.word_18 (instance_10_leaves v) = global_word_1565 v.
Proof. unfold Child1Stable.word_18, global_word_1565, Child1Stable.closed_word_18, global_closed_1565, Child1Stable.expr_word_18, global_expr_1565.
 rewrite instance_10_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1565.
Transparent Child1Stable.word_19 global_word_1566.
Lemma instance_10_word_19 v : Child1Stable.word_19 (instance_10_leaves v) = global_word_1566 v.
Proof. unfold Child1Stable.word_19, global_word_1566, Child1Stable.closed_word_19, global_closed_1566, Child1Stable.expr_word_19, global_expr_1566.
 rewrite instance_10_word_13 instance_10_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1566.
Transparent Child1Stable.word_20 global_word_1568.
Lemma instance_10_word_20 v : Child1Stable.word_20 (instance_10_leaves v) = global_word_1568 v.
Proof. unfold Child1Stable.word_20, global_word_1568, Child1Stable.closed_word_20, global_closed_1568, Child1Stable.expr_word_20, global_expr_1568.
 rewrite instance_10_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1568.
Transparent Child1Stable.word_21 global_word_1569.
Lemma instance_10_word_21 v : Child1Stable.word_21 (instance_10_leaves v) = global_word_1569 v.
Proof. unfold Child1Stable.word_21, global_word_1569, Child1Stable.closed_word_21, global_closed_1569, Child1Stable.expr_word_21, global_expr_1569.
 rewrite instance_10_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1569.
Transparent Child1Stable.word_22 global_word_1570.
Lemma instance_10_word_22 v : Child1Stable.word_22 (instance_10_leaves v) = global_word_1570 v.
Proof. unfold Child1Stable.word_22, global_word_1570, Child1Stable.closed_word_22, global_closed_1570, Child1Stable.expr_word_22, global_expr_1570.
 rewrite instance_10_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1570.
Definition instance_11_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1599 v
| 0, 1 => global_word_1595 v
| 0, 2 => global_word_512 v
| 0, 3 => global_word_517 v
| 0, 4 => global_word_507 v
| 0, 5 => global_word_536 v
| 0, 6 => global_word_501 v
| 10, 5 => global_word_530 v
| 10, 6 => global_word_557 v
| 11, 5 => global_word_550 v
| 11, 6 => global_word_564 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1599.
Lemma instance_11_word_0 v : Child2Stable.word_0 (instance_11_leaves v) = global_word_1599 v.
Proof. unfold Child2Stable.word_0, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1599.
Transparent Child2Stable.word_1 global_word_1595.
Lemma instance_11_word_1 v : Child2Stable.word_1 (instance_11_leaves v) = global_word_1595 v.
Proof. unfold Child2Stable.word_1, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1595.
Transparent Child2Stable.word_2 global_word_512.
Lemma instance_11_word_2 v : Child2Stable.word_2 (instance_11_leaves v) = global_word_512 v.
Proof. unfold Child2Stable.word_2, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_512.
Transparent Child2Stable.word_3 global_word_517.
Lemma instance_11_word_3 v : Child2Stable.word_3 (instance_11_leaves v) = global_word_517 v.
Proof. unfold Child2Stable.word_3, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_517.
Transparent Child2Stable.word_4 global_word_507.
Lemma instance_11_word_4 v : Child2Stable.word_4 (instance_11_leaves v) = global_word_507 v.
Proof. unfold Child2Stable.word_4, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_507.
Transparent Child2Stable.word_5 global_word_536.
Lemma instance_11_word_5 v : Child2Stable.word_5 (instance_11_leaves v) = global_word_536 v.
Proof. unfold Child2Stable.word_5, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_536.
Transparent Child2Stable.word_6 global_word_501.
Lemma instance_11_word_6 v : Child2Stable.word_6 (instance_11_leaves v) = global_word_501 v.
Proof. unfold Child2Stable.word_6, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_501.
Transparent Child2Stable.port_10_5 global_word_530.
Lemma instance_11_port_10_5 v : Child2Stable.port_10_5 (instance_11_leaves v) = global_word_530 v.
Proof. unfold Child2Stable.port_10_5, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_530.
Transparent Child2Stable.port_10_6 global_word_557.
Lemma instance_11_port_10_6 v : Child2Stable.port_10_6 (instance_11_leaves v) = global_word_557 v.
Proof. unfold Child2Stable.port_10_6, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_557.
Transparent Child2Stable.port_11_5 global_word_550.
Lemma instance_11_port_11_5 v : Child2Stable.port_11_5 (instance_11_leaves v) = global_word_550 v.
Proof. unfold Child2Stable.port_11_5, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_550.
Transparent Child2Stable.port_11_6 global_word_564.
Lemma instance_11_port_11_6 v : Child2Stable.port_11_6 (instance_11_leaves v) = global_word_564 v.
Proof. unfold Child2Stable.port_11_6, instance_11_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_564.
Transparent Child2Stable.word_12 global_word_1572.
Lemma instance_11_word_12 v : Child2Stable.word_12 (instance_11_leaves v) = global_word_1572 v.
Proof. unfold Child2Stable.word_12, global_word_1572, Child2Stable.closed_word_12, global_closed_1572, Child2Stable.expr_word_12, global_expr_1572.
 rewrite instance_11_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1572.
Transparent Child2Stable.word_13 global_word_1573.
Lemma instance_11_word_13 v : Child2Stable.word_13 (instance_11_leaves v) = global_word_1573 v.
Proof. unfold Child2Stable.word_13, global_word_1573, Child2Stable.closed_word_13, global_closed_1573, Child2Stable.expr_word_13, global_expr_1573.
 rewrite instance_11_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1573.
Transparent Child2Stable.word_14 global_word_1574.
Lemma instance_11_word_14 v : Child2Stable.word_14 (instance_11_leaves v) = global_word_1574 v.
Proof. unfold Child2Stable.word_14, global_word_1574, Child2Stable.closed_word_14, global_closed_1574, Child2Stable.expr_word_14, global_expr_1574.
 rewrite instance_11_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1574.
Transparent Child2Stable.word_15 global_word_1575.
Lemma instance_11_word_15 v : Child2Stable.word_15 (instance_11_leaves v) = global_word_1575 v.
Proof. unfold Child2Stable.word_15, global_word_1575, Child2Stable.closed_word_15, global_closed_1575, Child2Stable.expr_word_15, global_expr_1575.
 rewrite instance_11_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1575.
Transparent Child2Stable.word_16 global_word_1576.
Lemma instance_11_word_16 v : Child2Stable.word_16 (instance_11_leaves v) = global_word_1576 v.
Proof. unfold Child2Stable.word_16, global_word_1576, Child2Stable.closed_word_16, global_closed_1576, Child2Stable.expr_word_16, global_expr_1576.
 rewrite instance_11_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1576.
Transparent Child2Stable.word_17 global_word_1577.
Lemma instance_11_word_17 v : Child2Stable.word_17 (instance_11_leaves v) = global_word_1577 v.
Proof. unfold Child2Stable.word_17, global_word_1577, Child2Stable.closed_word_17, global_closed_1577, Child2Stable.expr_word_17, global_expr_1577.
 rewrite instance_11_word_12 instance_11_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1577.
Transparent Child2Stable.word_18 global_word_1578.
Lemma instance_11_word_18 v : Child2Stable.word_18 (instance_11_leaves v) = global_word_1578 v.
Proof. unfold Child2Stable.word_18, global_word_1578, Child2Stable.closed_word_18, global_closed_1578, Child2Stable.expr_word_18, global_expr_1578.
 rewrite instance_11_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1578.
Transparent Child2Stable.word_19 global_word_1579.
Lemma instance_11_word_19 v : Child2Stable.word_19 (instance_11_leaves v) = global_word_1579 v.
Proof. unfold Child2Stable.word_19, global_word_1579, Child2Stable.closed_word_19, global_closed_1579, Child2Stable.expr_word_19, global_expr_1579.
 rewrite instance_11_word_14 instance_11_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1579.
Transparent Child2Stable.word_20 global_word_1580.
Lemma instance_11_word_20 v : Child2Stable.word_20 (instance_11_leaves v) = global_word_1580 v.
Proof. unfold Child2Stable.word_20, global_word_1580, Child2Stable.closed_word_20, global_closed_1580, Child2Stable.expr_word_20, global_expr_1580.
 rewrite instance_11_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1580.
Transparent Child2Stable.word_21 global_word_1581.
Lemma instance_11_word_21 v : Child2Stable.word_21 (instance_11_leaves v) = global_word_1581 v.
Proof. unfold Child2Stable.word_21, global_word_1581, Child2Stable.closed_word_21, global_closed_1581, Child2Stable.expr_word_21, global_expr_1581.
 rewrite instance_11_word_15 instance_11_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1581.
Transparent Child2Stable.word_22 global_word_1582.
Lemma instance_11_word_22 v : Child2Stable.word_22 (instance_11_leaves v) = global_word_1582 v.
Proof. unfold Child2Stable.word_22, global_word_1582, Child2Stable.closed_word_22, global_closed_1582, Child2Stable.expr_word_22, global_expr_1582.
 rewrite instance_11_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1582.
Transparent Child2Stable.word_23 global_word_1583.
Lemma instance_11_word_23 v : Child2Stable.word_23 (instance_11_leaves v) = global_word_1583 v.
Proof. unfold Child2Stable.word_23, global_word_1583, Child2Stable.closed_word_23, global_closed_1583, Child2Stable.expr_word_23, global_expr_1583.
 rewrite instance_11_word_16 instance_11_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1583.
Transparent Child2Stable.word_24 global_word_1584.
Lemma instance_11_word_24 v : Child2Stable.word_24 (instance_11_leaves v) = global_word_1584 v.
Proof. unfold Child2Stable.word_24, global_word_1584, Child2Stable.closed_word_24, global_closed_1584, Child2Stable.expr_word_24, global_expr_1584.
 rewrite instance_11_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1584.
Transparent Child2Stable.word_41 global_word_551.
Lemma instance_11_word_41 v : Child2Stable.word_41 (instance_11_leaves v) = global_word_551 v.
Proof. unfold Child2Stable.word_41, global_word_551, Child2Stable.closed_word_41, global_closed_551, Child2Stable.expr_word_41, global_expr_551.
 rewrite instance_11_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_551.
Transparent Child2Stable.word_7 global_word_552.
Lemma instance_11_word_7 v : Child2Stable.word_7 (instance_11_leaves v) = global_word_552 v.
Proof. unfold Child2Stable.word_7, global_word_552, Child2Stable.closed_word_7, global_closed_552, Child2Stable.expr_word_7, global_expr_552.
 rewrite instance_11_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_552.
Transparent Child2Stable.word_25 global_word_1585.
Lemma instance_11_word_25 v : Child2Stable.word_25 (instance_11_leaves v) = global_word_1585 v.
Proof. unfold Child2Stable.word_25, global_word_1585, Child2Stable.closed_word_25, global_closed_1585, Child2Stable.expr_word_25, global_expr_1585.
 rewrite instance_11_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1585.
Transparent Child2Stable.word_42 global_word_558.
Lemma instance_11_word_42 v : Child2Stable.word_42 (instance_11_leaves v) = global_word_558 v.
Proof. unfold Child2Stable.word_42, global_word_558, Child2Stable.closed_word_42, global_closed_558, Child2Stable.expr_word_42, global_expr_558.
 rewrite instance_11_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_558.
Transparent Child2Stable.word_8 global_word_559.
Lemma instance_11_word_8 v : Child2Stable.word_8 (instance_11_leaves v) = global_word_559 v.
Proof. unfold Child2Stable.word_8, global_word_559, Child2Stable.closed_word_8, global_closed_559, Child2Stable.expr_word_8, global_expr_559.
 rewrite instance_11_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_559.
Transparent Child2Stable.word_26 global_word_1586.
Lemma instance_11_word_26 v : Child2Stable.word_26 (instance_11_leaves v) = global_word_1586 v.
Proof. unfold Child2Stable.word_26, global_word_1586, Child2Stable.closed_word_26, global_closed_1586, Child2Stable.expr_word_26, global_expr_1586.
 rewrite instance_11_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1586.
Transparent Child2Stable.word_27 global_word_1587.
Lemma instance_11_word_27 v : Child2Stable.word_27 (instance_11_leaves v) = global_word_1587 v.
Proof. unfold Child2Stable.word_27, global_word_1587, Child2Stable.closed_word_27, global_closed_1587, Child2Stable.expr_word_27, global_expr_1587.
 rewrite instance_11_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1587.
Transparent Child2Stable.word_43 global_word_565.
Lemma instance_11_word_43 v : Child2Stable.word_43 (instance_11_leaves v) = global_word_565 v.
Proof. unfold Child2Stable.word_43, global_word_565, Child2Stable.closed_word_43, global_closed_565, Child2Stable.expr_word_43, global_expr_565.
 rewrite instance_11_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_565.
Transparent Child2Stable.word_9 global_word_566.
Lemma instance_11_word_9 v : Child2Stable.word_9 (instance_11_leaves v) = global_word_566 v.
Proof. unfold Child2Stable.word_9, global_word_566, Child2Stable.closed_word_9, global_closed_566, Child2Stable.expr_word_9, global_expr_566.
 rewrite instance_11_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_566.
Transparent Child2Stable.word_28 global_word_1588.
Lemma instance_11_word_28 v : Child2Stable.word_28 (instance_11_leaves v) = global_word_1588 v.
Proof. unfold Child2Stable.word_28, global_word_1588, Child2Stable.closed_word_28, global_closed_1588, Child2Stable.expr_word_28, global_expr_1588.
 rewrite instance_11_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1588.
Transparent Child2Stable.word_29 global_word_1589.
Lemma instance_11_word_29 v : Child2Stable.word_29 (instance_11_leaves v) = global_word_1589 v.
Proof. unfold Child2Stable.word_29, global_word_1589, Child2Stable.closed_word_29, global_closed_1589, Child2Stable.expr_word_29, global_expr_1589.
 rewrite instance_11_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1589.
Transparent Child2Stable.word_30 global_word_1590.
Lemma instance_11_word_30 v : Child2Stable.word_30 (instance_11_leaves v) = global_word_1590 v.
Proof. unfold Child2Stable.word_30, global_word_1590, Child2Stable.closed_word_30, global_closed_1590, Child2Stable.expr_word_30, global_expr_1590.
 rewrite instance_11_word_25 instance_11_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1590.
Transparent Child2Stable.word_31 global_word_1591.
Lemma instance_11_word_31 v : Child2Stable.word_31 (instance_11_leaves v) = global_word_1591 v.
Proof. unfold Child2Stable.word_31, global_word_1591, Child2Stable.closed_word_31, global_closed_1591, Child2Stable.expr_word_31, global_expr_1591.
 rewrite instance_11_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1591.
Transparent Child2Stable.word_32 global_word_1592.
Lemma instance_11_word_32 v : Child2Stable.word_32 (instance_11_leaves v) = global_word_1592 v.
Proof. unfold Child2Stable.word_32, global_word_1592, Child2Stable.closed_word_32, global_closed_1592, Child2Stable.expr_word_32, global_expr_1592.
 rewrite instance_11_word_29 instance_11_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1592.
Transparent Child2Stable.word_33 global_word_1593.
Lemma instance_11_word_33 v : Child2Stable.word_33 (instance_11_leaves v) = global_word_1593 v.
Proof. unfold Child2Stable.word_33, global_word_1593, Child2Stable.closed_word_33, global_closed_1593, Child2Stable.expr_word_33, global_expr_1593.
 rewrite instance_11_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1593.
Transparent Child2Stable.word_34 global_word_1594.
Lemma instance_11_word_34 v : Child2Stable.word_34 (instance_11_leaves v) = global_word_1594 v.
Proof. unfold Child2Stable.word_34, global_word_1594, Child2Stable.closed_word_34, global_closed_1594, Child2Stable.expr_word_34, global_expr_1594.
 rewrite instance_11_word_24 instance_11_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1594.
Transparent Child2Stable.word_35 global_word_1596.
Lemma instance_11_word_35 v : Child2Stable.word_35 (instance_11_leaves v) = global_word_1596 v.
Proof. unfold Child2Stable.word_35, global_word_1596, Child2Stable.closed_word_35, global_closed_1596, Child2Stable.expr_word_35, global_expr_1596.
 rewrite instance_11_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1596.
Transparent Child2Stable.word_36 global_word_1597.
Lemma instance_11_word_36 v : Child2Stable.word_36 (instance_11_leaves v) = global_word_1597 v.
Proof. unfold Child2Stable.word_36, global_word_1597, Child2Stable.closed_word_36, global_closed_1597, Child2Stable.expr_word_36, global_expr_1597.
 rewrite instance_11_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1597.
Transparent Child2Stable.word_37 global_word_1598.
Lemma instance_11_word_37 v : Child2Stable.word_37 (instance_11_leaves v) = global_word_1598 v.
Proof. unfold Child2Stable.word_37, global_word_1598, Child2Stable.closed_word_37, global_closed_1598, Child2Stable.expr_word_37, global_expr_1598.
 rewrite instance_11_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1598.
Transparent Child2Stable.word_38 global_word_531.
Lemma instance_11_word_38 v : Child2Stable.word_38 (instance_11_leaves v) = global_word_531 v.
Proof. unfold Child2Stable.word_38, global_word_531, Child2Stable.closed_word_38, global_closed_531, Child2Stable.expr_word_38, global_expr_531.
 rewrite instance_11_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_531.
Transparent Child2Stable.word_39 global_word_537.
Lemma instance_11_word_39 v : Child2Stable.word_39 (instance_11_leaves v) = global_word_537 v.
Proof. unfold Child2Stable.word_39, global_word_537, Child2Stable.closed_word_39, global_closed_537, Child2Stable.expr_word_39, global_expr_537.
 rewrite instance_11_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_537.
Transparent Child2Stable.word_40 global_word_502.
Lemma instance_11_word_40 v : Child2Stable.word_40 (instance_11_leaves v) = global_word_502 v.
Proof. unfold Child2Stable.word_40, global_word_502, Child2Stable.closed_word_40, global_closed_502, Child2Stable.expr_word_40, global_expr_502.
 rewrite instance_11_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_502.
Transparent Child2Stable.port_10_0 global_word_1600.
Lemma instance_11_port_10_0 v : Child2Stable.port_10_0 (instance_11_leaves v) = global_word_1600 v.
Proof. unfold Child2Stable.port_10_0, global_word_1600, Child2Stable.closed_port_10_0, global_closed_1600, Child2Stable.expr_port_10_0, global_expr_1600.
 rewrite instance_11_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1600.
Transparent Child2Stable.port_10_1 global_word_1601.
Lemma instance_11_port_10_1 v : Child2Stable.port_10_1 (instance_11_leaves v) = global_word_1601 v.
Proof. unfold Child2Stable.port_10_1, global_word_1601, Child2Stable.closed_port_10_1, global_closed_1601, Child2Stable.expr_port_10_1, global_expr_1601.
 rewrite instance_11_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1601.
Transparent Child2Stable.port_10_2 global_word_513.
Lemma instance_11_port_10_2 v : Child2Stable.port_10_2 (instance_11_leaves v) = global_word_513 v.
Proof. unfold Child2Stable.port_10_2, global_word_513, Child2Stable.closed_port_10_2, global_closed_513, Child2Stable.expr_port_10_2, global_expr_513.
 rewrite instance_11_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_513.
Transparent Child2Stable.port_10_3 global_word_518.
Lemma instance_11_port_10_3 v : Child2Stable.port_10_3 (instance_11_leaves v) = global_word_518 v.
Proof. unfold Child2Stable.port_10_3, global_word_518, Child2Stable.closed_port_10_3, global_closed_518, Child2Stable.expr_port_10_3, global_expr_518.
 rewrite instance_11_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_518.
Transparent Child2Stable.port_10_4 global_word_508.
Lemma instance_11_port_10_4 v : Child2Stable.port_10_4 (instance_11_leaves v) = global_word_508 v.
Proof. unfold Child2Stable.port_10_4, global_word_508, Child2Stable.closed_port_10_4, global_closed_508, Child2Stable.expr_port_10_4, global_expr_508.
 rewrite instance_11_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_508.
Transparent Child2Stable.port_11_0 global_word_1602.
Lemma instance_11_port_11_0 v : Child2Stable.port_11_0 (instance_11_leaves v) = global_word_1602 v.
Proof. unfold Child2Stable.port_11_0, global_word_1602, Child2Stable.closed_port_11_0, global_closed_1602, Child2Stable.expr_port_11_0, global_expr_1602.
 rewrite instance_11_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1602.
Transparent Child2Stable.port_11_1 global_word_1603.
Lemma instance_11_port_11_1 v : Child2Stable.port_11_1 (instance_11_leaves v) = global_word_1603 v.
Proof. unfold Child2Stable.port_11_1, global_word_1603, Child2Stable.closed_port_11_1, global_closed_1603, Child2Stable.expr_port_11_1, global_expr_1603.
 rewrite instance_11_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1603.
Transparent Child2Stable.port_11_2 global_word_532.
Lemma instance_11_port_11_2 v : Child2Stable.port_11_2 (instance_11_leaves v) = global_word_532 v.
Proof. unfold Child2Stable.port_11_2, global_word_532, Child2Stable.closed_port_11_2, global_closed_532, Child2Stable.expr_port_11_2, global_expr_532.
 rewrite instance_11_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_532.
Transparent Child2Stable.port_11_3 global_word_538.
Lemma instance_11_port_11_3 v : Child2Stable.port_11_3 (instance_11_leaves v) = global_word_538 v.
Proof. unfold Child2Stable.port_11_3, global_word_538, Child2Stable.closed_port_11_3, global_closed_538, Child2Stable.expr_port_11_3, global_expr_538.
 rewrite instance_11_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_538.
Transparent Child2Stable.port_11_4 global_word_503.
Lemma instance_11_port_11_4 v : Child2Stable.port_11_4 (instance_11_leaves v) = global_word_503 v.
Proof. unfold Child2Stable.port_11_4, global_word_503, Child2Stable.closed_port_11_4, global_closed_503, Child2Stable.expr_port_11_4, global_expr_503.
 rewrite instance_11_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_503.
Definition instance_12_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1621 v
| 0, 1 => global_word_1617 v
| 0, 2 => global_word_514 v
| 0, 3 => global_word_519 v
| 0, 4 => global_word_509 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1621.
Lemma instance_12_word_0 v : Child1Stable.word_0 (instance_12_leaves v) = global_word_1621 v.
Proof. unfold Child1Stable.word_0, instance_12_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1621.
Transparent Child1Stable.word_1 global_word_1617.
Lemma instance_12_word_1 v : Child1Stable.word_1 (instance_12_leaves v) = global_word_1617 v.
Proof. unfold Child1Stable.word_1, instance_12_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1617.
Transparent Child1Stable.word_2 global_word_514.
Lemma instance_12_word_2 v : Child1Stable.word_2 (instance_12_leaves v) = global_word_514 v.
Proof. unfold Child1Stable.word_2, instance_12_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_514.
Transparent Child1Stable.word_3 global_word_519.
Lemma instance_12_word_3 v : Child1Stable.word_3 (instance_12_leaves v) = global_word_519 v.
Proof. unfold Child1Stable.word_3, instance_12_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_519.
Transparent Child1Stable.word_4 global_word_509.
Lemma instance_12_word_4 v : Child1Stable.word_4 (instance_12_leaves v) = global_word_509 v.
Proof. unfold Child1Stable.word_4, instance_12_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_509.
Transparent Child1Stable.word_7 global_word_1604.
Lemma instance_12_word_7 v : Child1Stable.word_7 (instance_12_leaves v) = global_word_1604 v.
Proof. unfold Child1Stable.word_7, global_word_1604, Child1Stable.closed_word_7, global_closed_1604, Child1Stable.expr_word_7, global_expr_1604.
 rewrite instance_12_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1604.
Transparent Child1Stable.word_8 global_word_1605.
Lemma instance_12_word_8 v : Child1Stable.word_8 (instance_12_leaves v) = global_word_1605 v.
Proof. unfold Child1Stable.word_8, global_word_1605, Child1Stable.closed_word_8, global_closed_1605, Child1Stable.expr_word_8, global_expr_1605.
 rewrite instance_12_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1605.
Transparent Child1Stable.word_9 global_word_1606.
Lemma instance_12_word_9 v : Child1Stable.word_9 (instance_12_leaves v) = global_word_1606 v.
Proof. unfold Child1Stable.word_9, global_word_1606, Child1Stable.closed_word_9, global_closed_1606, Child1Stable.expr_word_9, global_expr_1606.
 rewrite instance_12_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1606.
Transparent Child1Stable.word_10 global_word_1607.
Lemma instance_12_word_10 v : Child1Stable.word_10 (instance_12_leaves v) = global_word_1607 v.
Proof. unfold Child1Stable.word_10, global_word_1607, Child1Stable.closed_word_10, global_closed_1607, Child1Stable.expr_word_10, global_expr_1607.
 rewrite instance_12_word_7 instance_12_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1607.
Transparent Child1Stable.word_11 global_word_1608.
Lemma instance_12_word_11 v : Child1Stable.word_11 (instance_12_leaves v) = global_word_1608 v.
Proof. unfold Child1Stable.word_11, global_word_1608, Child1Stable.closed_word_11, global_closed_1608, Child1Stable.expr_word_11, global_expr_1608.
 rewrite instance_12_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1608.
Transparent Child1Stable.word_12 global_word_1609.
Lemma instance_12_word_12 v : Child1Stable.word_12 (instance_12_leaves v) = global_word_1609 v.
Proof. unfold Child1Stable.word_12, global_word_1609, Child1Stable.closed_word_12, global_closed_1609, Child1Stable.expr_word_12, global_expr_1609.
 rewrite instance_12_word_9 instance_12_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1609.
Transparent Child1Stable.word_13 global_word_1610.
Lemma instance_12_word_13 v : Child1Stable.word_13 (instance_12_leaves v) = global_word_1610 v.
Proof. unfold Child1Stable.word_13, global_word_1610, Child1Stable.closed_word_13, global_closed_1610, Child1Stable.expr_word_13, global_expr_1610.
 rewrite instance_12_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1610.
Transparent Child1Stable.word_25 global_word_510.
Lemma instance_12_word_25 v : Child1Stable.word_25 (instance_12_leaves v) = global_word_510 v.
Proof. unfold Child1Stable.word_25, global_word_510, Child1Stable.closed_word_25, global_closed_510, Child1Stable.expr_word_25, global_expr_510.
 rewrite instance_12_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_510.
Transparent Child1Stable.word_23 global_word_515.
Lemma instance_12_word_23 v : Child1Stable.word_23 (instance_12_leaves v) = global_word_515 v.
Proof. unfold Child1Stable.word_23, global_word_515, Child1Stable.closed_word_23, global_closed_515, Child1Stable.expr_word_23, global_expr_515.
 rewrite instance_12_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_515.
Transparent Child1Stable.word_24 global_word_520.
Lemma instance_12_word_24 v : Child1Stable.word_24 (instance_12_leaves v) = global_word_520 v.
Proof. unfold Child1Stable.word_24, global_word_520, Child1Stable.closed_word_24, global_closed_520, Child1Stable.expr_word_24, global_expr_520.
 rewrite instance_12_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_520.
Transparent Child1Stable.word_26 global_word_521.
Lemma instance_12_word_26 v : Child1Stable.word_26 (instance_12_leaves v) = global_word_521 v.
Proof. unfold Child1Stable.word_26, global_word_521, Child1Stable.closed_word_26, global_closed_521, Child1Stable.expr_word_26, global_expr_521.
 rewrite instance_12_word_23 instance_12_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_521.
Transparent Child1Stable.word_28 global_word_522.
Lemma instance_12_word_28 v : Child1Stable.word_28 (instance_12_leaves v) = global_word_522 v.
Proof. unfold Child1Stable.word_28, global_word_522, Child1Stable.closed_word_28, global_closed_522, Child1Stable.expr_word_28, global_expr_522.
 rewrite instance_12_word_25 instance_12_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_522.
Transparent Child1Stable.word_27 global_word_523.
Lemma instance_12_word_27 v : Child1Stable.word_27 (instance_12_leaves v) = global_word_523 v.
Proof. unfold Child1Stable.word_27, global_word_523, Child1Stable.closed_word_27, global_closed_523, Child1Stable.expr_word_27, global_expr_523.
 rewrite instance_12_word_23 instance_12_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_523.
Transparent Child1Stable.word_29 global_word_524.
Lemma instance_12_word_29 v : Child1Stable.word_29 (instance_12_leaves v) = global_word_524 v.
Proof. unfold Child1Stable.word_29, global_word_524, Child1Stable.closed_word_29, global_closed_524, Child1Stable.expr_word_29, global_expr_524.
 rewrite instance_12_word_25 instance_12_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_524.
Transparent Child1Stable.word_30 global_word_525.
Lemma instance_12_word_30 v : Child1Stable.word_30 (instance_12_leaves v) = global_word_525 v.
Proof. unfold Child1Stable.word_30, global_word_525, Child1Stable.closed_word_30, global_closed_525, Child1Stable.expr_word_30, global_expr_525.
 rewrite instance_12_word_27 instance_12_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_525.
Transparent Child1Stable.word_31 global_word_526.
Lemma instance_12_word_31 v : Child1Stable.word_31 (instance_12_leaves v) = global_word_526 v.
Proof. unfold Child1Stable.word_31, global_word_526, Child1Stable.closed_word_31, global_closed_526, Child1Stable.expr_word_31, global_expr_526.
 rewrite instance_12_word_28 instance_12_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_526.
Transparent Child1Stable.word_32 global_word_527.
Lemma instance_12_word_32 v : Child1Stable.word_32 (instance_12_leaves v) = global_word_527 v.
Proof. unfold Child1Stable.word_32, global_word_527, Child1Stable.closed_word_32, global_closed_527, Child1Stable.expr_word_32, global_expr_527.
 rewrite instance_12_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_527.
Transparent Child1Stable.word_33 global_word_528.
Lemma instance_12_word_33 v : Child1Stable.word_33 (instance_12_leaves v) = global_word_528 v.
Proof. unfold Child1Stable.word_33, global_word_528, Child1Stable.closed_word_33, global_closed_528, Child1Stable.expr_word_33, global_expr_528.
 rewrite instance_12_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_528.
Transparent Child1Stable.word_5 global_word_529.
Lemma instance_12_word_5 v : Child1Stable.word_5 (instance_12_leaves v) = global_word_529 v.
Proof. unfold Child1Stable.word_5, global_word_529, Child1Stable.closed_word_5, global_closed_529, Child1Stable.expr_word_5, global_expr_529.
 rewrite instance_12_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_529.
Transparent Child1Stable.word_14 global_word_1611.
Lemma instance_12_word_14 v : Child1Stable.word_14 (instance_12_leaves v) = global_word_1611 v.
Proof. unfold Child1Stable.word_14, global_word_1611, Child1Stable.closed_word_14, global_closed_1611, Child1Stable.expr_word_14, global_expr_1611.
 rewrite instance_12_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1611.
Transparent Child1Stable.word_34 global_word_555.
Lemma instance_12_word_34 v : Child1Stable.word_34 (instance_12_leaves v) = global_word_555 v.
Proof. unfold Child1Stable.word_34, global_word_555, Child1Stable.closed_word_34, global_closed_555, Child1Stable.expr_word_34, global_expr_555.
 rewrite instance_12_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_555.
Transparent Child1Stable.word_6 global_word_556.
Lemma instance_12_word_6 v : Child1Stable.word_6 (instance_12_leaves v) = global_word_556 v.
Proof. unfold Child1Stable.word_6, global_word_556, Child1Stable.closed_word_6, global_closed_556, Child1Stable.expr_word_6, global_expr_556.
 rewrite instance_12_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_556.
Transparent Child1Stable.word_15 global_word_1612.
Lemma instance_12_word_15 v : Child1Stable.word_15 (instance_12_leaves v) = global_word_1612 v.
Proof. unfold Child1Stable.word_15, global_word_1612, Child1Stable.closed_word_15, global_closed_1612, Child1Stable.expr_word_15, global_expr_1612.
 rewrite instance_12_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1612.
Transparent Child1Stable.word_16 global_word_1613.
Lemma instance_12_word_16 v : Child1Stable.word_16 (instance_12_leaves v) = global_word_1613 v.
Proof. unfold Child1Stable.word_16, global_word_1613, Child1Stable.closed_word_16, global_closed_1613, Child1Stable.expr_word_16, global_expr_1613.
 rewrite instance_12_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1613.
Transparent Child1Stable.word_17 global_word_1614.
Lemma instance_12_word_17 v : Child1Stable.word_17 (instance_12_leaves v) = global_word_1614 v.
Proof. unfold Child1Stable.word_17, global_word_1614, Child1Stable.closed_word_17, global_closed_1614, Child1Stable.expr_word_17, global_expr_1614.
 rewrite instance_12_word_14 instance_12_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1614.
Transparent Child1Stable.word_18 global_word_1615.
Lemma instance_12_word_18 v : Child1Stable.word_18 (instance_12_leaves v) = global_word_1615 v.
Proof. unfold Child1Stable.word_18, global_word_1615, Child1Stable.closed_word_18, global_closed_1615, Child1Stable.expr_word_18, global_expr_1615.
 rewrite instance_12_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1615.
Transparent Child1Stable.word_19 global_word_1616.
Lemma instance_12_word_19 v : Child1Stable.word_19 (instance_12_leaves v) = global_word_1616 v.
Proof. unfold Child1Stable.word_19, global_word_1616, Child1Stable.closed_word_19, global_closed_1616, Child1Stable.expr_word_19, global_expr_1616.
 rewrite instance_12_word_13 instance_12_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1616.
Transparent Child1Stable.word_20 global_word_1618.
Lemma instance_12_word_20 v : Child1Stable.word_20 (instance_12_leaves v) = global_word_1618 v.
Proof. unfold Child1Stable.word_20, global_word_1618, Child1Stable.closed_word_20, global_closed_1618, Child1Stable.expr_word_20, global_expr_1618.
 rewrite instance_12_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1618.
Transparent Child1Stable.word_21 global_word_1619.
Lemma instance_12_word_21 v : Child1Stable.word_21 (instance_12_leaves v) = global_word_1619 v.
Proof. unfold Child1Stable.word_21, global_word_1619, Child1Stable.closed_word_21, global_closed_1619, Child1Stable.expr_word_21, global_expr_1619.
 rewrite instance_12_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1619.
Transparent Child1Stable.word_22 global_word_1620.
Lemma instance_12_word_22 v : Child1Stable.word_22 (instance_12_leaves v) = global_word_1620 v.
Proof. unfold Child1Stable.word_22, global_word_1620, Child1Stable.closed_word_22, global_closed_1620, Child1Stable.expr_word_22, global_expr_1620.
 rewrite instance_12_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1620.
Definition instance_13_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1639 v
| 0, 1 => global_word_1635 v
| 0, 2 => global_word_533 v
| 0, 3 => global_word_539 v
| 0, 4 => global_word_504 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1639.
Lemma instance_13_word_0 v : Child1Stable.word_0 (instance_13_leaves v) = global_word_1639 v.
Proof. unfold Child1Stable.word_0, instance_13_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1639.
Transparent Child1Stable.word_1 global_word_1635.
Lemma instance_13_word_1 v : Child1Stable.word_1 (instance_13_leaves v) = global_word_1635 v.
Proof. unfold Child1Stable.word_1, instance_13_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1635.
Transparent Child1Stable.word_2 global_word_533.
Lemma instance_13_word_2 v : Child1Stable.word_2 (instance_13_leaves v) = global_word_533 v.
Proof. unfold Child1Stable.word_2, instance_13_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_533.
Transparent Child1Stable.word_3 global_word_539.
Lemma instance_13_word_3 v : Child1Stable.word_3 (instance_13_leaves v) = global_word_539 v.
Proof. unfold Child1Stable.word_3, instance_13_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_539.
Transparent Child1Stable.word_4 global_word_504.
Lemma instance_13_word_4 v : Child1Stable.word_4 (instance_13_leaves v) = global_word_504 v.
Proof. unfold Child1Stable.word_4, instance_13_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_504.
Transparent Child1Stable.word_7 global_word_1622.
Lemma instance_13_word_7 v : Child1Stable.word_7 (instance_13_leaves v) = global_word_1622 v.
Proof. unfold Child1Stable.word_7, global_word_1622, Child1Stable.closed_word_7, global_closed_1622, Child1Stable.expr_word_7, global_expr_1622.
 rewrite instance_13_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1622.
Transparent Child1Stable.word_8 global_word_1623.
Lemma instance_13_word_8 v : Child1Stable.word_8 (instance_13_leaves v) = global_word_1623 v.
Proof. unfold Child1Stable.word_8, global_word_1623, Child1Stable.closed_word_8, global_closed_1623, Child1Stable.expr_word_8, global_expr_1623.
 rewrite instance_13_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1623.
Transparent Child1Stable.word_9 global_word_1624.
Lemma instance_13_word_9 v : Child1Stable.word_9 (instance_13_leaves v) = global_word_1624 v.
Proof. unfold Child1Stable.word_9, global_word_1624, Child1Stable.closed_word_9, global_closed_1624, Child1Stable.expr_word_9, global_expr_1624.
 rewrite instance_13_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1624.
Transparent Child1Stable.word_10 global_word_1625.
Lemma instance_13_word_10 v : Child1Stable.word_10 (instance_13_leaves v) = global_word_1625 v.
Proof. unfold Child1Stable.word_10, global_word_1625, Child1Stable.closed_word_10, global_closed_1625, Child1Stable.expr_word_10, global_expr_1625.
 rewrite instance_13_word_7 instance_13_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1625.
Transparent Child1Stable.word_11 global_word_1626.
Lemma instance_13_word_11 v : Child1Stable.word_11 (instance_13_leaves v) = global_word_1626 v.
Proof. unfold Child1Stable.word_11, global_word_1626, Child1Stable.closed_word_11, global_closed_1626, Child1Stable.expr_word_11, global_expr_1626.
 rewrite instance_13_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1626.
Transparent Child1Stable.word_12 global_word_1627.
Lemma instance_13_word_12 v : Child1Stable.word_12 (instance_13_leaves v) = global_word_1627 v.
Proof. unfold Child1Stable.word_12, global_word_1627, Child1Stable.closed_word_12, global_closed_1627, Child1Stable.expr_word_12, global_expr_1627.
 rewrite instance_13_word_9 instance_13_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1627.
Transparent Child1Stable.word_13 global_word_1628.
Lemma instance_13_word_13 v : Child1Stable.word_13 (instance_13_leaves v) = global_word_1628 v.
Proof. unfold Child1Stable.word_13, global_word_1628, Child1Stable.closed_word_13, global_closed_1628, Child1Stable.expr_word_13, global_expr_1628.
 rewrite instance_13_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1628.
Transparent Child1Stable.word_25 global_word_505.
Lemma instance_13_word_25 v : Child1Stable.word_25 (instance_13_leaves v) = global_word_505 v.
Proof. unfold Child1Stable.word_25, global_word_505, Child1Stable.closed_word_25, global_closed_505, Child1Stable.expr_word_25, global_expr_505.
 rewrite instance_13_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_505.
Transparent Child1Stable.word_23 global_word_534.
Lemma instance_13_word_23 v : Child1Stable.word_23 (instance_13_leaves v) = global_word_534 v.
Proof. unfold Child1Stable.word_23, global_word_534, Child1Stable.closed_word_23, global_closed_534, Child1Stable.expr_word_23, global_expr_534.
 rewrite instance_13_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_534.
Transparent Child1Stable.word_24 global_word_540.
Lemma instance_13_word_24 v : Child1Stable.word_24 (instance_13_leaves v) = global_word_540 v.
Proof. unfold Child1Stable.word_24, global_word_540, Child1Stable.closed_word_24, global_closed_540, Child1Stable.expr_word_24, global_expr_540.
 rewrite instance_13_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_540.
Transparent Child1Stable.word_26 global_word_541.
Lemma instance_13_word_26 v : Child1Stable.word_26 (instance_13_leaves v) = global_word_541 v.
Proof. unfold Child1Stable.word_26, global_word_541, Child1Stable.closed_word_26, global_closed_541, Child1Stable.expr_word_26, global_expr_541.
 rewrite instance_13_word_23 instance_13_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_541.
Transparent Child1Stable.word_28 global_word_542.
Lemma instance_13_word_28 v : Child1Stable.word_28 (instance_13_leaves v) = global_word_542 v.
Proof. unfold Child1Stable.word_28, global_word_542, Child1Stable.closed_word_28, global_closed_542, Child1Stable.expr_word_28, global_expr_542.
 rewrite instance_13_word_25 instance_13_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_542.
Transparent Child1Stable.word_27 global_word_543.
Lemma instance_13_word_27 v : Child1Stable.word_27 (instance_13_leaves v) = global_word_543 v.
Proof. unfold Child1Stable.word_27, global_word_543, Child1Stable.closed_word_27, global_closed_543, Child1Stable.expr_word_27, global_expr_543.
 rewrite instance_13_word_23 instance_13_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_543.
Transparent Child1Stable.word_29 global_word_544.
Lemma instance_13_word_29 v : Child1Stable.word_29 (instance_13_leaves v) = global_word_544 v.
Proof. unfold Child1Stable.word_29, global_word_544, Child1Stable.closed_word_29, global_closed_544, Child1Stable.expr_word_29, global_expr_544.
 rewrite instance_13_word_25 instance_13_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_544.
Transparent Child1Stable.word_30 global_word_545.
Lemma instance_13_word_30 v : Child1Stable.word_30 (instance_13_leaves v) = global_word_545 v.
Proof. unfold Child1Stable.word_30, global_word_545, Child1Stable.closed_word_30, global_closed_545, Child1Stable.expr_word_30, global_expr_545.
 rewrite instance_13_word_27 instance_13_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_545.
Transparent Child1Stable.word_31 global_word_546.
Lemma instance_13_word_31 v : Child1Stable.word_31 (instance_13_leaves v) = global_word_546 v.
Proof. unfold Child1Stable.word_31, global_word_546, Child1Stable.closed_word_31, global_closed_546, Child1Stable.expr_word_31, global_expr_546.
 rewrite instance_13_word_28 instance_13_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_546.
Transparent Child1Stable.word_32 global_word_547.
Lemma instance_13_word_32 v : Child1Stable.word_32 (instance_13_leaves v) = global_word_547 v.
Proof. unfold Child1Stable.word_32, global_word_547, Child1Stable.closed_word_32, global_closed_547, Child1Stable.expr_word_32, global_expr_547.
 rewrite instance_13_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_547.
Transparent Child1Stable.word_33 global_word_548.
Lemma instance_13_word_33 v : Child1Stable.word_33 (instance_13_leaves v) = global_word_548 v.
Proof. unfold Child1Stable.word_33, global_word_548, Child1Stable.closed_word_33, global_closed_548, Child1Stable.expr_word_33, global_expr_548.
 rewrite instance_13_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_548.
Transparent Child1Stable.word_5 global_word_549.
Lemma instance_13_word_5 v : Child1Stable.word_5 (instance_13_leaves v) = global_word_549 v.
Proof. unfold Child1Stable.word_5, global_word_549, Child1Stable.closed_word_5, global_closed_549, Child1Stable.expr_word_5, global_expr_549.
 rewrite instance_13_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_549.
Transparent Child1Stable.word_14 global_word_1629.
Lemma instance_13_word_14 v : Child1Stable.word_14 (instance_13_leaves v) = global_word_1629 v.
Proof. unfold Child1Stable.word_14, global_word_1629, Child1Stable.closed_word_14, global_closed_1629, Child1Stable.expr_word_14, global_expr_1629.
 rewrite instance_13_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1629.
Transparent Child1Stable.word_34 global_word_562.
Lemma instance_13_word_34 v : Child1Stable.word_34 (instance_13_leaves v) = global_word_562 v.
Proof. unfold Child1Stable.word_34, global_word_562, Child1Stable.closed_word_34, global_closed_562, Child1Stable.expr_word_34, global_expr_562.
 rewrite instance_13_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_562.
Transparent Child1Stable.word_6 global_word_563.
Lemma instance_13_word_6 v : Child1Stable.word_6 (instance_13_leaves v) = global_word_563 v.
Proof. unfold Child1Stable.word_6, global_word_563, Child1Stable.closed_word_6, global_closed_563, Child1Stable.expr_word_6, global_expr_563.
 rewrite instance_13_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_563.
Transparent Child1Stable.word_15 global_word_1630.
Lemma instance_13_word_15 v : Child1Stable.word_15 (instance_13_leaves v) = global_word_1630 v.
Proof. unfold Child1Stable.word_15, global_word_1630, Child1Stable.closed_word_15, global_closed_1630, Child1Stable.expr_word_15, global_expr_1630.
 rewrite instance_13_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1630.
Transparent Child1Stable.word_16 global_word_1631.
Lemma instance_13_word_16 v : Child1Stable.word_16 (instance_13_leaves v) = global_word_1631 v.
Proof. unfold Child1Stable.word_16, global_word_1631, Child1Stable.closed_word_16, global_closed_1631, Child1Stable.expr_word_16, global_expr_1631.
 rewrite instance_13_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1631.
Transparent Child1Stable.word_17 global_word_1632.
Lemma instance_13_word_17 v : Child1Stable.word_17 (instance_13_leaves v) = global_word_1632 v.
Proof. unfold Child1Stable.word_17, global_word_1632, Child1Stable.closed_word_17, global_closed_1632, Child1Stable.expr_word_17, global_expr_1632.
 rewrite instance_13_word_14 instance_13_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1632.
Transparent Child1Stable.word_18 global_word_1633.
Lemma instance_13_word_18 v : Child1Stable.word_18 (instance_13_leaves v) = global_word_1633 v.
Proof. unfold Child1Stable.word_18, global_word_1633, Child1Stable.closed_word_18, global_closed_1633, Child1Stable.expr_word_18, global_expr_1633.
 rewrite instance_13_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1633.
Transparent Child1Stable.word_19 global_word_1634.
Lemma instance_13_word_19 v : Child1Stable.word_19 (instance_13_leaves v) = global_word_1634 v.
Proof. unfold Child1Stable.word_19, global_word_1634, Child1Stable.closed_word_19, global_closed_1634, Child1Stable.expr_word_19, global_expr_1634.
 rewrite instance_13_word_13 instance_13_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1634.
Transparent Child1Stable.word_20 global_word_1636.
Lemma instance_13_word_20 v : Child1Stable.word_20 (instance_13_leaves v) = global_word_1636 v.
Proof. unfold Child1Stable.word_20, global_word_1636, Child1Stable.closed_word_20, global_closed_1636, Child1Stable.expr_word_20, global_expr_1636.
 rewrite instance_13_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1636.
Transparent Child1Stable.word_21 global_word_1637.
Lemma instance_13_word_21 v : Child1Stable.word_21 (instance_13_leaves v) = global_word_1637 v.
Proof. unfold Child1Stable.word_21, global_word_1637, Child1Stable.closed_word_21, global_closed_1637, Child1Stable.expr_word_21, global_expr_1637.
 rewrite instance_13_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1637.
Transparent Child1Stable.word_22 global_word_1638.
Lemma instance_13_word_22 v : Child1Stable.word_22 (instance_13_leaves v) = global_word_1638 v.
Proof. unfold Child1Stable.word_22, global_word_1638, Child1Stable.closed_word_22, global_closed_1638, Child1Stable.expr_word_22, global_expr_1638.
 rewrite instance_13_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1638.
Definition instance_14_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1667 v
| 0, 1 => global_word_1663 v
| 0, 2 => global_word_581 v
| 0, 3 => global_word_586 v
| 0, 4 => global_word_576 v
| 0, 5 => global_word_605 v
| 0, 6 => global_word_570 v
| 10, 5 => global_word_599 v
| 10, 6 => global_word_626 v
| 11, 5 => global_word_619 v
| 11, 6 => global_word_633 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1667.
Lemma instance_14_word_0 v : Child2Stable.word_0 (instance_14_leaves v) = global_word_1667 v.
Proof. unfold Child2Stable.word_0, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1667.
Transparent Child2Stable.word_1 global_word_1663.
Lemma instance_14_word_1 v : Child2Stable.word_1 (instance_14_leaves v) = global_word_1663 v.
Proof. unfold Child2Stable.word_1, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1663.
Transparent Child2Stable.word_2 global_word_581.
Lemma instance_14_word_2 v : Child2Stable.word_2 (instance_14_leaves v) = global_word_581 v.
Proof. unfold Child2Stable.word_2, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_581.
Transparent Child2Stable.word_3 global_word_586.
Lemma instance_14_word_3 v : Child2Stable.word_3 (instance_14_leaves v) = global_word_586 v.
Proof. unfold Child2Stable.word_3, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_586.
Transparent Child2Stable.word_4 global_word_576.
Lemma instance_14_word_4 v : Child2Stable.word_4 (instance_14_leaves v) = global_word_576 v.
Proof. unfold Child2Stable.word_4, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_576.
Transparent Child2Stable.word_5 global_word_605.
Lemma instance_14_word_5 v : Child2Stable.word_5 (instance_14_leaves v) = global_word_605 v.
Proof. unfold Child2Stable.word_5, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_605.
Transparent Child2Stable.word_6 global_word_570.
Lemma instance_14_word_6 v : Child2Stable.word_6 (instance_14_leaves v) = global_word_570 v.
Proof. unfold Child2Stable.word_6, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_570.
Transparent Child2Stable.port_10_5 global_word_599.
Lemma instance_14_port_10_5 v : Child2Stable.port_10_5 (instance_14_leaves v) = global_word_599 v.
Proof. unfold Child2Stable.port_10_5, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_599.
Transparent Child2Stable.port_10_6 global_word_626.
Lemma instance_14_port_10_6 v : Child2Stable.port_10_6 (instance_14_leaves v) = global_word_626 v.
Proof. unfold Child2Stable.port_10_6, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_626.
Transparent Child2Stable.port_11_5 global_word_619.
Lemma instance_14_port_11_5 v : Child2Stable.port_11_5 (instance_14_leaves v) = global_word_619 v.
Proof. unfold Child2Stable.port_11_5, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_619.
Transparent Child2Stable.port_11_6 global_word_633.
Lemma instance_14_port_11_6 v : Child2Stable.port_11_6 (instance_14_leaves v) = global_word_633 v.
Proof. unfold Child2Stable.port_11_6, instance_14_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_633.
Transparent Child2Stable.word_12 global_word_1640.
Lemma instance_14_word_12 v : Child2Stable.word_12 (instance_14_leaves v) = global_word_1640 v.
Proof. unfold Child2Stable.word_12, global_word_1640, Child2Stable.closed_word_12, global_closed_1640, Child2Stable.expr_word_12, global_expr_1640.
 rewrite instance_14_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1640.
Transparent Child2Stable.word_13 global_word_1641.
Lemma instance_14_word_13 v : Child2Stable.word_13 (instance_14_leaves v) = global_word_1641 v.
Proof. unfold Child2Stable.word_13, global_word_1641, Child2Stable.closed_word_13, global_closed_1641, Child2Stable.expr_word_13, global_expr_1641.
 rewrite instance_14_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1641.
Transparent Child2Stable.word_14 global_word_1642.
Lemma instance_14_word_14 v : Child2Stable.word_14 (instance_14_leaves v) = global_word_1642 v.
Proof. unfold Child2Stable.word_14, global_word_1642, Child2Stable.closed_word_14, global_closed_1642, Child2Stable.expr_word_14, global_expr_1642.
 rewrite instance_14_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1642.
Transparent Child2Stable.word_15 global_word_1643.
Lemma instance_14_word_15 v : Child2Stable.word_15 (instance_14_leaves v) = global_word_1643 v.
Proof. unfold Child2Stable.word_15, global_word_1643, Child2Stable.closed_word_15, global_closed_1643, Child2Stable.expr_word_15, global_expr_1643.
 rewrite instance_14_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1643.
Transparent Child2Stable.word_16 global_word_1644.
Lemma instance_14_word_16 v : Child2Stable.word_16 (instance_14_leaves v) = global_word_1644 v.
Proof. unfold Child2Stable.word_16, global_word_1644, Child2Stable.closed_word_16, global_closed_1644, Child2Stable.expr_word_16, global_expr_1644.
 rewrite instance_14_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1644.
Transparent Child2Stable.word_17 global_word_1645.
Lemma instance_14_word_17 v : Child2Stable.word_17 (instance_14_leaves v) = global_word_1645 v.
Proof. unfold Child2Stable.word_17, global_word_1645, Child2Stable.closed_word_17, global_closed_1645, Child2Stable.expr_word_17, global_expr_1645.
 rewrite instance_14_word_12 instance_14_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1645.
Transparent Child2Stable.word_18 global_word_1646.
Lemma instance_14_word_18 v : Child2Stable.word_18 (instance_14_leaves v) = global_word_1646 v.
Proof. unfold Child2Stable.word_18, global_word_1646, Child2Stable.closed_word_18, global_closed_1646, Child2Stable.expr_word_18, global_expr_1646.
 rewrite instance_14_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1646.
Transparent Child2Stable.word_19 global_word_1647.
Lemma instance_14_word_19 v : Child2Stable.word_19 (instance_14_leaves v) = global_word_1647 v.
Proof. unfold Child2Stable.word_19, global_word_1647, Child2Stable.closed_word_19, global_closed_1647, Child2Stable.expr_word_19, global_expr_1647.
 rewrite instance_14_word_14 instance_14_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1647.
Transparent Child2Stable.word_20 global_word_1648.
Lemma instance_14_word_20 v : Child2Stable.word_20 (instance_14_leaves v) = global_word_1648 v.
Proof. unfold Child2Stable.word_20, global_word_1648, Child2Stable.closed_word_20, global_closed_1648, Child2Stable.expr_word_20, global_expr_1648.
 rewrite instance_14_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1648.
Transparent Child2Stable.word_21 global_word_1649.
Lemma instance_14_word_21 v : Child2Stable.word_21 (instance_14_leaves v) = global_word_1649 v.
Proof. unfold Child2Stable.word_21, global_word_1649, Child2Stable.closed_word_21, global_closed_1649, Child2Stable.expr_word_21, global_expr_1649.
 rewrite instance_14_word_15 instance_14_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1649.
Transparent Child2Stable.word_22 global_word_1650.
Lemma instance_14_word_22 v : Child2Stable.word_22 (instance_14_leaves v) = global_word_1650 v.
Proof. unfold Child2Stable.word_22, global_word_1650, Child2Stable.closed_word_22, global_closed_1650, Child2Stable.expr_word_22, global_expr_1650.
 rewrite instance_14_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1650.
Transparent Child2Stable.word_23 global_word_1651.
Lemma instance_14_word_23 v : Child2Stable.word_23 (instance_14_leaves v) = global_word_1651 v.
Proof. unfold Child2Stable.word_23, global_word_1651, Child2Stable.closed_word_23, global_closed_1651, Child2Stable.expr_word_23, global_expr_1651.
 rewrite instance_14_word_16 instance_14_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1651.
Transparent Child2Stable.word_24 global_word_1652.
Lemma instance_14_word_24 v : Child2Stable.word_24 (instance_14_leaves v) = global_word_1652 v.
Proof. unfold Child2Stable.word_24, global_word_1652, Child2Stable.closed_word_24, global_closed_1652, Child2Stable.expr_word_24, global_expr_1652.
 rewrite instance_14_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1652.
Transparent Child2Stable.word_41 global_word_620.
Lemma instance_14_word_41 v : Child2Stable.word_41 (instance_14_leaves v) = global_word_620 v.
Proof. unfold Child2Stable.word_41, global_word_620, Child2Stable.closed_word_41, global_closed_620, Child2Stable.expr_word_41, global_expr_620.
 rewrite instance_14_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_620.
Transparent Child2Stable.word_7 global_word_621.
Lemma instance_14_word_7 v : Child2Stable.word_7 (instance_14_leaves v) = global_word_621 v.
Proof. unfold Child2Stable.word_7, global_word_621, Child2Stable.closed_word_7, global_closed_621, Child2Stable.expr_word_7, global_expr_621.
 rewrite instance_14_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_621.
Transparent Child2Stable.word_25 global_word_1653.
Lemma instance_14_word_25 v : Child2Stable.word_25 (instance_14_leaves v) = global_word_1653 v.
Proof. unfold Child2Stable.word_25, global_word_1653, Child2Stable.closed_word_25, global_closed_1653, Child2Stable.expr_word_25, global_expr_1653.
 rewrite instance_14_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1653.
Transparent Child2Stable.word_42 global_word_627.
Lemma instance_14_word_42 v : Child2Stable.word_42 (instance_14_leaves v) = global_word_627 v.
Proof. unfold Child2Stable.word_42, global_word_627, Child2Stable.closed_word_42, global_closed_627, Child2Stable.expr_word_42, global_expr_627.
 rewrite instance_14_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_627.
Transparent Child2Stable.word_8 global_word_628.
Lemma instance_14_word_8 v : Child2Stable.word_8 (instance_14_leaves v) = global_word_628 v.
Proof. unfold Child2Stable.word_8, global_word_628, Child2Stable.closed_word_8, global_closed_628, Child2Stable.expr_word_8, global_expr_628.
 rewrite instance_14_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_628.
Transparent Child2Stable.word_26 global_word_1654.
Lemma instance_14_word_26 v : Child2Stable.word_26 (instance_14_leaves v) = global_word_1654 v.
Proof. unfold Child2Stable.word_26, global_word_1654, Child2Stable.closed_word_26, global_closed_1654, Child2Stable.expr_word_26, global_expr_1654.
 rewrite instance_14_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1654.
Transparent Child2Stable.word_27 global_word_1655.
Lemma instance_14_word_27 v : Child2Stable.word_27 (instance_14_leaves v) = global_word_1655 v.
Proof. unfold Child2Stable.word_27, global_word_1655, Child2Stable.closed_word_27, global_closed_1655, Child2Stable.expr_word_27, global_expr_1655.
 rewrite instance_14_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1655.
Transparent Child2Stable.word_43 global_word_634.
Lemma instance_14_word_43 v : Child2Stable.word_43 (instance_14_leaves v) = global_word_634 v.
Proof. unfold Child2Stable.word_43, global_word_634, Child2Stable.closed_word_43, global_closed_634, Child2Stable.expr_word_43, global_expr_634.
 rewrite instance_14_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_634.
Transparent Child2Stable.word_9 global_word_635.
Lemma instance_14_word_9 v : Child2Stable.word_9 (instance_14_leaves v) = global_word_635 v.
Proof. unfold Child2Stable.word_9, global_word_635, Child2Stable.closed_word_9, global_closed_635, Child2Stable.expr_word_9, global_expr_635.
 rewrite instance_14_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_635.
Transparent Child2Stable.word_28 global_word_1656.
Lemma instance_14_word_28 v : Child2Stable.word_28 (instance_14_leaves v) = global_word_1656 v.
Proof. unfold Child2Stable.word_28, global_word_1656, Child2Stable.closed_word_28, global_closed_1656, Child2Stable.expr_word_28, global_expr_1656.
 rewrite instance_14_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1656.
Transparent Child2Stable.word_29 global_word_1657.
Lemma instance_14_word_29 v : Child2Stable.word_29 (instance_14_leaves v) = global_word_1657 v.
Proof. unfold Child2Stable.word_29, global_word_1657, Child2Stable.closed_word_29, global_closed_1657, Child2Stable.expr_word_29, global_expr_1657.
 rewrite instance_14_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1657.
Transparent Child2Stable.word_30 global_word_1658.
Lemma instance_14_word_30 v : Child2Stable.word_30 (instance_14_leaves v) = global_word_1658 v.
Proof. unfold Child2Stable.word_30, global_word_1658, Child2Stable.closed_word_30, global_closed_1658, Child2Stable.expr_word_30, global_expr_1658.
 rewrite instance_14_word_25 instance_14_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1658.
Transparent Child2Stable.word_31 global_word_1659.
Lemma instance_14_word_31 v : Child2Stable.word_31 (instance_14_leaves v) = global_word_1659 v.
Proof. unfold Child2Stable.word_31, global_word_1659, Child2Stable.closed_word_31, global_closed_1659, Child2Stable.expr_word_31, global_expr_1659.
 rewrite instance_14_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1659.
Transparent Child2Stable.word_32 global_word_1660.
Lemma instance_14_word_32 v : Child2Stable.word_32 (instance_14_leaves v) = global_word_1660 v.
Proof. unfold Child2Stable.word_32, global_word_1660, Child2Stable.closed_word_32, global_closed_1660, Child2Stable.expr_word_32, global_expr_1660.
 rewrite instance_14_word_29 instance_14_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1660.
Transparent Child2Stable.word_33 global_word_1661.
Lemma instance_14_word_33 v : Child2Stable.word_33 (instance_14_leaves v) = global_word_1661 v.
Proof. unfold Child2Stable.word_33, global_word_1661, Child2Stable.closed_word_33, global_closed_1661, Child2Stable.expr_word_33, global_expr_1661.
 rewrite instance_14_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1661.
Transparent Child2Stable.word_34 global_word_1662.
Lemma instance_14_word_34 v : Child2Stable.word_34 (instance_14_leaves v) = global_word_1662 v.
Proof. unfold Child2Stable.word_34, global_word_1662, Child2Stable.closed_word_34, global_closed_1662, Child2Stable.expr_word_34, global_expr_1662.
 rewrite instance_14_word_24 instance_14_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1662.
Transparent Child2Stable.word_35 global_word_1664.
Lemma instance_14_word_35 v : Child2Stable.word_35 (instance_14_leaves v) = global_word_1664 v.
Proof. unfold Child2Stable.word_35, global_word_1664, Child2Stable.closed_word_35, global_closed_1664, Child2Stable.expr_word_35, global_expr_1664.
 rewrite instance_14_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1664.
Transparent Child2Stable.word_36 global_word_1665.
Lemma instance_14_word_36 v : Child2Stable.word_36 (instance_14_leaves v) = global_word_1665 v.
Proof. unfold Child2Stable.word_36, global_word_1665, Child2Stable.closed_word_36, global_closed_1665, Child2Stable.expr_word_36, global_expr_1665.
 rewrite instance_14_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1665.
Transparent Child2Stable.word_37 global_word_1666.
Lemma instance_14_word_37 v : Child2Stable.word_37 (instance_14_leaves v) = global_word_1666 v.
Proof. unfold Child2Stable.word_37, global_word_1666, Child2Stable.closed_word_37, global_closed_1666, Child2Stable.expr_word_37, global_expr_1666.
 rewrite instance_14_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1666.
Transparent Child2Stable.word_38 global_word_600.
Lemma instance_14_word_38 v : Child2Stable.word_38 (instance_14_leaves v) = global_word_600 v.
Proof. unfold Child2Stable.word_38, global_word_600, Child2Stable.closed_word_38, global_closed_600, Child2Stable.expr_word_38, global_expr_600.
 rewrite instance_14_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_600.
Transparent Child2Stable.word_39 global_word_606.
Lemma instance_14_word_39 v : Child2Stable.word_39 (instance_14_leaves v) = global_word_606 v.
Proof. unfold Child2Stable.word_39, global_word_606, Child2Stable.closed_word_39, global_closed_606, Child2Stable.expr_word_39, global_expr_606.
 rewrite instance_14_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_606.
Transparent Child2Stable.word_40 global_word_571.
Lemma instance_14_word_40 v : Child2Stable.word_40 (instance_14_leaves v) = global_word_571 v.
Proof. unfold Child2Stable.word_40, global_word_571, Child2Stable.closed_word_40, global_closed_571, Child2Stable.expr_word_40, global_expr_571.
 rewrite instance_14_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_571.
Transparent Child2Stable.port_10_0 global_word_1668.
Lemma instance_14_port_10_0 v : Child2Stable.port_10_0 (instance_14_leaves v) = global_word_1668 v.
Proof. unfold Child2Stable.port_10_0, global_word_1668, Child2Stable.closed_port_10_0, global_closed_1668, Child2Stable.expr_port_10_0, global_expr_1668.
 rewrite instance_14_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1668.
Transparent Child2Stable.port_10_1 global_word_1669.
Lemma instance_14_port_10_1 v : Child2Stable.port_10_1 (instance_14_leaves v) = global_word_1669 v.
Proof. unfold Child2Stable.port_10_1, global_word_1669, Child2Stable.closed_port_10_1, global_closed_1669, Child2Stable.expr_port_10_1, global_expr_1669.
 rewrite instance_14_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1669.
Transparent Child2Stable.port_10_2 global_word_582.
Lemma instance_14_port_10_2 v : Child2Stable.port_10_2 (instance_14_leaves v) = global_word_582 v.
Proof. unfold Child2Stable.port_10_2, global_word_582, Child2Stable.closed_port_10_2, global_closed_582, Child2Stable.expr_port_10_2, global_expr_582.
 rewrite instance_14_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_582.
Transparent Child2Stable.port_10_3 global_word_587.
Lemma instance_14_port_10_3 v : Child2Stable.port_10_3 (instance_14_leaves v) = global_word_587 v.
Proof. unfold Child2Stable.port_10_3, global_word_587, Child2Stable.closed_port_10_3, global_closed_587, Child2Stable.expr_port_10_3, global_expr_587.
 rewrite instance_14_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_587.
Transparent Child2Stable.port_10_4 global_word_577.
Lemma instance_14_port_10_4 v : Child2Stable.port_10_4 (instance_14_leaves v) = global_word_577 v.
Proof. unfold Child2Stable.port_10_4, global_word_577, Child2Stable.closed_port_10_4, global_closed_577, Child2Stable.expr_port_10_4, global_expr_577.
 rewrite instance_14_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_577.
Transparent Child2Stable.port_11_0 global_word_1670.
Lemma instance_14_port_11_0 v : Child2Stable.port_11_0 (instance_14_leaves v) = global_word_1670 v.
Proof. unfold Child2Stable.port_11_0, global_word_1670, Child2Stable.closed_port_11_0, global_closed_1670, Child2Stable.expr_port_11_0, global_expr_1670.
 rewrite instance_14_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1670.
Transparent Child2Stable.port_11_1 global_word_1671.
Lemma instance_14_port_11_1 v : Child2Stable.port_11_1 (instance_14_leaves v) = global_word_1671 v.
Proof. unfold Child2Stable.port_11_1, global_word_1671, Child2Stable.closed_port_11_1, global_closed_1671, Child2Stable.expr_port_11_1, global_expr_1671.
 rewrite instance_14_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1671.
Transparent Child2Stable.port_11_2 global_word_601.
Lemma instance_14_port_11_2 v : Child2Stable.port_11_2 (instance_14_leaves v) = global_word_601 v.
Proof. unfold Child2Stable.port_11_2, global_word_601, Child2Stable.closed_port_11_2, global_closed_601, Child2Stable.expr_port_11_2, global_expr_601.
 rewrite instance_14_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_601.
Transparent Child2Stable.port_11_3 global_word_607.
Lemma instance_14_port_11_3 v : Child2Stable.port_11_3 (instance_14_leaves v) = global_word_607 v.
Proof. unfold Child2Stable.port_11_3, global_word_607, Child2Stable.closed_port_11_3, global_closed_607, Child2Stable.expr_port_11_3, global_expr_607.
 rewrite instance_14_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_607.
Transparent Child2Stable.port_11_4 global_word_572.
Lemma instance_14_port_11_4 v : Child2Stable.port_11_4 (instance_14_leaves v) = global_word_572 v.
Proof. unfold Child2Stable.port_11_4, global_word_572, Child2Stable.closed_port_11_4, global_closed_572, Child2Stable.expr_port_11_4, global_expr_572.
 rewrite instance_14_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_572.
Definition instance_15_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1689 v
| 0, 1 => global_word_1685 v
| 0, 2 => global_word_583 v
| 0, 3 => global_word_588 v
| 0, 4 => global_word_578 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1689.
Lemma instance_15_word_0 v : Child1Stable.word_0 (instance_15_leaves v) = global_word_1689 v.
Proof. unfold Child1Stable.word_0, instance_15_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1689.
Transparent Child1Stable.word_1 global_word_1685.
Lemma instance_15_word_1 v : Child1Stable.word_1 (instance_15_leaves v) = global_word_1685 v.
Proof. unfold Child1Stable.word_1, instance_15_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1685.
Transparent Child1Stable.word_2 global_word_583.
Lemma instance_15_word_2 v : Child1Stable.word_2 (instance_15_leaves v) = global_word_583 v.
Proof. unfold Child1Stable.word_2, instance_15_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_583.
Transparent Child1Stable.word_3 global_word_588.
Lemma instance_15_word_3 v : Child1Stable.word_3 (instance_15_leaves v) = global_word_588 v.
Proof. unfold Child1Stable.word_3, instance_15_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_588.
Transparent Child1Stable.word_4 global_word_578.
Lemma instance_15_word_4 v : Child1Stable.word_4 (instance_15_leaves v) = global_word_578 v.
Proof. unfold Child1Stable.word_4, instance_15_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_578.
Transparent Child1Stable.word_7 global_word_1672.
Lemma instance_15_word_7 v : Child1Stable.word_7 (instance_15_leaves v) = global_word_1672 v.
Proof. unfold Child1Stable.word_7, global_word_1672, Child1Stable.closed_word_7, global_closed_1672, Child1Stable.expr_word_7, global_expr_1672.
 rewrite instance_15_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1672.
Transparent Child1Stable.word_8 global_word_1673.
Lemma instance_15_word_8 v : Child1Stable.word_8 (instance_15_leaves v) = global_word_1673 v.
Proof. unfold Child1Stable.word_8, global_word_1673, Child1Stable.closed_word_8, global_closed_1673, Child1Stable.expr_word_8, global_expr_1673.
 rewrite instance_15_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1673.
Transparent Child1Stable.word_9 global_word_1674.
Lemma instance_15_word_9 v : Child1Stable.word_9 (instance_15_leaves v) = global_word_1674 v.
Proof. unfold Child1Stable.word_9, global_word_1674, Child1Stable.closed_word_9, global_closed_1674, Child1Stable.expr_word_9, global_expr_1674.
 rewrite instance_15_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1674.
Transparent Child1Stable.word_10 global_word_1675.
Lemma instance_15_word_10 v : Child1Stable.word_10 (instance_15_leaves v) = global_word_1675 v.
Proof. unfold Child1Stable.word_10, global_word_1675, Child1Stable.closed_word_10, global_closed_1675, Child1Stable.expr_word_10, global_expr_1675.
 rewrite instance_15_word_7 instance_15_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1675.
Transparent Child1Stable.word_11 global_word_1676.
Lemma instance_15_word_11 v : Child1Stable.word_11 (instance_15_leaves v) = global_word_1676 v.
Proof. unfold Child1Stable.word_11, global_word_1676, Child1Stable.closed_word_11, global_closed_1676, Child1Stable.expr_word_11, global_expr_1676.
 rewrite instance_15_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1676.
Transparent Child1Stable.word_12 global_word_1677.
Lemma instance_15_word_12 v : Child1Stable.word_12 (instance_15_leaves v) = global_word_1677 v.
Proof. unfold Child1Stable.word_12, global_word_1677, Child1Stable.closed_word_12, global_closed_1677, Child1Stable.expr_word_12, global_expr_1677.
 rewrite instance_15_word_9 instance_15_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1677.
Transparent Child1Stable.word_13 global_word_1678.
Lemma instance_15_word_13 v : Child1Stable.word_13 (instance_15_leaves v) = global_word_1678 v.
Proof. unfold Child1Stable.word_13, global_word_1678, Child1Stable.closed_word_13, global_closed_1678, Child1Stable.expr_word_13, global_expr_1678.
 rewrite instance_15_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1678.
Transparent Child1Stable.word_25 global_word_579.
Lemma instance_15_word_25 v : Child1Stable.word_25 (instance_15_leaves v) = global_word_579 v.
Proof. unfold Child1Stable.word_25, global_word_579, Child1Stable.closed_word_25, global_closed_579, Child1Stable.expr_word_25, global_expr_579.
 rewrite instance_15_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_579.
Transparent Child1Stable.word_23 global_word_584.
Lemma instance_15_word_23 v : Child1Stable.word_23 (instance_15_leaves v) = global_word_584 v.
Proof. unfold Child1Stable.word_23, global_word_584, Child1Stable.closed_word_23, global_closed_584, Child1Stable.expr_word_23, global_expr_584.
 rewrite instance_15_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_584.
Transparent Child1Stable.word_24 global_word_589.
Lemma instance_15_word_24 v : Child1Stable.word_24 (instance_15_leaves v) = global_word_589 v.
Proof. unfold Child1Stable.word_24, global_word_589, Child1Stable.closed_word_24, global_closed_589, Child1Stable.expr_word_24, global_expr_589.
 rewrite instance_15_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_589.
Transparent Child1Stable.word_26 global_word_590.
Lemma instance_15_word_26 v : Child1Stable.word_26 (instance_15_leaves v) = global_word_590 v.
Proof. unfold Child1Stable.word_26, global_word_590, Child1Stable.closed_word_26, global_closed_590, Child1Stable.expr_word_26, global_expr_590.
 rewrite instance_15_word_23 instance_15_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_590.
Transparent Child1Stable.word_28 global_word_591.
Lemma instance_15_word_28 v : Child1Stable.word_28 (instance_15_leaves v) = global_word_591 v.
Proof. unfold Child1Stable.word_28, global_word_591, Child1Stable.closed_word_28, global_closed_591, Child1Stable.expr_word_28, global_expr_591.
 rewrite instance_15_word_25 instance_15_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_591.
Transparent Child1Stable.word_27 global_word_592.
Lemma instance_15_word_27 v : Child1Stable.word_27 (instance_15_leaves v) = global_word_592 v.
Proof. unfold Child1Stable.word_27, global_word_592, Child1Stable.closed_word_27, global_closed_592, Child1Stable.expr_word_27, global_expr_592.
 rewrite instance_15_word_23 instance_15_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_592.
Transparent Child1Stable.word_29 global_word_593.
Lemma instance_15_word_29 v : Child1Stable.word_29 (instance_15_leaves v) = global_word_593 v.
Proof. unfold Child1Stable.word_29, global_word_593, Child1Stable.closed_word_29, global_closed_593, Child1Stable.expr_word_29, global_expr_593.
 rewrite instance_15_word_25 instance_15_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_593.
Transparent Child1Stable.word_30 global_word_594.
Lemma instance_15_word_30 v : Child1Stable.word_30 (instance_15_leaves v) = global_word_594 v.
Proof. unfold Child1Stable.word_30, global_word_594, Child1Stable.closed_word_30, global_closed_594, Child1Stable.expr_word_30, global_expr_594.
 rewrite instance_15_word_27 instance_15_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_594.
Transparent Child1Stable.word_31 global_word_595.
Lemma instance_15_word_31 v : Child1Stable.word_31 (instance_15_leaves v) = global_word_595 v.
Proof. unfold Child1Stable.word_31, global_word_595, Child1Stable.closed_word_31, global_closed_595, Child1Stable.expr_word_31, global_expr_595.
 rewrite instance_15_word_28 instance_15_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_595.
Transparent Child1Stable.word_32 global_word_596.
Lemma instance_15_word_32 v : Child1Stable.word_32 (instance_15_leaves v) = global_word_596 v.
Proof. unfold Child1Stable.word_32, global_word_596, Child1Stable.closed_word_32, global_closed_596, Child1Stable.expr_word_32, global_expr_596.
 rewrite instance_15_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_596.
Transparent Child1Stable.word_33 global_word_597.
Lemma instance_15_word_33 v : Child1Stable.word_33 (instance_15_leaves v) = global_word_597 v.
Proof. unfold Child1Stable.word_33, global_word_597, Child1Stable.closed_word_33, global_closed_597, Child1Stable.expr_word_33, global_expr_597.
 rewrite instance_15_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_597.
Transparent Child1Stable.word_5 global_word_598.
Lemma instance_15_word_5 v : Child1Stable.word_5 (instance_15_leaves v) = global_word_598 v.
Proof. unfold Child1Stable.word_5, global_word_598, Child1Stable.closed_word_5, global_closed_598, Child1Stable.expr_word_5, global_expr_598.
 rewrite instance_15_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_598.
Transparent Child1Stable.word_14 global_word_1679.
Lemma instance_15_word_14 v : Child1Stable.word_14 (instance_15_leaves v) = global_word_1679 v.
Proof. unfold Child1Stable.word_14, global_word_1679, Child1Stable.closed_word_14, global_closed_1679, Child1Stable.expr_word_14, global_expr_1679.
 rewrite instance_15_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1679.
Transparent Child1Stable.word_34 global_word_624.
Lemma instance_15_word_34 v : Child1Stable.word_34 (instance_15_leaves v) = global_word_624 v.
Proof. unfold Child1Stable.word_34, global_word_624, Child1Stable.closed_word_34, global_closed_624, Child1Stable.expr_word_34, global_expr_624.
 rewrite instance_15_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_624.
Transparent Child1Stable.word_6 global_word_625.
Lemma instance_15_word_6 v : Child1Stable.word_6 (instance_15_leaves v) = global_word_625 v.
Proof. unfold Child1Stable.word_6, global_word_625, Child1Stable.closed_word_6, global_closed_625, Child1Stable.expr_word_6, global_expr_625.
 rewrite instance_15_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_625.
Transparent Child1Stable.word_15 global_word_1680.
Lemma instance_15_word_15 v : Child1Stable.word_15 (instance_15_leaves v) = global_word_1680 v.
Proof. unfold Child1Stable.word_15, global_word_1680, Child1Stable.closed_word_15, global_closed_1680, Child1Stable.expr_word_15, global_expr_1680.
 rewrite instance_15_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1680.
Transparent Child1Stable.word_16 global_word_1681.
Lemma instance_15_word_16 v : Child1Stable.word_16 (instance_15_leaves v) = global_word_1681 v.
Proof. unfold Child1Stable.word_16, global_word_1681, Child1Stable.closed_word_16, global_closed_1681, Child1Stable.expr_word_16, global_expr_1681.
 rewrite instance_15_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1681.
Transparent Child1Stable.word_17 global_word_1682.
Lemma instance_15_word_17 v : Child1Stable.word_17 (instance_15_leaves v) = global_word_1682 v.
Proof. unfold Child1Stable.word_17, global_word_1682, Child1Stable.closed_word_17, global_closed_1682, Child1Stable.expr_word_17, global_expr_1682.
 rewrite instance_15_word_14 instance_15_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1682.
Transparent Child1Stable.word_18 global_word_1683.
Lemma instance_15_word_18 v : Child1Stable.word_18 (instance_15_leaves v) = global_word_1683 v.
Proof. unfold Child1Stable.word_18, global_word_1683, Child1Stable.closed_word_18, global_closed_1683, Child1Stable.expr_word_18, global_expr_1683.
 rewrite instance_15_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1683.
Transparent Child1Stable.word_19 global_word_1684.
Lemma instance_15_word_19 v : Child1Stable.word_19 (instance_15_leaves v) = global_word_1684 v.
Proof. unfold Child1Stable.word_19, global_word_1684, Child1Stable.closed_word_19, global_closed_1684, Child1Stable.expr_word_19, global_expr_1684.
 rewrite instance_15_word_13 instance_15_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1684.
Transparent Child1Stable.word_20 global_word_1686.
Lemma instance_15_word_20 v : Child1Stable.word_20 (instance_15_leaves v) = global_word_1686 v.
Proof. unfold Child1Stable.word_20, global_word_1686, Child1Stable.closed_word_20, global_closed_1686, Child1Stable.expr_word_20, global_expr_1686.
 rewrite instance_15_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1686.
Transparent Child1Stable.word_21 global_word_1687.
Lemma instance_15_word_21 v : Child1Stable.word_21 (instance_15_leaves v) = global_word_1687 v.
Proof. unfold Child1Stable.word_21, global_word_1687, Child1Stable.closed_word_21, global_closed_1687, Child1Stable.expr_word_21, global_expr_1687.
 rewrite instance_15_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1687.
Transparent Child1Stable.word_22 global_word_1688.
Lemma instance_15_word_22 v : Child1Stable.word_22 (instance_15_leaves v) = global_word_1688 v.
Proof. unfold Child1Stable.word_22, global_word_1688, Child1Stable.closed_word_22, global_closed_1688, Child1Stable.expr_word_22, global_expr_1688.
 rewrite instance_15_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1688.
Definition instance_16_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1707 v
| 0, 1 => global_word_1703 v
| 0, 2 => global_word_602 v
| 0, 3 => global_word_608 v
| 0, 4 => global_word_573 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1707.
Lemma instance_16_word_0 v : Child1Stable.word_0 (instance_16_leaves v) = global_word_1707 v.
Proof. unfold Child1Stable.word_0, instance_16_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1707.
Transparent Child1Stable.word_1 global_word_1703.
Lemma instance_16_word_1 v : Child1Stable.word_1 (instance_16_leaves v) = global_word_1703 v.
Proof. unfold Child1Stable.word_1, instance_16_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1703.
Transparent Child1Stable.word_2 global_word_602.
Lemma instance_16_word_2 v : Child1Stable.word_2 (instance_16_leaves v) = global_word_602 v.
Proof. unfold Child1Stable.word_2, instance_16_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_602.
Transparent Child1Stable.word_3 global_word_608.
Lemma instance_16_word_3 v : Child1Stable.word_3 (instance_16_leaves v) = global_word_608 v.
Proof. unfold Child1Stable.word_3, instance_16_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_608.
Transparent Child1Stable.word_4 global_word_573.
Lemma instance_16_word_4 v : Child1Stable.word_4 (instance_16_leaves v) = global_word_573 v.
Proof. unfold Child1Stable.word_4, instance_16_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_573.
Transparent Child1Stable.word_7 global_word_1690.
Lemma instance_16_word_7 v : Child1Stable.word_7 (instance_16_leaves v) = global_word_1690 v.
Proof. unfold Child1Stable.word_7, global_word_1690, Child1Stable.closed_word_7, global_closed_1690, Child1Stable.expr_word_7, global_expr_1690.
 rewrite instance_16_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1690.
Transparent Child1Stable.word_8 global_word_1691.
Lemma instance_16_word_8 v : Child1Stable.word_8 (instance_16_leaves v) = global_word_1691 v.
Proof. unfold Child1Stable.word_8, global_word_1691, Child1Stable.closed_word_8, global_closed_1691, Child1Stable.expr_word_8, global_expr_1691.
 rewrite instance_16_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1691.
Transparent Child1Stable.word_9 global_word_1692.
Lemma instance_16_word_9 v : Child1Stable.word_9 (instance_16_leaves v) = global_word_1692 v.
Proof. unfold Child1Stable.word_9, global_word_1692, Child1Stable.closed_word_9, global_closed_1692, Child1Stable.expr_word_9, global_expr_1692.
 rewrite instance_16_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1692.
Transparent Child1Stable.word_10 global_word_1693.
Lemma instance_16_word_10 v : Child1Stable.word_10 (instance_16_leaves v) = global_word_1693 v.
Proof. unfold Child1Stable.word_10, global_word_1693, Child1Stable.closed_word_10, global_closed_1693, Child1Stable.expr_word_10, global_expr_1693.
 rewrite instance_16_word_7 instance_16_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1693.
Transparent Child1Stable.word_11 global_word_1694.
Lemma instance_16_word_11 v : Child1Stable.word_11 (instance_16_leaves v) = global_word_1694 v.
Proof. unfold Child1Stable.word_11, global_word_1694, Child1Stable.closed_word_11, global_closed_1694, Child1Stable.expr_word_11, global_expr_1694.
 rewrite instance_16_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1694.
Transparent Child1Stable.word_12 global_word_1695.
Lemma instance_16_word_12 v : Child1Stable.word_12 (instance_16_leaves v) = global_word_1695 v.
Proof. unfold Child1Stable.word_12, global_word_1695, Child1Stable.closed_word_12, global_closed_1695, Child1Stable.expr_word_12, global_expr_1695.
 rewrite instance_16_word_9 instance_16_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1695.
Transparent Child1Stable.word_13 global_word_1696.
Lemma instance_16_word_13 v : Child1Stable.word_13 (instance_16_leaves v) = global_word_1696 v.
Proof. unfold Child1Stable.word_13, global_word_1696, Child1Stable.closed_word_13, global_closed_1696, Child1Stable.expr_word_13, global_expr_1696.
 rewrite instance_16_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1696.
Transparent Child1Stable.word_25 global_word_574.
Lemma instance_16_word_25 v : Child1Stable.word_25 (instance_16_leaves v) = global_word_574 v.
Proof. unfold Child1Stable.word_25, global_word_574, Child1Stable.closed_word_25, global_closed_574, Child1Stable.expr_word_25, global_expr_574.
 rewrite instance_16_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_574.
Transparent Child1Stable.word_23 global_word_603.
Lemma instance_16_word_23 v : Child1Stable.word_23 (instance_16_leaves v) = global_word_603 v.
Proof. unfold Child1Stable.word_23, global_word_603, Child1Stable.closed_word_23, global_closed_603, Child1Stable.expr_word_23, global_expr_603.
 rewrite instance_16_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_603.
Transparent Child1Stable.word_24 global_word_609.
Lemma instance_16_word_24 v : Child1Stable.word_24 (instance_16_leaves v) = global_word_609 v.
Proof. unfold Child1Stable.word_24, global_word_609, Child1Stable.closed_word_24, global_closed_609, Child1Stable.expr_word_24, global_expr_609.
 rewrite instance_16_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_609.
Transparent Child1Stable.word_26 global_word_610.
Lemma instance_16_word_26 v : Child1Stable.word_26 (instance_16_leaves v) = global_word_610 v.
Proof. unfold Child1Stable.word_26, global_word_610, Child1Stable.closed_word_26, global_closed_610, Child1Stable.expr_word_26, global_expr_610.
 rewrite instance_16_word_23 instance_16_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_610.
Transparent Child1Stable.word_28 global_word_611.
Lemma instance_16_word_28 v : Child1Stable.word_28 (instance_16_leaves v) = global_word_611 v.
Proof. unfold Child1Stable.word_28, global_word_611, Child1Stable.closed_word_28, global_closed_611, Child1Stable.expr_word_28, global_expr_611.
 rewrite instance_16_word_25 instance_16_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_611.
Transparent Child1Stable.word_27 global_word_612.
Lemma instance_16_word_27 v : Child1Stable.word_27 (instance_16_leaves v) = global_word_612 v.
Proof. unfold Child1Stable.word_27, global_word_612, Child1Stable.closed_word_27, global_closed_612, Child1Stable.expr_word_27, global_expr_612.
 rewrite instance_16_word_23 instance_16_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_612.
Transparent Child1Stable.word_29 global_word_613.
Lemma instance_16_word_29 v : Child1Stable.word_29 (instance_16_leaves v) = global_word_613 v.
Proof. unfold Child1Stable.word_29, global_word_613, Child1Stable.closed_word_29, global_closed_613, Child1Stable.expr_word_29, global_expr_613.
 rewrite instance_16_word_25 instance_16_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_613.
Transparent Child1Stable.word_30 global_word_614.
Lemma instance_16_word_30 v : Child1Stable.word_30 (instance_16_leaves v) = global_word_614 v.
Proof. unfold Child1Stable.word_30, global_word_614, Child1Stable.closed_word_30, global_closed_614, Child1Stable.expr_word_30, global_expr_614.
 rewrite instance_16_word_27 instance_16_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_614.
Transparent Child1Stable.word_31 global_word_615.
Lemma instance_16_word_31 v : Child1Stable.word_31 (instance_16_leaves v) = global_word_615 v.
Proof. unfold Child1Stable.word_31, global_word_615, Child1Stable.closed_word_31, global_closed_615, Child1Stable.expr_word_31, global_expr_615.
 rewrite instance_16_word_28 instance_16_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_615.
Transparent Child1Stable.word_32 global_word_616.
Lemma instance_16_word_32 v : Child1Stable.word_32 (instance_16_leaves v) = global_word_616 v.
Proof. unfold Child1Stable.word_32, global_word_616, Child1Stable.closed_word_32, global_closed_616, Child1Stable.expr_word_32, global_expr_616.
 rewrite instance_16_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_616.
Transparent Child1Stable.word_33 global_word_617.
Lemma instance_16_word_33 v : Child1Stable.word_33 (instance_16_leaves v) = global_word_617 v.
Proof. unfold Child1Stable.word_33, global_word_617, Child1Stable.closed_word_33, global_closed_617, Child1Stable.expr_word_33, global_expr_617.
 rewrite instance_16_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_617.
Transparent Child1Stable.word_5 global_word_618.
Lemma instance_16_word_5 v : Child1Stable.word_5 (instance_16_leaves v) = global_word_618 v.
Proof. unfold Child1Stable.word_5, global_word_618, Child1Stable.closed_word_5, global_closed_618, Child1Stable.expr_word_5, global_expr_618.
 rewrite instance_16_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_618.
Transparent Child1Stable.word_14 global_word_1697.
Lemma instance_16_word_14 v : Child1Stable.word_14 (instance_16_leaves v) = global_word_1697 v.
Proof. unfold Child1Stable.word_14, global_word_1697, Child1Stable.closed_word_14, global_closed_1697, Child1Stable.expr_word_14, global_expr_1697.
 rewrite instance_16_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1697.
Transparent Child1Stable.word_34 global_word_631.
Lemma instance_16_word_34 v : Child1Stable.word_34 (instance_16_leaves v) = global_word_631 v.
Proof. unfold Child1Stable.word_34, global_word_631, Child1Stable.closed_word_34, global_closed_631, Child1Stable.expr_word_34, global_expr_631.
 rewrite instance_16_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_631.
Transparent Child1Stable.word_6 global_word_632.
Lemma instance_16_word_6 v : Child1Stable.word_6 (instance_16_leaves v) = global_word_632 v.
Proof. unfold Child1Stable.word_6, global_word_632, Child1Stable.closed_word_6, global_closed_632, Child1Stable.expr_word_6, global_expr_632.
 rewrite instance_16_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_632.
Transparent Child1Stable.word_15 global_word_1698.
Lemma instance_16_word_15 v : Child1Stable.word_15 (instance_16_leaves v) = global_word_1698 v.
Proof. unfold Child1Stable.word_15, global_word_1698, Child1Stable.closed_word_15, global_closed_1698, Child1Stable.expr_word_15, global_expr_1698.
 rewrite instance_16_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1698.
Transparent Child1Stable.word_16 global_word_1699.
Lemma instance_16_word_16 v : Child1Stable.word_16 (instance_16_leaves v) = global_word_1699 v.
Proof. unfold Child1Stable.word_16, global_word_1699, Child1Stable.closed_word_16, global_closed_1699, Child1Stable.expr_word_16, global_expr_1699.
 rewrite instance_16_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1699.
Transparent Child1Stable.word_17 global_word_1700.
Lemma instance_16_word_17 v : Child1Stable.word_17 (instance_16_leaves v) = global_word_1700 v.
Proof. unfold Child1Stable.word_17, global_word_1700, Child1Stable.closed_word_17, global_closed_1700, Child1Stable.expr_word_17, global_expr_1700.
 rewrite instance_16_word_14 instance_16_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1700.
Transparent Child1Stable.word_18 global_word_1701.
Lemma instance_16_word_18 v : Child1Stable.word_18 (instance_16_leaves v) = global_word_1701 v.
Proof. unfold Child1Stable.word_18, global_word_1701, Child1Stable.closed_word_18, global_closed_1701, Child1Stable.expr_word_18, global_expr_1701.
 rewrite instance_16_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1701.
Transparent Child1Stable.word_19 global_word_1702.
Lemma instance_16_word_19 v : Child1Stable.word_19 (instance_16_leaves v) = global_word_1702 v.
Proof. unfold Child1Stable.word_19, global_word_1702, Child1Stable.closed_word_19, global_closed_1702, Child1Stable.expr_word_19, global_expr_1702.
 rewrite instance_16_word_13 instance_16_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1702.
Transparent Child1Stable.word_20 global_word_1704.
Lemma instance_16_word_20 v : Child1Stable.word_20 (instance_16_leaves v) = global_word_1704 v.
Proof. unfold Child1Stable.word_20, global_word_1704, Child1Stable.closed_word_20, global_closed_1704, Child1Stable.expr_word_20, global_expr_1704.
 rewrite instance_16_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1704.
Transparent Child1Stable.word_21 global_word_1705.
Lemma instance_16_word_21 v : Child1Stable.word_21 (instance_16_leaves v) = global_word_1705 v.
Proof. unfold Child1Stable.word_21, global_word_1705, Child1Stable.closed_word_21, global_closed_1705, Child1Stable.expr_word_21, global_expr_1705.
 rewrite instance_16_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1705.
Transparent Child1Stable.word_22 global_word_1706.
Lemma instance_16_word_22 v : Child1Stable.word_22 (instance_16_leaves v) = global_word_1706 v.
Proof. unfold Child1Stable.word_22, global_word_1706, Child1Stable.closed_word_22, global_closed_1706, Child1Stable.expr_word_22, global_expr_1706.
 rewrite instance_16_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1706.
Definition instance_17_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1735 v
| 0, 1 => global_word_1731 v
| 0, 2 => global_word_650 v
| 0, 3 => global_word_655 v
| 0, 4 => global_word_645 v
| 0, 5 => global_word_674 v
| 0, 6 => global_word_639 v
| 10, 5 => global_word_668 v
| 10, 6 => global_word_695 v
| 11, 5 => global_word_688 v
| 11, 6 => global_word_702 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1735.
Lemma instance_17_word_0 v : Child2Stable.word_0 (instance_17_leaves v) = global_word_1735 v.
Proof. unfold Child2Stable.word_0, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1735.
Transparent Child2Stable.word_1 global_word_1731.
Lemma instance_17_word_1 v : Child2Stable.word_1 (instance_17_leaves v) = global_word_1731 v.
Proof. unfold Child2Stable.word_1, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1731.
Transparent Child2Stable.word_2 global_word_650.
Lemma instance_17_word_2 v : Child2Stable.word_2 (instance_17_leaves v) = global_word_650 v.
Proof. unfold Child2Stable.word_2, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_650.
Transparent Child2Stable.word_3 global_word_655.
Lemma instance_17_word_3 v : Child2Stable.word_3 (instance_17_leaves v) = global_word_655 v.
Proof. unfold Child2Stable.word_3, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_655.
Transparent Child2Stable.word_4 global_word_645.
Lemma instance_17_word_4 v : Child2Stable.word_4 (instance_17_leaves v) = global_word_645 v.
Proof. unfold Child2Stable.word_4, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_645.
Transparent Child2Stable.word_5 global_word_674.
Lemma instance_17_word_5 v : Child2Stable.word_5 (instance_17_leaves v) = global_word_674 v.
Proof. unfold Child2Stable.word_5, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_674.
Transparent Child2Stable.word_6 global_word_639.
Lemma instance_17_word_6 v : Child2Stable.word_6 (instance_17_leaves v) = global_word_639 v.
Proof. unfold Child2Stable.word_6, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_639.
Transparent Child2Stable.port_10_5 global_word_668.
Lemma instance_17_port_10_5 v : Child2Stable.port_10_5 (instance_17_leaves v) = global_word_668 v.
Proof. unfold Child2Stable.port_10_5, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_668.
Transparent Child2Stable.port_10_6 global_word_695.
Lemma instance_17_port_10_6 v : Child2Stable.port_10_6 (instance_17_leaves v) = global_word_695 v.
Proof. unfold Child2Stable.port_10_6, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_695.
Transparent Child2Stable.port_11_5 global_word_688.
Lemma instance_17_port_11_5 v : Child2Stable.port_11_5 (instance_17_leaves v) = global_word_688 v.
Proof. unfold Child2Stable.port_11_5, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_688.
Transparent Child2Stable.port_11_6 global_word_702.
Lemma instance_17_port_11_6 v : Child2Stable.port_11_6 (instance_17_leaves v) = global_word_702 v.
Proof. unfold Child2Stable.port_11_6, instance_17_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_702.
Transparent Child2Stable.word_12 global_word_1708.
Lemma instance_17_word_12 v : Child2Stable.word_12 (instance_17_leaves v) = global_word_1708 v.
Proof. unfold Child2Stable.word_12, global_word_1708, Child2Stable.closed_word_12, global_closed_1708, Child2Stable.expr_word_12, global_expr_1708.
 rewrite instance_17_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1708.
Transparent Child2Stable.word_13 global_word_1709.
Lemma instance_17_word_13 v : Child2Stable.word_13 (instance_17_leaves v) = global_word_1709 v.
Proof. unfold Child2Stable.word_13, global_word_1709, Child2Stable.closed_word_13, global_closed_1709, Child2Stable.expr_word_13, global_expr_1709.
 rewrite instance_17_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1709.
Transparent Child2Stable.word_14 global_word_1710.
Lemma instance_17_word_14 v : Child2Stable.word_14 (instance_17_leaves v) = global_word_1710 v.
Proof. unfold Child2Stable.word_14, global_word_1710, Child2Stable.closed_word_14, global_closed_1710, Child2Stable.expr_word_14, global_expr_1710.
 rewrite instance_17_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1710.
Transparent Child2Stable.word_15 global_word_1711.
Lemma instance_17_word_15 v : Child2Stable.word_15 (instance_17_leaves v) = global_word_1711 v.
Proof. unfold Child2Stable.word_15, global_word_1711, Child2Stable.closed_word_15, global_closed_1711, Child2Stable.expr_word_15, global_expr_1711.
 rewrite instance_17_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1711.
Transparent Child2Stable.word_16 global_word_1712.
Lemma instance_17_word_16 v : Child2Stable.word_16 (instance_17_leaves v) = global_word_1712 v.
Proof. unfold Child2Stable.word_16, global_word_1712, Child2Stable.closed_word_16, global_closed_1712, Child2Stable.expr_word_16, global_expr_1712.
 rewrite instance_17_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1712.
Transparent Child2Stable.word_17 global_word_1713.
Lemma instance_17_word_17 v : Child2Stable.word_17 (instance_17_leaves v) = global_word_1713 v.
Proof. unfold Child2Stable.word_17, global_word_1713, Child2Stable.closed_word_17, global_closed_1713, Child2Stable.expr_word_17, global_expr_1713.
 rewrite instance_17_word_12 instance_17_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1713.
Transparent Child2Stable.word_18 global_word_1714.
Lemma instance_17_word_18 v : Child2Stable.word_18 (instance_17_leaves v) = global_word_1714 v.
Proof. unfold Child2Stable.word_18, global_word_1714, Child2Stable.closed_word_18, global_closed_1714, Child2Stable.expr_word_18, global_expr_1714.
 rewrite instance_17_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1714.
Transparent Child2Stable.word_19 global_word_1715.
Lemma instance_17_word_19 v : Child2Stable.word_19 (instance_17_leaves v) = global_word_1715 v.
Proof. unfold Child2Stable.word_19, global_word_1715, Child2Stable.closed_word_19, global_closed_1715, Child2Stable.expr_word_19, global_expr_1715.
 rewrite instance_17_word_14 instance_17_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1715.
Transparent Child2Stable.word_20 global_word_1716.
Lemma instance_17_word_20 v : Child2Stable.word_20 (instance_17_leaves v) = global_word_1716 v.
Proof. unfold Child2Stable.word_20, global_word_1716, Child2Stable.closed_word_20, global_closed_1716, Child2Stable.expr_word_20, global_expr_1716.
 rewrite instance_17_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1716.
Transparent Child2Stable.word_21 global_word_1717.
Lemma instance_17_word_21 v : Child2Stable.word_21 (instance_17_leaves v) = global_word_1717 v.
Proof. unfold Child2Stable.word_21, global_word_1717, Child2Stable.closed_word_21, global_closed_1717, Child2Stable.expr_word_21, global_expr_1717.
 rewrite instance_17_word_15 instance_17_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1717.
Transparent Child2Stable.word_22 global_word_1718.
Lemma instance_17_word_22 v : Child2Stable.word_22 (instance_17_leaves v) = global_word_1718 v.
Proof. unfold Child2Stable.word_22, global_word_1718, Child2Stable.closed_word_22, global_closed_1718, Child2Stable.expr_word_22, global_expr_1718.
 rewrite instance_17_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1718.
Transparent Child2Stable.word_23 global_word_1719.
Lemma instance_17_word_23 v : Child2Stable.word_23 (instance_17_leaves v) = global_word_1719 v.
Proof. unfold Child2Stable.word_23, global_word_1719, Child2Stable.closed_word_23, global_closed_1719, Child2Stable.expr_word_23, global_expr_1719.
 rewrite instance_17_word_16 instance_17_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1719.
Transparent Child2Stable.word_24 global_word_1720.
Lemma instance_17_word_24 v : Child2Stable.word_24 (instance_17_leaves v) = global_word_1720 v.
Proof. unfold Child2Stable.word_24, global_word_1720, Child2Stable.closed_word_24, global_closed_1720, Child2Stable.expr_word_24, global_expr_1720.
 rewrite instance_17_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1720.
Transparent Child2Stable.word_41 global_word_689.
Lemma instance_17_word_41 v : Child2Stable.word_41 (instance_17_leaves v) = global_word_689 v.
Proof. unfold Child2Stable.word_41, global_word_689, Child2Stable.closed_word_41, global_closed_689, Child2Stable.expr_word_41, global_expr_689.
 rewrite instance_17_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_689.
Transparent Child2Stable.word_7 global_word_690.
Lemma instance_17_word_7 v : Child2Stable.word_7 (instance_17_leaves v) = global_word_690 v.
Proof. unfold Child2Stable.word_7, global_word_690, Child2Stable.closed_word_7, global_closed_690, Child2Stable.expr_word_7, global_expr_690.
 rewrite instance_17_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_690.
Transparent Child2Stable.word_25 global_word_1721.
Lemma instance_17_word_25 v : Child2Stable.word_25 (instance_17_leaves v) = global_word_1721 v.
Proof. unfold Child2Stable.word_25, global_word_1721, Child2Stable.closed_word_25, global_closed_1721, Child2Stable.expr_word_25, global_expr_1721.
 rewrite instance_17_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1721.
Transparent Child2Stable.word_42 global_word_696.
Lemma instance_17_word_42 v : Child2Stable.word_42 (instance_17_leaves v) = global_word_696 v.
Proof. unfold Child2Stable.word_42, global_word_696, Child2Stable.closed_word_42, global_closed_696, Child2Stable.expr_word_42, global_expr_696.
 rewrite instance_17_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_696.
Transparent Child2Stable.word_8 global_word_697.
Lemma instance_17_word_8 v : Child2Stable.word_8 (instance_17_leaves v) = global_word_697 v.
Proof. unfold Child2Stable.word_8, global_word_697, Child2Stable.closed_word_8, global_closed_697, Child2Stable.expr_word_8, global_expr_697.
 rewrite instance_17_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_697.
Transparent Child2Stable.word_26 global_word_1722.
Lemma instance_17_word_26 v : Child2Stable.word_26 (instance_17_leaves v) = global_word_1722 v.
Proof. unfold Child2Stable.word_26, global_word_1722, Child2Stable.closed_word_26, global_closed_1722, Child2Stable.expr_word_26, global_expr_1722.
 rewrite instance_17_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1722.
Transparent Child2Stable.word_27 global_word_1723.
Lemma instance_17_word_27 v : Child2Stable.word_27 (instance_17_leaves v) = global_word_1723 v.
Proof. unfold Child2Stable.word_27, global_word_1723, Child2Stable.closed_word_27, global_closed_1723, Child2Stable.expr_word_27, global_expr_1723.
 rewrite instance_17_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1723.
Transparent Child2Stable.word_43 global_word_703.
Lemma instance_17_word_43 v : Child2Stable.word_43 (instance_17_leaves v) = global_word_703 v.
Proof. unfold Child2Stable.word_43, global_word_703, Child2Stable.closed_word_43, global_closed_703, Child2Stable.expr_word_43, global_expr_703.
 rewrite instance_17_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_703.
Transparent Child2Stable.word_9 global_word_704.
Lemma instance_17_word_9 v : Child2Stable.word_9 (instance_17_leaves v) = global_word_704 v.
Proof. unfold Child2Stable.word_9, global_word_704, Child2Stable.closed_word_9, global_closed_704, Child2Stable.expr_word_9, global_expr_704.
 rewrite instance_17_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_704.
Transparent Child2Stable.word_28 global_word_1724.
Lemma instance_17_word_28 v : Child2Stable.word_28 (instance_17_leaves v) = global_word_1724 v.
Proof. unfold Child2Stable.word_28, global_word_1724, Child2Stable.closed_word_28, global_closed_1724, Child2Stable.expr_word_28, global_expr_1724.
 rewrite instance_17_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1724.
Transparent Child2Stable.word_29 global_word_1725.
Lemma instance_17_word_29 v : Child2Stable.word_29 (instance_17_leaves v) = global_word_1725 v.
Proof. unfold Child2Stable.word_29, global_word_1725, Child2Stable.closed_word_29, global_closed_1725, Child2Stable.expr_word_29, global_expr_1725.
 rewrite instance_17_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1725.
Transparent Child2Stable.word_30 global_word_1726.
Lemma instance_17_word_30 v : Child2Stable.word_30 (instance_17_leaves v) = global_word_1726 v.
Proof. unfold Child2Stable.word_30, global_word_1726, Child2Stable.closed_word_30, global_closed_1726, Child2Stable.expr_word_30, global_expr_1726.
 rewrite instance_17_word_25 instance_17_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1726.
Transparent Child2Stable.word_31 global_word_1727.
Lemma instance_17_word_31 v : Child2Stable.word_31 (instance_17_leaves v) = global_word_1727 v.
Proof. unfold Child2Stable.word_31, global_word_1727, Child2Stable.closed_word_31, global_closed_1727, Child2Stable.expr_word_31, global_expr_1727.
 rewrite instance_17_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1727.
Transparent Child2Stable.word_32 global_word_1728.
Lemma instance_17_word_32 v : Child2Stable.word_32 (instance_17_leaves v) = global_word_1728 v.
Proof. unfold Child2Stable.word_32, global_word_1728, Child2Stable.closed_word_32, global_closed_1728, Child2Stable.expr_word_32, global_expr_1728.
 rewrite instance_17_word_29 instance_17_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1728.
Transparent Child2Stable.word_33 global_word_1729.
Lemma instance_17_word_33 v : Child2Stable.word_33 (instance_17_leaves v) = global_word_1729 v.
Proof. unfold Child2Stable.word_33, global_word_1729, Child2Stable.closed_word_33, global_closed_1729, Child2Stable.expr_word_33, global_expr_1729.
 rewrite instance_17_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1729.
Transparent Child2Stable.word_34 global_word_1730.
Lemma instance_17_word_34 v : Child2Stable.word_34 (instance_17_leaves v) = global_word_1730 v.
Proof. unfold Child2Stable.word_34, global_word_1730, Child2Stable.closed_word_34, global_closed_1730, Child2Stable.expr_word_34, global_expr_1730.
 rewrite instance_17_word_24 instance_17_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1730.
Transparent Child2Stable.word_35 global_word_1732.
Lemma instance_17_word_35 v : Child2Stable.word_35 (instance_17_leaves v) = global_word_1732 v.
Proof. unfold Child2Stable.word_35, global_word_1732, Child2Stable.closed_word_35, global_closed_1732, Child2Stable.expr_word_35, global_expr_1732.
 rewrite instance_17_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1732.
Transparent Child2Stable.word_36 global_word_1733.
Lemma instance_17_word_36 v : Child2Stable.word_36 (instance_17_leaves v) = global_word_1733 v.
Proof. unfold Child2Stable.word_36, global_word_1733, Child2Stable.closed_word_36, global_closed_1733, Child2Stable.expr_word_36, global_expr_1733.
 rewrite instance_17_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1733.
Transparent Child2Stable.word_37 global_word_1734.
Lemma instance_17_word_37 v : Child2Stable.word_37 (instance_17_leaves v) = global_word_1734 v.
Proof. unfold Child2Stable.word_37, global_word_1734, Child2Stable.closed_word_37, global_closed_1734, Child2Stable.expr_word_37, global_expr_1734.
 rewrite instance_17_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1734.
Transparent Child2Stable.word_38 global_word_669.
Lemma instance_17_word_38 v : Child2Stable.word_38 (instance_17_leaves v) = global_word_669 v.
Proof. unfold Child2Stable.word_38, global_word_669, Child2Stable.closed_word_38, global_closed_669, Child2Stable.expr_word_38, global_expr_669.
 rewrite instance_17_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_669.
Transparent Child2Stable.word_39 global_word_675.
Lemma instance_17_word_39 v : Child2Stable.word_39 (instance_17_leaves v) = global_word_675 v.
Proof. unfold Child2Stable.word_39, global_word_675, Child2Stable.closed_word_39, global_closed_675, Child2Stable.expr_word_39, global_expr_675.
 rewrite instance_17_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_675.
Transparent Child2Stable.word_40 global_word_640.
Lemma instance_17_word_40 v : Child2Stable.word_40 (instance_17_leaves v) = global_word_640 v.
Proof. unfold Child2Stable.word_40, global_word_640, Child2Stable.closed_word_40, global_closed_640, Child2Stable.expr_word_40, global_expr_640.
 rewrite instance_17_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_640.
Transparent Child2Stable.port_10_0 global_word_1736.
Lemma instance_17_port_10_0 v : Child2Stable.port_10_0 (instance_17_leaves v) = global_word_1736 v.
Proof. unfold Child2Stable.port_10_0, global_word_1736, Child2Stable.closed_port_10_0, global_closed_1736, Child2Stable.expr_port_10_0, global_expr_1736.
 rewrite instance_17_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1736.
Transparent Child2Stable.port_10_1 global_word_1737.
Lemma instance_17_port_10_1 v : Child2Stable.port_10_1 (instance_17_leaves v) = global_word_1737 v.
Proof. unfold Child2Stable.port_10_1, global_word_1737, Child2Stable.closed_port_10_1, global_closed_1737, Child2Stable.expr_port_10_1, global_expr_1737.
 rewrite instance_17_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1737.
Transparent Child2Stable.port_10_2 global_word_651.
Lemma instance_17_port_10_2 v : Child2Stable.port_10_2 (instance_17_leaves v) = global_word_651 v.
Proof. unfold Child2Stable.port_10_2, global_word_651, Child2Stable.closed_port_10_2, global_closed_651, Child2Stable.expr_port_10_2, global_expr_651.
 rewrite instance_17_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_651.
Transparent Child2Stable.port_10_3 global_word_656.
Lemma instance_17_port_10_3 v : Child2Stable.port_10_3 (instance_17_leaves v) = global_word_656 v.
Proof. unfold Child2Stable.port_10_3, global_word_656, Child2Stable.closed_port_10_3, global_closed_656, Child2Stable.expr_port_10_3, global_expr_656.
 rewrite instance_17_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_656.
Transparent Child2Stable.port_10_4 global_word_646.
Lemma instance_17_port_10_4 v : Child2Stable.port_10_4 (instance_17_leaves v) = global_word_646 v.
Proof. unfold Child2Stable.port_10_4, global_word_646, Child2Stable.closed_port_10_4, global_closed_646, Child2Stable.expr_port_10_4, global_expr_646.
 rewrite instance_17_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_646.
Transparent Child2Stable.port_11_0 global_word_1738.
Lemma instance_17_port_11_0 v : Child2Stable.port_11_0 (instance_17_leaves v) = global_word_1738 v.
Proof. unfold Child2Stable.port_11_0, global_word_1738, Child2Stable.closed_port_11_0, global_closed_1738, Child2Stable.expr_port_11_0, global_expr_1738.
 rewrite instance_17_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1738.
Transparent Child2Stable.port_11_1 global_word_1739.
Lemma instance_17_port_11_1 v : Child2Stable.port_11_1 (instance_17_leaves v) = global_word_1739 v.
Proof. unfold Child2Stable.port_11_1, global_word_1739, Child2Stable.closed_port_11_1, global_closed_1739, Child2Stable.expr_port_11_1, global_expr_1739.
 rewrite instance_17_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1739.
Transparent Child2Stable.port_11_2 global_word_670.
Lemma instance_17_port_11_2 v : Child2Stable.port_11_2 (instance_17_leaves v) = global_word_670 v.
Proof. unfold Child2Stable.port_11_2, global_word_670, Child2Stable.closed_port_11_2, global_closed_670, Child2Stable.expr_port_11_2, global_expr_670.
 rewrite instance_17_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_670.
Transparent Child2Stable.port_11_3 global_word_676.
Lemma instance_17_port_11_3 v : Child2Stable.port_11_3 (instance_17_leaves v) = global_word_676 v.
Proof. unfold Child2Stable.port_11_3, global_word_676, Child2Stable.closed_port_11_3, global_closed_676, Child2Stable.expr_port_11_3, global_expr_676.
 rewrite instance_17_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_676.
Transparent Child2Stable.port_11_4 global_word_641.
Lemma instance_17_port_11_4 v : Child2Stable.port_11_4 (instance_17_leaves v) = global_word_641 v.
Proof. unfold Child2Stable.port_11_4, global_word_641, Child2Stable.closed_port_11_4, global_closed_641, Child2Stable.expr_port_11_4, global_expr_641.
 rewrite instance_17_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_641.
Definition instance_18_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1757 v
| 0, 1 => global_word_1753 v
| 0, 2 => global_word_652 v
| 0, 3 => global_word_657 v
| 0, 4 => global_word_647 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1757.
Lemma instance_18_word_0 v : Child1Stable.word_0 (instance_18_leaves v) = global_word_1757 v.
Proof. unfold Child1Stable.word_0, instance_18_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1757.
Transparent Child1Stable.word_1 global_word_1753.
Lemma instance_18_word_1 v : Child1Stable.word_1 (instance_18_leaves v) = global_word_1753 v.
Proof. unfold Child1Stable.word_1, instance_18_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1753.
Transparent Child1Stable.word_2 global_word_652.
Lemma instance_18_word_2 v : Child1Stable.word_2 (instance_18_leaves v) = global_word_652 v.
Proof. unfold Child1Stable.word_2, instance_18_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_652.
Transparent Child1Stable.word_3 global_word_657.
Lemma instance_18_word_3 v : Child1Stable.word_3 (instance_18_leaves v) = global_word_657 v.
Proof. unfold Child1Stable.word_3, instance_18_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_657.
Transparent Child1Stable.word_4 global_word_647.
Lemma instance_18_word_4 v : Child1Stable.word_4 (instance_18_leaves v) = global_word_647 v.
Proof. unfold Child1Stable.word_4, instance_18_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_647.
Transparent Child1Stable.word_7 global_word_1740.
Lemma instance_18_word_7 v : Child1Stable.word_7 (instance_18_leaves v) = global_word_1740 v.
Proof. unfold Child1Stable.word_7, global_word_1740, Child1Stable.closed_word_7, global_closed_1740, Child1Stable.expr_word_7, global_expr_1740.
 rewrite instance_18_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1740.
Transparent Child1Stable.word_8 global_word_1741.
Lemma instance_18_word_8 v : Child1Stable.word_8 (instance_18_leaves v) = global_word_1741 v.
Proof. unfold Child1Stable.word_8, global_word_1741, Child1Stable.closed_word_8, global_closed_1741, Child1Stable.expr_word_8, global_expr_1741.
 rewrite instance_18_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1741.
Transparent Child1Stable.word_9 global_word_1742.
Lemma instance_18_word_9 v : Child1Stable.word_9 (instance_18_leaves v) = global_word_1742 v.
Proof. unfold Child1Stable.word_9, global_word_1742, Child1Stable.closed_word_9, global_closed_1742, Child1Stable.expr_word_9, global_expr_1742.
 rewrite instance_18_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1742.
Transparent Child1Stable.word_10 global_word_1743.
Lemma instance_18_word_10 v : Child1Stable.word_10 (instance_18_leaves v) = global_word_1743 v.
Proof. unfold Child1Stable.word_10, global_word_1743, Child1Stable.closed_word_10, global_closed_1743, Child1Stable.expr_word_10, global_expr_1743.
 rewrite instance_18_word_7 instance_18_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1743.
Transparent Child1Stable.word_11 global_word_1744.
Lemma instance_18_word_11 v : Child1Stable.word_11 (instance_18_leaves v) = global_word_1744 v.
Proof. unfold Child1Stable.word_11, global_word_1744, Child1Stable.closed_word_11, global_closed_1744, Child1Stable.expr_word_11, global_expr_1744.
 rewrite instance_18_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1744.
Transparent Child1Stable.word_12 global_word_1745.
Lemma instance_18_word_12 v : Child1Stable.word_12 (instance_18_leaves v) = global_word_1745 v.
Proof. unfold Child1Stable.word_12, global_word_1745, Child1Stable.closed_word_12, global_closed_1745, Child1Stable.expr_word_12, global_expr_1745.
 rewrite instance_18_word_9 instance_18_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1745.
Transparent Child1Stable.word_13 global_word_1746.
Lemma instance_18_word_13 v : Child1Stable.word_13 (instance_18_leaves v) = global_word_1746 v.
Proof. unfold Child1Stable.word_13, global_word_1746, Child1Stable.closed_word_13, global_closed_1746, Child1Stable.expr_word_13, global_expr_1746.
 rewrite instance_18_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1746.
Transparent Child1Stable.word_25 global_word_648.
Lemma instance_18_word_25 v : Child1Stable.word_25 (instance_18_leaves v) = global_word_648 v.
Proof. unfold Child1Stable.word_25, global_word_648, Child1Stable.closed_word_25, global_closed_648, Child1Stable.expr_word_25, global_expr_648.
 rewrite instance_18_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_648.
Transparent Child1Stable.word_23 global_word_653.
Lemma instance_18_word_23 v : Child1Stable.word_23 (instance_18_leaves v) = global_word_653 v.
Proof. unfold Child1Stable.word_23, global_word_653, Child1Stable.closed_word_23, global_closed_653, Child1Stable.expr_word_23, global_expr_653.
 rewrite instance_18_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_653.
Transparent Child1Stable.word_24 global_word_658.
Lemma instance_18_word_24 v : Child1Stable.word_24 (instance_18_leaves v) = global_word_658 v.
Proof. unfold Child1Stable.word_24, global_word_658, Child1Stable.closed_word_24, global_closed_658, Child1Stable.expr_word_24, global_expr_658.
 rewrite instance_18_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_658.
Transparent Child1Stable.word_26 global_word_659.
Lemma instance_18_word_26 v : Child1Stable.word_26 (instance_18_leaves v) = global_word_659 v.
Proof. unfold Child1Stable.word_26, global_word_659, Child1Stable.closed_word_26, global_closed_659, Child1Stable.expr_word_26, global_expr_659.
 rewrite instance_18_word_23 instance_18_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_659.
Transparent Child1Stable.word_28 global_word_660.
Lemma instance_18_word_28 v : Child1Stable.word_28 (instance_18_leaves v) = global_word_660 v.
Proof. unfold Child1Stable.word_28, global_word_660, Child1Stable.closed_word_28, global_closed_660, Child1Stable.expr_word_28, global_expr_660.
 rewrite instance_18_word_25 instance_18_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_660.
Transparent Child1Stable.word_27 global_word_661.
Lemma instance_18_word_27 v : Child1Stable.word_27 (instance_18_leaves v) = global_word_661 v.
Proof. unfold Child1Stable.word_27, global_word_661, Child1Stable.closed_word_27, global_closed_661, Child1Stable.expr_word_27, global_expr_661.
 rewrite instance_18_word_23 instance_18_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_661.
Transparent Child1Stable.word_29 global_word_662.
Lemma instance_18_word_29 v : Child1Stable.word_29 (instance_18_leaves v) = global_word_662 v.
Proof. unfold Child1Stable.word_29, global_word_662, Child1Stable.closed_word_29, global_closed_662, Child1Stable.expr_word_29, global_expr_662.
 rewrite instance_18_word_25 instance_18_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_662.
Transparent Child1Stable.word_30 global_word_663.
Lemma instance_18_word_30 v : Child1Stable.word_30 (instance_18_leaves v) = global_word_663 v.
Proof. unfold Child1Stable.word_30, global_word_663, Child1Stable.closed_word_30, global_closed_663, Child1Stable.expr_word_30, global_expr_663.
 rewrite instance_18_word_27 instance_18_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_663.
Transparent Child1Stable.word_31 global_word_664.
Lemma instance_18_word_31 v : Child1Stable.word_31 (instance_18_leaves v) = global_word_664 v.
Proof. unfold Child1Stable.word_31, global_word_664, Child1Stable.closed_word_31, global_closed_664, Child1Stable.expr_word_31, global_expr_664.
 rewrite instance_18_word_28 instance_18_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_664.
Transparent Child1Stable.word_32 global_word_665.
Lemma instance_18_word_32 v : Child1Stable.word_32 (instance_18_leaves v) = global_word_665 v.
Proof. unfold Child1Stable.word_32, global_word_665, Child1Stable.closed_word_32, global_closed_665, Child1Stable.expr_word_32, global_expr_665.
 rewrite instance_18_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_665.
Transparent Child1Stable.word_33 global_word_666.
Lemma instance_18_word_33 v : Child1Stable.word_33 (instance_18_leaves v) = global_word_666 v.
Proof. unfold Child1Stable.word_33, global_word_666, Child1Stable.closed_word_33, global_closed_666, Child1Stable.expr_word_33, global_expr_666.
 rewrite instance_18_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_666.
Transparent Child1Stable.word_5 global_word_667.
Lemma instance_18_word_5 v : Child1Stable.word_5 (instance_18_leaves v) = global_word_667 v.
Proof. unfold Child1Stable.word_5, global_word_667, Child1Stable.closed_word_5, global_closed_667, Child1Stable.expr_word_5, global_expr_667.
 rewrite instance_18_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_667.
Transparent Child1Stable.word_14 global_word_1747.
Lemma instance_18_word_14 v : Child1Stable.word_14 (instance_18_leaves v) = global_word_1747 v.
Proof. unfold Child1Stable.word_14, global_word_1747, Child1Stable.closed_word_14, global_closed_1747, Child1Stable.expr_word_14, global_expr_1747.
 rewrite instance_18_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1747.
Transparent Child1Stable.word_34 global_word_693.
Lemma instance_18_word_34 v : Child1Stable.word_34 (instance_18_leaves v) = global_word_693 v.
Proof. unfold Child1Stable.word_34, global_word_693, Child1Stable.closed_word_34, global_closed_693, Child1Stable.expr_word_34, global_expr_693.
 rewrite instance_18_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_693.
Transparent Child1Stable.word_6 global_word_694.
Lemma instance_18_word_6 v : Child1Stable.word_6 (instance_18_leaves v) = global_word_694 v.
Proof. unfold Child1Stable.word_6, global_word_694, Child1Stable.closed_word_6, global_closed_694, Child1Stable.expr_word_6, global_expr_694.
 rewrite instance_18_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_694.
Transparent Child1Stable.word_15 global_word_1748.
Lemma instance_18_word_15 v : Child1Stable.word_15 (instance_18_leaves v) = global_word_1748 v.
Proof. unfold Child1Stable.word_15, global_word_1748, Child1Stable.closed_word_15, global_closed_1748, Child1Stable.expr_word_15, global_expr_1748.
 rewrite instance_18_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1748.
Transparent Child1Stable.word_16 global_word_1749.
Lemma instance_18_word_16 v : Child1Stable.word_16 (instance_18_leaves v) = global_word_1749 v.
Proof. unfold Child1Stable.word_16, global_word_1749, Child1Stable.closed_word_16, global_closed_1749, Child1Stable.expr_word_16, global_expr_1749.
 rewrite instance_18_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1749.
Transparent Child1Stable.word_17 global_word_1750.
Lemma instance_18_word_17 v : Child1Stable.word_17 (instance_18_leaves v) = global_word_1750 v.
Proof. unfold Child1Stable.word_17, global_word_1750, Child1Stable.closed_word_17, global_closed_1750, Child1Stable.expr_word_17, global_expr_1750.
 rewrite instance_18_word_14 instance_18_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1750.
Transparent Child1Stable.word_18 global_word_1751.
Lemma instance_18_word_18 v : Child1Stable.word_18 (instance_18_leaves v) = global_word_1751 v.
Proof. unfold Child1Stable.word_18, global_word_1751, Child1Stable.closed_word_18, global_closed_1751, Child1Stable.expr_word_18, global_expr_1751.
 rewrite instance_18_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1751.
Transparent Child1Stable.word_19 global_word_1752.
Lemma instance_18_word_19 v : Child1Stable.word_19 (instance_18_leaves v) = global_word_1752 v.
Proof. unfold Child1Stable.word_19, global_word_1752, Child1Stable.closed_word_19, global_closed_1752, Child1Stable.expr_word_19, global_expr_1752.
 rewrite instance_18_word_13 instance_18_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1752.
Transparent Child1Stable.word_20 global_word_1754.
Lemma instance_18_word_20 v : Child1Stable.word_20 (instance_18_leaves v) = global_word_1754 v.
Proof. unfold Child1Stable.word_20, global_word_1754, Child1Stable.closed_word_20, global_closed_1754, Child1Stable.expr_word_20, global_expr_1754.
 rewrite instance_18_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1754.
Transparent Child1Stable.word_21 global_word_1755.
Lemma instance_18_word_21 v : Child1Stable.word_21 (instance_18_leaves v) = global_word_1755 v.
Proof. unfold Child1Stable.word_21, global_word_1755, Child1Stable.closed_word_21, global_closed_1755, Child1Stable.expr_word_21, global_expr_1755.
 rewrite instance_18_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1755.
Transparent Child1Stable.word_22 global_word_1756.
Lemma instance_18_word_22 v : Child1Stable.word_22 (instance_18_leaves v) = global_word_1756 v.
Proof. unfold Child1Stable.word_22, global_word_1756, Child1Stable.closed_word_22, global_closed_1756, Child1Stable.expr_word_22, global_expr_1756.
 rewrite instance_18_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1756.
Definition instance_19_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1775 v
| 0, 1 => global_word_1771 v
| 0, 2 => global_word_671 v
| 0, 3 => global_word_677 v
| 0, 4 => global_word_642 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1775.
Lemma instance_19_word_0 v : Child1Stable.word_0 (instance_19_leaves v) = global_word_1775 v.
Proof. unfold Child1Stable.word_0, instance_19_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1775.
Transparent Child1Stable.word_1 global_word_1771.
Lemma instance_19_word_1 v : Child1Stable.word_1 (instance_19_leaves v) = global_word_1771 v.
Proof. unfold Child1Stable.word_1, instance_19_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1771.
Transparent Child1Stable.word_2 global_word_671.
Lemma instance_19_word_2 v : Child1Stable.word_2 (instance_19_leaves v) = global_word_671 v.
Proof. unfold Child1Stable.word_2, instance_19_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_671.
Transparent Child1Stable.word_3 global_word_677.
Lemma instance_19_word_3 v : Child1Stable.word_3 (instance_19_leaves v) = global_word_677 v.
Proof. unfold Child1Stable.word_3, instance_19_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_677.
Transparent Child1Stable.word_4 global_word_642.
Lemma instance_19_word_4 v : Child1Stable.word_4 (instance_19_leaves v) = global_word_642 v.
Proof. unfold Child1Stable.word_4, instance_19_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_642.
Transparent Child1Stable.word_7 global_word_1758.
Lemma instance_19_word_7 v : Child1Stable.word_7 (instance_19_leaves v) = global_word_1758 v.
Proof. unfold Child1Stable.word_7, global_word_1758, Child1Stable.closed_word_7, global_closed_1758, Child1Stable.expr_word_7, global_expr_1758.
 rewrite instance_19_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1758.
Transparent Child1Stable.word_8 global_word_1759.
Lemma instance_19_word_8 v : Child1Stable.word_8 (instance_19_leaves v) = global_word_1759 v.
Proof. unfold Child1Stable.word_8, global_word_1759, Child1Stable.closed_word_8, global_closed_1759, Child1Stable.expr_word_8, global_expr_1759.
 rewrite instance_19_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1759.
Transparent Child1Stable.word_9 global_word_1760.
Lemma instance_19_word_9 v : Child1Stable.word_9 (instance_19_leaves v) = global_word_1760 v.
Proof. unfold Child1Stable.word_9, global_word_1760, Child1Stable.closed_word_9, global_closed_1760, Child1Stable.expr_word_9, global_expr_1760.
 rewrite instance_19_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1760.
Transparent Child1Stable.word_10 global_word_1761.
Lemma instance_19_word_10 v : Child1Stable.word_10 (instance_19_leaves v) = global_word_1761 v.
Proof. unfold Child1Stable.word_10, global_word_1761, Child1Stable.closed_word_10, global_closed_1761, Child1Stable.expr_word_10, global_expr_1761.
 rewrite instance_19_word_7 instance_19_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1761.
Transparent Child1Stable.word_11 global_word_1762.
Lemma instance_19_word_11 v : Child1Stable.word_11 (instance_19_leaves v) = global_word_1762 v.
Proof. unfold Child1Stable.word_11, global_word_1762, Child1Stable.closed_word_11, global_closed_1762, Child1Stable.expr_word_11, global_expr_1762.
 rewrite instance_19_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1762.
Transparent Child1Stable.word_12 global_word_1763.
Lemma instance_19_word_12 v : Child1Stable.word_12 (instance_19_leaves v) = global_word_1763 v.
Proof. unfold Child1Stable.word_12, global_word_1763, Child1Stable.closed_word_12, global_closed_1763, Child1Stable.expr_word_12, global_expr_1763.
 rewrite instance_19_word_9 instance_19_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1763.
Transparent Child1Stable.word_13 global_word_1764.
Lemma instance_19_word_13 v : Child1Stable.word_13 (instance_19_leaves v) = global_word_1764 v.
Proof. unfold Child1Stable.word_13, global_word_1764, Child1Stable.closed_word_13, global_closed_1764, Child1Stable.expr_word_13, global_expr_1764.
 rewrite instance_19_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1764.
Transparent Child1Stable.word_25 global_word_643.
Lemma instance_19_word_25 v : Child1Stable.word_25 (instance_19_leaves v) = global_word_643 v.
Proof. unfold Child1Stable.word_25, global_word_643, Child1Stable.closed_word_25, global_closed_643, Child1Stable.expr_word_25, global_expr_643.
 rewrite instance_19_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_643.
Transparent Child1Stable.word_23 global_word_672.
Lemma instance_19_word_23 v : Child1Stable.word_23 (instance_19_leaves v) = global_word_672 v.
Proof. unfold Child1Stable.word_23, global_word_672, Child1Stable.closed_word_23, global_closed_672, Child1Stable.expr_word_23, global_expr_672.
 rewrite instance_19_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_672.
Transparent Child1Stable.word_24 global_word_678.
Lemma instance_19_word_24 v : Child1Stable.word_24 (instance_19_leaves v) = global_word_678 v.
Proof. unfold Child1Stable.word_24, global_word_678, Child1Stable.closed_word_24, global_closed_678, Child1Stable.expr_word_24, global_expr_678.
 rewrite instance_19_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_678.
Transparent Child1Stable.word_26 global_word_679.
Lemma instance_19_word_26 v : Child1Stable.word_26 (instance_19_leaves v) = global_word_679 v.
Proof. unfold Child1Stable.word_26, global_word_679, Child1Stable.closed_word_26, global_closed_679, Child1Stable.expr_word_26, global_expr_679.
 rewrite instance_19_word_23 instance_19_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_679.
Transparent Child1Stable.word_28 global_word_680.
Lemma instance_19_word_28 v : Child1Stable.word_28 (instance_19_leaves v) = global_word_680 v.
Proof. unfold Child1Stable.word_28, global_word_680, Child1Stable.closed_word_28, global_closed_680, Child1Stable.expr_word_28, global_expr_680.
 rewrite instance_19_word_25 instance_19_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_680.
Transparent Child1Stable.word_27 global_word_681.
Lemma instance_19_word_27 v : Child1Stable.word_27 (instance_19_leaves v) = global_word_681 v.
Proof. unfold Child1Stable.word_27, global_word_681, Child1Stable.closed_word_27, global_closed_681, Child1Stable.expr_word_27, global_expr_681.
 rewrite instance_19_word_23 instance_19_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_681.
Transparent Child1Stable.word_29 global_word_682.
Lemma instance_19_word_29 v : Child1Stable.word_29 (instance_19_leaves v) = global_word_682 v.
Proof. unfold Child1Stable.word_29, global_word_682, Child1Stable.closed_word_29, global_closed_682, Child1Stable.expr_word_29, global_expr_682.
 rewrite instance_19_word_25 instance_19_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_682.
Transparent Child1Stable.word_30 global_word_683.
Lemma instance_19_word_30 v : Child1Stable.word_30 (instance_19_leaves v) = global_word_683 v.
Proof. unfold Child1Stable.word_30, global_word_683, Child1Stable.closed_word_30, global_closed_683, Child1Stable.expr_word_30, global_expr_683.
 rewrite instance_19_word_27 instance_19_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_683.
Transparent Child1Stable.word_31 global_word_684.
Lemma instance_19_word_31 v : Child1Stable.word_31 (instance_19_leaves v) = global_word_684 v.
Proof. unfold Child1Stable.word_31, global_word_684, Child1Stable.closed_word_31, global_closed_684, Child1Stable.expr_word_31, global_expr_684.
 rewrite instance_19_word_28 instance_19_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_684.
Transparent Child1Stable.word_32 global_word_685.
Lemma instance_19_word_32 v : Child1Stable.word_32 (instance_19_leaves v) = global_word_685 v.
Proof. unfold Child1Stable.word_32, global_word_685, Child1Stable.closed_word_32, global_closed_685, Child1Stable.expr_word_32, global_expr_685.
 rewrite instance_19_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_685.
Transparent Child1Stable.word_33 global_word_686.
Lemma instance_19_word_33 v : Child1Stable.word_33 (instance_19_leaves v) = global_word_686 v.
Proof. unfold Child1Stable.word_33, global_word_686, Child1Stable.closed_word_33, global_closed_686, Child1Stable.expr_word_33, global_expr_686.
 rewrite instance_19_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_686.
Transparent Child1Stable.word_5 global_word_687.
Lemma instance_19_word_5 v : Child1Stable.word_5 (instance_19_leaves v) = global_word_687 v.
Proof. unfold Child1Stable.word_5, global_word_687, Child1Stable.closed_word_5, global_closed_687, Child1Stable.expr_word_5, global_expr_687.
 rewrite instance_19_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_687.
Transparent Child1Stable.word_14 global_word_1765.
Lemma instance_19_word_14 v : Child1Stable.word_14 (instance_19_leaves v) = global_word_1765 v.
Proof. unfold Child1Stable.word_14, global_word_1765, Child1Stable.closed_word_14, global_closed_1765, Child1Stable.expr_word_14, global_expr_1765.
 rewrite instance_19_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1765.
Transparent Child1Stable.word_34 global_word_700.
Lemma instance_19_word_34 v : Child1Stable.word_34 (instance_19_leaves v) = global_word_700 v.
Proof. unfold Child1Stable.word_34, global_word_700, Child1Stable.closed_word_34, global_closed_700, Child1Stable.expr_word_34, global_expr_700.
 rewrite instance_19_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_700.
Transparent Child1Stable.word_6 global_word_701.
Lemma instance_19_word_6 v : Child1Stable.word_6 (instance_19_leaves v) = global_word_701 v.
Proof. unfold Child1Stable.word_6, global_word_701, Child1Stable.closed_word_6, global_closed_701, Child1Stable.expr_word_6, global_expr_701.
 rewrite instance_19_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_701.
Transparent Child1Stable.word_15 global_word_1766.
Lemma instance_19_word_15 v : Child1Stable.word_15 (instance_19_leaves v) = global_word_1766 v.
Proof. unfold Child1Stable.word_15, global_word_1766, Child1Stable.closed_word_15, global_closed_1766, Child1Stable.expr_word_15, global_expr_1766.
 rewrite instance_19_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1766.
Transparent Child1Stable.word_16 global_word_1767.
Lemma instance_19_word_16 v : Child1Stable.word_16 (instance_19_leaves v) = global_word_1767 v.
Proof. unfold Child1Stable.word_16, global_word_1767, Child1Stable.closed_word_16, global_closed_1767, Child1Stable.expr_word_16, global_expr_1767.
 rewrite instance_19_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1767.
Transparent Child1Stable.word_17 global_word_1768.
Lemma instance_19_word_17 v : Child1Stable.word_17 (instance_19_leaves v) = global_word_1768 v.
Proof. unfold Child1Stable.word_17, global_word_1768, Child1Stable.closed_word_17, global_closed_1768, Child1Stable.expr_word_17, global_expr_1768.
 rewrite instance_19_word_14 instance_19_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1768.
Transparent Child1Stable.word_18 global_word_1769.
Lemma instance_19_word_18 v : Child1Stable.word_18 (instance_19_leaves v) = global_word_1769 v.
Proof. unfold Child1Stable.word_18, global_word_1769, Child1Stable.closed_word_18, global_closed_1769, Child1Stable.expr_word_18, global_expr_1769.
 rewrite instance_19_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1769.
Transparent Child1Stable.word_19 global_word_1770.
Lemma instance_19_word_19 v : Child1Stable.word_19 (instance_19_leaves v) = global_word_1770 v.
Proof. unfold Child1Stable.word_19, global_word_1770, Child1Stable.closed_word_19, global_closed_1770, Child1Stable.expr_word_19, global_expr_1770.
 rewrite instance_19_word_13 instance_19_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1770.
Transparent Child1Stable.word_20 global_word_1772.
Lemma instance_19_word_20 v : Child1Stable.word_20 (instance_19_leaves v) = global_word_1772 v.
Proof. unfold Child1Stable.word_20, global_word_1772, Child1Stable.closed_word_20, global_closed_1772, Child1Stable.expr_word_20, global_expr_1772.
 rewrite instance_19_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1772.
Transparent Child1Stable.word_21 global_word_1773.
Lemma instance_19_word_21 v : Child1Stable.word_21 (instance_19_leaves v) = global_word_1773 v.
Proof. unfold Child1Stable.word_21, global_word_1773, Child1Stable.closed_word_21, global_closed_1773, Child1Stable.expr_word_21, global_expr_1773.
 rewrite instance_19_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1773.
Transparent Child1Stable.word_22 global_word_1774.
Lemma instance_19_word_22 v : Child1Stable.word_22 (instance_19_leaves v) = global_word_1774 v.
Proof. unfold Child1Stable.word_22, global_word_1774, Child1Stable.closed_word_22, global_closed_1774, Child1Stable.expr_word_22, global_expr_1774.
 rewrite instance_19_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1774.
Definition instance_20_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1803 v
| 0, 1 => global_word_1799 v
| 0, 2 => global_word_719 v
| 0, 3 => global_word_724 v
| 0, 4 => global_word_714 v
| 0, 5 => global_word_743 v
| 0, 6 => global_word_708 v
| 10, 5 => global_word_737 v
| 10, 6 => global_word_764 v
| 11, 5 => global_word_757 v
| 11, 6 => global_word_771 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1803.
Lemma instance_20_word_0 v : Child2Stable.word_0 (instance_20_leaves v) = global_word_1803 v.
Proof. unfold Child2Stable.word_0, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1803.
Transparent Child2Stable.word_1 global_word_1799.
Lemma instance_20_word_1 v : Child2Stable.word_1 (instance_20_leaves v) = global_word_1799 v.
Proof. unfold Child2Stable.word_1, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1799.
Transparent Child2Stable.word_2 global_word_719.
Lemma instance_20_word_2 v : Child2Stable.word_2 (instance_20_leaves v) = global_word_719 v.
Proof. unfold Child2Stable.word_2, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_719.
Transparent Child2Stable.word_3 global_word_724.
Lemma instance_20_word_3 v : Child2Stable.word_3 (instance_20_leaves v) = global_word_724 v.
Proof. unfold Child2Stable.word_3, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_724.
Transparent Child2Stable.word_4 global_word_714.
Lemma instance_20_word_4 v : Child2Stable.word_4 (instance_20_leaves v) = global_word_714 v.
Proof. unfold Child2Stable.word_4, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_714.
Transparent Child2Stable.word_5 global_word_743.
Lemma instance_20_word_5 v : Child2Stable.word_5 (instance_20_leaves v) = global_word_743 v.
Proof. unfold Child2Stable.word_5, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_743.
Transparent Child2Stable.word_6 global_word_708.
Lemma instance_20_word_6 v : Child2Stable.word_6 (instance_20_leaves v) = global_word_708 v.
Proof. unfold Child2Stable.word_6, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_708.
Transparent Child2Stable.port_10_5 global_word_737.
Lemma instance_20_port_10_5 v : Child2Stable.port_10_5 (instance_20_leaves v) = global_word_737 v.
Proof. unfold Child2Stable.port_10_5, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_737.
Transparent Child2Stable.port_10_6 global_word_764.
Lemma instance_20_port_10_6 v : Child2Stable.port_10_6 (instance_20_leaves v) = global_word_764 v.
Proof. unfold Child2Stable.port_10_6, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_764.
Transparent Child2Stable.port_11_5 global_word_757.
Lemma instance_20_port_11_5 v : Child2Stable.port_11_5 (instance_20_leaves v) = global_word_757 v.
Proof. unfold Child2Stable.port_11_5, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_757.
Transparent Child2Stable.port_11_6 global_word_771.
Lemma instance_20_port_11_6 v : Child2Stable.port_11_6 (instance_20_leaves v) = global_word_771 v.
Proof. unfold Child2Stable.port_11_6, instance_20_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_771.
Transparent Child2Stable.word_12 global_word_1776.
Lemma instance_20_word_12 v : Child2Stable.word_12 (instance_20_leaves v) = global_word_1776 v.
Proof. unfold Child2Stable.word_12, global_word_1776, Child2Stable.closed_word_12, global_closed_1776, Child2Stable.expr_word_12, global_expr_1776.
 rewrite instance_20_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1776.
Transparent Child2Stable.word_13 global_word_1777.
Lemma instance_20_word_13 v : Child2Stable.word_13 (instance_20_leaves v) = global_word_1777 v.
Proof. unfold Child2Stable.word_13, global_word_1777, Child2Stable.closed_word_13, global_closed_1777, Child2Stable.expr_word_13, global_expr_1777.
 rewrite instance_20_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1777.
Transparent Child2Stable.word_14 global_word_1778.
Lemma instance_20_word_14 v : Child2Stable.word_14 (instance_20_leaves v) = global_word_1778 v.
Proof. unfold Child2Stable.word_14, global_word_1778, Child2Stable.closed_word_14, global_closed_1778, Child2Stable.expr_word_14, global_expr_1778.
 rewrite instance_20_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1778.
Transparent Child2Stable.word_15 global_word_1779.
Lemma instance_20_word_15 v : Child2Stable.word_15 (instance_20_leaves v) = global_word_1779 v.
Proof. unfold Child2Stable.word_15, global_word_1779, Child2Stable.closed_word_15, global_closed_1779, Child2Stable.expr_word_15, global_expr_1779.
 rewrite instance_20_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1779.
Transparent Child2Stable.word_16 global_word_1780.
Lemma instance_20_word_16 v : Child2Stable.word_16 (instance_20_leaves v) = global_word_1780 v.
Proof. unfold Child2Stable.word_16, global_word_1780, Child2Stable.closed_word_16, global_closed_1780, Child2Stable.expr_word_16, global_expr_1780.
 rewrite instance_20_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1780.
Transparent Child2Stable.word_17 global_word_1781.
Lemma instance_20_word_17 v : Child2Stable.word_17 (instance_20_leaves v) = global_word_1781 v.
Proof. unfold Child2Stable.word_17, global_word_1781, Child2Stable.closed_word_17, global_closed_1781, Child2Stable.expr_word_17, global_expr_1781.
 rewrite instance_20_word_12 instance_20_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1781.
Transparent Child2Stable.word_18 global_word_1782.
Lemma instance_20_word_18 v : Child2Stable.word_18 (instance_20_leaves v) = global_word_1782 v.
Proof. unfold Child2Stable.word_18, global_word_1782, Child2Stable.closed_word_18, global_closed_1782, Child2Stable.expr_word_18, global_expr_1782.
 rewrite instance_20_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1782.
Transparent Child2Stable.word_19 global_word_1783.
Lemma instance_20_word_19 v : Child2Stable.word_19 (instance_20_leaves v) = global_word_1783 v.
Proof. unfold Child2Stable.word_19, global_word_1783, Child2Stable.closed_word_19, global_closed_1783, Child2Stable.expr_word_19, global_expr_1783.
 rewrite instance_20_word_14 instance_20_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1783.
Transparent Child2Stable.word_20 global_word_1784.
Lemma instance_20_word_20 v : Child2Stable.word_20 (instance_20_leaves v) = global_word_1784 v.
Proof. unfold Child2Stable.word_20, global_word_1784, Child2Stable.closed_word_20, global_closed_1784, Child2Stable.expr_word_20, global_expr_1784.
 rewrite instance_20_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1784.
Transparent Child2Stable.word_21 global_word_1785.
Lemma instance_20_word_21 v : Child2Stable.word_21 (instance_20_leaves v) = global_word_1785 v.
Proof. unfold Child2Stable.word_21, global_word_1785, Child2Stable.closed_word_21, global_closed_1785, Child2Stable.expr_word_21, global_expr_1785.
 rewrite instance_20_word_15 instance_20_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1785.
Transparent Child2Stable.word_22 global_word_1786.
Lemma instance_20_word_22 v : Child2Stable.word_22 (instance_20_leaves v) = global_word_1786 v.
Proof. unfold Child2Stable.word_22, global_word_1786, Child2Stable.closed_word_22, global_closed_1786, Child2Stable.expr_word_22, global_expr_1786.
 rewrite instance_20_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1786.
Transparent Child2Stable.word_23 global_word_1787.
Lemma instance_20_word_23 v : Child2Stable.word_23 (instance_20_leaves v) = global_word_1787 v.
Proof. unfold Child2Stable.word_23, global_word_1787, Child2Stable.closed_word_23, global_closed_1787, Child2Stable.expr_word_23, global_expr_1787.
 rewrite instance_20_word_16 instance_20_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1787.
Transparent Child2Stable.word_24 global_word_1788.
Lemma instance_20_word_24 v : Child2Stable.word_24 (instance_20_leaves v) = global_word_1788 v.
Proof. unfold Child2Stable.word_24, global_word_1788, Child2Stable.closed_word_24, global_closed_1788, Child2Stable.expr_word_24, global_expr_1788.
 rewrite instance_20_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1788.
Transparent Child2Stable.word_41 global_word_758.
Lemma instance_20_word_41 v : Child2Stable.word_41 (instance_20_leaves v) = global_word_758 v.
Proof. unfold Child2Stable.word_41, global_word_758, Child2Stable.closed_word_41, global_closed_758, Child2Stable.expr_word_41, global_expr_758.
 rewrite instance_20_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_758.
Transparent Child2Stable.word_7 global_word_759.
Lemma instance_20_word_7 v : Child2Stable.word_7 (instance_20_leaves v) = global_word_759 v.
Proof. unfold Child2Stable.word_7, global_word_759, Child2Stable.closed_word_7, global_closed_759, Child2Stable.expr_word_7, global_expr_759.
 rewrite instance_20_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_759.
Transparent Child2Stable.word_25 global_word_1789.
Lemma instance_20_word_25 v : Child2Stable.word_25 (instance_20_leaves v) = global_word_1789 v.
Proof. unfold Child2Stable.word_25, global_word_1789, Child2Stable.closed_word_25, global_closed_1789, Child2Stable.expr_word_25, global_expr_1789.
 rewrite instance_20_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1789.
Transparent Child2Stable.word_42 global_word_765.
Lemma instance_20_word_42 v : Child2Stable.word_42 (instance_20_leaves v) = global_word_765 v.
Proof. unfold Child2Stable.word_42, global_word_765, Child2Stable.closed_word_42, global_closed_765, Child2Stable.expr_word_42, global_expr_765.
 rewrite instance_20_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_765.
Transparent Child2Stable.word_8 global_word_766.
Lemma instance_20_word_8 v : Child2Stable.word_8 (instance_20_leaves v) = global_word_766 v.
Proof. unfold Child2Stable.word_8, global_word_766, Child2Stable.closed_word_8, global_closed_766, Child2Stable.expr_word_8, global_expr_766.
 rewrite instance_20_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_766.
Transparent Child2Stable.word_26 global_word_1790.
Lemma instance_20_word_26 v : Child2Stable.word_26 (instance_20_leaves v) = global_word_1790 v.
Proof. unfold Child2Stable.word_26, global_word_1790, Child2Stable.closed_word_26, global_closed_1790, Child2Stable.expr_word_26, global_expr_1790.
 rewrite instance_20_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1790.
Transparent Child2Stable.word_27 global_word_1791.
Lemma instance_20_word_27 v : Child2Stable.word_27 (instance_20_leaves v) = global_word_1791 v.
Proof. unfold Child2Stable.word_27, global_word_1791, Child2Stable.closed_word_27, global_closed_1791, Child2Stable.expr_word_27, global_expr_1791.
 rewrite instance_20_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1791.
Transparent Child2Stable.word_43 global_word_772.
Lemma instance_20_word_43 v : Child2Stable.word_43 (instance_20_leaves v) = global_word_772 v.
Proof. unfold Child2Stable.word_43, global_word_772, Child2Stable.closed_word_43, global_closed_772, Child2Stable.expr_word_43, global_expr_772.
 rewrite instance_20_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_772.
Transparent Child2Stable.word_9 global_word_773.
Lemma instance_20_word_9 v : Child2Stable.word_9 (instance_20_leaves v) = global_word_773 v.
Proof. unfold Child2Stable.word_9, global_word_773, Child2Stable.closed_word_9, global_closed_773, Child2Stable.expr_word_9, global_expr_773.
 rewrite instance_20_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_773.
Transparent Child2Stable.word_28 global_word_1792.
Lemma instance_20_word_28 v : Child2Stable.word_28 (instance_20_leaves v) = global_word_1792 v.
Proof. unfold Child2Stable.word_28, global_word_1792, Child2Stable.closed_word_28, global_closed_1792, Child2Stable.expr_word_28, global_expr_1792.
 rewrite instance_20_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1792.
Transparent Child2Stable.word_29 global_word_1793.
Lemma instance_20_word_29 v : Child2Stable.word_29 (instance_20_leaves v) = global_word_1793 v.
Proof. unfold Child2Stable.word_29, global_word_1793, Child2Stable.closed_word_29, global_closed_1793, Child2Stable.expr_word_29, global_expr_1793.
 rewrite instance_20_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1793.
Transparent Child2Stable.word_30 global_word_1794.
Lemma instance_20_word_30 v : Child2Stable.word_30 (instance_20_leaves v) = global_word_1794 v.
Proof. unfold Child2Stable.word_30, global_word_1794, Child2Stable.closed_word_30, global_closed_1794, Child2Stable.expr_word_30, global_expr_1794.
 rewrite instance_20_word_25 instance_20_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1794.
Transparent Child2Stable.word_31 global_word_1795.
Lemma instance_20_word_31 v : Child2Stable.word_31 (instance_20_leaves v) = global_word_1795 v.
Proof. unfold Child2Stable.word_31, global_word_1795, Child2Stable.closed_word_31, global_closed_1795, Child2Stable.expr_word_31, global_expr_1795.
 rewrite instance_20_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1795.
Transparent Child2Stable.word_32 global_word_1796.
Lemma instance_20_word_32 v : Child2Stable.word_32 (instance_20_leaves v) = global_word_1796 v.
Proof. unfold Child2Stable.word_32, global_word_1796, Child2Stable.closed_word_32, global_closed_1796, Child2Stable.expr_word_32, global_expr_1796.
 rewrite instance_20_word_29 instance_20_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1796.
Transparent Child2Stable.word_33 global_word_1797.
Lemma instance_20_word_33 v : Child2Stable.word_33 (instance_20_leaves v) = global_word_1797 v.
Proof. unfold Child2Stable.word_33, global_word_1797, Child2Stable.closed_word_33, global_closed_1797, Child2Stable.expr_word_33, global_expr_1797.
 rewrite instance_20_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1797.
Transparent Child2Stable.word_34 global_word_1798.
Lemma instance_20_word_34 v : Child2Stable.word_34 (instance_20_leaves v) = global_word_1798 v.
Proof. unfold Child2Stable.word_34, global_word_1798, Child2Stable.closed_word_34, global_closed_1798, Child2Stable.expr_word_34, global_expr_1798.
 rewrite instance_20_word_24 instance_20_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1798.
Transparent Child2Stable.word_35 global_word_1800.
Lemma instance_20_word_35 v : Child2Stable.word_35 (instance_20_leaves v) = global_word_1800 v.
Proof. unfold Child2Stable.word_35, global_word_1800, Child2Stable.closed_word_35, global_closed_1800, Child2Stable.expr_word_35, global_expr_1800.
 rewrite instance_20_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1800.
Transparent Child2Stable.word_36 global_word_1801.
Lemma instance_20_word_36 v : Child2Stable.word_36 (instance_20_leaves v) = global_word_1801 v.
Proof. unfold Child2Stable.word_36, global_word_1801, Child2Stable.closed_word_36, global_closed_1801, Child2Stable.expr_word_36, global_expr_1801.
 rewrite instance_20_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1801.
Transparent Child2Stable.word_37 global_word_1802.
Lemma instance_20_word_37 v : Child2Stable.word_37 (instance_20_leaves v) = global_word_1802 v.
Proof. unfold Child2Stable.word_37, global_word_1802, Child2Stable.closed_word_37, global_closed_1802, Child2Stable.expr_word_37, global_expr_1802.
 rewrite instance_20_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1802.
Transparent Child2Stable.word_38 global_word_738.
Lemma instance_20_word_38 v : Child2Stable.word_38 (instance_20_leaves v) = global_word_738 v.
Proof. unfold Child2Stable.word_38, global_word_738, Child2Stable.closed_word_38, global_closed_738, Child2Stable.expr_word_38, global_expr_738.
 rewrite instance_20_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_738.
Transparent Child2Stable.word_39 global_word_744.
Lemma instance_20_word_39 v : Child2Stable.word_39 (instance_20_leaves v) = global_word_744 v.
Proof. unfold Child2Stable.word_39, global_word_744, Child2Stable.closed_word_39, global_closed_744, Child2Stable.expr_word_39, global_expr_744.
 rewrite instance_20_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_744.
Transparent Child2Stable.word_40 global_word_709.
Lemma instance_20_word_40 v : Child2Stable.word_40 (instance_20_leaves v) = global_word_709 v.
Proof. unfold Child2Stable.word_40, global_word_709, Child2Stable.closed_word_40, global_closed_709, Child2Stable.expr_word_40, global_expr_709.
 rewrite instance_20_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_709.
Transparent Child2Stable.port_10_0 global_word_1804.
Lemma instance_20_port_10_0 v : Child2Stable.port_10_0 (instance_20_leaves v) = global_word_1804 v.
Proof. unfold Child2Stable.port_10_0, global_word_1804, Child2Stable.closed_port_10_0, global_closed_1804, Child2Stable.expr_port_10_0, global_expr_1804.
 rewrite instance_20_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1804.
Transparent Child2Stable.port_10_1 global_word_1805.
Lemma instance_20_port_10_1 v : Child2Stable.port_10_1 (instance_20_leaves v) = global_word_1805 v.
Proof. unfold Child2Stable.port_10_1, global_word_1805, Child2Stable.closed_port_10_1, global_closed_1805, Child2Stable.expr_port_10_1, global_expr_1805.
 rewrite instance_20_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1805.
Transparent Child2Stable.port_10_2 global_word_720.
Lemma instance_20_port_10_2 v : Child2Stable.port_10_2 (instance_20_leaves v) = global_word_720 v.
Proof. unfold Child2Stable.port_10_2, global_word_720, Child2Stable.closed_port_10_2, global_closed_720, Child2Stable.expr_port_10_2, global_expr_720.
 rewrite instance_20_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_720.
Transparent Child2Stable.port_10_3 global_word_725.
Lemma instance_20_port_10_3 v : Child2Stable.port_10_3 (instance_20_leaves v) = global_word_725 v.
Proof. unfold Child2Stable.port_10_3, global_word_725, Child2Stable.closed_port_10_3, global_closed_725, Child2Stable.expr_port_10_3, global_expr_725.
 rewrite instance_20_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_725.
Transparent Child2Stable.port_10_4 global_word_715.
Lemma instance_20_port_10_4 v : Child2Stable.port_10_4 (instance_20_leaves v) = global_word_715 v.
Proof. unfold Child2Stable.port_10_4, global_word_715, Child2Stable.closed_port_10_4, global_closed_715, Child2Stable.expr_port_10_4, global_expr_715.
 rewrite instance_20_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_715.
Transparent Child2Stable.port_11_0 global_word_1806.
Lemma instance_20_port_11_0 v : Child2Stable.port_11_0 (instance_20_leaves v) = global_word_1806 v.
Proof. unfold Child2Stable.port_11_0, global_word_1806, Child2Stable.closed_port_11_0, global_closed_1806, Child2Stable.expr_port_11_0, global_expr_1806.
 rewrite instance_20_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1806.
Transparent Child2Stable.port_11_1 global_word_1807.
Lemma instance_20_port_11_1 v : Child2Stable.port_11_1 (instance_20_leaves v) = global_word_1807 v.
Proof. unfold Child2Stable.port_11_1, global_word_1807, Child2Stable.closed_port_11_1, global_closed_1807, Child2Stable.expr_port_11_1, global_expr_1807.
 rewrite instance_20_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1807.
Transparent Child2Stable.port_11_2 global_word_739.
Lemma instance_20_port_11_2 v : Child2Stable.port_11_2 (instance_20_leaves v) = global_word_739 v.
Proof. unfold Child2Stable.port_11_2, global_word_739, Child2Stable.closed_port_11_2, global_closed_739, Child2Stable.expr_port_11_2, global_expr_739.
 rewrite instance_20_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_739.
Transparent Child2Stable.port_11_3 global_word_745.
Lemma instance_20_port_11_3 v : Child2Stable.port_11_3 (instance_20_leaves v) = global_word_745 v.
Proof. unfold Child2Stable.port_11_3, global_word_745, Child2Stable.closed_port_11_3, global_closed_745, Child2Stable.expr_port_11_3, global_expr_745.
 rewrite instance_20_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_745.
Transparent Child2Stable.port_11_4 global_word_710.
Lemma instance_20_port_11_4 v : Child2Stable.port_11_4 (instance_20_leaves v) = global_word_710 v.
Proof. unfold Child2Stable.port_11_4, global_word_710, Child2Stable.closed_port_11_4, global_closed_710, Child2Stable.expr_port_11_4, global_expr_710.
 rewrite instance_20_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_710.
Definition instance_21_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1825 v
| 0, 1 => global_word_1821 v
| 0, 2 => global_word_721 v
| 0, 3 => global_word_726 v
| 0, 4 => global_word_716 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1825.
Lemma instance_21_word_0 v : Child1Stable.word_0 (instance_21_leaves v) = global_word_1825 v.
Proof. unfold Child1Stable.word_0, instance_21_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1825.
Transparent Child1Stable.word_1 global_word_1821.
Lemma instance_21_word_1 v : Child1Stable.word_1 (instance_21_leaves v) = global_word_1821 v.
Proof. unfold Child1Stable.word_1, instance_21_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1821.
Transparent Child1Stable.word_2 global_word_721.
Lemma instance_21_word_2 v : Child1Stable.word_2 (instance_21_leaves v) = global_word_721 v.
Proof. unfold Child1Stable.word_2, instance_21_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_721.
Transparent Child1Stable.word_3 global_word_726.
Lemma instance_21_word_3 v : Child1Stable.word_3 (instance_21_leaves v) = global_word_726 v.
Proof. unfold Child1Stable.word_3, instance_21_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_726.
Transparent Child1Stable.word_4 global_word_716.
Lemma instance_21_word_4 v : Child1Stable.word_4 (instance_21_leaves v) = global_word_716 v.
Proof. unfold Child1Stable.word_4, instance_21_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_716.
Transparent Child1Stable.word_7 global_word_1808.
Lemma instance_21_word_7 v : Child1Stable.word_7 (instance_21_leaves v) = global_word_1808 v.
Proof. unfold Child1Stable.word_7, global_word_1808, Child1Stable.closed_word_7, global_closed_1808, Child1Stable.expr_word_7, global_expr_1808.
 rewrite instance_21_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1808.
Transparent Child1Stable.word_8 global_word_1809.
Lemma instance_21_word_8 v : Child1Stable.word_8 (instance_21_leaves v) = global_word_1809 v.
Proof. unfold Child1Stable.word_8, global_word_1809, Child1Stable.closed_word_8, global_closed_1809, Child1Stable.expr_word_8, global_expr_1809.
 rewrite instance_21_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1809.
Transparent Child1Stable.word_9 global_word_1810.
Lemma instance_21_word_9 v : Child1Stable.word_9 (instance_21_leaves v) = global_word_1810 v.
Proof. unfold Child1Stable.word_9, global_word_1810, Child1Stable.closed_word_9, global_closed_1810, Child1Stable.expr_word_9, global_expr_1810.
 rewrite instance_21_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1810.
Transparent Child1Stable.word_10 global_word_1811.
Lemma instance_21_word_10 v : Child1Stable.word_10 (instance_21_leaves v) = global_word_1811 v.
Proof. unfold Child1Stable.word_10, global_word_1811, Child1Stable.closed_word_10, global_closed_1811, Child1Stable.expr_word_10, global_expr_1811.
 rewrite instance_21_word_7 instance_21_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1811.
Transparent Child1Stable.word_11 global_word_1812.
Lemma instance_21_word_11 v : Child1Stable.word_11 (instance_21_leaves v) = global_word_1812 v.
Proof. unfold Child1Stable.word_11, global_word_1812, Child1Stable.closed_word_11, global_closed_1812, Child1Stable.expr_word_11, global_expr_1812.
 rewrite instance_21_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1812.
Transparent Child1Stable.word_12 global_word_1813.
Lemma instance_21_word_12 v : Child1Stable.word_12 (instance_21_leaves v) = global_word_1813 v.
Proof. unfold Child1Stable.word_12, global_word_1813, Child1Stable.closed_word_12, global_closed_1813, Child1Stable.expr_word_12, global_expr_1813.
 rewrite instance_21_word_9 instance_21_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1813.
Transparent Child1Stable.word_13 global_word_1814.
Lemma instance_21_word_13 v : Child1Stable.word_13 (instance_21_leaves v) = global_word_1814 v.
Proof. unfold Child1Stable.word_13, global_word_1814, Child1Stable.closed_word_13, global_closed_1814, Child1Stable.expr_word_13, global_expr_1814.
 rewrite instance_21_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1814.
Transparent Child1Stable.word_25 global_word_717.
Lemma instance_21_word_25 v : Child1Stable.word_25 (instance_21_leaves v) = global_word_717 v.
Proof. unfold Child1Stable.word_25, global_word_717, Child1Stable.closed_word_25, global_closed_717, Child1Stable.expr_word_25, global_expr_717.
 rewrite instance_21_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_717.
Transparent Child1Stable.word_23 global_word_722.
Lemma instance_21_word_23 v : Child1Stable.word_23 (instance_21_leaves v) = global_word_722 v.
Proof. unfold Child1Stable.word_23, global_word_722, Child1Stable.closed_word_23, global_closed_722, Child1Stable.expr_word_23, global_expr_722.
 rewrite instance_21_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_722.
Transparent Child1Stable.word_24 global_word_727.
Lemma instance_21_word_24 v : Child1Stable.word_24 (instance_21_leaves v) = global_word_727 v.
Proof. unfold Child1Stable.word_24, global_word_727, Child1Stable.closed_word_24, global_closed_727, Child1Stable.expr_word_24, global_expr_727.
 rewrite instance_21_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_727.
Transparent Child1Stable.word_26 global_word_728.
Lemma instance_21_word_26 v : Child1Stable.word_26 (instance_21_leaves v) = global_word_728 v.
Proof. unfold Child1Stable.word_26, global_word_728, Child1Stable.closed_word_26, global_closed_728, Child1Stable.expr_word_26, global_expr_728.
 rewrite instance_21_word_23 instance_21_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_728.
Transparent Child1Stable.word_28 global_word_729.
Lemma instance_21_word_28 v : Child1Stable.word_28 (instance_21_leaves v) = global_word_729 v.
Proof. unfold Child1Stable.word_28, global_word_729, Child1Stable.closed_word_28, global_closed_729, Child1Stable.expr_word_28, global_expr_729.
 rewrite instance_21_word_25 instance_21_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_729.
Transparent Child1Stable.word_27 global_word_730.
Lemma instance_21_word_27 v : Child1Stable.word_27 (instance_21_leaves v) = global_word_730 v.
Proof. unfold Child1Stable.word_27, global_word_730, Child1Stable.closed_word_27, global_closed_730, Child1Stable.expr_word_27, global_expr_730.
 rewrite instance_21_word_23 instance_21_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_730.
Transparent Child1Stable.word_29 global_word_731.
Lemma instance_21_word_29 v : Child1Stable.word_29 (instance_21_leaves v) = global_word_731 v.
Proof. unfold Child1Stable.word_29, global_word_731, Child1Stable.closed_word_29, global_closed_731, Child1Stable.expr_word_29, global_expr_731.
 rewrite instance_21_word_25 instance_21_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_731.
Transparent Child1Stable.word_30 global_word_732.
Lemma instance_21_word_30 v : Child1Stable.word_30 (instance_21_leaves v) = global_word_732 v.
Proof. unfold Child1Stable.word_30, global_word_732, Child1Stable.closed_word_30, global_closed_732, Child1Stable.expr_word_30, global_expr_732.
 rewrite instance_21_word_27 instance_21_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_732.
Transparent Child1Stable.word_31 global_word_733.
Lemma instance_21_word_31 v : Child1Stable.word_31 (instance_21_leaves v) = global_word_733 v.
Proof. unfold Child1Stable.word_31, global_word_733, Child1Stable.closed_word_31, global_closed_733, Child1Stable.expr_word_31, global_expr_733.
 rewrite instance_21_word_28 instance_21_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_733.
Transparent Child1Stable.word_32 global_word_734.
Lemma instance_21_word_32 v : Child1Stable.word_32 (instance_21_leaves v) = global_word_734 v.
Proof. unfold Child1Stable.word_32, global_word_734, Child1Stable.closed_word_32, global_closed_734, Child1Stable.expr_word_32, global_expr_734.
 rewrite instance_21_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_734.
Transparent Child1Stable.word_33 global_word_735.
Lemma instance_21_word_33 v : Child1Stable.word_33 (instance_21_leaves v) = global_word_735 v.
Proof. unfold Child1Stable.word_33, global_word_735, Child1Stable.closed_word_33, global_closed_735, Child1Stable.expr_word_33, global_expr_735.
 rewrite instance_21_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_735.
Transparent Child1Stable.word_5 global_word_736.
Lemma instance_21_word_5 v : Child1Stable.word_5 (instance_21_leaves v) = global_word_736 v.
Proof. unfold Child1Stable.word_5, global_word_736, Child1Stable.closed_word_5, global_closed_736, Child1Stable.expr_word_5, global_expr_736.
 rewrite instance_21_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_736.
Transparent Child1Stable.word_14 global_word_1815.
Lemma instance_21_word_14 v : Child1Stable.word_14 (instance_21_leaves v) = global_word_1815 v.
Proof. unfold Child1Stable.word_14, global_word_1815, Child1Stable.closed_word_14, global_closed_1815, Child1Stable.expr_word_14, global_expr_1815.
 rewrite instance_21_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1815.
Transparent Child1Stable.word_34 global_word_762.
Lemma instance_21_word_34 v : Child1Stable.word_34 (instance_21_leaves v) = global_word_762 v.
Proof. unfold Child1Stable.word_34, global_word_762, Child1Stable.closed_word_34, global_closed_762, Child1Stable.expr_word_34, global_expr_762.
 rewrite instance_21_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_762.
Transparent Child1Stable.word_6 global_word_763.
Lemma instance_21_word_6 v : Child1Stable.word_6 (instance_21_leaves v) = global_word_763 v.
Proof. unfold Child1Stable.word_6, global_word_763, Child1Stable.closed_word_6, global_closed_763, Child1Stable.expr_word_6, global_expr_763.
 rewrite instance_21_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_763.
Transparent Child1Stable.word_15 global_word_1816.
Lemma instance_21_word_15 v : Child1Stable.word_15 (instance_21_leaves v) = global_word_1816 v.
Proof. unfold Child1Stable.word_15, global_word_1816, Child1Stable.closed_word_15, global_closed_1816, Child1Stable.expr_word_15, global_expr_1816.
 rewrite instance_21_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1816.
Transparent Child1Stable.word_16 global_word_1817.
Lemma instance_21_word_16 v : Child1Stable.word_16 (instance_21_leaves v) = global_word_1817 v.
Proof. unfold Child1Stable.word_16, global_word_1817, Child1Stable.closed_word_16, global_closed_1817, Child1Stable.expr_word_16, global_expr_1817.
 rewrite instance_21_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1817.
Transparent Child1Stable.word_17 global_word_1818.
Lemma instance_21_word_17 v : Child1Stable.word_17 (instance_21_leaves v) = global_word_1818 v.
Proof. unfold Child1Stable.word_17, global_word_1818, Child1Stable.closed_word_17, global_closed_1818, Child1Stable.expr_word_17, global_expr_1818.
 rewrite instance_21_word_14 instance_21_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1818.
Transparent Child1Stable.word_18 global_word_1819.
Lemma instance_21_word_18 v : Child1Stable.word_18 (instance_21_leaves v) = global_word_1819 v.
Proof. unfold Child1Stable.word_18, global_word_1819, Child1Stable.closed_word_18, global_closed_1819, Child1Stable.expr_word_18, global_expr_1819.
 rewrite instance_21_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1819.
Transparent Child1Stable.word_19 global_word_1820.
Lemma instance_21_word_19 v : Child1Stable.word_19 (instance_21_leaves v) = global_word_1820 v.
Proof. unfold Child1Stable.word_19, global_word_1820, Child1Stable.closed_word_19, global_closed_1820, Child1Stable.expr_word_19, global_expr_1820.
 rewrite instance_21_word_13 instance_21_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1820.
Transparent Child1Stable.word_20 global_word_1822.
Lemma instance_21_word_20 v : Child1Stable.word_20 (instance_21_leaves v) = global_word_1822 v.
Proof. unfold Child1Stable.word_20, global_word_1822, Child1Stable.closed_word_20, global_closed_1822, Child1Stable.expr_word_20, global_expr_1822.
 rewrite instance_21_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1822.
Transparent Child1Stable.word_21 global_word_1823.
Lemma instance_21_word_21 v : Child1Stable.word_21 (instance_21_leaves v) = global_word_1823 v.
Proof. unfold Child1Stable.word_21, global_word_1823, Child1Stable.closed_word_21, global_closed_1823, Child1Stable.expr_word_21, global_expr_1823.
 rewrite instance_21_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1823.
Transparent Child1Stable.word_22 global_word_1824.
Lemma instance_21_word_22 v : Child1Stable.word_22 (instance_21_leaves v) = global_word_1824 v.
Proof. unfold Child1Stable.word_22, global_word_1824, Child1Stable.closed_word_22, global_closed_1824, Child1Stable.expr_word_22, global_expr_1824.
 rewrite instance_21_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1824.
Definition instance_22_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1843 v
| 0, 1 => global_word_1839 v
| 0, 2 => global_word_740 v
| 0, 3 => global_word_746 v
| 0, 4 => global_word_711 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1843.
Lemma instance_22_word_0 v : Child1Stable.word_0 (instance_22_leaves v) = global_word_1843 v.
Proof. unfold Child1Stable.word_0, instance_22_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1843.
Transparent Child1Stable.word_1 global_word_1839.
Lemma instance_22_word_1 v : Child1Stable.word_1 (instance_22_leaves v) = global_word_1839 v.
Proof. unfold Child1Stable.word_1, instance_22_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1839.
Transparent Child1Stable.word_2 global_word_740.
Lemma instance_22_word_2 v : Child1Stable.word_2 (instance_22_leaves v) = global_word_740 v.
Proof. unfold Child1Stable.word_2, instance_22_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_740.
Transparent Child1Stable.word_3 global_word_746.
Lemma instance_22_word_3 v : Child1Stable.word_3 (instance_22_leaves v) = global_word_746 v.
Proof. unfold Child1Stable.word_3, instance_22_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_746.
Transparent Child1Stable.word_4 global_word_711.
Lemma instance_22_word_4 v : Child1Stable.word_4 (instance_22_leaves v) = global_word_711 v.
Proof. unfold Child1Stable.word_4, instance_22_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_711.
Transparent Child1Stable.word_7 global_word_1826.
Lemma instance_22_word_7 v : Child1Stable.word_7 (instance_22_leaves v) = global_word_1826 v.
Proof. unfold Child1Stable.word_7, global_word_1826, Child1Stable.closed_word_7, global_closed_1826, Child1Stable.expr_word_7, global_expr_1826.
 rewrite instance_22_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1826.
Transparent Child1Stable.word_8 global_word_1827.
Lemma instance_22_word_8 v : Child1Stable.word_8 (instance_22_leaves v) = global_word_1827 v.
Proof. unfold Child1Stable.word_8, global_word_1827, Child1Stable.closed_word_8, global_closed_1827, Child1Stable.expr_word_8, global_expr_1827.
 rewrite instance_22_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1827.
Transparent Child1Stable.word_9 global_word_1828.
Lemma instance_22_word_9 v : Child1Stable.word_9 (instance_22_leaves v) = global_word_1828 v.
Proof. unfold Child1Stable.word_9, global_word_1828, Child1Stable.closed_word_9, global_closed_1828, Child1Stable.expr_word_9, global_expr_1828.
 rewrite instance_22_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1828.
Transparent Child1Stable.word_10 global_word_1829.
Lemma instance_22_word_10 v : Child1Stable.word_10 (instance_22_leaves v) = global_word_1829 v.
Proof. unfold Child1Stable.word_10, global_word_1829, Child1Stable.closed_word_10, global_closed_1829, Child1Stable.expr_word_10, global_expr_1829.
 rewrite instance_22_word_7 instance_22_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1829.
Transparent Child1Stable.word_11 global_word_1830.
Lemma instance_22_word_11 v : Child1Stable.word_11 (instance_22_leaves v) = global_word_1830 v.
Proof. unfold Child1Stable.word_11, global_word_1830, Child1Stable.closed_word_11, global_closed_1830, Child1Stable.expr_word_11, global_expr_1830.
 rewrite instance_22_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1830.
Transparent Child1Stable.word_12 global_word_1831.
Lemma instance_22_word_12 v : Child1Stable.word_12 (instance_22_leaves v) = global_word_1831 v.
Proof. unfold Child1Stable.word_12, global_word_1831, Child1Stable.closed_word_12, global_closed_1831, Child1Stable.expr_word_12, global_expr_1831.
 rewrite instance_22_word_9 instance_22_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1831.
Transparent Child1Stable.word_13 global_word_1832.
Lemma instance_22_word_13 v : Child1Stable.word_13 (instance_22_leaves v) = global_word_1832 v.
Proof. unfold Child1Stable.word_13, global_word_1832, Child1Stable.closed_word_13, global_closed_1832, Child1Stable.expr_word_13, global_expr_1832.
 rewrite instance_22_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1832.
Transparent Child1Stable.word_25 global_word_712.
Lemma instance_22_word_25 v : Child1Stable.word_25 (instance_22_leaves v) = global_word_712 v.
Proof. unfold Child1Stable.word_25, global_word_712, Child1Stable.closed_word_25, global_closed_712, Child1Stable.expr_word_25, global_expr_712.
 rewrite instance_22_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_712.
Transparent Child1Stable.word_23 global_word_741.
Lemma instance_22_word_23 v : Child1Stable.word_23 (instance_22_leaves v) = global_word_741 v.
Proof. unfold Child1Stable.word_23, global_word_741, Child1Stable.closed_word_23, global_closed_741, Child1Stable.expr_word_23, global_expr_741.
 rewrite instance_22_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_741.
Transparent Child1Stable.word_24 global_word_747.
Lemma instance_22_word_24 v : Child1Stable.word_24 (instance_22_leaves v) = global_word_747 v.
Proof. unfold Child1Stable.word_24, global_word_747, Child1Stable.closed_word_24, global_closed_747, Child1Stable.expr_word_24, global_expr_747.
 rewrite instance_22_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_747.
Transparent Child1Stable.word_26 global_word_748.
Lemma instance_22_word_26 v : Child1Stable.word_26 (instance_22_leaves v) = global_word_748 v.
Proof. unfold Child1Stable.word_26, global_word_748, Child1Stable.closed_word_26, global_closed_748, Child1Stable.expr_word_26, global_expr_748.
 rewrite instance_22_word_23 instance_22_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_748.
Transparent Child1Stable.word_28 global_word_749.
Lemma instance_22_word_28 v : Child1Stable.word_28 (instance_22_leaves v) = global_word_749 v.
Proof. unfold Child1Stable.word_28, global_word_749, Child1Stable.closed_word_28, global_closed_749, Child1Stable.expr_word_28, global_expr_749.
 rewrite instance_22_word_25 instance_22_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_749.
Transparent Child1Stable.word_27 global_word_750.
Lemma instance_22_word_27 v : Child1Stable.word_27 (instance_22_leaves v) = global_word_750 v.
Proof. unfold Child1Stable.word_27, global_word_750, Child1Stable.closed_word_27, global_closed_750, Child1Stable.expr_word_27, global_expr_750.
 rewrite instance_22_word_23 instance_22_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_750.
Transparent Child1Stable.word_29 global_word_751.
Lemma instance_22_word_29 v : Child1Stable.word_29 (instance_22_leaves v) = global_word_751 v.
Proof. unfold Child1Stable.word_29, global_word_751, Child1Stable.closed_word_29, global_closed_751, Child1Stable.expr_word_29, global_expr_751.
 rewrite instance_22_word_25 instance_22_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_751.
Transparent Child1Stable.word_30 global_word_752.
Lemma instance_22_word_30 v : Child1Stable.word_30 (instance_22_leaves v) = global_word_752 v.
Proof. unfold Child1Stable.word_30, global_word_752, Child1Stable.closed_word_30, global_closed_752, Child1Stable.expr_word_30, global_expr_752.
 rewrite instance_22_word_27 instance_22_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_752.
Transparent Child1Stable.word_31 global_word_753.
Lemma instance_22_word_31 v : Child1Stable.word_31 (instance_22_leaves v) = global_word_753 v.
Proof. unfold Child1Stable.word_31, global_word_753, Child1Stable.closed_word_31, global_closed_753, Child1Stable.expr_word_31, global_expr_753.
 rewrite instance_22_word_28 instance_22_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_753.
Transparent Child1Stable.word_32 global_word_754.
Lemma instance_22_word_32 v : Child1Stable.word_32 (instance_22_leaves v) = global_word_754 v.
Proof. unfold Child1Stable.word_32, global_word_754, Child1Stable.closed_word_32, global_closed_754, Child1Stable.expr_word_32, global_expr_754.
 rewrite instance_22_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_754.
Transparent Child1Stable.word_33 global_word_755.
Lemma instance_22_word_33 v : Child1Stable.word_33 (instance_22_leaves v) = global_word_755 v.
Proof. unfold Child1Stable.word_33, global_word_755, Child1Stable.closed_word_33, global_closed_755, Child1Stable.expr_word_33, global_expr_755.
 rewrite instance_22_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_755.
Transparent Child1Stable.word_5 global_word_756.
Lemma instance_22_word_5 v : Child1Stable.word_5 (instance_22_leaves v) = global_word_756 v.
Proof. unfold Child1Stable.word_5, global_word_756, Child1Stable.closed_word_5, global_closed_756, Child1Stable.expr_word_5, global_expr_756.
 rewrite instance_22_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_756.
Transparent Child1Stable.word_14 global_word_1833.
Lemma instance_22_word_14 v : Child1Stable.word_14 (instance_22_leaves v) = global_word_1833 v.
Proof. unfold Child1Stable.word_14, global_word_1833, Child1Stable.closed_word_14, global_closed_1833, Child1Stable.expr_word_14, global_expr_1833.
 rewrite instance_22_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1833.
Transparent Child1Stable.word_34 global_word_769.
Lemma instance_22_word_34 v : Child1Stable.word_34 (instance_22_leaves v) = global_word_769 v.
Proof. unfold Child1Stable.word_34, global_word_769, Child1Stable.closed_word_34, global_closed_769, Child1Stable.expr_word_34, global_expr_769.
 rewrite instance_22_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_769.
Transparent Child1Stable.word_6 global_word_770.
Lemma instance_22_word_6 v : Child1Stable.word_6 (instance_22_leaves v) = global_word_770 v.
Proof. unfold Child1Stable.word_6, global_word_770, Child1Stable.closed_word_6, global_closed_770, Child1Stable.expr_word_6, global_expr_770.
 rewrite instance_22_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_770.
Transparent Child1Stable.word_15 global_word_1834.
Lemma instance_22_word_15 v : Child1Stable.word_15 (instance_22_leaves v) = global_word_1834 v.
Proof. unfold Child1Stable.word_15, global_word_1834, Child1Stable.closed_word_15, global_closed_1834, Child1Stable.expr_word_15, global_expr_1834.
 rewrite instance_22_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1834.
Transparent Child1Stable.word_16 global_word_1835.
Lemma instance_22_word_16 v : Child1Stable.word_16 (instance_22_leaves v) = global_word_1835 v.
Proof. unfold Child1Stable.word_16, global_word_1835, Child1Stable.closed_word_16, global_closed_1835, Child1Stable.expr_word_16, global_expr_1835.
 rewrite instance_22_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1835.
Transparent Child1Stable.word_17 global_word_1836.
Lemma instance_22_word_17 v : Child1Stable.word_17 (instance_22_leaves v) = global_word_1836 v.
Proof. unfold Child1Stable.word_17, global_word_1836, Child1Stable.closed_word_17, global_closed_1836, Child1Stable.expr_word_17, global_expr_1836.
 rewrite instance_22_word_14 instance_22_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1836.
Transparent Child1Stable.word_18 global_word_1837.
Lemma instance_22_word_18 v : Child1Stable.word_18 (instance_22_leaves v) = global_word_1837 v.
Proof. unfold Child1Stable.word_18, global_word_1837, Child1Stable.closed_word_18, global_closed_1837, Child1Stable.expr_word_18, global_expr_1837.
 rewrite instance_22_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1837.
Transparent Child1Stable.word_19 global_word_1838.
Lemma instance_22_word_19 v : Child1Stable.word_19 (instance_22_leaves v) = global_word_1838 v.
Proof. unfold Child1Stable.word_19, global_word_1838, Child1Stable.closed_word_19, global_closed_1838, Child1Stable.expr_word_19, global_expr_1838.
 rewrite instance_22_word_13 instance_22_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1838.
Transparent Child1Stable.word_20 global_word_1840.
Lemma instance_22_word_20 v : Child1Stable.word_20 (instance_22_leaves v) = global_word_1840 v.
Proof. unfold Child1Stable.word_20, global_word_1840, Child1Stable.closed_word_20, global_closed_1840, Child1Stable.expr_word_20, global_expr_1840.
 rewrite instance_22_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1840.
Transparent Child1Stable.word_21 global_word_1841.
Lemma instance_22_word_21 v : Child1Stable.word_21 (instance_22_leaves v) = global_word_1841 v.
Proof. unfold Child1Stable.word_21, global_word_1841, Child1Stable.closed_word_21, global_closed_1841, Child1Stable.expr_word_21, global_expr_1841.
 rewrite instance_22_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1841.
Transparent Child1Stable.word_22 global_word_1842.
Lemma instance_22_word_22 v : Child1Stable.word_22 (instance_22_leaves v) = global_word_1842 v.
Proof. unfold Child1Stable.word_22, global_word_1842, Child1Stable.closed_word_22, global_closed_1842, Child1Stable.expr_word_22, global_expr_1842.
 rewrite instance_22_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1842.
Definition instance_23_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1871 v
| 0, 1 => global_word_1867 v
| 0, 2 => global_word_788 v
| 0, 3 => global_word_793 v
| 0, 4 => global_word_783 v
| 0, 5 => global_word_812 v
| 0, 6 => global_word_777 v
| 10, 5 => global_word_806 v
| 10, 6 => global_word_833 v
| 11, 5 => global_word_826 v
| 11, 6 => global_word_840 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1871.
Lemma instance_23_word_0 v : Child2Stable.word_0 (instance_23_leaves v) = global_word_1871 v.
Proof. unfold Child2Stable.word_0, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1871.
Transparent Child2Stable.word_1 global_word_1867.
Lemma instance_23_word_1 v : Child2Stable.word_1 (instance_23_leaves v) = global_word_1867 v.
Proof. unfold Child2Stable.word_1, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1867.
Transparent Child2Stable.word_2 global_word_788.
Lemma instance_23_word_2 v : Child2Stable.word_2 (instance_23_leaves v) = global_word_788 v.
Proof. unfold Child2Stable.word_2, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_788.
Transparent Child2Stable.word_3 global_word_793.
Lemma instance_23_word_3 v : Child2Stable.word_3 (instance_23_leaves v) = global_word_793 v.
Proof. unfold Child2Stable.word_3, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_793.
Transparent Child2Stable.word_4 global_word_783.
Lemma instance_23_word_4 v : Child2Stable.word_4 (instance_23_leaves v) = global_word_783 v.
Proof. unfold Child2Stable.word_4, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_783.
Transparent Child2Stable.word_5 global_word_812.
Lemma instance_23_word_5 v : Child2Stable.word_5 (instance_23_leaves v) = global_word_812 v.
Proof. unfold Child2Stable.word_5, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_812.
Transparent Child2Stable.word_6 global_word_777.
Lemma instance_23_word_6 v : Child2Stable.word_6 (instance_23_leaves v) = global_word_777 v.
Proof. unfold Child2Stable.word_6, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_777.
Transparent Child2Stable.port_10_5 global_word_806.
Lemma instance_23_port_10_5 v : Child2Stable.port_10_5 (instance_23_leaves v) = global_word_806 v.
Proof. unfold Child2Stable.port_10_5, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_806.
Transparent Child2Stable.port_10_6 global_word_833.
Lemma instance_23_port_10_6 v : Child2Stable.port_10_6 (instance_23_leaves v) = global_word_833 v.
Proof. unfold Child2Stable.port_10_6, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_833.
Transparent Child2Stable.port_11_5 global_word_826.
Lemma instance_23_port_11_5 v : Child2Stable.port_11_5 (instance_23_leaves v) = global_word_826 v.
Proof. unfold Child2Stable.port_11_5, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_826.
Transparent Child2Stable.port_11_6 global_word_840.
Lemma instance_23_port_11_6 v : Child2Stable.port_11_6 (instance_23_leaves v) = global_word_840 v.
Proof. unfold Child2Stable.port_11_6, instance_23_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_840.
Transparent Child2Stable.word_12 global_word_1844.
Lemma instance_23_word_12 v : Child2Stable.word_12 (instance_23_leaves v) = global_word_1844 v.
Proof. unfold Child2Stable.word_12, global_word_1844, Child2Stable.closed_word_12, global_closed_1844, Child2Stable.expr_word_12, global_expr_1844.
 rewrite instance_23_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1844.
Transparent Child2Stable.word_13 global_word_1845.
Lemma instance_23_word_13 v : Child2Stable.word_13 (instance_23_leaves v) = global_word_1845 v.
Proof. unfold Child2Stable.word_13, global_word_1845, Child2Stable.closed_word_13, global_closed_1845, Child2Stable.expr_word_13, global_expr_1845.
 rewrite instance_23_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1845.
Transparent Child2Stable.word_14 global_word_1846.
Lemma instance_23_word_14 v : Child2Stable.word_14 (instance_23_leaves v) = global_word_1846 v.
Proof. unfold Child2Stable.word_14, global_word_1846, Child2Stable.closed_word_14, global_closed_1846, Child2Stable.expr_word_14, global_expr_1846.
 rewrite instance_23_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1846.
Transparent Child2Stable.word_15 global_word_1847.
Lemma instance_23_word_15 v : Child2Stable.word_15 (instance_23_leaves v) = global_word_1847 v.
Proof. unfold Child2Stable.word_15, global_word_1847, Child2Stable.closed_word_15, global_closed_1847, Child2Stable.expr_word_15, global_expr_1847.
 rewrite instance_23_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1847.
Transparent Child2Stable.word_16 global_word_1848.
Lemma instance_23_word_16 v : Child2Stable.word_16 (instance_23_leaves v) = global_word_1848 v.
Proof. unfold Child2Stable.word_16, global_word_1848, Child2Stable.closed_word_16, global_closed_1848, Child2Stable.expr_word_16, global_expr_1848.
 rewrite instance_23_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1848.
Transparent Child2Stable.word_17 global_word_1849.
Lemma instance_23_word_17 v : Child2Stable.word_17 (instance_23_leaves v) = global_word_1849 v.
Proof. unfold Child2Stable.word_17, global_word_1849, Child2Stable.closed_word_17, global_closed_1849, Child2Stable.expr_word_17, global_expr_1849.
 rewrite instance_23_word_12 instance_23_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1849.
Transparent Child2Stable.word_18 global_word_1850.
Lemma instance_23_word_18 v : Child2Stable.word_18 (instance_23_leaves v) = global_word_1850 v.
Proof. unfold Child2Stable.word_18, global_word_1850, Child2Stable.closed_word_18, global_closed_1850, Child2Stable.expr_word_18, global_expr_1850.
 rewrite instance_23_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1850.
Transparent Child2Stable.word_19 global_word_1851.
Lemma instance_23_word_19 v : Child2Stable.word_19 (instance_23_leaves v) = global_word_1851 v.
Proof. unfold Child2Stable.word_19, global_word_1851, Child2Stable.closed_word_19, global_closed_1851, Child2Stable.expr_word_19, global_expr_1851.
 rewrite instance_23_word_14 instance_23_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1851.
Transparent Child2Stable.word_20 global_word_1852.
Lemma instance_23_word_20 v : Child2Stable.word_20 (instance_23_leaves v) = global_word_1852 v.
Proof. unfold Child2Stable.word_20, global_word_1852, Child2Stable.closed_word_20, global_closed_1852, Child2Stable.expr_word_20, global_expr_1852.
 rewrite instance_23_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1852.
Transparent Child2Stable.word_21 global_word_1853.
Lemma instance_23_word_21 v : Child2Stable.word_21 (instance_23_leaves v) = global_word_1853 v.
Proof. unfold Child2Stable.word_21, global_word_1853, Child2Stable.closed_word_21, global_closed_1853, Child2Stable.expr_word_21, global_expr_1853.
 rewrite instance_23_word_15 instance_23_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1853.
Transparent Child2Stable.word_22 global_word_1854.
Lemma instance_23_word_22 v : Child2Stable.word_22 (instance_23_leaves v) = global_word_1854 v.
Proof. unfold Child2Stable.word_22, global_word_1854, Child2Stable.closed_word_22, global_closed_1854, Child2Stable.expr_word_22, global_expr_1854.
 rewrite instance_23_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1854.
Transparent Child2Stable.word_23 global_word_1855.
Lemma instance_23_word_23 v : Child2Stable.word_23 (instance_23_leaves v) = global_word_1855 v.
Proof. unfold Child2Stable.word_23, global_word_1855, Child2Stable.closed_word_23, global_closed_1855, Child2Stable.expr_word_23, global_expr_1855.
 rewrite instance_23_word_16 instance_23_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1855.
Transparent Child2Stable.word_24 global_word_1856.
Lemma instance_23_word_24 v : Child2Stable.word_24 (instance_23_leaves v) = global_word_1856 v.
Proof. unfold Child2Stable.word_24, global_word_1856, Child2Stable.closed_word_24, global_closed_1856, Child2Stable.expr_word_24, global_expr_1856.
 rewrite instance_23_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1856.
Transparent Child2Stable.word_41 global_word_827.
Lemma instance_23_word_41 v : Child2Stable.word_41 (instance_23_leaves v) = global_word_827 v.
Proof. unfold Child2Stable.word_41, global_word_827, Child2Stable.closed_word_41, global_closed_827, Child2Stable.expr_word_41, global_expr_827.
 rewrite instance_23_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_827.
Transparent Child2Stable.word_7 global_word_828.
Lemma instance_23_word_7 v : Child2Stable.word_7 (instance_23_leaves v) = global_word_828 v.
Proof. unfold Child2Stable.word_7, global_word_828, Child2Stable.closed_word_7, global_closed_828, Child2Stable.expr_word_7, global_expr_828.
 rewrite instance_23_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_828.
Transparent Child2Stable.word_25 global_word_1857.
Lemma instance_23_word_25 v : Child2Stable.word_25 (instance_23_leaves v) = global_word_1857 v.
Proof. unfold Child2Stable.word_25, global_word_1857, Child2Stable.closed_word_25, global_closed_1857, Child2Stable.expr_word_25, global_expr_1857.
 rewrite instance_23_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1857.
Transparent Child2Stable.word_42 global_word_834.
Lemma instance_23_word_42 v : Child2Stable.word_42 (instance_23_leaves v) = global_word_834 v.
Proof. unfold Child2Stable.word_42, global_word_834, Child2Stable.closed_word_42, global_closed_834, Child2Stable.expr_word_42, global_expr_834.
 rewrite instance_23_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_834.
Transparent Child2Stable.word_8 global_word_835.
Lemma instance_23_word_8 v : Child2Stable.word_8 (instance_23_leaves v) = global_word_835 v.
Proof. unfold Child2Stable.word_8, global_word_835, Child2Stable.closed_word_8, global_closed_835, Child2Stable.expr_word_8, global_expr_835.
 rewrite instance_23_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_835.
Transparent Child2Stable.word_26 global_word_1858.
Lemma instance_23_word_26 v : Child2Stable.word_26 (instance_23_leaves v) = global_word_1858 v.
Proof. unfold Child2Stable.word_26, global_word_1858, Child2Stable.closed_word_26, global_closed_1858, Child2Stable.expr_word_26, global_expr_1858.
 rewrite instance_23_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1858.
Transparent Child2Stable.word_27 global_word_1859.
Lemma instance_23_word_27 v : Child2Stable.word_27 (instance_23_leaves v) = global_word_1859 v.
Proof. unfold Child2Stable.word_27, global_word_1859, Child2Stable.closed_word_27, global_closed_1859, Child2Stable.expr_word_27, global_expr_1859.
 rewrite instance_23_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1859.
Transparent Child2Stable.word_43 global_word_841.
Lemma instance_23_word_43 v : Child2Stable.word_43 (instance_23_leaves v) = global_word_841 v.
Proof. unfold Child2Stable.word_43, global_word_841, Child2Stable.closed_word_43, global_closed_841, Child2Stable.expr_word_43, global_expr_841.
 rewrite instance_23_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_841.
Transparent Child2Stable.word_9 global_word_842.
Lemma instance_23_word_9 v : Child2Stable.word_9 (instance_23_leaves v) = global_word_842 v.
Proof. unfold Child2Stable.word_9, global_word_842, Child2Stable.closed_word_9, global_closed_842, Child2Stable.expr_word_9, global_expr_842.
 rewrite instance_23_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_842.
Transparent Child2Stable.word_28 global_word_1860.
Lemma instance_23_word_28 v : Child2Stable.word_28 (instance_23_leaves v) = global_word_1860 v.
Proof. unfold Child2Stable.word_28, global_word_1860, Child2Stable.closed_word_28, global_closed_1860, Child2Stable.expr_word_28, global_expr_1860.
 rewrite instance_23_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1860.
Transparent Child2Stable.word_29 global_word_1861.
Lemma instance_23_word_29 v : Child2Stable.word_29 (instance_23_leaves v) = global_word_1861 v.
Proof. unfold Child2Stable.word_29, global_word_1861, Child2Stable.closed_word_29, global_closed_1861, Child2Stable.expr_word_29, global_expr_1861.
 rewrite instance_23_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1861.
Transparent Child2Stable.word_30 global_word_1862.
Lemma instance_23_word_30 v : Child2Stable.word_30 (instance_23_leaves v) = global_word_1862 v.
Proof. unfold Child2Stable.word_30, global_word_1862, Child2Stable.closed_word_30, global_closed_1862, Child2Stable.expr_word_30, global_expr_1862.
 rewrite instance_23_word_25 instance_23_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1862.
Transparent Child2Stable.word_31 global_word_1863.
Lemma instance_23_word_31 v : Child2Stable.word_31 (instance_23_leaves v) = global_word_1863 v.
Proof. unfold Child2Stable.word_31, global_word_1863, Child2Stable.closed_word_31, global_closed_1863, Child2Stable.expr_word_31, global_expr_1863.
 rewrite instance_23_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1863.
Transparent Child2Stable.word_32 global_word_1864.
Lemma instance_23_word_32 v : Child2Stable.word_32 (instance_23_leaves v) = global_word_1864 v.
Proof. unfold Child2Stable.word_32, global_word_1864, Child2Stable.closed_word_32, global_closed_1864, Child2Stable.expr_word_32, global_expr_1864.
 rewrite instance_23_word_29 instance_23_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1864.
Transparent Child2Stable.word_33 global_word_1865.
Lemma instance_23_word_33 v : Child2Stable.word_33 (instance_23_leaves v) = global_word_1865 v.
Proof. unfold Child2Stable.word_33, global_word_1865, Child2Stable.closed_word_33, global_closed_1865, Child2Stable.expr_word_33, global_expr_1865.
 rewrite instance_23_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1865.
Transparent Child2Stable.word_34 global_word_1866.
Lemma instance_23_word_34 v : Child2Stable.word_34 (instance_23_leaves v) = global_word_1866 v.
Proof. unfold Child2Stable.word_34, global_word_1866, Child2Stable.closed_word_34, global_closed_1866, Child2Stable.expr_word_34, global_expr_1866.
 rewrite instance_23_word_24 instance_23_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1866.
Transparent Child2Stable.word_35 global_word_1868.
Lemma instance_23_word_35 v : Child2Stable.word_35 (instance_23_leaves v) = global_word_1868 v.
Proof. unfold Child2Stable.word_35, global_word_1868, Child2Stable.closed_word_35, global_closed_1868, Child2Stable.expr_word_35, global_expr_1868.
 rewrite instance_23_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1868.
Transparent Child2Stable.word_36 global_word_1869.
Lemma instance_23_word_36 v : Child2Stable.word_36 (instance_23_leaves v) = global_word_1869 v.
Proof. unfold Child2Stable.word_36, global_word_1869, Child2Stable.closed_word_36, global_closed_1869, Child2Stable.expr_word_36, global_expr_1869.
 rewrite instance_23_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1869.
Transparent Child2Stable.word_37 global_word_1870.
Lemma instance_23_word_37 v : Child2Stable.word_37 (instance_23_leaves v) = global_word_1870 v.
Proof. unfold Child2Stable.word_37, global_word_1870, Child2Stable.closed_word_37, global_closed_1870, Child2Stable.expr_word_37, global_expr_1870.
 rewrite instance_23_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1870.
Transparent Child2Stable.word_38 global_word_807.
Lemma instance_23_word_38 v : Child2Stable.word_38 (instance_23_leaves v) = global_word_807 v.
Proof. unfold Child2Stable.word_38, global_word_807, Child2Stable.closed_word_38, global_closed_807, Child2Stable.expr_word_38, global_expr_807.
 rewrite instance_23_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_807.
Transparent Child2Stable.word_39 global_word_813.
Lemma instance_23_word_39 v : Child2Stable.word_39 (instance_23_leaves v) = global_word_813 v.
Proof. unfold Child2Stable.word_39, global_word_813, Child2Stable.closed_word_39, global_closed_813, Child2Stable.expr_word_39, global_expr_813.
 rewrite instance_23_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_813.
Transparent Child2Stable.word_40 global_word_778.
Lemma instance_23_word_40 v : Child2Stable.word_40 (instance_23_leaves v) = global_word_778 v.
Proof. unfold Child2Stable.word_40, global_word_778, Child2Stable.closed_word_40, global_closed_778, Child2Stable.expr_word_40, global_expr_778.
 rewrite instance_23_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_778.
Transparent Child2Stable.port_10_0 global_word_1872.
Lemma instance_23_port_10_0 v : Child2Stable.port_10_0 (instance_23_leaves v) = global_word_1872 v.
Proof. unfold Child2Stable.port_10_0, global_word_1872, Child2Stable.closed_port_10_0, global_closed_1872, Child2Stable.expr_port_10_0, global_expr_1872.
 rewrite instance_23_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1872.
Transparent Child2Stable.port_10_1 global_word_1873.
Lemma instance_23_port_10_1 v : Child2Stable.port_10_1 (instance_23_leaves v) = global_word_1873 v.
Proof. unfold Child2Stable.port_10_1, global_word_1873, Child2Stable.closed_port_10_1, global_closed_1873, Child2Stable.expr_port_10_1, global_expr_1873.
 rewrite instance_23_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1873.
Transparent Child2Stable.port_10_2 global_word_789.
Lemma instance_23_port_10_2 v : Child2Stable.port_10_2 (instance_23_leaves v) = global_word_789 v.
Proof. unfold Child2Stable.port_10_2, global_word_789, Child2Stable.closed_port_10_2, global_closed_789, Child2Stable.expr_port_10_2, global_expr_789.
 rewrite instance_23_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_789.
Transparent Child2Stable.port_10_3 global_word_794.
Lemma instance_23_port_10_3 v : Child2Stable.port_10_3 (instance_23_leaves v) = global_word_794 v.
Proof. unfold Child2Stable.port_10_3, global_word_794, Child2Stable.closed_port_10_3, global_closed_794, Child2Stable.expr_port_10_3, global_expr_794.
 rewrite instance_23_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_794.
Transparent Child2Stable.port_10_4 global_word_784.
Lemma instance_23_port_10_4 v : Child2Stable.port_10_4 (instance_23_leaves v) = global_word_784 v.
Proof. unfold Child2Stable.port_10_4, global_word_784, Child2Stable.closed_port_10_4, global_closed_784, Child2Stable.expr_port_10_4, global_expr_784.
 rewrite instance_23_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_784.
Transparent Child2Stable.port_11_0 global_word_1874.
Lemma instance_23_port_11_0 v : Child2Stable.port_11_0 (instance_23_leaves v) = global_word_1874 v.
Proof. unfold Child2Stable.port_11_0, global_word_1874, Child2Stable.closed_port_11_0, global_closed_1874, Child2Stable.expr_port_11_0, global_expr_1874.
 rewrite instance_23_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1874.
Transparent Child2Stable.port_11_1 global_word_1875.
Lemma instance_23_port_11_1 v : Child2Stable.port_11_1 (instance_23_leaves v) = global_word_1875 v.
Proof. unfold Child2Stable.port_11_1, global_word_1875, Child2Stable.closed_port_11_1, global_closed_1875, Child2Stable.expr_port_11_1, global_expr_1875.
 rewrite instance_23_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1875.
Transparent Child2Stable.port_11_2 global_word_808.
Lemma instance_23_port_11_2 v : Child2Stable.port_11_2 (instance_23_leaves v) = global_word_808 v.
Proof. unfold Child2Stable.port_11_2, global_word_808, Child2Stable.closed_port_11_2, global_closed_808, Child2Stable.expr_port_11_2, global_expr_808.
 rewrite instance_23_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_808.
Transparent Child2Stable.port_11_3 global_word_814.
Lemma instance_23_port_11_3 v : Child2Stable.port_11_3 (instance_23_leaves v) = global_word_814 v.
Proof. unfold Child2Stable.port_11_3, global_word_814, Child2Stable.closed_port_11_3, global_closed_814, Child2Stable.expr_port_11_3, global_expr_814.
 rewrite instance_23_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_814.
Transparent Child2Stable.port_11_4 global_word_779.
Lemma instance_23_port_11_4 v : Child2Stable.port_11_4 (instance_23_leaves v) = global_word_779 v.
Proof. unfold Child2Stable.port_11_4, global_word_779, Child2Stable.closed_port_11_4, global_closed_779, Child2Stable.expr_port_11_4, global_expr_779.
 rewrite instance_23_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_779.
Definition instance_24_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1893 v
| 0, 1 => global_word_1889 v
| 0, 2 => global_word_790 v
| 0, 3 => global_word_795 v
| 0, 4 => global_word_785 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1893.
Lemma instance_24_word_0 v : Child1Stable.word_0 (instance_24_leaves v) = global_word_1893 v.
Proof. unfold Child1Stable.word_0, instance_24_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1893.
Transparent Child1Stable.word_1 global_word_1889.
Lemma instance_24_word_1 v : Child1Stable.word_1 (instance_24_leaves v) = global_word_1889 v.
Proof. unfold Child1Stable.word_1, instance_24_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1889.
Transparent Child1Stable.word_2 global_word_790.
Lemma instance_24_word_2 v : Child1Stable.word_2 (instance_24_leaves v) = global_word_790 v.
Proof. unfold Child1Stable.word_2, instance_24_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_790.
Transparent Child1Stable.word_3 global_word_795.
Lemma instance_24_word_3 v : Child1Stable.word_3 (instance_24_leaves v) = global_word_795 v.
Proof. unfold Child1Stable.word_3, instance_24_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_795.
Transparent Child1Stable.word_4 global_word_785.
Lemma instance_24_word_4 v : Child1Stable.word_4 (instance_24_leaves v) = global_word_785 v.
Proof. unfold Child1Stable.word_4, instance_24_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_785.
Transparent Child1Stable.word_7 global_word_1876.
Lemma instance_24_word_7 v : Child1Stable.word_7 (instance_24_leaves v) = global_word_1876 v.
Proof. unfold Child1Stable.word_7, global_word_1876, Child1Stable.closed_word_7, global_closed_1876, Child1Stable.expr_word_7, global_expr_1876.
 rewrite instance_24_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1876.
Transparent Child1Stable.word_8 global_word_1877.
Lemma instance_24_word_8 v : Child1Stable.word_8 (instance_24_leaves v) = global_word_1877 v.
Proof. unfold Child1Stable.word_8, global_word_1877, Child1Stable.closed_word_8, global_closed_1877, Child1Stable.expr_word_8, global_expr_1877.
 rewrite instance_24_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1877.
Transparent Child1Stable.word_9 global_word_1878.
Lemma instance_24_word_9 v : Child1Stable.word_9 (instance_24_leaves v) = global_word_1878 v.
Proof. unfold Child1Stable.word_9, global_word_1878, Child1Stable.closed_word_9, global_closed_1878, Child1Stable.expr_word_9, global_expr_1878.
 rewrite instance_24_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1878.
Transparent Child1Stable.word_10 global_word_1879.
Lemma instance_24_word_10 v : Child1Stable.word_10 (instance_24_leaves v) = global_word_1879 v.
Proof. unfold Child1Stable.word_10, global_word_1879, Child1Stable.closed_word_10, global_closed_1879, Child1Stable.expr_word_10, global_expr_1879.
 rewrite instance_24_word_7 instance_24_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1879.
Transparent Child1Stable.word_11 global_word_1880.
Lemma instance_24_word_11 v : Child1Stable.word_11 (instance_24_leaves v) = global_word_1880 v.
Proof. unfold Child1Stable.word_11, global_word_1880, Child1Stable.closed_word_11, global_closed_1880, Child1Stable.expr_word_11, global_expr_1880.
 rewrite instance_24_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1880.
Transparent Child1Stable.word_12 global_word_1881.
Lemma instance_24_word_12 v : Child1Stable.word_12 (instance_24_leaves v) = global_word_1881 v.
Proof. unfold Child1Stable.word_12, global_word_1881, Child1Stable.closed_word_12, global_closed_1881, Child1Stable.expr_word_12, global_expr_1881.
 rewrite instance_24_word_9 instance_24_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1881.
Transparent Child1Stable.word_13 global_word_1882.
Lemma instance_24_word_13 v : Child1Stable.word_13 (instance_24_leaves v) = global_word_1882 v.
Proof. unfold Child1Stable.word_13, global_word_1882, Child1Stable.closed_word_13, global_closed_1882, Child1Stable.expr_word_13, global_expr_1882.
 rewrite instance_24_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1882.
Transparent Child1Stable.word_25 global_word_786.
Lemma instance_24_word_25 v : Child1Stable.word_25 (instance_24_leaves v) = global_word_786 v.
Proof. unfold Child1Stable.word_25, global_word_786, Child1Stable.closed_word_25, global_closed_786, Child1Stable.expr_word_25, global_expr_786.
 rewrite instance_24_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_786.
Transparent Child1Stable.word_23 global_word_791.
Lemma instance_24_word_23 v : Child1Stable.word_23 (instance_24_leaves v) = global_word_791 v.
Proof. unfold Child1Stable.word_23, global_word_791, Child1Stable.closed_word_23, global_closed_791, Child1Stable.expr_word_23, global_expr_791.
 rewrite instance_24_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_791.
Transparent Child1Stable.word_24 global_word_796.
Lemma instance_24_word_24 v : Child1Stable.word_24 (instance_24_leaves v) = global_word_796 v.
Proof. unfold Child1Stable.word_24, global_word_796, Child1Stable.closed_word_24, global_closed_796, Child1Stable.expr_word_24, global_expr_796.
 rewrite instance_24_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_796.
Transparent Child1Stable.word_26 global_word_797.
Lemma instance_24_word_26 v : Child1Stable.word_26 (instance_24_leaves v) = global_word_797 v.
Proof. unfold Child1Stable.word_26, global_word_797, Child1Stable.closed_word_26, global_closed_797, Child1Stable.expr_word_26, global_expr_797.
 rewrite instance_24_word_23 instance_24_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_797.
Transparent Child1Stable.word_28 global_word_798.
Lemma instance_24_word_28 v : Child1Stable.word_28 (instance_24_leaves v) = global_word_798 v.
Proof. unfold Child1Stable.word_28, global_word_798, Child1Stable.closed_word_28, global_closed_798, Child1Stable.expr_word_28, global_expr_798.
 rewrite instance_24_word_25 instance_24_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_798.
Transparent Child1Stable.word_27 global_word_799.
Lemma instance_24_word_27 v : Child1Stable.word_27 (instance_24_leaves v) = global_word_799 v.
Proof. unfold Child1Stable.word_27, global_word_799, Child1Stable.closed_word_27, global_closed_799, Child1Stable.expr_word_27, global_expr_799.
 rewrite instance_24_word_23 instance_24_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_799.
Transparent Child1Stable.word_29 global_word_800.
Lemma instance_24_word_29 v : Child1Stable.word_29 (instance_24_leaves v) = global_word_800 v.
Proof. unfold Child1Stable.word_29, global_word_800, Child1Stable.closed_word_29, global_closed_800, Child1Stable.expr_word_29, global_expr_800.
 rewrite instance_24_word_25 instance_24_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_800.
Transparent Child1Stable.word_30 global_word_801.
Lemma instance_24_word_30 v : Child1Stable.word_30 (instance_24_leaves v) = global_word_801 v.
Proof. unfold Child1Stable.word_30, global_word_801, Child1Stable.closed_word_30, global_closed_801, Child1Stable.expr_word_30, global_expr_801.
 rewrite instance_24_word_27 instance_24_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_801.
Transparent Child1Stable.word_31 global_word_802.
Lemma instance_24_word_31 v : Child1Stable.word_31 (instance_24_leaves v) = global_word_802 v.
Proof. unfold Child1Stable.word_31, global_word_802, Child1Stable.closed_word_31, global_closed_802, Child1Stable.expr_word_31, global_expr_802.
 rewrite instance_24_word_28 instance_24_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_802.
Transparent Child1Stable.word_32 global_word_803.
Lemma instance_24_word_32 v : Child1Stable.word_32 (instance_24_leaves v) = global_word_803 v.
Proof. unfold Child1Stable.word_32, global_word_803, Child1Stable.closed_word_32, global_closed_803, Child1Stable.expr_word_32, global_expr_803.
 rewrite instance_24_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_803.
Transparent Child1Stable.word_33 global_word_804.
Lemma instance_24_word_33 v : Child1Stable.word_33 (instance_24_leaves v) = global_word_804 v.
Proof. unfold Child1Stable.word_33, global_word_804, Child1Stable.closed_word_33, global_closed_804, Child1Stable.expr_word_33, global_expr_804.
 rewrite instance_24_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_804.
Transparent Child1Stable.word_5 global_word_805.
Lemma instance_24_word_5 v : Child1Stable.word_5 (instance_24_leaves v) = global_word_805 v.
Proof. unfold Child1Stable.word_5, global_word_805, Child1Stable.closed_word_5, global_closed_805, Child1Stable.expr_word_5, global_expr_805.
 rewrite instance_24_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_805.
Transparent Child1Stable.word_14 global_word_1883.
Lemma instance_24_word_14 v : Child1Stable.word_14 (instance_24_leaves v) = global_word_1883 v.
Proof. unfold Child1Stable.word_14, global_word_1883, Child1Stable.closed_word_14, global_closed_1883, Child1Stable.expr_word_14, global_expr_1883.
 rewrite instance_24_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1883.
Transparent Child1Stable.word_34 global_word_831.
Lemma instance_24_word_34 v : Child1Stable.word_34 (instance_24_leaves v) = global_word_831 v.
Proof. unfold Child1Stable.word_34, global_word_831, Child1Stable.closed_word_34, global_closed_831, Child1Stable.expr_word_34, global_expr_831.
 rewrite instance_24_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_831.
Transparent Child1Stable.word_6 global_word_832.
Lemma instance_24_word_6 v : Child1Stable.word_6 (instance_24_leaves v) = global_word_832 v.
Proof. unfold Child1Stable.word_6, global_word_832, Child1Stable.closed_word_6, global_closed_832, Child1Stable.expr_word_6, global_expr_832.
 rewrite instance_24_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_832.
Transparent Child1Stable.word_15 global_word_1884.
Lemma instance_24_word_15 v : Child1Stable.word_15 (instance_24_leaves v) = global_word_1884 v.
Proof. unfold Child1Stable.word_15, global_word_1884, Child1Stable.closed_word_15, global_closed_1884, Child1Stable.expr_word_15, global_expr_1884.
 rewrite instance_24_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1884.
Transparent Child1Stable.word_16 global_word_1885.
Lemma instance_24_word_16 v : Child1Stable.word_16 (instance_24_leaves v) = global_word_1885 v.
Proof. unfold Child1Stable.word_16, global_word_1885, Child1Stable.closed_word_16, global_closed_1885, Child1Stable.expr_word_16, global_expr_1885.
 rewrite instance_24_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1885.
Transparent Child1Stable.word_17 global_word_1886.
Lemma instance_24_word_17 v : Child1Stable.word_17 (instance_24_leaves v) = global_word_1886 v.
Proof. unfold Child1Stable.word_17, global_word_1886, Child1Stable.closed_word_17, global_closed_1886, Child1Stable.expr_word_17, global_expr_1886.
 rewrite instance_24_word_14 instance_24_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1886.
Transparent Child1Stable.word_18 global_word_1887.
Lemma instance_24_word_18 v : Child1Stable.word_18 (instance_24_leaves v) = global_word_1887 v.
Proof. unfold Child1Stable.word_18, global_word_1887, Child1Stable.closed_word_18, global_closed_1887, Child1Stable.expr_word_18, global_expr_1887.
 rewrite instance_24_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1887.
Transparent Child1Stable.word_19 global_word_1888.
Lemma instance_24_word_19 v : Child1Stable.word_19 (instance_24_leaves v) = global_word_1888 v.
Proof. unfold Child1Stable.word_19, global_word_1888, Child1Stable.closed_word_19, global_closed_1888, Child1Stable.expr_word_19, global_expr_1888.
 rewrite instance_24_word_13 instance_24_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1888.
Transparent Child1Stable.word_20 global_word_1890.
Lemma instance_24_word_20 v : Child1Stable.word_20 (instance_24_leaves v) = global_word_1890 v.
Proof. unfold Child1Stable.word_20, global_word_1890, Child1Stable.closed_word_20, global_closed_1890, Child1Stable.expr_word_20, global_expr_1890.
 rewrite instance_24_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1890.
Transparent Child1Stable.word_21 global_word_1891.
Lemma instance_24_word_21 v : Child1Stable.word_21 (instance_24_leaves v) = global_word_1891 v.
Proof. unfold Child1Stable.word_21, global_word_1891, Child1Stable.closed_word_21, global_closed_1891, Child1Stable.expr_word_21, global_expr_1891.
 rewrite instance_24_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1891.
Transparent Child1Stable.word_22 global_word_1892.
Lemma instance_24_word_22 v : Child1Stable.word_22 (instance_24_leaves v) = global_word_1892 v.
Proof. unfold Child1Stable.word_22, global_word_1892, Child1Stable.closed_word_22, global_closed_1892, Child1Stable.expr_word_22, global_expr_1892.
 rewrite instance_24_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1892.
Definition instance_25_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1911 v
| 0, 1 => global_word_1907 v
| 0, 2 => global_word_809 v
| 0, 3 => global_word_815 v
| 0, 4 => global_word_780 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1911.
Lemma instance_25_word_0 v : Child1Stable.word_0 (instance_25_leaves v) = global_word_1911 v.
Proof. unfold Child1Stable.word_0, instance_25_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1911.
Transparent Child1Stable.word_1 global_word_1907.
Lemma instance_25_word_1 v : Child1Stable.word_1 (instance_25_leaves v) = global_word_1907 v.
Proof. unfold Child1Stable.word_1, instance_25_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1907.
Transparent Child1Stable.word_2 global_word_809.
Lemma instance_25_word_2 v : Child1Stable.word_2 (instance_25_leaves v) = global_word_809 v.
Proof. unfold Child1Stable.word_2, instance_25_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_809.
Transparent Child1Stable.word_3 global_word_815.
Lemma instance_25_word_3 v : Child1Stable.word_3 (instance_25_leaves v) = global_word_815 v.
Proof. unfold Child1Stable.word_3, instance_25_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_815.
Transparent Child1Stable.word_4 global_word_780.
Lemma instance_25_word_4 v : Child1Stable.word_4 (instance_25_leaves v) = global_word_780 v.
Proof. unfold Child1Stable.word_4, instance_25_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_780.
Transparent Child1Stable.word_7 global_word_1894.
Lemma instance_25_word_7 v : Child1Stable.word_7 (instance_25_leaves v) = global_word_1894 v.
Proof. unfold Child1Stable.word_7, global_word_1894, Child1Stable.closed_word_7, global_closed_1894, Child1Stable.expr_word_7, global_expr_1894.
 rewrite instance_25_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1894.
Transparent Child1Stable.word_8 global_word_1895.
Lemma instance_25_word_8 v : Child1Stable.word_8 (instance_25_leaves v) = global_word_1895 v.
Proof. unfold Child1Stable.word_8, global_word_1895, Child1Stable.closed_word_8, global_closed_1895, Child1Stable.expr_word_8, global_expr_1895.
 rewrite instance_25_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1895.
Transparent Child1Stable.word_9 global_word_1896.
Lemma instance_25_word_9 v : Child1Stable.word_9 (instance_25_leaves v) = global_word_1896 v.
Proof. unfold Child1Stable.word_9, global_word_1896, Child1Stable.closed_word_9, global_closed_1896, Child1Stable.expr_word_9, global_expr_1896.
 rewrite instance_25_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1896.
Transparent Child1Stable.word_10 global_word_1897.
Lemma instance_25_word_10 v : Child1Stable.word_10 (instance_25_leaves v) = global_word_1897 v.
Proof. unfold Child1Stable.word_10, global_word_1897, Child1Stable.closed_word_10, global_closed_1897, Child1Stable.expr_word_10, global_expr_1897.
 rewrite instance_25_word_7 instance_25_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1897.
Transparent Child1Stable.word_11 global_word_1898.
Lemma instance_25_word_11 v : Child1Stable.word_11 (instance_25_leaves v) = global_word_1898 v.
Proof. unfold Child1Stable.word_11, global_word_1898, Child1Stable.closed_word_11, global_closed_1898, Child1Stable.expr_word_11, global_expr_1898.
 rewrite instance_25_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1898.
Transparent Child1Stable.word_12 global_word_1899.
Lemma instance_25_word_12 v : Child1Stable.word_12 (instance_25_leaves v) = global_word_1899 v.
Proof. unfold Child1Stable.word_12, global_word_1899, Child1Stable.closed_word_12, global_closed_1899, Child1Stable.expr_word_12, global_expr_1899.
 rewrite instance_25_word_9 instance_25_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1899.
Transparent Child1Stable.word_13 global_word_1900.
Lemma instance_25_word_13 v : Child1Stable.word_13 (instance_25_leaves v) = global_word_1900 v.
Proof. unfold Child1Stable.word_13, global_word_1900, Child1Stable.closed_word_13, global_closed_1900, Child1Stable.expr_word_13, global_expr_1900.
 rewrite instance_25_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1900.
Transparent Child1Stable.word_25 global_word_781.
Lemma instance_25_word_25 v : Child1Stable.word_25 (instance_25_leaves v) = global_word_781 v.
Proof. unfold Child1Stable.word_25, global_word_781, Child1Stable.closed_word_25, global_closed_781, Child1Stable.expr_word_25, global_expr_781.
 rewrite instance_25_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_781.
Transparent Child1Stable.word_23 global_word_810.
Lemma instance_25_word_23 v : Child1Stable.word_23 (instance_25_leaves v) = global_word_810 v.
Proof. unfold Child1Stable.word_23, global_word_810, Child1Stable.closed_word_23, global_closed_810, Child1Stable.expr_word_23, global_expr_810.
 rewrite instance_25_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_810.
Transparent Child1Stable.word_24 global_word_816.
Lemma instance_25_word_24 v : Child1Stable.word_24 (instance_25_leaves v) = global_word_816 v.
Proof. unfold Child1Stable.word_24, global_word_816, Child1Stable.closed_word_24, global_closed_816, Child1Stable.expr_word_24, global_expr_816.
 rewrite instance_25_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_816.
Transparent Child1Stable.word_26 global_word_817.
Lemma instance_25_word_26 v : Child1Stable.word_26 (instance_25_leaves v) = global_word_817 v.
Proof. unfold Child1Stable.word_26, global_word_817, Child1Stable.closed_word_26, global_closed_817, Child1Stable.expr_word_26, global_expr_817.
 rewrite instance_25_word_23 instance_25_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_817.
Transparent Child1Stable.word_28 global_word_818.
Lemma instance_25_word_28 v : Child1Stable.word_28 (instance_25_leaves v) = global_word_818 v.
Proof. unfold Child1Stable.word_28, global_word_818, Child1Stable.closed_word_28, global_closed_818, Child1Stable.expr_word_28, global_expr_818.
 rewrite instance_25_word_25 instance_25_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_818.
Transparent Child1Stable.word_27 global_word_819.
Lemma instance_25_word_27 v : Child1Stable.word_27 (instance_25_leaves v) = global_word_819 v.
Proof. unfold Child1Stable.word_27, global_word_819, Child1Stable.closed_word_27, global_closed_819, Child1Stable.expr_word_27, global_expr_819.
 rewrite instance_25_word_23 instance_25_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_819.
Transparent Child1Stable.word_29 global_word_820.
Lemma instance_25_word_29 v : Child1Stable.word_29 (instance_25_leaves v) = global_word_820 v.
Proof. unfold Child1Stable.word_29, global_word_820, Child1Stable.closed_word_29, global_closed_820, Child1Stable.expr_word_29, global_expr_820.
 rewrite instance_25_word_25 instance_25_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_820.
Transparent Child1Stable.word_30 global_word_821.
Lemma instance_25_word_30 v : Child1Stable.word_30 (instance_25_leaves v) = global_word_821 v.
Proof. unfold Child1Stable.word_30, global_word_821, Child1Stable.closed_word_30, global_closed_821, Child1Stable.expr_word_30, global_expr_821.
 rewrite instance_25_word_27 instance_25_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_821.
Transparent Child1Stable.word_31 global_word_822.
Lemma instance_25_word_31 v : Child1Stable.word_31 (instance_25_leaves v) = global_word_822 v.
Proof. unfold Child1Stable.word_31, global_word_822, Child1Stable.closed_word_31, global_closed_822, Child1Stable.expr_word_31, global_expr_822.
 rewrite instance_25_word_28 instance_25_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_822.
Transparent Child1Stable.word_32 global_word_823.
Lemma instance_25_word_32 v : Child1Stable.word_32 (instance_25_leaves v) = global_word_823 v.
Proof. unfold Child1Stable.word_32, global_word_823, Child1Stable.closed_word_32, global_closed_823, Child1Stable.expr_word_32, global_expr_823.
 rewrite instance_25_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_823.
Transparent Child1Stable.word_33 global_word_824.
Lemma instance_25_word_33 v : Child1Stable.word_33 (instance_25_leaves v) = global_word_824 v.
Proof. unfold Child1Stable.word_33, global_word_824, Child1Stable.closed_word_33, global_closed_824, Child1Stable.expr_word_33, global_expr_824.
 rewrite instance_25_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_824.
Transparent Child1Stable.word_5 global_word_825.
Lemma instance_25_word_5 v : Child1Stable.word_5 (instance_25_leaves v) = global_word_825 v.
Proof. unfold Child1Stable.word_5, global_word_825, Child1Stable.closed_word_5, global_closed_825, Child1Stable.expr_word_5, global_expr_825.
 rewrite instance_25_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_825.
Transparent Child1Stable.word_14 global_word_1901.
Lemma instance_25_word_14 v : Child1Stable.word_14 (instance_25_leaves v) = global_word_1901 v.
Proof. unfold Child1Stable.word_14, global_word_1901, Child1Stable.closed_word_14, global_closed_1901, Child1Stable.expr_word_14, global_expr_1901.
 rewrite instance_25_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1901.
Transparent Child1Stable.word_34 global_word_838.
Lemma instance_25_word_34 v : Child1Stable.word_34 (instance_25_leaves v) = global_word_838 v.
Proof. unfold Child1Stable.word_34, global_word_838, Child1Stable.closed_word_34, global_closed_838, Child1Stable.expr_word_34, global_expr_838.
 rewrite instance_25_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_838.
Transparent Child1Stable.word_6 global_word_839.
Lemma instance_25_word_6 v : Child1Stable.word_6 (instance_25_leaves v) = global_word_839 v.
Proof. unfold Child1Stable.word_6, global_word_839, Child1Stable.closed_word_6, global_closed_839, Child1Stable.expr_word_6, global_expr_839.
 rewrite instance_25_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_839.
Transparent Child1Stable.word_15 global_word_1902.
Lemma instance_25_word_15 v : Child1Stable.word_15 (instance_25_leaves v) = global_word_1902 v.
Proof. unfold Child1Stable.word_15, global_word_1902, Child1Stable.closed_word_15, global_closed_1902, Child1Stable.expr_word_15, global_expr_1902.
 rewrite instance_25_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1902.
Transparent Child1Stable.word_16 global_word_1903.
Lemma instance_25_word_16 v : Child1Stable.word_16 (instance_25_leaves v) = global_word_1903 v.
Proof. unfold Child1Stable.word_16, global_word_1903, Child1Stable.closed_word_16, global_closed_1903, Child1Stable.expr_word_16, global_expr_1903.
 rewrite instance_25_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1903.
Transparent Child1Stable.word_17 global_word_1904.
Lemma instance_25_word_17 v : Child1Stable.word_17 (instance_25_leaves v) = global_word_1904 v.
Proof. unfold Child1Stable.word_17, global_word_1904, Child1Stable.closed_word_17, global_closed_1904, Child1Stable.expr_word_17, global_expr_1904.
 rewrite instance_25_word_14 instance_25_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1904.
Transparent Child1Stable.word_18 global_word_1905.
Lemma instance_25_word_18 v : Child1Stable.word_18 (instance_25_leaves v) = global_word_1905 v.
Proof. unfold Child1Stable.word_18, global_word_1905, Child1Stable.closed_word_18, global_closed_1905, Child1Stable.expr_word_18, global_expr_1905.
 rewrite instance_25_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1905.
Transparent Child1Stable.word_19 global_word_1906.
Lemma instance_25_word_19 v : Child1Stable.word_19 (instance_25_leaves v) = global_word_1906 v.
Proof. unfold Child1Stable.word_19, global_word_1906, Child1Stable.closed_word_19, global_closed_1906, Child1Stable.expr_word_19, global_expr_1906.
 rewrite instance_25_word_13 instance_25_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1906.
Transparent Child1Stable.word_20 global_word_1908.
Lemma instance_25_word_20 v : Child1Stable.word_20 (instance_25_leaves v) = global_word_1908 v.
Proof. unfold Child1Stable.word_20, global_word_1908, Child1Stable.closed_word_20, global_closed_1908, Child1Stable.expr_word_20, global_expr_1908.
 rewrite instance_25_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1908.
Transparent Child1Stable.word_21 global_word_1909.
Lemma instance_25_word_21 v : Child1Stable.word_21 (instance_25_leaves v) = global_word_1909 v.
Proof. unfold Child1Stable.word_21, global_word_1909, Child1Stable.closed_word_21, global_closed_1909, Child1Stable.expr_word_21, global_expr_1909.
 rewrite instance_25_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1909.
Transparent Child1Stable.word_22 global_word_1910.
Lemma instance_25_word_22 v : Child1Stable.word_22 (instance_25_leaves v) = global_word_1910 v.
Proof. unfold Child1Stable.word_22, global_word_1910, Child1Stable.closed_word_22, global_closed_1910, Child1Stable.expr_word_22, global_expr_1910.
 rewrite instance_25_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1910.
Definition instance_26_leaves (v:global_leaves) : Child2Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1939 v
| 0, 1 => global_word_1935 v
| 0, 2 => global_word_857 v
| 0, 3 => global_word_862 v
| 0, 4 => global_word_852 v
| 0, 5 => global_word_881 v
| 0, 6 => global_word_846 v
| 10, 5 => global_word_875 v
| 10, 6 => global_word_902 v
| 11, 5 => global_word_895 v
| 11, 6 => global_word_909 v
| _,_ => [::] end.
Transparent Child2Stable.word_0 global_word_1939.
Lemma instance_26_word_0 v : Child2Stable.word_0 (instance_26_leaves v) = global_word_1939 v.
Proof. unfold Child2Stable.word_0, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.word_0 global_word_1939.
Transparent Child2Stable.word_1 global_word_1935.
Lemma instance_26_word_1 v : Child2Stable.word_1 (instance_26_leaves v) = global_word_1935 v.
Proof. unfold Child2Stable.word_1, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.word_1 global_word_1935.
Transparent Child2Stable.word_2 global_word_857.
Lemma instance_26_word_2 v : Child2Stable.word_2 (instance_26_leaves v) = global_word_857 v.
Proof. unfold Child2Stable.word_2, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.word_2 global_word_857.
Transparent Child2Stable.word_3 global_word_862.
Lemma instance_26_word_3 v : Child2Stable.word_3 (instance_26_leaves v) = global_word_862 v.
Proof. unfold Child2Stable.word_3, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.word_3 global_word_862.
Transparent Child2Stable.word_4 global_word_852.
Lemma instance_26_word_4 v : Child2Stable.word_4 (instance_26_leaves v) = global_word_852 v.
Proof. unfold Child2Stable.word_4, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.word_4 global_word_852.
Transparent Child2Stable.word_5 global_word_881.
Lemma instance_26_word_5 v : Child2Stable.word_5 (instance_26_leaves v) = global_word_881 v.
Proof. unfold Child2Stable.word_5, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.word_5 global_word_881.
Transparent Child2Stable.word_6 global_word_846.
Lemma instance_26_word_6 v : Child2Stable.word_6 (instance_26_leaves v) = global_word_846 v.
Proof. unfold Child2Stable.word_6, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.word_6 global_word_846.
Transparent Child2Stable.port_10_5 global_word_875.
Lemma instance_26_port_10_5 v : Child2Stable.port_10_5 (instance_26_leaves v) = global_word_875 v.
Proof. unfold Child2Stable.port_10_5, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_5 global_word_875.
Transparent Child2Stable.port_10_6 global_word_902.
Lemma instance_26_port_10_6 v : Child2Stable.port_10_6 (instance_26_leaves v) = global_word_902 v.
Proof. unfold Child2Stable.port_10_6, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.port_10_6 global_word_902.
Transparent Child2Stable.port_11_5 global_word_895.
Lemma instance_26_port_11_5 v : Child2Stable.port_11_5 (instance_26_leaves v) = global_word_895 v.
Proof. unfold Child2Stable.port_11_5, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_5 global_word_895.
Transparent Child2Stable.port_11_6 global_word_909.
Lemma instance_26_port_11_6 v : Child2Stable.port_11_6 (instance_26_leaves v) = global_word_909 v.
Proof. unfold Child2Stable.port_11_6, instance_26_leaves. reflexivity. Qed.
Opaque Child2Stable.port_11_6 global_word_909.
Transparent Child2Stable.word_12 global_word_1912.
Lemma instance_26_word_12 v : Child2Stable.word_12 (instance_26_leaves v) = global_word_1912 v.
Proof. unfold Child2Stable.word_12, global_word_1912, Child2Stable.closed_word_12, global_closed_1912, Child2Stable.expr_word_12, global_expr_1912.
 rewrite instance_26_word_2.
 reflexivity. Qed. Opaque Child2Stable.word_12 global_word_1912.
Transparent Child2Stable.word_13 global_word_1913.
Lemma instance_26_word_13 v : Child2Stable.word_13 (instance_26_leaves v) = global_word_1913 v.
Proof. unfold Child2Stable.word_13, global_word_1913, Child2Stable.closed_word_13, global_closed_1913, Child2Stable.expr_word_13, global_expr_1913.
 rewrite instance_26_word_3.
 reflexivity. Qed. Opaque Child2Stable.word_13 global_word_1913.
Transparent Child2Stable.word_14 global_word_1914.
Lemma instance_26_word_14 v : Child2Stable.word_14 (instance_26_leaves v) = global_word_1914 v.
Proof. unfold Child2Stable.word_14, global_word_1914, Child2Stable.closed_word_14, global_closed_1914, Child2Stable.expr_word_14, global_expr_1914.
 rewrite instance_26_word_4.
 reflexivity. Qed. Opaque Child2Stable.word_14 global_word_1914.
Transparent Child2Stable.word_15 global_word_1915.
Lemma instance_26_word_15 v : Child2Stable.word_15 (instance_26_leaves v) = global_word_1915 v.
Proof. unfold Child2Stable.word_15, global_word_1915, Child2Stable.closed_word_15, global_closed_1915, Child2Stable.expr_word_15, global_expr_1915.
 rewrite instance_26_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_15 global_word_1915.
Transparent Child2Stable.word_16 global_word_1916.
Lemma instance_26_word_16 v : Child2Stable.word_16 (instance_26_leaves v) = global_word_1916 v.
Proof. unfold Child2Stable.word_16, global_word_1916, Child2Stable.closed_word_16, global_closed_1916, Child2Stable.expr_word_16, global_expr_1916.
 rewrite instance_26_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_16 global_word_1916.
Transparent Child2Stable.word_17 global_word_1917.
Lemma instance_26_word_17 v : Child2Stable.word_17 (instance_26_leaves v) = global_word_1917 v.
Proof. unfold Child2Stable.word_17, global_word_1917, Child2Stable.closed_word_17, global_closed_1917, Child2Stable.expr_word_17, global_expr_1917.
 rewrite instance_26_word_12 instance_26_word_13.
 reflexivity. Qed. Opaque Child2Stable.word_17 global_word_1917.
Transparent Child2Stable.word_18 global_word_1918.
Lemma instance_26_word_18 v : Child2Stable.word_18 (instance_26_leaves v) = global_word_1918 v.
Proof. unfold Child2Stable.word_18, global_word_1918, Child2Stable.closed_word_18, global_closed_1918, Child2Stable.expr_word_18, global_expr_1918.
 rewrite instance_26_word_17.
 reflexivity. Qed. Opaque Child2Stable.word_18 global_word_1918.
Transparent Child2Stable.word_19 global_word_1919.
Lemma instance_26_word_19 v : Child2Stable.word_19 (instance_26_leaves v) = global_word_1919 v.
Proof. unfold Child2Stable.word_19, global_word_1919, Child2Stable.closed_word_19, global_closed_1919, Child2Stable.expr_word_19, global_expr_1919.
 rewrite instance_26_word_14 instance_26_word_18.
 reflexivity. Qed. Opaque Child2Stable.word_19 global_word_1919.
Transparent Child2Stable.word_20 global_word_1920.
Lemma instance_26_word_20 v : Child2Stable.word_20 (instance_26_leaves v) = global_word_1920 v.
Proof. unfold Child2Stable.word_20, global_word_1920, Child2Stable.closed_word_20, global_closed_1920, Child2Stable.expr_word_20, global_expr_1920.
 rewrite instance_26_word_19.
 reflexivity. Qed. Opaque Child2Stable.word_20 global_word_1920.
Transparent Child2Stable.word_21 global_word_1921.
Lemma instance_26_word_21 v : Child2Stable.word_21 (instance_26_leaves v) = global_word_1921 v.
Proof. unfold Child2Stable.word_21, global_word_1921, Child2Stable.closed_word_21, global_closed_1921, Child2Stable.expr_word_21, global_expr_1921.
 rewrite instance_26_word_15 instance_26_word_20.
 reflexivity. Qed. Opaque Child2Stable.word_21 global_word_1921.
Transparent Child2Stable.word_22 global_word_1922.
Lemma instance_26_word_22 v : Child2Stable.word_22 (instance_26_leaves v) = global_word_1922 v.
Proof. unfold Child2Stable.word_22, global_word_1922, Child2Stable.closed_word_22, global_closed_1922, Child2Stable.expr_word_22, global_expr_1922.
 rewrite instance_26_word_21.
 reflexivity. Qed. Opaque Child2Stable.word_22 global_word_1922.
Transparent Child2Stable.word_23 global_word_1923.
Lemma instance_26_word_23 v : Child2Stable.word_23 (instance_26_leaves v) = global_word_1923 v.
Proof. unfold Child2Stable.word_23, global_word_1923, Child2Stable.closed_word_23, global_closed_1923, Child2Stable.expr_word_23, global_expr_1923.
 rewrite instance_26_word_16 instance_26_word_22.
 reflexivity. Qed. Opaque Child2Stable.word_23 global_word_1923.
Transparent Child2Stable.word_24 global_word_1924.
Lemma instance_26_word_24 v : Child2Stable.word_24 (instance_26_leaves v) = global_word_1924 v.
Proof. unfold Child2Stable.word_24, global_word_1924, Child2Stable.closed_word_24, global_closed_1924, Child2Stable.expr_word_24, global_expr_1924.
 rewrite instance_26_word_23.
 reflexivity. Qed. Opaque Child2Stable.word_24 global_word_1924.
Transparent Child2Stable.word_41 global_word_896.
Lemma instance_26_word_41 v : Child2Stable.word_41 (instance_26_leaves v) = global_word_896 v.
Proof. unfold Child2Stable.word_41, global_word_896, Child2Stable.closed_word_41, global_closed_896, Child2Stable.expr_word_41, global_expr_896.
 rewrite instance_26_port_11_5.
 reflexivity. Qed. Opaque Child2Stable.word_41 global_word_896.
Transparent Child2Stable.word_7 global_word_897.
Lemma instance_26_word_7 v : Child2Stable.word_7 (instance_26_leaves v) = global_word_897 v.
Proof. unfold Child2Stable.word_7, global_word_897, Child2Stable.closed_word_7, global_closed_897, Child2Stable.expr_word_7, global_expr_897.
 rewrite instance_26_word_41.
 reflexivity. Qed. Opaque Child2Stable.word_7 global_word_897.
Transparent Child2Stable.word_25 global_word_1925.
Lemma instance_26_word_25 v : Child2Stable.word_25 (instance_26_leaves v) = global_word_1925 v.
Proof. unfold Child2Stable.word_25, global_word_1925, Child2Stable.closed_word_25, global_closed_1925, Child2Stable.expr_word_25, global_expr_1925.
 rewrite instance_26_word_7.
 reflexivity. Qed. Opaque Child2Stable.word_25 global_word_1925.
Transparent Child2Stable.word_42 global_word_903.
Lemma instance_26_word_42 v : Child2Stable.word_42 (instance_26_leaves v) = global_word_903 v.
Proof. unfold Child2Stable.word_42, global_word_903, Child2Stable.closed_word_42, global_closed_903, Child2Stable.expr_word_42, global_expr_903.
 rewrite instance_26_port_10_6.
 reflexivity. Qed. Opaque Child2Stable.word_42 global_word_903.
Transparent Child2Stable.word_8 global_word_904.
Lemma instance_26_word_8 v : Child2Stable.word_8 (instance_26_leaves v) = global_word_904 v.
Proof. unfold Child2Stable.word_8, global_word_904, Child2Stable.closed_word_8, global_closed_904, Child2Stable.expr_word_8, global_expr_904.
 rewrite instance_26_word_42.
 reflexivity. Qed. Opaque Child2Stable.word_8 global_word_904.
Transparent Child2Stable.word_26 global_word_1926.
Lemma instance_26_word_26 v : Child2Stable.word_26 (instance_26_leaves v) = global_word_1926 v.
Proof. unfold Child2Stable.word_26, global_word_1926, Child2Stable.closed_word_26, global_closed_1926, Child2Stable.expr_word_26, global_expr_1926.
 rewrite instance_26_word_8.
 reflexivity. Qed. Opaque Child2Stable.word_26 global_word_1926.
Transparent Child2Stable.word_27 global_word_1927.
Lemma instance_26_word_27 v : Child2Stable.word_27 (instance_26_leaves v) = global_word_1927 v.
Proof. unfold Child2Stable.word_27, global_word_1927, Child2Stable.closed_word_27, global_closed_1927, Child2Stable.expr_word_27, global_expr_1927.
 rewrite instance_26_word_26.
 reflexivity. Qed. Opaque Child2Stable.word_27 global_word_1927.
Transparent Child2Stable.word_43 global_word_910.
Lemma instance_26_word_43 v : Child2Stable.word_43 (instance_26_leaves v) = global_word_910 v.
Proof. unfold Child2Stable.word_43, global_word_910, Child2Stable.closed_word_43, global_closed_910, Child2Stable.expr_word_43, global_expr_910.
 rewrite instance_26_port_11_6.
 reflexivity. Qed. Opaque Child2Stable.word_43 global_word_910.
Transparent Child2Stable.word_9 global_word_911.
Lemma instance_26_word_9 v : Child2Stable.word_9 (instance_26_leaves v) = global_word_911 v.
Proof. unfold Child2Stable.word_9, global_word_911, Child2Stable.closed_word_9, global_closed_911, Child2Stable.expr_word_9, global_expr_911.
 rewrite instance_26_word_43.
 reflexivity. Qed. Opaque Child2Stable.word_9 global_word_911.
Transparent Child2Stable.word_28 global_word_1928.
Lemma instance_26_word_28 v : Child2Stable.word_28 (instance_26_leaves v) = global_word_1928 v.
Proof. unfold Child2Stable.word_28, global_word_1928, Child2Stable.closed_word_28, global_closed_1928, Child2Stable.expr_word_28, global_expr_1928.
 rewrite instance_26_word_9.
 reflexivity. Qed. Opaque Child2Stable.word_28 global_word_1928.
Transparent Child2Stable.word_29 global_word_1929.
Lemma instance_26_word_29 v : Child2Stable.word_29 (instance_26_leaves v) = global_word_1929 v.
Proof. unfold Child2Stable.word_29, global_word_1929, Child2Stable.closed_word_29, global_closed_1929, Child2Stable.expr_word_29, global_expr_1929.
 rewrite instance_26_word_28.
 reflexivity. Qed. Opaque Child2Stable.word_29 global_word_1929.
Transparent Child2Stable.word_30 global_word_1930.
Lemma instance_26_word_30 v : Child2Stable.word_30 (instance_26_leaves v) = global_word_1930 v.
Proof. unfold Child2Stable.word_30, global_word_1930, Child2Stable.closed_word_30, global_closed_1930, Child2Stable.expr_word_30, global_expr_1930.
 rewrite instance_26_word_25 instance_26_word_27.
 reflexivity. Qed. Opaque Child2Stable.word_30 global_word_1930.
Transparent Child2Stable.word_31 global_word_1931.
Lemma instance_26_word_31 v : Child2Stable.word_31 (instance_26_leaves v) = global_word_1931 v.
Proof. unfold Child2Stable.word_31, global_word_1931, Child2Stable.closed_word_31, global_closed_1931, Child2Stable.expr_word_31, global_expr_1931.
 rewrite instance_26_word_30.
 reflexivity. Qed. Opaque Child2Stable.word_31 global_word_1931.
Transparent Child2Stable.word_32 global_word_1932.
Lemma instance_26_word_32 v : Child2Stable.word_32 (instance_26_leaves v) = global_word_1932 v.
Proof. unfold Child2Stable.word_32, global_word_1932, Child2Stable.closed_word_32, global_closed_1932, Child2Stable.expr_word_32, global_expr_1932.
 rewrite instance_26_word_29 instance_26_word_31.
 reflexivity. Qed. Opaque Child2Stable.word_32 global_word_1932.
Transparent Child2Stable.word_33 global_word_1933.
Lemma instance_26_word_33 v : Child2Stable.word_33 (instance_26_leaves v) = global_word_1933 v.
Proof. unfold Child2Stable.word_33, global_word_1933, Child2Stable.closed_word_33, global_closed_1933, Child2Stable.expr_word_33, global_expr_1933.
 rewrite instance_26_word_32.
 reflexivity. Qed. Opaque Child2Stable.word_33 global_word_1933.
Transparent Child2Stable.word_34 global_word_1934.
Lemma instance_26_word_34 v : Child2Stable.word_34 (instance_26_leaves v) = global_word_1934 v.
Proof. unfold Child2Stable.word_34, global_word_1934, Child2Stable.closed_word_34, global_closed_1934, Child2Stable.expr_word_34, global_expr_1934.
 rewrite instance_26_word_24 instance_26_word_33.
 reflexivity. Qed. Opaque Child2Stable.word_34 global_word_1934.
Transparent Child2Stable.word_35 global_word_1936.
Lemma instance_26_word_35 v : Child2Stable.word_35 (instance_26_leaves v) = global_word_1936 v.
Proof. unfold Child2Stable.word_35, global_word_1936, Child2Stable.closed_word_35, global_closed_1936, Child2Stable.expr_word_35, global_expr_1936.
 rewrite instance_26_word_1.
 reflexivity. Qed. Opaque Child2Stable.word_35 global_word_1936.
Transparent Child2Stable.word_36 global_word_1937.
Lemma instance_26_word_36 v : Child2Stable.word_36 (instance_26_leaves v) = global_word_1937 v.
Proof. unfold Child2Stable.word_36, global_word_1937, Child2Stable.closed_word_36, global_closed_1937, Child2Stable.expr_word_36, global_expr_1937.
 rewrite instance_26_word_35.
 reflexivity. Qed. Opaque Child2Stable.word_36 global_word_1937.
Transparent Child2Stable.word_37 global_word_1938.
Lemma instance_26_word_37 v : Child2Stable.word_37 (instance_26_leaves v) = global_word_1938 v.
Proof. unfold Child2Stable.word_37, global_word_1938, Child2Stable.closed_word_37, global_closed_1938, Child2Stable.expr_word_37, global_expr_1938.
 rewrite instance_26_word_34.
 reflexivity. Qed. Opaque Child2Stable.word_37 global_word_1938.
Transparent Child2Stable.word_38 global_word_876.
Lemma instance_26_word_38 v : Child2Stable.word_38 (instance_26_leaves v) = global_word_876 v.
Proof. unfold Child2Stable.word_38, global_word_876, Child2Stable.closed_word_38, global_closed_876, Child2Stable.expr_word_38, global_expr_876.
 rewrite instance_26_port_10_5.
 reflexivity. Qed. Opaque Child2Stable.word_38 global_word_876.
Transparent Child2Stable.word_39 global_word_882.
Lemma instance_26_word_39 v : Child2Stable.word_39 (instance_26_leaves v) = global_word_882 v.
Proof. unfold Child2Stable.word_39, global_word_882, Child2Stable.closed_word_39, global_closed_882, Child2Stable.expr_word_39, global_expr_882.
 rewrite instance_26_word_5.
 reflexivity. Qed. Opaque Child2Stable.word_39 global_word_882.
Transparent Child2Stable.word_40 global_word_847.
Lemma instance_26_word_40 v : Child2Stable.word_40 (instance_26_leaves v) = global_word_847 v.
Proof. unfold Child2Stable.word_40, global_word_847, Child2Stable.closed_word_40, global_closed_847, Child2Stable.expr_word_40, global_expr_847.
 rewrite instance_26_word_6.
 reflexivity. Qed. Opaque Child2Stable.word_40 global_word_847.
Transparent Child2Stable.port_10_0 global_word_1940.
Lemma instance_26_port_10_0 v : Child2Stable.port_10_0 (instance_26_leaves v) = global_word_1940 v.
Proof. unfold Child2Stable.port_10_0, global_word_1940, Child2Stable.closed_port_10_0, global_closed_1940, Child2Stable.expr_port_10_0, global_expr_1940.
 rewrite instance_26_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_10_0 global_word_1940.
Transparent Child2Stable.port_10_1 global_word_1941.
Lemma instance_26_port_10_1 v : Child2Stable.port_10_1 (instance_26_leaves v) = global_word_1941 v.
Proof. unfold Child2Stable.port_10_1, global_word_1941, Child2Stable.closed_port_10_1, global_closed_1941, Child2Stable.expr_port_10_1, global_expr_1941.
 rewrite instance_26_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_10_1 global_word_1941.
Transparent Child2Stable.port_10_2 global_word_858.
Lemma instance_26_port_10_2 v : Child2Stable.port_10_2 (instance_26_leaves v) = global_word_858 v.
Proof. unfold Child2Stable.port_10_2, global_word_858, Child2Stable.closed_port_10_2, global_closed_858, Child2Stable.expr_port_10_2, global_expr_858.
 rewrite instance_26_word_2.
 reflexivity. Qed. Opaque Child2Stable.port_10_2 global_word_858.
Transparent Child2Stable.port_10_3 global_word_863.
Lemma instance_26_port_10_3 v : Child2Stable.port_10_3 (instance_26_leaves v) = global_word_863 v.
Proof. unfold Child2Stable.port_10_3, global_word_863, Child2Stable.closed_port_10_3, global_closed_863, Child2Stable.expr_port_10_3, global_expr_863.
 rewrite instance_26_word_3.
 reflexivity. Qed. Opaque Child2Stable.port_10_3 global_word_863.
Transparent Child2Stable.port_10_4 global_word_853.
Lemma instance_26_port_10_4 v : Child2Stable.port_10_4 (instance_26_leaves v) = global_word_853 v.
Proof. unfold Child2Stable.port_10_4, global_word_853, Child2Stable.closed_port_10_4, global_closed_853, Child2Stable.expr_port_10_4, global_expr_853.
 rewrite instance_26_word_4.
 reflexivity. Qed. Opaque Child2Stable.port_10_4 global_word_853.
Transparent Child2Stable.port_11_0 global_word_1942.
Lemma instance_26_port_11_0 v : Child2Stable.port_11_0 (instance_26_leaves v) = global_word_1942 v.
Proof. unfold Child2Stable.port_11_0, global_word_1942, Child2Stable.closed_port_11_0, global_closed_1942, Child2Stable.expr_port_11_0, global_expr_1942.
 rewrite instance_26_word_0.
 reflexivity. Qed. Opaque Child2Stable.port_11_0 global_word_1942.
Transparent Child2Stable.port_11_1 global_word_1943.
Lemma instance_26_port_11_1 v : Child2Stable.port_11_1 (instance_26_leaves v) = global_word_1943 v.
Proof. unfold Child2Stable.port_11_1, global_word_1943, Child2Stable.closed_port_11_1, global_closed_1943, Child2Stable.expr_port_11_1, global_expr_1943.
 rewrite instance_26_word_1.
 reflexivity. Qed. Opaque Child2Stable.port_11_1 global_word_1943.
Transparent Child2Stable.port_11_2 global_word_877.
Lemma instance_26_port_11_2 v : Child2Stable.port_11_2 (instance_26_leaves v) = global_word_877 v.
Proof. unfold Child2Stable.port_11_2, global_word_877, Child2Stable.closed_port_11_2, global_closed_877, Child2Stable.expr_port_11_2, global_expr_877.
 rewrite instance_26_word_38.
 reflexivity. Qed. Opaque Child2Stable.port_11_2 global_word_877.
Transparent Child2Stable.port_11_3 global_word_883.
Lemma instance_26_port_11_3 v : Child2Stable.port_11_3 (instance_26_leaves v) = global_word_883 v.
Proof. unfold Child2Stable.port_11_3, global_word_883, Child2Stable.closed_port_11_3, global_closed_883, Child2Stable.expr_port_11_3, global_expr_883.
 rewrite instance_26_word_39.
 reflexivity. Qed. Opaque Child2Stable.port_11_3 global_word_883.
Transparent Child2Stable.port_11_4 global_word_848.
Lemma instance_26_port_11_4 v : Child2Stable.port_11_4 (instance_26_leaves v) = global_word_848 v.
Proof. unfold Child2Stable.port_11_4, global_word_848, Child2Stable.closed_port_11_4, global_closed_848, Child2Stable.expr_port_11_4, global_expr_848.
 rewrite instance_26_word_40.
 reflexivity. Qed. Opaque Child2Stable.port_11_4 global_word_848.
Definition instance_27_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1961 v
| 0, 1 => global_word_1957 v
| 0, 2 => global_word_859 v
| 0, 3 => global_word_864 v
| 0, 4 => global_word_854 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1961.
Lemma instance_27_word_0 v : Child1Stable.word_0 (instance_27_leaves v) = global_word_1961 v.
Proof. unfold Child1Stable.word_0, instance_27_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1961.
Transparent Child1Stable.word_1 global_word_1957.
Lemma instance_27_word_1 v : Child1Stable.word_1 (instance_27_leaves v) = global_word_1957 v.
Proof. unfold Child1Stable.word_1, instance_27_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1957.
Transparent Child1Stable.word_2 global_word_859.
Lemma instance_27_word_2 v : Child1Stable.word_2 (instance_27_leaves v) = global_word_859 v.
Proof. unfold Child1Stable.word_2, instance_27_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_859.
Transparent Child1Stable.word_3 global_word_864.
Lemma instance_27_word_3 v : Child1Stable.word_3 (instance_27_leaves v) = global_word_864 v.
Proof. unfold Child1Stable.word_3, instance_27_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_864.
Transparent Child1Stable.word_4 global_word_854.
Lemma instance_27_word_4 v : Child1Stable.word_4 (instance_27_leaves v) = global_word_854 v.
Proof. unfold Child1Stable.word_4, instance_27_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_854.
Transparent Child1Stable.word_7 global_word_1944.
Lemma instance_27_word_7 v : Child1Stable.word_7 (instance_27_leaves v) = global_word_1944 v.
Proof. unfold Child1Stable.word_7, global_word_1944, Child1Stable.closed_word_7, global_closed_1944, Child1Stable.expr_word_7, global_expr_1944.
 rewrite instance_27_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1944.
Transparent Child1Stable.word_8 global_word_1945.
Lemma instance_27_word_8 v : Child1Stable.word_8 (instance_27_leaves v) = global_word_1945 v.
Proof. unfold Child1Stable.word_8, global_word_1945, Child1Stable.closed_word_8, global_closed_1945, Child1Stable.expr_word_8, global_expr_1945.
 rewrite instance_27_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1945.
Transparent Child1Stable.word_9 global_word_1946.
Lemma instance_27_word_9 v : Child1Stable.word_9 (instance_27_leaves v) = global_word_1946 v.
Proof. unfold Child1Stable.word_9, global_word_1946, Child1Stable.closed_word_9, global_closed_1946, Child1Stable.expr_word_9, global_expr_1946.
 rewrite instance_27_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1946.
Transparent Child1Stable.word_10 global_word_1947.
Lemma instance_27_word_10 v : Child1Stable.word_10 (instance_27_leaves v) = global_word_1947 v.
Proof. unfold Child1Stable.word_10, global_word_1947, Child1Stable.closed_word_10, global_closed_1947, Child1Stable.expr_word_10, global_expr_1947.
 rewrite instance_27_word_7 instance_27_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1947.
Transparent Child1Stable.word_11 global_word_1948.
Lemma instance_27_word_11 v : Child1Stable.word_11 (instance_27_leaves v) = global_word_1948 v.
Proof. unfold Child1Stable.word_11, global_word_1948, Child1Stable.closed_word_11, global_closed_1948, Child1Stable.expr_word_11, global_expr_1948.
 rewrite instance_27_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1948.
Transparent Child1Stable.word_12 global_word_1949.
Lemma instance_27_word_12 v : Child1Stable.word_12 (instance_27_leaves v) = global_word_1949 v.
Proof. unfold Child1Stable.word_12, global_word_1949, Child1Stable.closed_word_12, global_closed_1949, Child1Stable.expr_word_12, global_expr_1949.
 rewrite instance_27_word_9 instance_27_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1949.
Transparent Child1Stable.word_13 global_word_1950.
Lemma instance_27_word_13 v : Child1Stable.word_13 (instance_27_leaves v) = global_word_1950 v.
Proof. unfold Child1Stable.word_13, global_word_1950, Child1Stable.closed_word_13, global_closed_1950, Child1Stable.expr_word_13, global_expr_1950.
 rewrite instance_27_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1950.
Transparent Child1Stable.word_25 global_word_855.
Lemma instance_27_word_25 v : Child1Stable.word_25 (instance_27_leaves v) = global_word_855 v.
Proof. unfold Child1Stable.word_25, global_word_855, Child1Stable.closed_word_25, global_closed_855, Child1Stable.expr_word_25, global_expr_855.
 rewrite instance_27_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_855.
Transparent Child1Stable.word_23 global_word_860.
Lemma instance_27_word_23 v : Child1Stable.word_23 (instance_27_leaves v) = global_word_860 v.
Proof. unfold Child1Stable.word_23, global_word_860, Child1Stable.closed_word_23, global_closed_860, Child1Stable.expr_word_23, global_expr_860.
 rewrite instance_27_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_860.
Transparent Child1Stable.word_24 global_word_865.
Lemma instance_27_word_24 v : Child1Stable.word_24 (instance_27_leaves v) = global_word_865 v.
Proof. unfold Child1Stable.word_24, global_word_865, Child1Stable.closed_word_24, global_closed_865, Child1Stable.expr_word_24, global_expr_865.
 rewrite instance_27_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_865.
Transparent Child1Stable.word_26 global_word_866.
Lemma instance_27_word_26 v : Child1Stable.word_26 (instance_27_leaves v) = global_word_866 v.
Proof. unfold Child1Stable.word_26, global_word_866, Child1Stable.closed_word_26, global_closed_866, Child1Stable.expr_word_26, global_expr_866.
 rewrite instance_27_word_23 instance_27_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_866.
Transparent Child1Stable.word_28 global_word_867.
Lemma instance_27_word_28 v : Child1Stable.word_28 (instance_27_leaves v) = global_word_867 v.
Proof. unfold Child1Stable.word_28, global_word_867, Child1Stable.closed_word_28, global_closed_867, Child1Stable.expr_word_28, global_expr_867.
 rewrite instance_27_word_25 instance_27_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_867.
Transparent Child1Stable.word_27 global_word_868.
Lemma instance_27_word_27 v : Child1Stable.word_27 (instance_27_leaves v) = global_word_868 v.
Proof. unfold Child1Stable.word_27, global_word_868, Child1Stable.closed_word_27, global_closed_868, Child1Stable.expr_word_27, global_expr_868.
 rewrite instance_27_word_23 instance_27_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_868.
Transparent Child1Stable.word_29 global_word_869.
Lemma instance_27_word_29 v : Child1Stable.word_29 (instance_27_leaves v) = global_word_869 v.
Proof. unfold Child1Stable.word_29, global_word_869, Child1Stable.closed_word_29, global_closed_869, Child1Stable.expr_word_29, global_expr_869.
 rewrite instance_27_word_25 instance_27_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_869.
Transparent Child1Stable.word_30 global_word_870.
Lemma instance_27_word_30 v : Child1Stable.word_30 (instance_27_leaves v) = global_word_870 v.
Proof. unfold Child1Stable.word_30, global_word_870, Child1Stable.closed_word_30, global_closed_870, Child1Stable.expr_word_30, global_expr_870.
 rewrite instance_27_word_27 instance_27_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_870.
Transparent Child1Stable.word_31 global_word_871.
Lemma instance_27_word_31 v : Child1Stable.word_31 (instance_27_leaves v) = global_word_871 v.
Proof. unfold Child1Stable.word_31, global_word_871, Child1Stable.closed_word_31, global_closed_871, Child1Stable.expr_word_31, global_expr_871.
 rewrite instance_27_word_28 instance_27_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_871.
Transparent Child1Stable.word_32 global_word_872.
Lemma instance_27_word_32 v : Child1Stable.word_32 (instance_27_leaves v) = global_word_872 v.
Proof. unfold Child1Stable.word_32, global_word_872, Child1Stable.closed_word_32, global_closed_872, Child1Stable.expr_word_32, global_expr_872.
 rewrite instance_27_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_872.
Transparent Child1Stable.word_33 global_word_873.
Lemma instance_27_word_33 v : Child1Stable.word_33 (instance_27_leaves v) = global_word_873 v.
Proof. unfold Child1Stable.word_33, global_word_873, Child1Stable.closed_word_33, global_closed_873, Child1Stable.expr_word_33, global_expr_873.
 rewrite instance_27_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_873.
Transparent Child1Stable.word_5 global_word_874.
Lemma instance_27_word_5 v : Child1Stable.word_5 (instance_27_leaves v) = global_word_874 v.
Proof. unfold Child1Stable.word_5, global_word_874, Child1Stable.closed_word_5, global_closed_874, Child1Stable.expr_word_5, global_expr_874.
 rewrite instance_27_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_874.
Transparent Child1Stable.word_14 global_word_1951.
Lemma instance_27_word_14 v : Child1Stable.word_14 (instance_27_leaves v) = global_word_1951 v.
Proof. unfold Child1Stable.word_14, global_word_1951, Child1Stable.closed_word_14, global_closed_1951, Child1Stable.expr_word_14, global_expr_1951.
 rewrite instance_27_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1951.
Transparent Child1Stable.word_34 global_word_900.
Lemma instance_27_word_34 v : Child1Stable.word_34 (instance_27_leaves v) = global_word_900 v.
Proof. unfold Child1Stable.word_34, global_word_900, Child1Stable.closed_word_34, global_closed_900, Child1Stable.expr_word_34, global_expr_900.
 rewrite instance_27_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_900.
Transparent Child1Stable.word_6 global_word_901.
Lemma instance_27_word_6 v : Child1Stable.word_6 (instance_27_leaves v) = global_word_901 v.
Proof. unfold Child1Stable.word_6, global_word_901, Child1Stable.closed_word_6, global_closed_901, Child1Stable.expr_word_6, global_expr_901.
 rewrite instance_27_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_901.
Transparent Child1Stable.word_15 global_word_1952.
Lemma instance_27_word_15 v : Child1Stable.word_15 (instance_27_leaves v) = global_word_1952 v.
Proof. unfold Child1Stable.word_15, global_word_1952, Child1Stable.closed_word_15, global_closed_1952, Child1Stable.expr_word_15, global_expr_1952.
 rewrite instance_27_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1952.
Transparent Child1Stable.word_16 global_word_1953.
Lemma instance_27_word_16 v : Child1Stable.word_16 (instance_27_leaves v) = global_word_1953 v.
Proof. unfold Child1Stable.word_16, global_word_1953, Child1Stable.closed_word_16, global_closed_1953, Child1Stable.expr_word_16, global_expr_1953.
 rewrite instance_27_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1953.
Transparent Child1Stable.word_17 global_word_1954.
Lemma instance_27_word_17 v : Child1Stable.word_17 (instance_27_leaves v) = global_word_1954 v.
Proof. unfold Child1Stable.word_17, global_word_1954, Child1Stable.closed_word_17, global_closed_1954, Child1Stable.expr_word_17, global_expr_1954.
 rewrite instance_27_word_14 instance_27_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1954.
Transparent Child1Stable.word_18 global_word_1955.
Lemma instance_27_word_18 v : Child1Stable.word_18 (instance_27_leaves v) = global_word_1955 v.
Proof. unfold Child1Stable.word_18, global_word_1955, Child1Stable.closed_word_18, global_closed_1955, Child1Stable.expr_word_18, global_expr_1955.
 rewrite instance_27_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1955.
Transparent Child1Stable.word_19 global_word_1956.
Lemma instance_27_word_19 v : Child1Stable.word_19 (instance_27_leaves v) = global_word_1956 v.
Proof. unfold Child1Stable.word_19, global_word_1956, Child1Stable.closed_word_19, global_closed_1956, Child1Stable.expr_word_19, global_expr_1956.
 rewrite instance_27_word_13 instance_27_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1956.
Transparent Child1Stable.word_20 global_word_1958.
Lemma instance_27_word_20 v : Child1Stable.word_20 (instance_27_leaves v) = global_word_1958 v.
Proof. unfold Child1Stable.word_20, global_word_1958, Child1Stable.closed_word_20, global_closed_1958, Child1Stable.expr_word_20, global_expr_1958.
 rewrite instance_27_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1958.
Transparent Child1Stable.word_21 global_word_1959.
Lemma instance_27_word_21 v : Child1Stable.word_21 (instance_27_leaves v) = global_word_1959 v.
Proof. unfold Child1Stable.word_21, global_word_1959, Child1Stable.closed_word_21, global_closed_1959, Child1Stable.expr_word_21, global_expr_1959.
 rewrite instance_27_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1959.
Transparent Child1Stable.word_22 global_word_1960.
Lemma instance_27_word_22 v : Child1Stable.word_22 (instance_27_leaves v) = global_word_1960 v.
Proof. unfold Child1Stable.word_22, global_word_1960, Child1Stable.closed_word_22, global_closed_1960, Child1Stable.expr_word_22, global_expr_1960.
 rewrite instance_27_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1960.
Definition instance_28_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1979 v
| 0, 1 => global_word_1975 v
| 0, 2 => global_word_878 v
| 0, 3 => global_word_884 v
| 0, 4 => global_word_849 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1979.
Lemma instance_28_word_0 v : Child1Stable.word_0 (instance_28_leaves v) = global_word_1979 v.
Proof. unfold Child1Stable.word_0, instance_28_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1979.
Transparent Child1Stable.word_1 global_word_1975.
Lemma instance_28_word_1 v : Child1Stable.word_1 (instance_28_leaves v) = global_word_1975 v.
Proof. unfold Child1Stable.word_1, instance_28_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1975.
Transparent Child1Stable.word_2 global_word_878.
Lemma instance_28_word_2 v : Child1Stable.word_2 (instance_28_leaves v) = global_word_878 v.
Proof. unfold Child1Stable.word_2, instance_28_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_878.
Transparent Child1Stable.word_3 global_word_884.
Lemma instance_28_word_3 v : Child1Stable.word_3 (instance_28_leaves v) = global_word_884 v.
Proof. unfold Child1Stable.word_3, instance_28_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_884.
Transparent Child1Stable.word_4 global_word_849.
Lemma instance_28_word_4 v : Child1Stable.word_4 (instance_28_leaves v) = global_word_849 v.
Proof. unfold Child1Stable.word_4, instance_28_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_849.
Transparent Child1Stable.word_7 global_word_1962.
Lemma instance_28_word_7 v : Child1Stable.word_7 (instance_28_leaves v) = global_word_1962 v.
Proof. unfold Child1Stable.word_7, global_word_1962, Child1Stable.closed_word_7, global_closed_1962, Child1Stable.expr_word_7, global_expr_1962.
 rewrite instance_28_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1962.
Transparent Child1Stable.word_8 global_word_1963.
Lemma instance_28_word_8 v : Child1Stable.word_8 (instance_28_leaves v) = global_word_1963 v.
Proof. unfold Child1Stable.word_8, global_word_1963, Child1Stable.closed_word_8, global_closed_1963, Child1Stable.expr_word_8, global_expr_1963.
 rewrite instance_28_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1963.
Transparent Child1Stable.word_9 global_word_1964.
Lemma instance_28_word_9 v : Child1Stable.word_9 (instance_28_leaves v) = global_word_1964 v.
Proof. unfold Child1Stable.word_9, global_word_1964, Child1Stable.closed_word_9, global_closed_1964, Child1Stable.expr_word_9, global_expr_1964.
 rewrite instance_28_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1964.
Transparent Child1Stable.word_10 global_word_1965.
Lemma instance_28_word_10 v : Child1Stable.word_10 (instance_28_leaves v) = global_word_1965 v.
Proof. unfold Child1Stable.word_10, global_word_1965, Child1Stable.closed_word_10, global_closed_1965, Child1Stable.expr_word_10, global_expr_1965.
 rewrite instance_28_word_7 instance_28_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1965.
Transparent Child1Stable.word_11 global_word_1966.
Lemma instance_28_word_11 v : Child1Stable.word_11 (instance_28_leaves v) = global_word_1966 v.
Proof. unfold Child1Stable.word_11, global_word_1966, Child1Stable.closed_word_11, global_closed_1966, Child1Stable.expr_word_11, global_expr_1966.
 rewrite instance_28_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1966.
Transparent Child1Stable.word_12 global_word_1967.
Lemma instance_28_word_12 v : Child1Stable.word_12 (instance_28_leaves v) = global_word_1967 v.
Proof. unfold Child1Stable.word_12, global_word_1967, Child1Stable.closed_word_12, global_closed_1967, Child1Stable.expr_word_12, global_expr_1967.
 rewrite instance_28_word_9 instance_28_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1967.
Transparent Child1Stable.word_13 global_word_1968.
Lemma instance_28_word_13 v : Child1Stable.word_13 (instance_28_leaves v) = global_word_1968 v.
Proof. unfold Child1Stable.word_13, global_word_1968, Child1Stable.closed_word_13, global_closed_1968, Child1Stable.expr_word_13, global_expr_1968.
 rewrite instance_28_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1968.
Transparent Child1Stable.word_25 global_word_850.
Lemma instance_28_word_25 v : Child1Stable.word_25 (instance_28_leaves v) = global_word_850 v.
Proof. unfold Child1Stable.word_25, global_word_850, Child1Stable.closed_word_25, global_closed_850, Child1Stable.expr_word_25, global_expr_850.
 rewrite instance_28_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_850.
Transparent Child1Stable.word_23 global_word_879.
Lemma instance_28_word_23 v : Child1Stable.word_23 (instance_28_leaves v) = global_word_879 v.
Proof. unfold Child1Stable.word_23, global_word_879, Child1Stable.closed_word_23, global_closed_879, Child1Stable.expr_word_23, global_expr_879.
 rewrite instance_28_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_879.
Transparent Child1Stable.word_24 global_word_885.
Lemma instance_28_word_24 v : Child1Stable.word_24 (instance_28_leaves v) = global_word_885 v.
Proof. unfold Child1Stable.word_24, global_word_885, Child1Stable.closed_word_24, global_closed_885, Child1Stable.expr_word_24, global_expr_885.
 rewrite instance_28_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_885.
Transparent Child1Stable.word_26 global_word_886.
Lemma instance_28_word_26 v : Child1Stable.word_26 (instance_28_leaves v) = global_word_886 v.
Proof. unfold Child1Stable.word_26, global_word_886, Child1Stable.closed_word_26, global_closed_886, Child1Stable.expr_word_26, global_expr_886.
 rewrite instance_28_word_23 instance_28_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_886.
Transparent Child1Stable.word_28 global_word_887.
Lemma instance_28_word_28 v : Child1Stable.word_28 (instance_28_leaves v) = global_word_887 v.
Proof. unfold Child1Stable.word_28, global_word_887, Child1Stable.closed_word_28, global_closed_887, Child1Stable.expr_word_28, global_expr_887.
 rewrite instance_28_word_25 instance_28_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_887.
Transparent Child1Stable.word_27 global_word_888.
Lemma instance_28_word_27 v : Child1Stable.word_27 (instance_28_leaves v) = global_word_888 v.
Proof. unfold Child1Stable.word_27, global_word_888, Child1Stable.closed_word_27, global_closed_888, Child1Stable.expr_word_27, global_expr_888.
 rewrite instance_28_word_23 instance_28_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_888.
Transparent Child1Stable.word_29 global_word_889.
Lemma instance_28_word_29 v : Child1Stable.word_29 (instance_28_leaves v) = global_word_889 v.
Proof. unfold Child1Stable.word_29, global_word_889, Child1Stable.closed_word_29, global_closed_889, Child1Stable.expr_word_29, global_expr_889.
 rewrite instance_28_word_25 instance_28_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_889.
Transparent Child1Stable.word_30 global_word_890.
Lemma instance_28_word_30 v : Child1Stable.word_30 (instance_28_leaves v) = global_word_890 v.
Proof. unfold Child1Stable.word_30, global_word_890, Child1Stable.closed_word_30, global_closed_890, Child1Stable.expr_word_30, global_expr_890.
 rewrite instance_28_word_27 instance_28_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_890.
Transparent Child1Stable.word_31 global_word_891.
Lemma instance_28_word_31 v : Child1Stable.word_31 (instance_28_leaves v) = global_word_891 v.
Proof. unfold Child1Stable.word_31, global_word_891, Child1Stable.closed_word_31, global_closed_891, Child1Stable.expr_word_31, global_expr_891.
 rewrite instance_28_word_28 instance_28_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_891.
Transparent Child1Stable.word_32 global_word_892.
Lemma instance_28_word_32 v : Child1Stable.word_32 (instance_28_leaves v) = global_word_892 v.
Proof. unfold Child1Stable.word_32, global_word_892, Child1Stable.closed_word_32, global_closed_892, Child1Stable.expr_word_32, global_expr_892.
 rewrite instance_28_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_892.
Transparent Child1Stable.word_33 global_word_893.
Lemma instance_28_word_33 v : Child1Stable.word_33 (instance_28_leaves v) = global_word_893 v.
Proof. unfold Child1Stable.word_33, global_word_893, Child1Stable.closed_word_33, global_closed_893, Child1Stable.expr_word_33, global_expr_893.
 rewrite instance_28_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_893.
Transparent Child1Stable.word_5 global_word_894.
Lemma instance_28_word_5 v : Child1Stable.word_5 (instance_28_leaves v) = global_word_894 v.
Proof. unfold Child1Stable.word_5, global_word_894, Child1Stable.closed_word_5, global_closed_894, Child1Stable.expr_word_5, global_expr_894.
 rewrite instance_28_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_894.
Transparent Child1Stable.word_14 global_word_1969.
Lemma instance_28_word_14 v : Child1Stable.word_14 (instance_28_leaves v) = global_word_1969 v.
Proof. unfold Child1Stable.word_14, global_word_1969, Child1Stable.closed_word_14, global_closed_1969, Child1Stable.expr_word_14, global_expr_1969.
 rewrite instance_28_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1969.
Transparent Child1Stable.word_34 global_word_907.
Lemma instance_28_word_34 v : Child1Stable.word_34 (instance_28_leaves v) = global_word_907 v.
Proof. unfold Child1Stable.word_34, global_word_907, Child1Stable.closed_word_34, global_closed_907, Child1Stable.expr_word_34, global_expr_907.
 rewrite instance_28_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_907.
Transparent Child1Stable.word_6 global_word_908.
Lemma instance_28_word_6 v : Child1Stable.word_6 (instance_28_leaves v) = global_word_908 v.
Proof. unfold Child1Stable.word_6, global_word_908, Child1Stable.closed_word_6, global_closed_908, Child1Stable.expr_word_6, global_expr_908.
 rewrite instance_28_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_908.
Transparent Child1Stable.word_15 global_word_1970.
Lemma instance_28_word_15 v : Child1Stable.word_15 (instance_28_leaves v) = global_word_1970 v.
Proof. unfold Child1Stable.word_15, global_word_1970, Child1Stable.closed_word_15, global_closed_1970, Child1Stable.expr_word_15, global_expr_1970.
 rewrite instance_28_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1970.
Transparent Child1Stable.word_16 global_word_1971.
Lemma instance_28_word_16 v : Child1Stable.word_16 (instance_28_leaves v) = global_word_1971 v.
Proof. unfold Child1Stable.word_16, global_word_1971, Child1Stable.closed_word_16, global_closed_1971, Child1Stable.expr_word_16, global_expr_1971.
 rewrite instance_28_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1971.
Transparent Child1Stable.word_17 global_word_1972.
Lemma instance_28_word_17 v : Child1Stable.word_17 (instance_28_leaves v) = global_word_1972 v.
Proof. unfold Child1Stable.word_17, global_word_1972, Child1Stable.closed_word_17, global_closed_1972, Child1Stable.expr_word_17, global_expr_1972.
 rewrite instance_28_word_14 instance_28_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1972.
Transparent Child1Stable.word_18 global_word_1973.
Lemma instance_28_word_18 v : Child1Stable.word_18 (instance_28_leaves v) = global_word_1973 v.
Proof. unfold Child1Stable.word_18, global_word_1973, Child1Stable.closed_word_18, global_closed_1973, Child1Stable.expr_word_18, global_expr_1973.
 rewrite instance_28_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1973.
Transparent Child1Stable.word_19 global_word_1974.
Lemma instance_28_word_19 v : Child1Stable.word_19 (instance_28_leaves v) = global_word_1974 v.
Proof. unfold Child1Stable.word_19, global_word_1974, Child1Stable.closed_word_19, global_closed_1974, Child1Stable.expr_word_19, global_expr_1974.
 rewrite instance_28_word_13 instance_28_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1974.
Transparent Child1Stable.word_20 global_word_1976.
Lemma instance_28_word_20 v : Child1Stable.word_20 (instance_28_leaves v) = global_word_1976 v.
Proof. unfold Child1Stable.word_20, global_word_1976, Child1Stable.closed_word_20, global_closed_1976, Child1Stable.expr_word_20, global_expr_1976.
 rewrite instance_28_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1976.
Transparent Child1Stable.word_21 global_word_1977.
Lemma instance_28_word_21 v : Child1Stable.word_21 (instance_28_leaves v) = global_word_1977 v.
Proof. unfold Child1Stable.word_21, global_word_1977, Child1Stable.closed_word_21, global_closed_1977, Child1Stable.expr_word_21, global_expr_1977.
 rewrite instance_28_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1977.
Transparent Child1Stable.word_22 global_word_1978.
Lemma instance_28_word_22 v : Child1Stable.word_22 (instance_28_leaves v) = global_word_1978 v.
Proof. unfold Child1Stable.word_22, global_word_1978, Child1Stable.closed_word_22, global_closed_1978, Child1Stable.expr_word_22, global_expr_1978.
 rewrite instance_28_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1978.
Definition instance_29_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_1997 v
| 0, 1 => global_word_1993 v
| 0, 2 => global_word_918 v
| 0, 3 => global_word_921 v
| 0, 4 => global_word_915 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_1997.
Lemma instance_29_word_0 v : Child1Stable.word_0 (instance_29_leaves v) = global_word_1997 v.
Proof. unfold Child1Stable.word_0, instance_29_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_1997.
Transparent Child1Stable.word_1 global_word_1993.
Lemma instance_29_word_1 v : Child1Stable.word_1 (instance_29_leaves v) = global_word_1993 v.
Proof. unfold Child1Stable.word_1, instance_29_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_1993.
Transparent Child1Stable.word_2 global_word_918.
Lemma instance_29_word_2 v : Child1Stable.word_2 (instance_29_leaves v) = global_word_918 v.
Proof. unfold Child1Stable.word_2, instance_29_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_918.
Transparent Child1Stable.word_3 global_word_921.
Lemma instance_29_word_3 v : Child1Stable.word_3 (instance_29_leaves v) = global_word_921 v.
Proof. unfold Child1Stable.word_3, instance_29_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_921.
Transparent Child1Stable.word_4 global_word_915.
Lemma instance_29_word_4 v : Child1Stable.word_4 (instance_29_leaves v) = global_word_915 v.
Proof. unfold Child1Stable.word_4, instance_29_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_915.
Transparent Child1Stable.word_7 global_word_1980.
Lemma instance_29_word_7 v : Child1Stable.word_7 (instance_29_leaves v) = global_word_1980 v.
Proof. unfold Child1Stable.word_7, global_word_1980, Child1Stable.closed_word_7, global_closed_1980, Child1Stable.expr_word_7, global_expr_1980.
 rewrite instance_29_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_1980.
Transparent Child1Stable.word_8 global_word_1981.
Lemma instance_29_word_8 v : Child1Stable.word_8 (instance_29_leaves v) = global_word_1981 v.
Proof. unfold Child1Stable.word_8, global_word_1981, Child1Stable.closed_word_8, global_closed_1981, Child1Stable.expr_word_8, global_expr_1981.
 rewrite instance_29_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_1981.
Transparent Child1Stable.word_9 global_word_1982.
Lemma instance_29_word_9 v : Child1Stable.word_9 (instance_29_leaves v) = global_word_1982 v.
Proof. unfold Child1Stable.word_9, global_word_1982, Child1Stable.closed_word_9, global_closed_1982, Child1Stable.expr_word_9, global_expr_1982.
 rewrite instance_29_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_1982.
Transparent Child1Stable.word_10 global_word_1983.
Lemma instance_29_word_10 v : Child1Stable.word_10 (instance_29_leaves v) = global_word_1983 v.
Proof. unfold Child1Stable.word_10, global_word_1983, Child1Stable.closed_word_10, global_closed_1983, Child1Stable.expr_word_10, global_expr_1983.
 rewrite instance_29_word_7 instance_29_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_1983.
Transparent Child1Stable.word_11 global_word_1984.
Lemma instance_29_word_11 v : Child1Stable.word_11 (instance_29_leaves v) = global_word_1984 v.
Proof. unfold Child1Stable.word_11, global_word_1984, Child1Stable.closed_word_11, global_closed_1984, Child1Stable.expr_word_11, global_expr_1984.
 rewrite instance_29_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_1984.
Transparent Child1Stable.word_12 global_word_1985.
Lemma instance_29_word_12 v : Child1Stable.word_12 (instance_29_leaves v) = global_word_1985 v.
Proof. unfold Child1Stable.word_12, global_word_1985, Child1Stable.closed_word_12, global_closed_1985, Child1Stable.expr_word_12, global_expr_1985.
 rewrite instance_29_word_9 instance_29_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_1985.
Transparent Child1Stable.word_13 global_word_1986.
Lemma instance_29_word_13 v : Child1Stable.word_13 (instance_29_leaves v) = global_word_1986 v.
Proof. unfold Child1Stable.word_13, global_word_1986, Child1Stable.closed_word_13, global_closed_1986, Child1Stable.expr_word_13, global_expr_1986.
 rewrite instance_29_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_1986.
Transparent Child1Stable.word_25 global_word_916.
Lemma instance_29_word_25 v : Child1Stable.word_25 (instance_29_leaves v) = global_word_916 v.
Proof. unfold Child1Stable.word_25, global_word_916, Child1Stable.closed_word_25, global_closed_916, Child1Stable.expr_word_25, global_expr_916.
 rewrite instance_29_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_916.
Transparent Child1Stable.word_23 global_word_919.
Lemma instance_29_word_23 v : Child1Stable.word_23 (instance_29_leaves v) = global_word_919 v.
Proof. unfold Child1Stable.word_23, global_word_919, Child1Stable.closed_word_23, global_closed_919, Child1Stable.expr_word_23, global_expr_919.
 rewrite instance_29_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_919.
Transparent Child1Stable.word_24 global_word_922.
Lemma instance_29_word_24 v : Child1Stable.word_24 (instance_29_leaves v) = global_word_922 v.
Proof. unfold Child1Stable.word_24, global_word_922, Child1Stable.closed_word_24, global_closed_922, Child1Stable.expr_word_24, global_expr_922.
 rewrite instance_29_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_922.
Transparent Child1Stable.word_26 global_word_923.
Lemma instance_29_word_26 v : Child1Stable.word_26 (instance_29_leaves v) = global_word_923 v.
Proof. unfold Child1Stable.word_26, global_word_923, Child1Stable.closed_word_26, global_closed_923, Child1Stable.expr_word_26, global_expr_923.
 rewrite instance_29_word_23 instance_29_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_923.
Transparent Child1Stable.word_28 global_word_924.
Lemma instance_29_word_28 v : Child1Stable.word_28 (instance_29_leaves v) = global_word_924 v.
Proof. unfold Child1Stable.word_28, global_word_924, Child1Stable.closed_word_28, global_closed_924, Child1Stable.expr_word_28, global_expr_924.
 rewrite instance_29_word_25 instance_29_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_924.
Transparent Child1Stable.word_27 global_word_925.
Lemma instance_29_word_27 v : Child1Stable.word_27 (instance_29_leaves v) = global_word_925 v.
Proof. unfold Child1Stable.word_27, global_word_925, Child1Stable.closed_word_27, global_closed_925, Child1Stable.expr_word_27, global_expr_925.
 rewrite instance_29_word_23 instance_29_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_925.
Transparent Child1Stable.word_29 global_word_926.
Lemma instance_29_word_29 v : Child1Stable.word_29 (instance_29_leaves v) = global_word_926 v.
Proof. unfold Child1Stable.word_29, global_word_926, Child1Stable.closed_word_29, global_closed_926, Child1Stable.expr_word_29, global_expr_926.
 rewrite instance_29_word_25 instance_29_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_926.
Transparent Child1Stable.word_30 global_word_927.
Lemma instance_29_word_30 v : Child1Stable.word_30 (instance_29_leaves v) = global_word_927 v.
Proof. unfold Child1Stable.word_30, global_word_927, Child1Stable.closed_word_30, global_closed_927, Child1Stable.expr_word_30, global_expr_927.
 rewrite instance_29_word_27 instance_29_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_927.
Transparent Child1Stable.word_31 global_word_928.
Lemma instance_29_word_31 v : Child1Stable.word_31 (instance_29_leaves v) = global_word_928 v.
Proof. unfold Child1Stable.word_31, global_word_928, Child1Stable.closed_word_31, global_closed_928, Child1Stable.expr_word_31, global_expr_928.
 rewrite instance_29_word_28 instance_29_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_928.
Transparent Child1Stable.word_32 global_word_929.
Lemma instance_29_word_32 v : Child1Stable.word_32 (instance_29_leaves v) = global_word_929 v.
Proof. unfold Child1Stable.word_32, global_word_929, Child1Stable.closed_word_32, global_closed_929, Child1Stable.expr_word_32, global_expr_929.
 rewrite instance_29_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_929.
Transparent Child1Stable.word_33 global_word_930.
Lemma instance_29_word_33 v : Child1Stable.word_33 (instance_29_leaves v) = global_word_930 v.
Proof. unfold Child1Stable.word_33, global_word_930, Child1Stable.closed_word_33, global_closed_930, Child1Stable.expr_word_33, global_expr_930.
 rewrite instance_29_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_930.
Transparent Child1Stable.word_5 global_word_931.
Lemma instance_29_word_5 v : Child1Stable.word_5 (instance_29_leaves v) = global_word_931 v.
Proof. unfold Child1Stable.word_5, global_word_931, Child1Stable.closed_word_5, global_closed_931, Child1Stable.expr_word_5, global_expr_931.
 rewrite instance_29_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_931.
Transparent Child1Stable.word_14 global_word_1987.
Lemma instance_29_word_14 v : Child1Stable.word_14 (instance_29_leaves v) = global_word_1987 v.
Proof. unfold Child1Stable.word_14, global_word_1987, Child1Stable.closed_word_14, global_closed_1987, Child1Stable.expr_word_14, global_expr_1987.
 rewrite instance_29_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_1987.
Transparent Child1Stable.word_34 global_word_934.
Lemma instance_29_word_34 v : Child1Stable.word_34 (instance_29_leaves v) = global_word_934 v.
Proof. unfold Child1Stable.word_34, global_word_934, Child1Stable.closed_word_34, global_closed_934, Child1Stable.expr_word_34, global_expr_934.
 rewrite instance_29_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_934.
Transparent Child1Stable.word_6 global_word_935.
Lemma instance_29_word_6 v : Child1Stable.word_6 (instance_29_leaves v) = global_word_935 v.
Proof. unfold Child1Stable.word_6, global_word_935, Child1Stable.closed_word_6, global_closed_935, Child1Stable.expr_word_6, global_expr_935.
 rewrite instance_29_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_935.
Transparent Child1Stable.word_15 global_word_1988.
Lemma instance_29_word_15 v : Child1Stable.word_15 (instance_29_leaves v) = global_word_1988 v.
Proof. unfold Child1Stable.word_15, global_word_1988, Child1Stable.closed_word_15, global_closed_1988, Child1Stable.expr_word_15, global_expr_1988.
 rewrite instance_29_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_1988.
Transparent Child1Stable.word_16 global_word_1989.
Lemma instance_29_word_16 v : Child1Stable.word_16 (instance_29_leaves v) = global_word_1989 v.
Proof. unfold Child1Stable.word_16, global_word_1989, Child1Stable.closed_word_16, global_closed_1989, Child1Stable.expr_word_16, global_expr_1989.
 rewrite instance_29_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_1989.
Transparent Child1Stable.word_17 global_word_1990.
Lemma instance_29_word_17 v : Child1Stable.word_17 (instance_29_leaves v) = global_word_1990 v.
Proof. unfold Child1Stable.word_17, global_word_1990, Child1Stable.closed_word_17, global_closed_1990, Child1Stable.expr_word_17, global_expr_1990.
 rewrite instance_29_word_14 instance_29_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_1990.
Transparent Child1Stable.word_18 global_word_1991.
Lemma instance_29_word_18 v : Child1Stable.word_18 (instance_29_leaves v) = global_word_1991 v.
Proof. unfold Child1Stable.word_18, global_word_1991, Child1Stable.closed_word_18, global_closed_1991, Child1Stable.expr_word_18, global_expr_1991.
 rewrite instance_29_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_1991.
Transparent Child1Stable.word_19 global_word_1992.
Lemma instance_29_word_19 v : Child1Stable.word_19 (instance_29_leaves v) = global_word_1992 v.
Proof. unfold Child1Stable.word_19, global_word_1992, Child1Stable.closed_word_19, global_closed_1992, Child1Stable.expr_word_19, global_expr_1992.
 rewrite instance_29_word_13 instance_29_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_1992.
Transparent Child1Stable.word_20 global_word_1994.
Lemma instance_29_word_20 v : Child1Stable.word_20 (instance_29_leaves v) = global_word_1994 v.
Proof. unfold Child1Stable.word_20, global_word_1994, Child1Stable.closed_word_20, global_closed_1994, Child1Stable.expr_word_20, global_expr_1994.
 rewrite instance_29_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_1994.
Transparent Child1Stable.word_21 global_word_1995.
Lemma instance_29_word_21 v : Child1Stable.word_21 (instance_29_leaves v) = global_word_1995 v.
Proof. unfold Child1Stable.word_21, global_word_1995, Child1Stable.closed_word_21, global_closed_1995, Child1Stable.expr_word_21, global_expr_1995.
 rewrite instance_29_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_1995.
Transparent Child1Stable.word_22 global_word_1996.
Lemma instance_29_word_22 v : Child1Stable.word_22 (instance_29_leaves v) = global_word_1996 v.
Proof. unfold Child1Stable.word_22, global_word_1996, Child1Stable.closed_word_22, global_closed_1996, Child1Stable.expr_word_22, global_expr_1996.
 rewrite instance_29_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_1996.
Definition instance_30_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2012 v
| 0, 1 => global_word_2008 v
| 0, 2 => global_word_939 v
| 0, 3 => global_word_942 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2012.
Lemma instance_30_word_0 v : Child0Stable.word_0 (instance_30_leaves v) = global_word_2012 v.
Proof. unfold Child0Stable.word_0, instance_30_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2012.
Transparent Child0Stable.word_1 global_word_2008.
Lemma instance_30_word_1 v : Child0Stable.word_1 (instance_30_leaves v) = global_word_2008 v.
Proof. unfold Child0Stable.word_1, instance_30_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2008.
Transparent Child0Stable.word_2 global_word_939.
Lemma instance_30_word_2 v : Child0Stable.word_2 (instance_30_leaves v) = global_word_939 v.
Proof. unfold Child0Stable.word_2, instance_30_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_939.
Transparent Child0Stable.word_3 global_word_942.
Lemma instance_30_word_3 v : Child0Stable.word_3 (instance_30_leaves v) = global_word_942 v.
Proof. unfold Child0Stable.word_3, instance_30_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_942.
Transparent Child0Stable.word_6 global_word_1998.
Lemma instance_30_word_6 v : Child0Stable.word_6 (instance_30_leaves v) = global_word_1998 v.
Proof. unfold Child0Stable.word_6, global_word_1998, Child0Stable.closed_word_6, global_closed_1998, Child0Stable.expr_word_6, global_expr_1998.
 rewrite instance_30_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_1998.
Transparent Child0Stable.word_7 global_word_1999.
Lemma instance_30_word_7 v : Child0Stable.word_7 (instance_30_leaves v) = global_word_1999 v.
Proof. unfold Child0Stable.word_7, global_word_1999, Child0Stable.closed_word_7, global_closed_1999, Child0Stable.expr_word_7, global_expr_1999.
 rewrite instance_30_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_1999.
Transparent Child0Stable.word_8 global_word_2000.
Lemma instance_30_word_8 v : Child0Stable.word_8 (instance_30_leaves v) = global_word_2000 v.
Proof. unfold Child0Stable.word_8, global_word_2000, Child0Stable.closed_word_8, global_closed_2000, Child0Stable.expr_word_8, global_expr_2000.
 rewrite instance_30_word_6 instance_30_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2000.
Transparent Child0Stable.word_9 global_word_2001.
Lemma instance_30_word_9 v : Child0Stable.word_9 (instance_30_leaves v) = global_word_2001 v.
Proof. unfold Child0Stable.word_9, global_word_2001, Child0Stable.closed_word_9, global_closed_2001, Child0Stable.expr_word_9, global_expr_2001.
 rewrite instance_30_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2001.
Transparent Child0Stable.word_19 global_word_940.
Lemma instance_30_word_19 v : Child0Stable.word_19 (instance_30_leaves v) = global_word_940 v.
Proof. unfold Child0Stable.word_19, global_word_940, Child0Stable.closed_word_19, global_closed_940, Child0Stable.expr_word_19, global_expr_940.
 rewrite instance_30_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_940.
Transparent Child0Stable.word_20 global_word_943.
Lemma instance_30_word_20 v : Child0Stable.word_20 (instance_30_leaves v) = global_word_943 v.
Proof. unfold Child0Stable.word_20, global_word_943, Child0Stable.closed_word_20, global_closed_943, Child0Stable.expr_word_20, global_expr_943.
 rewrite instance_30_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_943.
Transparent Child0Stable.word_21 global_word_944.
Lemma instance_30_word_21 v : Child0Stable.word_21 (instance_30_leaves v) = global_word_944 v.
Proof. unfold Child0Stable.word_21, global_word_944, Child0Stable.closed_word_21, global_closed_944, Child0Stable.expr_word_21, global_expr_944.
 rewrite instance_30_word_19 instance_30_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_944.
Transparent Child0Stable.word_22 global_word_945.
Lemma instance_30_word_22 v : Child0Stable.word_22 (instance_30_leaves v) = global_word_945 v.
Proof. unfold Child0Stable.word_22, global_word_945, Child0Stable.closed_word_22, global_closed_945, Child0Stable.expr_word_22, global_expr_945.
 rewrite instance_30_word_19 instance_30_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_945.
Transparent Child0Stable.word_23 global_word_946.
Lemma instance_30_word_23 v : Child0Stable.word_23 (instance_30_leaves v) = global_word_946 v.
Proof. unfold Child0Stable.word_23, global_word_946, Child0Stable.closed_word_23, global_closed_946, Child0Stable.expr_word_23, global_expr_946.
 rewrite instance_30_word_21 instance_30_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_946.
Transparent Child0Stable.word_24 global_word_947.
Lemma instance_30_word_24 v : Child0Stable.word_24 (instance_30_leaves v) = global_word_947 v.
Proof. unfold Child0Stable.word_24, global_word_947, Child0Stable.closed_word_24, global_closed_947, Child0Stable.expr_word_24, global_expr_947.
 rewrite instance_30_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_947.
Transparent Child0Stable.word_25 global_word_948.
Lemma instance_30_word_25 v : Child0Stable.word_25 (instance_30_leaves v) = global_word_948 v.
Proof. unfold Child0Stable.word_25, global_word_948, Child0Stable.closed_word_25, global_closed_948, Child0Stable.expr_word_25, global_expr_948.
 rewrite instance_30_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_948.
Transparent Child0Stable.word_4 global_word_949.
Lemma instance_30_word_4 v : Child0Stable.word_4 (instance_30_leaves v) = global_word_949 v.
Proof. unfold Child0Stable.word_4, global_word_949, Child0Stable.closed_word_4, global_closed_949, Child0Stable.expr_word_4, global_expr_949.
 rewrite instance_30_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_949.
Transparent Child0Stable.word_10 global_word_2002.
Lemma instance_30_word_10 v : Child0Stable.word_10 (instance_30_leaves v) = global_word_2002 v.
Proof. unfold Child0Stable.word_10, global_word_2002, Child0Stable.closed_word_10, global_closed_2002, Child0Stable.expr_word_10, global_expr_2002.
 rewrite instance_30_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2002.
Transparent Child0Stable.word_26 global_word_952.
Lemma instance_30_word_26 v : Child0Stable.word_26 (instance_30_leaves v) = global_word_952 v.
Proof. unfold Child0Stable.word_26, global_word_952, Child0Stable.closed_word_26, global_closed_952, Child0Stable.expr_word_26, global_expr_952.
 rewrite instance_30_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_952.
Transparent Child0Stable.word_5 global_word_953.
Lemma instance_30_word_5 v : Child0Stable.word_5 (instance_30_leaves v) = global_word_953 v.
Proof. unfold Child0Stable.word_5, global_word_953, Child0Stable.closed_word_5, global_closed_953, Child0Stable.expr_word_5, global_expr_953.
 rewrite instance_30_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_953.
Transparent Child0Stable.word_11 global_word_2003.
Lemma instance_30_word_11 v : Child0Stable.word_11 (instance_30_leaves v) = global_word_2003 v.
Proof. unfold Child0Stable.word_11, global_word_2003, Child0Stable.closed_word_11, global_closed_2003, Child0Stable.expr_word_11, global_expr_2003.
 rewrite instance_30_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2003.
Transparent Child0Stable.word_12 global_word_2004.
Lemma instance_30_word_12 v : Child0Stable.word_12 (instance_30_leaves v) = global_word_2004 v.
Proof. unfold Child0Stable.word_12, global_word_2004, Child0Stable.closed_word_12, global_closed_2004, Child0Stable.expr_word_12, global_expr_2004.
 rewrite instance_30_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2004.
Transparent Child0Stable.word_13 global_word_2005.
Lemma instance_30_word_13 v : Child0Stable.word_13 (instance_30_leaves v) = global_word_2005 v.
Proof. unfold Child0Stable.word_13, global_word_2005, Child0Stable.closed_word_13, global_closed_2005, Child0Stable.expr_word_13, global_expr_2005.
 rewrite instance_30_word_10 instance_30_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2005.
Transparent Child0Stable.word_14 global_word_2006.
Lemma instance_30_word_14 v : Child0Stable.word_14 (instance_30_leaves v) = global_word_2006 v.
Proof. unfold Child0Stable.word_14, global_word_2006, Child0Stable.closed_word_14, global_closed_2006, Child0Stable.expr_word_14, global_expr_2006.
 rewrite instance_30_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2006.
Transparent Child0Stable.word_15 global_word_2007.
Lemma instance_30_word_15 v : Child0Stable.word_15 (instance_30_leaves v) = global_word_2007 v.
Proof. unfold Child0Stable.word_15, global_word_2007, Child0Stable.closed_word_15, global_closed_2007, Child0Stable.expr_word_15, global_expr_2007.
 rewrite instance_30_word_9 instance_30_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2007.
Transparent Child0Stable.word_16 global_word_2009.
Lemma instance_30_word_16 v : Child0Stable.word_16 (instance_30_leaves v) = global_word_2009 v.
Proof. unfold Child0Stable.word_16, global_word_2009, Child0Stable.closed_word_16, global_closed_2009, Child0Stable.expr_word_16, global_expr_2009.
 rewrite instance_30_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2009.
Transparent Child0Stable.word_17 global_word_2010.
Lemma instance_30_word_17 v : Child0Stable.word_17 (instance_30_leaves v) = global_word_2010 v.
Proof. unfold Child0Stable.word_17, global_word_2010, Child0Stable.closed_word_17, global_closed_2010, Child0Stable.expr_word_17, global_expr_2010.
 rewrite instance_30_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2010.
Transparent Child0Stable.word_18 global_word_2011.
Lemma instance_30_word_18 v : Child0Stable.word_18 (instance_30_leaves v) = global_word_2011 v.
Proof. unfold Child0Stable.word_18, global_word_2011, Child0Stable.closed_word_18, global_closed_2011, Child0Stable.expr_word_18, global_expr_2011.
 rewrite instance_30_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2011.
Definition instance_31_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2027 v
| 0, 1 => global_word_2023 v
| 0, 2 => global_word_957 v
| 0, 3 => global_word_960 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2027.
Lemma instance_31_word_0 v : Child0Stable.word_0 (instance_31_leaves v) = global_word_2027 v.
Proof. unfold Child0Stable.word_0, instance_31_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2027.
Transparent Child0Stable.word_1 global_word_2023.
Lemma instance_31_word_1 v : Child0Stable.word_1 (instance_31_leaves v) = global_word_2023 v.
Proof. unfold Child0Stable.word_1, instance_31_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2023.
Transparent Child0Stable.word_2 global_word_957.
Lemma instance_31_word_2 v : Child0Stable.word_2 (instance_31_leaves v) = global_word_957 v.
Proof. unfold Child0Stable.word_2, instance_31_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_957.
Transparent Child0Stable.word_3 global_word_960.
Lemma instance_31_word_3 v : Child0Stable.word_3 (instance_31_leaves v) = global_word_960 v.
Proof. unfold Child0Stable.word_3, instance_31_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_960.
Transparent Child0Stable.word_6 global_word_2013.
Lemma instance_31_word_6 v : Child0Stable.word_6 (instance_31_leaves v) = global_word_2013 v.
Proof. unfold Child0Stable.word_6, global_word_2013, Child0Stable.closed_word_6, global_closed_2013, Child0Stable.expr_word_6, global_expr_2013.
 rewrite instance_31_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2013.
Transparent Child0Stable.word_7 global_word_2014.
Lemma instance_31_word_7 v : Child0Stable.word_7 (instance_31_leaves v) = global_word_2014 v.
Proof. unfold Child0Stable.word_7, global_word_2014, Child0Stable.closed_word_7, global_closed_2014, Child0Stable.expr_word_7, global_expr_2014.
 rewrite instance_31_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2014.
Transparent Child0Stable.word_8 global_word_2015.
Lemma instance_31_word_8 v : Child0Stable.word_8 (instance_31_leaves v) = global_word_2015 v.
Proof. unfold Child0Stable.word_8, global_word_2015, Child0Stable.closed_word_8, global_closed_2015, Child0Stable.expr_word_8, global_expr_2015.
 rewrite instance_31_word_6 instance_31_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2015.
Transparent Child0Stable.word_9 global_word_2016.
Lemma instance_31_word_9 v : Child0Stable.word_9 (instance_31_leaves v) = global_word_2016 v.
Proof. unfold Child0Stable.word_9, global_word_2016, Child0Stable.closed_word_9, global_closed_2016, Child0Stable.expr_word_9, global_expr_2016.
 rewrite instance_31_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2016.
Transparent Child0Stable.word_19 global_word_958.
Lemma instance_31_word_19 v : Child0Stable.word_19 (instance_31_leaves v) = global_word_958 v.
Proof. unfold Child0Stable.word_19, global_word_958, Child0Stable.closed_word_19, global_closed_958, Child0Stable.expr_word_19, global_expr_958.
 rewrite instance_31_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_958.
Transparent Child0Stable.word_20 global_word_961.
Lemma instance_31_word_20 v : Child0Stable.word_20 (instance_31_leaves v) = global_word_961 v.
Proof. unfold Child0Stable.word_20, global_word_961, Child0Stable.closed_word_20, global_closed_961, Child0Stable.expr_word_20, global_expr_961.
 rewrite instance_31_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_961.
Transparent Child0Stable.word_21 global_word_962.
Lemma instance_31_word_21 v : Child0Stable.word_21 (instance_31_leaves v) = global_word_962 v.
Proof. unfold Child0Stable.word_21, global_word_962, Child0Stable.closed_word_21, global_closed_962, Child0Stable.expr_word_21, global_expr_962.
 rewrite instance_31_word_19 instance_31_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_962.
Transparent Child0Stable.word_22 global_word_963.
Lemma instance_31_word_22 v : Child0Stable.word_22 (instance_31_leaves v) = global_word_963 v.
Proof. unfold Child0Stable.word_22, global_word_963, Child0Stable.closed_word_22, global_closed_963, Child0Stable.expr_word_22, global_expr_963.
 rewrite instance_31_word_19 instance_31_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_963.
Transparent Child0Stable.word_23 global_word_964.
Lemma instance_31_word_23 v : Child0Stable.word_23 (instance_31_leaves v) = global_word_964 v.
Proof. unfold Child0Stable.word_23, global_word_964, Child0Stable.closed_word_23, global_closed_964, Child0Stable.expr_word_23, global_expr_964.
 rewrite instance_31_word_21 instance_31_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_964.
Transparent Child0Stable.word_24 global_word_965.
Lemma instance_31_word_24 v : Child0Stable.word_24 (instance_31_leaves v) = global_word_965 v.
Proof. unfold Child0Stable.word_24, global_word_965, Child0Stable.closed_word_24, global_closed_965, Child0Stable.expr_word_24, global_expr_965.
 rewrite instance_31_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_965.
Transparent Child0Stable.word_25 global_word_966.
Lemma instance_31_word_25 v : Child0Stable.word_25 (instance_31_leaves v) = global_word_966 v.
Proof. unfold Child0Stable.word_25, global_word_966, Child0Stable.closed_word_25, global_closed_966, Child0Stable.expr_word_25, global_expr_966.
 rewrite instance_31_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_966.
Transparent Child0Stable.word_4 global_word_967.
Lemma instance_31_word_4 v : Child0Stable.word_4 (instance_31_leaves v) = global_word_967 v.
Proof. unfold Child0Stable.word_4, global_word_967, Child0Stable.closed_word_4, global_closed_967, Child0Stable.expr_word_4, global_expr_967.
 rewrite instance_31_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_967.
Transparent Child0Stable.word_10 global_word_2017.
Lemma instance_31_word_10 v : Child0Stable.word_10 (instance_31_leaves v) = global_word_2017 v.
Proof. unfold Child0Stable.word_10, global_word_2017, Child0Stable.closed_word_10, global_closed_2017, Child0Stable.expr_word_10, global_expr_2017.
 rewrite instance_31_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2017.
Transparent Child0Stable.word_26 global_word_970.
Lemma instance_31_word_26 v : Child0Stable.word_26 (instance_31_leaves v) = global_word_970 v.
Proof. unfold Child0Stable.word_26, global_word_970, Child0Stable.closed_word_26, global_closed_970, Child0Stable.expr_word_26, global_expr_970.
 rewrite instance_31_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_970.
Transparent Child0Stable.word_5 global_word_971.
Lemma instance_31_word_5 v : Child0Stable.word_5 (instance_31_leaves v) = global_word_971 v.
Proof. unfold Child0Stable.word_5, global_word_971, Child0Stable.closed_word_5, global_closed_971, Child0Stable.expr_word_5, global_expr_971.
 rewrite instance_31_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_971.
Transparent Child0Stable.word_11 global_word_2018.
Lemma instance_31_word_11 v : Child0Stable.word_11 (instance_31_leaves v) = global_word_2018 v.
Proof. unfold Child0Stable.word_11, global_word_2018, Child0Stable.closed_word_11, global_closed_2018, Child0Stable.expr_word_11, global_expr_2018.
 rewrite instance_31_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2018.
Transparent Child0Stable.word_12 global_word_2019.
Lemma instance_31_word_12 v : Child0Stable.word_12 (instance_31_leaves v) = global_word_2019 v.
Proof. unfold Child0Stable.word_12, global_word_2019, Child0Stable.closed_word_12, global_closed_2019, Child0Stable.expr_word_12, global_expr_2019.
 rewrite instance_31_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2019.
Transparent Child0Stable.word_13 global_word_2020.
Lemma instance_31_word_13 v : Child0Stable.word_13 (instance_31_leaves v) = global_word_2020 v.
Proof. unfold Child0Stable.word_13, global_word_2020, Child0Stable.closed_word_13, global_closed_2020, Child0Stable.expr_word_13, global_expr_2020.
 rewrite instance_31_word_10 instance_31_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2020.
Transparent Child0Stable.word_14 global_word_2021.
Lemma instance_31_word_14 v : Child0Stable.word_14 (instance_31_leaves v) = global_word_2021 v.
Proof. unfold Child0Stable.word_14, global_word_2021, Child0Stable.closed_word_14, global_closed_2021, Child0Stable.expr_word_14, global_expr_2021.
 rewrite instance_31_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2021.
Transparent Child0Stable.word_15 global_word_2022.
Lemma instance_31_word_15 v : Child0Stable.word_15 (instance_31_leaves v) = global_word_2022 v.
Proof. unfold Child0Stable.word_15, global_word_2022, Child0Stable.closed_word_15, global_closed_2022, Child0Stable.expr_word_15, global_expr_2022.
 rewrite instance_31_word_9 instance_31_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2022.
Transparent Child0Stable.word_16 global_word_2024.
Lemma instance_31_word_16 v : Child0Stable.word_16 (instance_31_leaves v) = global_word_2024 v.
Proof. unfold Child0Stable.word_16, global_word_2024, Child0Stable.closed_word_16, global_closed_2024, Child0Stable.expr_word_16, global_expr_2024.
 rewrite instance_31_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2024.
Transparent Child0Stable.word_17 global_word_2025.
Lemma instance_31_word_17 v : Child0Stable.word_17 (instance_31_leaves v) = global_word_2025 v.
Proof. unfold Child0Stable.word_17, global_word_2025, Child0Stable.closed_word_17, global_closed_2025, Child0Stable.expr_word_17, global_expr_2025.
 rewrite instance_31_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2025.
Transparent Child0Stable.word_18 global_word_2026.
Lemma instance_31_word_18 v : Child0Stable.word_18 (instance_31_leaves v) = global_word_2026 v.
Proof. unfold Child0Stable.word_18, global_word_2026, Child0Stable.closed_word_18, global_closed_2026, Child0Stable.expr_word_18, global_expr_2026.
 rewrite instance_31_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2026.
Definition instance_32_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2042 v
| 0, 1 => global_word_2038 v
| 0, 2 => global_word_975 v
| 0, 3 => global_word_978 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2042.
Lemma instance_32_word_0 v : Child0Stable.word_0 (instance_32_leaves v) = global_word_2042 v.
Proof. unfold Child0Stable.word_0, instance_32_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2042.
Transparent Child0Stable.word_1 global_word_2038.
Lemma instance_32_word_1 v : Child0Stable.word_1 (instance_32_leaves v) = global_word_2038 v.
Proof. unfold Child0Stable.word_1, instance_32_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2038.
Transparent Child0Stable.word_2 global_word_975.
Lemma instance_32_word_2 v : Child0Stable.word_2 (instance_32_leaves v) = global_word_975 v.
Proof. unfold Child0Stable.word_2, instance_32_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_975.
Transparent Child0Stable.word_3 global_word_978.
Lemma instance_32_word_3 v : Child0Stable.word_3 (instance_32_leaves v) = global_word_978 v.
Proof. unfold Child0Stable.word_3, instance_32_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_978.
Transparent Child0Stable.word_6 global_word_2028.
Lemma instance_32_word_6 v : Child0Stable.word_6 (instance_32_leaves v) = global_word_2028 v.
Proof. unfold Child0Stable.word_6, global_word_2028, Child0Stable.closed_word_6, global_closed_2028, Child0Stable.expr_word_6, global_expr_2028.
 rewrite instance_32_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2028.
Transparent Child0Stable.word_7 global_word_2029.
Lemma instance_32_word_7 v : Child0Stable.word_7 (instance_32_leaves v) = global_word_2029 v.
Proof. unfold Child0Stable.word_7, global_word_2029, Child0Stable.closed_word_7, global_closed_2029, Child0Stable.expr_word_7, global_expr_2029.
 rewrite instance_32_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2029.
Transparent Child0Stable.word_8 global_word_2030.
Lemma instance_32_word_8 v : Child0Stable.word_8 (instance_32_leaves v) = global_word_2030 v.
Proof. unfold Child0Stable.word_8, global_word_2030, Child0Stable.closed_word_8, global_closed_2030, Child0Stable.expr_word_8, global_expr_2030.
 rewrite instance_32_word_6 instance_32_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2030.
Transparent Child0Stable.word_9 global_word_2031.
Lemma instance_32_word_9 v : Child0Stable.word_9 (instance_32_leaves v) = global_word_2031 v.
Proof. unfold Child0Stable.word_9, global_word_2031, Child0Stable.closed_word_9, global_closed_2031, Child0Stable.expr_word_9, global_expr_2031.
 rewrite instance_32_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2031.
Transparent Child0Stable.word_19 global_word_976.
Lemma instance_32_word_19 v : Child0Stable.word_19 (instance_32_leaves v) = global_word_976 v.
Proof. unfold Child0Stable.word_19, global_word_976, Child0Stable.closed_word_19, global_closed_976, Child0Stable.expr_word_19, global_expr_976.
 rewrite instance_32_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_976.
Transparent Child0Stable.word_20 global_word_979.
Lemma instance_32_word_20 v : Child0Stable.word_20 (instance_32_leaves v) = global_word_979 v.
Proof. unfold Child0Stable.word_20, global_word_979, Child0Stable.closed_word_20, global_closed_979, Child0Stable.expr_word_20, global_expr_979.
 rewrite instance_32_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_979.
Transparent Child0Stable.word_21 global_word_980.
Lemma instance_32_word_21 v : Child0Stable.word_21 (instance_32_leaves v) = global_word_980 v.
Proof. unfold Child0Stable.word_21, global_word_980, Child0Stable.closed_word_21, global_closed_980, Child0Stable.expr_word_21, global_expr_980.
 rewrite instance_32_word_19 instance_32_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_980.
Transparent Child0Stable.word_22 global_word_981.
Lemma instance_32_word_22 v : Child0Stable.word_22 (instance_32_leaves v) = global_word_981 v.
Proof. unfold Child0Stable.word_22, global_word_981, Child0Stable.closed_word_22, global_closed_981, Child0Stable.expr_word_22, global_expr_981.
 rewrite instance_32_word_19 instance_32_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_981.
Transparent Child0Stable.word_23 global_word_982.
Lemma instance_32_word_23 v : Child0Stable.word_23 (instance_32_leaves v) = global_word_982 v.
Proof. unfold Child0Stable.word_23, global_word_982, Child0Stable.closed_word_23, global_closed_982, Child0Stable.expr_word_23, global_expr_982.
 rewrite instance_32_word_21 instance_32_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_982.
Transparent Child0Stable.word_24 global_word_983.
Lemma instance_32_word_24 v : Child0Stable.word_24 (instance_32_leaves v) = global_word_983 v.
Proof. unfold Child0Stable.word_24, global_word_983, Child0Stable.closed_word_24, global_closed_983, Child0Stable.expr_word_24, global_expr_983.
 rewrite instance_32_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_983.
Transparent Child0Stable.word_25 global_word_984.
Lemma instance_32_word_25 v : Child0Stable.word_25 (instance_32_leaves v) = global_word_984 v.
Proof. unfold Child0Stable.word_25, global_word_984, Child0Stable.closed_word_25, global_closed_984, Child0Stable.expr_word_25, global_expr_984.
 rewrite instance_32_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_984.
Transparent Child0Stable.word_4 global_word_985.
Lemma instance_32_word_4 v : Child0Stable.word_4 (instance_32_leaves v) = global_word_985 v.
Proof. unfold Child0Stable.word_4, global_word_985, Child0Stable.closed_word_4, global_closed_985, Child0Stable.expr_word_4, global_expr_985.
 rewrite instance_32_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_985.
Transparent Child0Stable.word_10 global_word_2032.
Lemma instance_32_word_10 v : Child0Stable.word_10 (instance_32_leaves v) = global_word_2032 v.
Proof. unfold Child0Stable.word_10, global_word_2032, Child0Stable.closed_word_10, global_closed_2032, Child0Stable.expr_word_10, global_expr_2032.
 rewrite instance_32_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2032.
Transparent Child0Stable.word_26 global_word_988.
Lemma instance_32_word_26 v : Child0Stable.word_26 (instance_32_leaves v) = global_word_988 v.
Proof. unfold Child0Stable.word_26, global_word_988, Child0Stable.closed_word_26, global_closed_988, Child0Stable.expr_word_26, global_expr_988.
 rewrite instance_32_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_988.
Transparent Child0Stable.word_5 global_word_989.
Lemma instance_32_word_5 v : Child0Stable.word_5 (instance_32_leaves v) = global_word_989 v.
Proof. unfold Child0Stable.word_5, global_word_989, Child0Stable.closed_word_5, global_closed_989, Child0Stable.expr_word_5, global_expr_989.
 rewrite instance_32_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_989.
Transparent Child0Stable.word_11 global_word_2033.
Lemma instance_32_word_11 v : Child0Stable.word_11 (instance_32_leaves v) = global_word_2033 v.
Proof. unfold Child0Stable.word_11, global_word_2033, Child0Stable.closed_word_11, global_closed_2033, Child0Stable.expr_word_11, global_expr_2033.
 rewrite instance_32_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2033.
Transparent Child0Stable.word_12 global_word_2034.
Lemma instance_32_word_12 v : Child0Stable.word_12 (instance_32_leaves v) = global_word_2034 v.
Proof. unfold Child0Stable.word_12, global_word_2034, Child0Stable.closed_word_12, global_closed_2034, Child0Stable.expr_word_12, global_expr_2034.
 rewrite instance_32_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2034.
Transparent Child0Stable.word_13 global_word_2035.
Lemma instance_32_word_13 v : Child0Stable.word_13 (instance_32_leaves v) = global_word_2035 v.
Proof. unfold Child0Stable.word_13, global_word_2035, Child0Stable.closed_word_13, global_closed_2035, Child0Stable.expr_word_13, global_expr_2035.
 rewrite instance_32_word_10 instance_32_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2035.
Transparent Child0Stable.word_14 global_word_2036.
Lemma instance_32_word_14 v : Child0Stable.word_14 (instance_32_leaves v) = global_word_2036 v.
Proof. unfold Child0Stable.word_14, global_word_2036, Child0Stable.closed_word_14, global_closed_2036, Child0Stable.expr_word_14, global_expr_2036.
 rewrite instance_32_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2036.
Transparent Child0Stable.word_15 global_word_2037.
Lemma instance_32_word_15 v : Child0Stable.word_15 (instance_32_leaves v) = global_word_2037 v.
Proof. unfold Child0Stable.word_15, global_word_2037, Child0Stable.closed_word_15, global_closed_2037, Child0Stable.expr_word_15, global_expr_2037.
 rewrite instance_32_word_9 instance_32_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2037.
Transparent Child0Stable.word_16 global_word_2039.
Lemma instance_32_word_16 v : Child0Stable.word_16 (instance_32_leaves v) = global_word_2039 v.
Proof. unfold Child0Stable.word_16, global_word_2039, Child0Stable.closed_word_16, global_closed_2039, Child0Stable.expr_word_16, global_expr_2039.
 rewrite instance_32_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2039.
Transparent Child0Stable.word_17 global_word_2040.
Lemma instance_32_word_17 v : Child0Stable.word_17 (instance_32_leaves v) = global_word_2040 v.
Proof. unfold Child0Stable.word_17, global_word_2040, Child0Stable.closed_word_17, global_closed_2040, Child0Stable.expr_word_17, global_expr_2040.
 rewrite instance_32_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2040.
Transparent Child0Stable.word_18 global_word_2041.
Lemma instance_32_word_18 v : Child0Stable.word_18 (instance_32_leaves v) = global_word_2041 v.
Proof. unfold Child0Stable.word_18, global_word_2041, Child0Stable.closed_word_18, global_closed_2041, Child0Stable.expr_word_18, global_expr_2041.
 rewrite instance_32_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2041.
Definition instance_33_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2057 v
| 0, 1 => global_word_2053 v
| 0, 2 => global_word_993 v
| 0, 3 => global_word_996 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2057.
Lemma instance_33_word_0 v : Child0Stable.word_0 (instance_33_leaves v) = global_word_2057 v.
Proof. unfold Child0Stable.word_0, instance_33_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2057.
Transparent Child0Stable.word_1 global_word_2053.
Lemma instance_33_word_1 v : Child0Stable.word_1 (instance_33_leaves v) = global_word_2053 v.
Proof. unfold Child0Stable.word_1, instance_33_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2053.
Transparent Child0Stable.word_2 global_word_993.
Lemma instance_33_word_2 v : Child0Stable.word_2 (instance_33_leaves v) = global_word_993 v.
Proof. unfold Child0Stable.word_2, instance_33_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_993.
Transparent Child0Stable.word_3 global_word_996.
Lemma instance_33_word_3 v : Child0Stable.word_3 (instance_33_leaves v) = global_word_996 v.
Proof. unfold Child0Stable.word_3, instance_33_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_996.
Transparent Child0Stable.word_6 global_word_2043.
Lemma instance_33_word_6 v : Child0Stable.word_6 (instance_33_leaves v) = global_word_2043 v.
Proof. unfold Child0Stable.word_6, global_word_2043, Child0Stable.closed_word_6, global_closed_2043, Child0Stable.expr_word_6, global_expr_2043.
 rewrite instance_33_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2043.
Transparent Child0Stable.word_7 global_word_2044.
Lemma instance_33_word_7 v : Child0Stable.word_7 (instance_33_leaves v) = global_word_2044 v.
Proof. unfold Child0Stable.word_7, global_word_2044, Child0Stable.closed_word_7, global_closed_2044, Child0Stable.expr_word_7, global_expr_2044.
 rewrite instance_33_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2044.
Transparent Child0Stable.word_8 global_word_2045.
Lemma instance_33_word_8 v : Child0Stable.word_8 (instance_33_leaves v) = global_word_2045 v.
Proof. unfold Child0Stable.word_8, global_word_2045, Child0Stable.closed_word_8, global_closed_2045, Child0Stable.expr_word_8, global_expr_2045.
 rewrite instance_33_word_6 instance_33_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2045.
Transparent Child0Stable.word_9 global_word_2046.
Lemma instance_33_word_9 v : Child0Stable.word_9 (instance_33_leaves v) = global_word_2046 v.
Proof. unfold Child0Stable.word_9, global_word_2046, Child0Stable.closed_word_9, global_closed_2046, Child0Stable.expr_word_9, global_expr_2046.
 rewrite instance_33_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2046.
Transparent Child0Stable.word_19 global_word_994.
Lemma instance_33_word_19 v : Child0Stable.word_19 (instance_33_leaves v) = global_word_994 v.
Proof. unfold Child0Stable.word_19, global_word_994, Child0Stable.closed_word_19, global_closed_994, Child0Stable.expr_word_19, global_expr_994.
 rewrite instance_33_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_994.
Transparent Child0Stable.word_20 global_word_997.
Lemma instance_33_word_20 v : Child0Stable.word_20 (instance_33_leaves v) = global_word_997 v.
Proof. unfold Child0Stable.word_20, global_word_997, Child0Stable.closed_word_20, global_closed_997, Child0Stable.expr_word_20, global_expr_997.
 rewrite instance_33_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_997.
Transparent Child0Stable.word_21 global_word_998.
Lemma instance_33_word_21 v : Child0Stable.word_21 (instance_33_leaves v) = global_word_998 v.
Proof. unfold Child0Stable.word_21, global_word_998, Child0Stable.closed_word_21, global_closed_998, Child0Stable.expr_word_21, global_expr_998.
 rewrite instance_33_word_19 instance_33_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_998.
Transparent Child0Stable.word_22 global_word_999.
Lemma instance_33_word_22 v : Child0Stable.word_22 (instance_33_leaves v) = global_word_999 v.
Proof. unfold Child0Stable.word_22, global_word_999, Child0Stable.closed_word_22, global_closed_999, Child0Stable.expr_word_22, global_expr_999.
 rewrite instance_33_word_19 instance_33_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_999.
Transparent Child0Stable.word_23 global_word_1000.
Lemma instance_33_word_23 v : Child0Stable.word_23 (instance_33_leaves v) = global_word_1000 v.
Proof. unfold Child0Stable.word_23, global_word_1000, Child0Stable.closed_word_23, global_closed_1000, Child0Stable.expr_word_23, global_expr_1000.
 rewrite instance_33_word_21 instance_33_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1000.
Transparent Child0Stable.word_24 global_word_1001.
Lemma instance_33_word_24 v : Child0Stable.word_24 (instance_33_leaves v) = global_word_1001 v.
Proof. unfold Child0Stable.word_24, global_word_1001, Child0Stable.closed_word_24, global_closed_1001, Child0Stable.expr_word_24, global_expr_1001.
 rewrite instance_33_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1001.
Transparent Child0Stable.word_25 global_word_1002.
Lemma instance_33_word_25 v : Child0Stable.word_25 (instance_33_leaves v) = global_word_1002 v.
Proof. unfold Child0Stable.word_25, global_word_1002, Child0Stable.closed_word_25, global_closed_1002, Child0Stable.expr_word_25, global_expr_1002.
 rewrite instance_33_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1002.
Transparent Child0Stable.word_4 global_word_1003.
Lemma instance_33_word_4 v : Child0Stable.word_4 (instance_33_leaves v) = global_word_1003 v.
Proof. unfold Child0Stable.word_4, global_word_1003, Child0Stable.closed_word_4, global_closed_1003, Child0Stable.expr_word_4, global_expr_1003.
 rewrite instance_33_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1003.
Transparent Child0Stable.word_10 global_word_2047.
Lemma instance_33_word_10 v : Child0Stable.word_10 (instance_33_leaves v) = global_word_2047 v.
Proof. unfold Child0Stable.word_10, global_word_2047, Child0Stable.closed_word_10, global_closed_2047, Child0Stable.expr_word_10, global_expr_2047.
 rewrite instance_33_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2047.
Transparent Child0Stable.word_26 global_word_1006.
Lemma instance_33_word_26 v : Child0Stable.word_26 (instance_33_leaves v) = global_word_1006 v.
Proof. unfold Child0Stable.word_26, global_word_1006, Child0Stable.closed_word_26, global_closed_1006, Child0Stable.expr_word_26, global_expr_1006.
 rewrite instance_33_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1006.
Transparent Child0Stable.word_5 global_word_1007.
Lemma instance_33_word_5 v : Child0Stable.word_5 (instance_33_leaves v) = global_word_1007 v.
Proof. unfold Child0Stable.word_5, global_word_1007, Child0Stable.closed_word_5, global_closed_1007, Child0Stable.expr_word_5, global_expr_1007.
 rewrite instance_33_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1007.
Transparent Child0Stable.word_11 global_word_2048.
Lemma instance_33_word_11 v : Child0Stable.word_11 (instance_33_leaves v) = global_word_2048 v.
Proof. unfold Child0Stable.word_11, global_word_2048, Child0Stable.closed_word_11, global_closed_2048, Child0Stable.expr_word_11, global_expr_2048.
 rewrite instance_33_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2048.
Transparent Child0Stable.word_12 global_word_2049.
Lemma instance_33_word_12 v : Child0Stable.word_12 (instance_33_leaves v) = global_word_2049 v.
Proof. unfold Child0Stable.word_12, global_word_2049, Child0Stable.closed_word_12, global_closed_2049, Child0Stable.expr_word_12, global_expr_2049.
 rewrite instance_33_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2049.
Transparent Child0Stable.word_13 global_word_2050.
Lemma instance_33_word_13 v : Child0Stable.word_13 (instance_33_leaves v) = global_word_2050 v.
Proof. unfold Child0Stable.word_13, global_word_2050, Child0Stable.closed_word_13, global_closed_2050, Child0Stable.expr_word_13, global_expr_2050.
 rewrite instance_33_word_10 instance_33_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2050.
Transparent Child0Stable.word_14 global_word_2051.
Lemma instance_33_word_14 v : Child0Stable.word_14 (instance_33_leaves v) = global_word_2051 v.
Proof. unfold Child0Stable.word_14, global_word_2051, Child0Stable.closed_word_14, global_closed_2051, Child0Stable.expr_word_14, global_expr_2051.
 rewrite instance_33_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2051.
Transparent Child0Stable.word_15 global_word_2052.
Lemma instance_33_word_15 v : Child0Stable.word_15 (instance_33_leaves v) = global_word_2052 v.
Proof. unfold Child0Stable.word_15, global_word_2052, Child0Stable.closed_word_15, global_closed_2052, Child0Stable.expr_word_15, global_expr_2052.
 rewrite instance_33_word_9 instance_33_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2052.
Transparent Child0Stable.word_16 global_word_2054.
Lemma instance_33_word_16 v : Child0Stable.word_16 (instance_33_leaves v) = global_word_2054 v.
Proof. unfold Child0Stable.word_16, global_word_2054, Child0Stable.closed_word_16, global_closed_2054, Child0Stable.expr_word_16, global_expr_2054.
 rewrite instance_33_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2054.
Transparent Child0Stable.word_17 global_word_2055.
Lemma instance_33_word_17 v : Child0Stable.word_17 (instance_33_leaves v) = global_word_2055 v.
Proof. unfold Child0Stable.word_17, global_word_2055, Child0Stable.closed_word_17, global_closed_2055, Child0Stable.expr_word_17, global_expr_2055.
 rewrite instance_33_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2055.
Transparent Child0Stable.word_18 global_word_2056.
Lemma instance_33_word_18 v : Child0Stable.word_18 (instance_33_leaves v) = global_word_2056 v.
Proof. unfold Child0Stable.word_18, global_word_2056, Child0Stable.closed_word_18, global_closed_2056, Child0Stable.expr_word_18, global_expr_2056.
 rewrite instance_33_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2056.
Definition instance_34_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2072 v
| 0, 1 => global_word_2068 v
| 0, 2 => global_word_1011 v
| 0, 3 => global_word_1014 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2072.
Lemma instance_34_word_0 v : Child0Stable.word_0 (instance_34_leaves v) = global_word_2072 v.
Proof. unfold Child0Stable.word_0, instance_34_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2072.
Transparent Child0Stable.word_1 global_word_2068.
Lemma instance_34_word_1 v : Child0Stable.word_1 (instance_34_leaves v) = global_word_2068 v.
Proof. unfold Child0Stable.word_1, instance_34_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2068.
Transparent Child0Stable.word_2 global_word_1011.
Lemma instance_34_word_2 v : Child0Stable.word_2 (instance_34_leaves v) = global_word_1011 v.
Proof. unfold Child0Stable.word_2, instance_34_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1011.
Transparent Child0Stable.word_3 global_word_1014.
Lemma instance_34_word_3 v : Child0Stable.word_3 (instance_34_leaves v) = global_word_1014 v.
Proof. unfold Child0Stable.word_3, instance_34_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1014.
Transparent Child0Stable.word_6 global_word_2058.
Lemma instance_34_word_6 v : Child0Stable.word_6 (instance_34_leaves v) = global_word_2058 v.
Proof. unfold Child0Stable.word_6, global_word_2058, Child0Stable.closed_word_6, global_closed_2058, Child0Stable.expr_word_6, global_expr_2058.
 rewrite instance_34_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2058.
Transparent Child0Stable.word_7 global_word_2059.
Lemma instance_34_word_7 v : Child0Stable.word_7 (instance_34_leaves v) = global_word_2059 v.
Proof. unfold Child0Stable.word_7, global_word_2059, Child0Stable.closed_word_7, global_closed_2059, Child0Stable.expr_word_7, global_expr_2059.
 rewrite instance_34_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2059.
Transparent Child0Stable.word_8 global_word_2060.
Lemma instance_34_word_8 v : Child0Stable.word_8 (instance_34_leaves v) = global_word_2060 v.
Proof. unfold Child0Stable.word_8, global_word_2060, Child0Stable.closed_word_8, global_closed_2060, Child0Stable.expr_word_8, global_expr_2060.
 rewrite instance_34_word_6 instance_34_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2060.
Transparent Child0Stable.word_9 global_word_2061.
Lemma instance_34_word_9 v : Child0Stable.word_9 (instance_34_leaves v) = global_word_2061 v.
Proof. unfold Child0Stable.word_9, global_word_2061, Child0Stable.closed_word_9, global_closed_2061, Child0Stable.expr_word_9, global_expr_2061.
 rewrite instance_34_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2061.
Transparent Child0Stable.word_19 global_word_1012.
Lemma instance_34_word_19 v : Child0Stable.word_19 (instance_34_leaves v) = global_word_1012 v.
Proof. unfold Child0Stable.word_19, global_word_1012, Child0Stable.closed_word_19, global_closed_1012, Child0Stable.expr_word_19, global_expr_1012.
 rewrite instance_34_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1012.
Transparent Child0Stable.word_20 global_word_1015.
Lemma instance_34_word_20 v : Child0Stable.word_20 (instance_34_leaves v) = global_word_1015 v.
Proof. unfold Child0Stable.word_20, global_word_1015, Child0Stable.closed_word_20, global_closed_1015, Child0Stable.expr_word_20, global_expr_1015.
 rewrite instance_34_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1015.
Transparent Child0Stable.word_21 global_word_1016.
Lemma instance_34_word_21 v : Child0Stable.word_21 (instance_34_leaves v) = global_word_1016 v.
Proof. unfold Child0Stable.word_21, global_word_1016, Child0Stable.closed_word_21, global_closed_1016, Child0Stable.expr_word_21, global_expr_1016.
 rewrite instance_34_word_19 instance_34_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1016.
Transparent Child0Stable.word_22 global_word_1017.
Lemma instance_34_word_22 v : Child0Stable.word_22 (instance_34_leaves v) = global_word_1017 v.
Proof. unfold Child0Stable.word_22, global_word_1017, Child0Stable.closed_word_22, global_closed_1017, Child0Stable.expr_word_22, global_expr_1017.
 rewrite instance_34_word_19 instance_34_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1017.
Transparent Child0Stable.word_23 global_word_1018.
Lemma instance_34_word_23 v : Child0Stable.word_23 (instance_34_leaves v) = global_word_1018 v.
Proof. unfold Child0Stable.word_23, global_word_1018, Child0Stable.closed_word_23, global_closed_1018, Child0Stable.expr_word_23, global_expr_1018.
 rewrite instance_34_word_21 instance_34_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1018.
Transparent Child0Stable.word_24 global_word_1019.
Lemma instance_34_word_24 v : Child0Stable.word_24 (instance_34_leaves v) = global_word_1019 v.
Proof. unfold Child0Stable.word_24, global_word_1019, Child0Stable.closed_word_24, global_closed_1019, Child0Stable.expr_word_24, global_expr_1019.
 rewrite instance_34_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1019.
Transparent Child0Stable.word_25 global_word_1020.
Lemma instance_34_word_25 v : Child0Stable.word_25 (instance_34_leaves v) = global_word_1020 v.
Proof. unfold Child0Stable.word_25, global_word_1020, Child0Stable.closed_word_25, global_closed_1020, Child0Stable.expr_word_25, global_expr_1020.
 rewrite instance_34_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1020.
Transparent Child0Stable.word_4 global_word_1021.
Lemma instance_34_word_4 v : Child0Stable.word_4 (instance_34_leaves v) = global_word_1021 v.
Proof. unfold Child0Stable.word_4, global_word_1021, Child0Stable.closed_word_4, global_closed_1021, Child0Stable.expr_word_4, global_expr_1021.
 rewrite instance_34_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1021.
Transparent Child0Stable.word_10 global_word_2062.
Lemma instance_34_word_10 v : Child0Stable.word_10 (instance_34_leaves v) = global_word_2062 v.
Proof. unfold Child0Stable.word_10, global_word_2062, Child0Stable.closed_word_10, global_closed_2062, Child0Stable.expr_word_10, global_expr_2062.
 rewrite instance_34_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2062.
Transparent Child0Stable.word_26 global_word_1024.
Lemma instance_34_word_26 v : Child0Stable.word_26 (instance_34_leaves v) = global_word_1024 v.
Proof. unfold Child0Stable.word_26, global_word_1024, Child0Stable.closed_word_26, global_closed_1024, Child0Stable.expr_word_26, global_expr_1024.
 rewrite instance_34_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1024.
Transparent Child0Stable.word_5 global_word_1025.
Lemma instance_34_word_5 v : Child0Stable.word_5 (instance_34_leaves v) = global_word_1025 v.
Proof. unfold Child0Stable.word_5, global_word_1025, Child0Stable.closed_word_5, global_closed_1025, Child0Stable.expr_word_5, global_expr_1025.
 rewrite instance_34_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1025.
Transparent Child0Stable.word_11 global_word_2063.
Lemma instance_34_word_11 v : Child0Stable.word_11 (instance_34_leaves v) = global_word_2063 v.
Proof. unfold Child0Stable.word_11, global_word_2063, Child0Stable.closed_word_11, global_closed_2063, Child0Stable.expr_word_11, global_expr_2063.
 rewrite instance_34_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2063.
Transparent Child0Stable.word_12 global_word_2064.
Lemma instance_34_word_12 v : Child0Stable.word_12 (instance_34_leaves v) = global_word_2064 v.
Proof. unfold Child0Stable.word_12, global_word_2064, Child0Stable.closed_word_12, global_closed_2064, Child0Stable.expr_word_12, global_expr_2064.
 rewrite instance_34_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2064.
Transparent Child0Stable.word_13 global_word_2065.
Lemma instance_34_word_13 v : Child0Stable.word_13 (instance_34_leaves v) = global_word_2065 v.
Proof. unfold Child0Stable.word_13, global_word_2065, Child0Stable.closed_word_13, global_closed_2065, Child0Stable.expr_word_13, global_expr_2065.
 rewrite instance_34_word_10 instance_34_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2065.
Transparent Child0Stable.word_14 global_word_2066.
Lemma instance_34_word_14 v : Child0Stable.word_14 (instance_34_leaves v) = global_word_2066 v.
Proof. unfold Child0Stable.word_14, global_word_2066, Child0Stable.closed_word_14, global_closed_2066, Child0Stable.expr_word_14, global_expr_2066.
 rewrite instance_34_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2066.
Transparent Child0Stable.word_15 global_word_2067.
Lemma instance_34_word_15 v : Child0Stable.word_15 (instance_34_leaves v) = global_word_2067 v.
Proof. unfold Child0Stable.word_15, global_word_2067, Child0Stable.closed_word_15, global_closed_2067, Child0Stable.expr_word_15, global_expr_2067.
 rewrite instance_34_word_9 instance_34_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2067.
Transparent Child0Stable.word_16 global_word_2069.
Lemma instance_34_word_16 v : Child0Stable.word_16 (instance_34_leaves v) = global_word_2069 v.
Proof. unfold Child0Stable.word_16, global_word_2069, Child0Stable.closed_word_16, global_closed_2069, Child0Stable.expr_word_16, global_expr_2069.
 rewrite instance_34_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2069.
Transparent Child0Stable.word_17 global_word_2070.
Lemma instance_34_word_17 v : Child0Stable.word_17 (instance_34_leaves v) = global_word_2070 v.
Proof. unfold Child0Stable.word_17, global_word_2070, Child0Stable.closed_word_17, global_closed_2070, Child0Stable.expr_word_17, global_expr_2070.
 rewrite instance_34_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2070.
Transparent Child0Stable.word_18 global_word_2071.
Lemma instance_34_word_18 v : Child0Stable.word_18 (instance_34_leaves v) = global_word_2071 v.
Proof. unfold Child0Stable.word_18, global_word_2071, Child0Stable.closed_word_18, global_closed_2071, Child0Stable.expr_word_18, global_expr_2071.
 rewrite instance_34_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2071.
Definition instance_35_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2087 v
| 0, 1 => global_word_2083 v
| 0, 2 => global_word_1029 v
| 0, 3 => global_word_1032 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2087.
Lemma instance_35_word_0 v : Child0Stable.word_0 (instance_35_leaves v) = global_word_2087 v.
Proof. unfold Child0Stable.word_0, instance_35_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2087.
Transparent Child0Stable.word_1 global_word_2083.
Lemma instance_35_word_1 v : Child0Stable.word_1 (instance_35_leaves v) = global_word_2083 v.
Proof. unfold Child0Stable.word_1, instance_35_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2083.
Transparent Child0Stable.word_2 global_word_1029.
Lemma instance_35_word_2 v : Child0Stable.word_2 (instance_35_leaves v) = global_word_1029 v.
Proof. unfold Child0Stable.word_2, instance_35_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1029.
Transparent Child0Stable.word_3 global_word_1032.
Lemma instance_35_word_3 v : Child0Stable.word_3 (instance_35_leaves v) = global_word_1032 v.
Proof. unfold Child0Stable.word_3, instance_35_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1032.
Transparent Child0Stable.word_6 global_word_2073.
Lemma instance_35_word_6 v : Child0Stable.word_6 (instance_35_leaves v) = global_word_2073 v.
Proof. unfold Child0Stable.word_6, global_word_2073, Child0Stable.closed_word_6, global_closed_2073, Child0Stable.expr_word_6, global_expr_2073.
 rewrite instance_35_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2073.
Transparent Child0Stable.word_7 global_word_2074.
Lemma instance_35_word_7 v : Child0Stable.word_7 (instance_35_leaves v) = global_word_2074 v.
Proof. unfold Child0Stable.word_7, global_word_2074, Child0Stable.closed_word_7, global_closed_2074, Child0Stable.expr_word_7, global_expr_2074.
 rewrite instance_35_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2074.
Transparent Child0Stable.word_8 global_word_2075.
Lemma instance_35_word_8 v : Child0Stable.word_8 (instance_35_leaves v) = global_word_2075 v.
Proof. unfold Child0Stable.word_8, global_word_2075, Child0Stable.closed_word_8, global_closed_2075, Child0Stable.expr_word_8, global_expr_2075.
 rewrite instance_35_word_6 instance_35_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2075.
Transparent Child0Stable.word_9 global_word_2076.
Lemma instance_35_word_9 v : Child0Stable.word_9 (instance_35_leaves v) = global_word_2076 v.
Proof. unfold Child0Stable.word_9, global_word_2076, Child0Stable.closed_word_9, global_closed_2076, Child0Stable.expr_word_9, global_expr_2076.
 rewrite instance_35_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2076.
Transparent Child0Stable.word_19 global_word_1030.
Lemma instance_35_word_19 v : Child0Stable.word_19 (instance_35_leaves v) = global_word_1030 v.
Proof. unfold Child0Stable.word_19, global_word_1030, Child0Stable.closed_word_19, global_closed_1030, Child0Stable.expr_word_19, global_expr_1030.
 rewrite instance_35_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1030.
Transparent Child0Stable.word_20 global_word_1033.
Lemma instance_35_word_20 v : Child0Stable.word_20 (instance_35_leaves v) = global_word_1033 v.
Proof. unfold Child0Stable.word_20, global_word_1033, Child0Stable.closed_word_20, global_closed_1033, Child0Stable.expr_word_20, global_expr_1033.
 rewrite instance_35_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1033.
Transparent Child0Stable.word_21 global_word_1034.
Lemma instance_35_word_21 v : Child0Stable.word_21 (instance_35_leaves v) = global_word_1034 v.
Proof. unfold Child0Stable.word_21, global_word_1034, Child0Stable.closed_word_21, global_closed_1034, Child0Stable.expr_word_21, global_expr_1034.
 rewrite instance_35_word_19 instance_35_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1034.
Transparent Child0Stable.word_22 global_word_1035.
Lemma instance_35_word_22 v : Child0Stable.word_22 (instance_35_leaves v) = global_word_1035 v.
Proof. unfold Child0Stable.word_22, global_word_1035, Child0Stable.closed_word_22, global_closed_1035, Child0Stable.expr_word_22, global_expr_1035.
 rewrite instance_35_word_19 instance_35_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1035.
Transparent Child0Stable.word_23 global_word_1036.
Lemma instance_35_word_23 v : Child0Stable.word_23 (instance_35_leaves v) = global_word_1036 v.
Proof. unfold Child0Stable.word_23, global_word_1036, Child0Stable.closed_word_23, global_closed_1036, Child0Stable.expr_word_23, global_expr_1036.
 rewrite instance_35_word_21 instance_35_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1036.
Transparent Child0Stable.word_24 global_word_1037.
Lemma instance_35_word_24 v : Child0Stable.word_24 (instance_35_leaves v) = global_word_1037 v.
Proof. unfold Child0Stable.word_24, global_word_1037, Child0Stable.closed_word_24, global_closed_1037, Child0Stable.expr_word_24, global_expr_1037.
 rewrite instance_35_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1037.
Transparent Child0Stable.word_25 global_word_1038.
Lemma instance_35_word_25 v : Child0Stable.word_25 (instance_35_leaves v) = global_word_1038 v.
Proof. unfold Child0Stable.word_25, global_word_1038, Child0Stable.closed_word_25, global_closed_1038, Child0Stable.expr_word_25, global_expr_1038.
 rewrite instance_35_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1038.
Transparent Child0Stable.word_4 global_word_1039.
Lemma instance_35_word_4 v : Child0Stable.word_4 (instance_35_leaves v) = global_word_1039 v.
Proof. unfold Child0Stable.word_4, global_word_1039, Child0Stable.closed_word_4, global_closed_1039, Child0Stable.expr_word_4, global_expr_1039.
 rewrite instance_35_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1039.
Transparent Child0Stable.word_10 global_word_2077.
Lemma instance_35_word_10 v : Child0Stable.word_10 (instance_35_leaves v) = global_word_2077 v.
Proof. unfold Child0Stable.word_10, global_word_2077, Child0Stable.closed_word_10, global_closed_2077, Child0Stable.expr_word_10, global_expr_2077.
 rewrite instance_35_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2077.
Transparent Child0Stable.word_26 global_word_1042.
Lemma instance_35_word_26 v : Child0Stable.word_26 (instance_35_leaves v) = global_word_1042 v.
Proof. unfold Child0Stable.word_26, global_word_1042, Child0Stable.closed_word_26, global_closed_1042, Child0Stable.expr_word_26, global_expr_1042.
 rewrite instance_35_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1042.
Transparent Child0Stable.word_5 global_word_1043.
Lemma instance_35_word_5 v : Child0Stable.word_5 (instance_35_leaves v) = global_word_1043 v.
Proof. unfold Child0Stable.word_5, global_word_1043, Child0Stable.closed_word_5, global_closed_1043, Child0Stable.expr_word_5, global_expr_1043.
 rewrite instance_35_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1043.
Transparent Child0Stable.word_11 global_word_2078.
Lemma instance_35_word_11 v : Child0Stable.word_11 (instance_35_leaves v) = global_word_2078 v.
Proof. unfold Child0Stable.word_11, global_word_2078, Child0Stable.closed_word_11, global_closed_2078, Child0Stable.expr_word_11, global_expr_2078.
 rewrite instance_35_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2078.
Transparent Child0Stable.word_12 global_word_2079.
Lemma instance_35_word_12 v : Child0Stable.word_12 (instance_35_leaves v) = global_word_2079 v.
Proof. unfold Child0Stable.word_12, global_word_2079, Child0Stable.closed_word_12, global_closed_2079, Child0Stable.expr_word_12, global_expr_2079.
 rewrite instance_35_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2079.
Transparent Child0Stable.word_13 global_word_2080.
Lemma instance_35_word_13 v : Child0Stable.word_13 (instance_35_leaves v) = global_word_2080 v.
Proof. unfold Child0Stable.word_13, global_word_2080, Child0Stable.closed_word_13, global_closed_2080, Child0Stable.expr_word_13, global_expr_2080.
 rewrite instance_35_word_10 instance_35_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2080.
Transparent Child0Stable.word_14 global_word_2081.
Lemma instance_35_word_14 v : Child0Stable.word_14 (instance_35_leaves v) = global_word_2081 v.
Proof. unfold Child0Stable.word_14, global_word_2081, Child0Stable.closed_word_14, global_closed_2081, Child0Stable.expr_word_14, global_expr_2081.
 rewrite instance_35_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2081.
Transparent Child0Stable.word_15 global_word_2082.
Lemma instance_35_word_15 v : Child0Stable.word_15 (instance_35_leaves v) = global_word_2082 v.
Proof. unfold Child0Stable.word_15, global_word_2082, Child0Stable.closed_word_15, global_closed_2082, Child0Stable.expr_word_15, global_expr_2082.
 rewrite instance_35_word_9 instance_35_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2082.
Transparent Child0Stable.word_16 global_word_2084.
Lemma instance_35_word_16 v : Child0Stable.word_16 (instance_35_leaves v) = global_word_2084 v.
Proof. unfold Child0Stable.word_16, global_word_2084, Child0Stable.closed_word_16, global_closed_2084, Child0Stable.expr_word_16, global_expr_2084.
 rewrite instance_35_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2084.
Transparent Child0Stable.word_17 global_word_2085.
Lemma instance_35_word_17 v : Child0Stable.word_17 (instance_35_leaves v) = global_word_2085 v.
Proof. unfold Child0Stable.word_17, global_word_2085, Child0Stable.closed_word_17, global_closed_2085, Child0Stable.expr_word_17, global_expr_2085.
 rewrite instance_35_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2085.
Transparent Child0Stable.word_18 global_word_2086.
Lemma instance_35_word_18 v : Child0Stable.word_18 (instance_35_leaves v) = global_word_2086 v.
Proof. unfold Child0Stable.word_18, global_word_2086, Child0Stable.closed_word_18, global_closed_2086, Child0Stable.expr_word_18, global_expr_2086.
 rewrite instance_35_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2086.
Definition instance_36_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2102 v
| 0, 1 => global_word_2098 v
| 0, 2 => global_word_1047 v
| 0, 3 => global_word_1050 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2102.
Lemma instance_36_word_0 v : Child0Stable.word_0 (instance_36_leaves v) = global_word_2102 v.
Proof. unfold Child0Stable.word_0, instance_36_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2102.
Transparent Child0Stable.word_1 global_word_2098.
Lemma instance_36_word_1 v : Child0Stable.word_1 (instance_36_leaves v) = global_word_2098 v.
Proof. unfold Child0Stable.word_1, instance_36_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2098.
Transparent Child0Stable.word_2 global_word_1047.
Lemma instance_36_word_2 v : Child0Stable.word_2 (instance_36_leaves v) = global_word_1047 v.
Proof. unfold Child0Stable.word_2, instance_36_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1047.
Transparent Child0Stable.word_3 global_word_1050.
Lemma instance_36_word_3 v : Child0Stable.word_3 (instance_36_leaves v) = global_word_1050 v.
Proof. unfold Child0Stable.word_3, instance_36_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1050.
Transparent Child0Stable.word_6 global_word_2088.
Lemma instance_36_word_6 v : Child0Stable.word_6 (instance_36_leaves v) = global_word_2088 v.
Proof. unfold Child0Stable.word_6, global_word_2088, Child0Stable.closed_word_6, global_closed_2088, Child0Stable.expr_word_6, global_expr_2088.
 rewrite instance_36_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2088.
Transparent Child0Stable.word_7 global_word_2089.
Lemma instance_36_word_7 v : Child0Stable.word_7 (instance_36_leaves v) = global_word_2089 v.
Proof. unfold Child0Stable.word_7, global_word_2089, Child0Stable.closed_word_7, global_closed_2089, Child0Stable.expr_word_7, global_expr_2089.
 rewrite instance_36_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2089.
Transparent Child0Stable.word_8 global_word_2090.
Lemma instance_36_word_8 v : Child0Stable.word_8 (instance_36_leaves v) = global_word_2090 v.
Proof. unfold Child0Stable.word_8, global_word_2090, Child0Stable.closed_word_8, global_closed_2090, Child0Stable.expr_word_8, global_expr_2090.
 rewrite instance_36_word_6 instance_36_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2090.
Transparent Child0Stable.word_9 global_word_2091.
Lemma instance_36_word_9 v : Child0Stable.word_9 (instance_36_leaves v) = global_word_2091 v.
Proof. unfold Child0Stable.word_9, global_word_2091, Child0Stable.closed_word_9, global_closed_2091, Child0Stable.expr_word_9, global_expr_2091.
 rewrite instance_36_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2091.
Transparent Child0Stable.word_19 global_word_1048.
Lemma instance_36_word_19 v : Child0Stable.word_19 (instance_36_leaves v) = global_word_1048 v.
Proof. unfold Child0Stable.word_19, global_word_1048, Child0Stable.closed_word_19, global_closed_1048, Child0Stable.expr_word_19, global_expr_1048.
 rewrite instance_36_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1048.
Transparent Child0Stable.word_20 global_word_1051.
Lemma instance_36_word_20 v : Child0Stable.word_20 (instance_36_leaves v) = global_word_1051 v.
Proof. unfold Child0Stable.word_20, global_word_1051, Child0Stable.closed_word_20, global_closed_1051, Child0Stable.expr_word_20, global_expr_1051.
 rewrite instance_36_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1051.
Transparent Child0Stable.word_21 global_word_1052.
Lemma instance_36_word_21 v : Child0Stable.word_21 (instance_36_leaves v) = global_word_1052 v.
Proof. unfold Child0Stable.word_21, global_word_1052, Child0Stable.closed_word_21, global_closed_1052, Child0Stable.expr_word_21, global_expr_1052.
 rewrite instance_36_word_19 instance_36_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1052.
Transparent Child0Stable.word_22 global_word_1053.
Lemma instance_36_word_22 v : Child0Stable.word_22 (instance_36_leaves v) = global_word_1053 v.
Proof. unfold Child0Stable.word_22, global_word_1053, Child0Stable.closed_word_22, global_closed_1053, Child0Stable.expr_word_22, global_expr_1053.
 rewrite instance_36_word_19 instance_36_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1053.
Transparent Child0Stable.word_23 global_word_1054.
Lemma instance_36_word_23 v : Child0Stable.word_23 (instance_36_leaves v) = global_word_1054 v.
Proof. unfold Child0Stable.word_23, global_word_1054, Child0Stable.closed_word_23, global_closed_1054, Child0Stable.expr_word_23, global_expr_1054.
 rewrite instance_36_word_21 instance_36_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1054.
Transparent Child0Stable.word_24 global_word_1055.
Lemma instance_36_word_24 v : Child0Stable.word_24 (instance_36_leaves v) = global_word_1055 v.
Proof. unfold Child0Stable.word_24, global_word_1055, Child0Stable.closed_word_24, global_closed_1055, Child0Stable.expr_word_24, global_expr_1055.
 rewrite instance_36_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1055.
Transparent Child0Stable.word_25 global_word_1056.
Lemma instance_36_word_25 v : Child0Stable.word_25 (instance_36_leaves v) = global_word_1056 v.
Proof. unfold Child0Stable.word_25, global_word_1056, Child0Stable.closed_word_25, global_closed_1056, Child0Stable.expr_word_25, global_expr_1056.
 rewrite instance_36_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1056.
Transparent Child0Stable.word_4 global_word_1057.
Lemma instance_36_word_4 v : Child0Stable.word_4 (instance_36_leaves v) = global_word_1057 v.
Proof. unfold Child0Stable.word_4, global_word_1057, Child0Stable.closed_word_4, global_closed_1057, Child0Stable.expr_word_4, global_expr_1057.
 rewrite instance_36_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1057.
Transparent Child0Stable.word_10 global_word_2092.
Lemma instance_36_word_10 v : Child0Stable.word_10 (instance_36_leaves v) = global_word_2092 v.
Proof. unfold Child0Stable.word_10, global_word_2092, Child0Stable.closed_word_10, global_closed_2092, Child0Stable.expr_word_10, global_expr_2092.
 rewrite instance_36_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2092.
Transparent Child0Stable.word_26 global_word_1060.
Lemma instance_36_word_26 v : Child0Stable.word_26 (instance_36_leaves v) = global_word_1060 v.
Proof. unfold Child0Stable.word_26, global_word_1060, Child0Stable.closed_word_26, global_closed_1060, Child0Stable.expr_word_26, global_expr_1060.
 rewrite instance_36_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1060.
Transparent Child0Stable.word_5 global_word_1061.
Lemma instance_36_word_5 v : Child0Stable.word_5 (instance_36_leaves v) = global_word_1061 v.
Proof. unfold Child0Stable.word_5, global_word_1061, Child0Stable.closed_word_5, global_closed_1061, Child0Stable.expr_word_5, global_expr_1061.
 rewrite instance_36_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1061.
Transparent Child0Stable.word_11 global_word_2093.
Lemma instance_36_word_11 v : Child0Stable.word_11 (instance_36_leaves v) = global_word_2093 v.
Proof. unfold Child0Stable.word_11, global_word_2093, Child0Stable.closed_word_11, global_closed_2093, Child0Stable.expr_word_11, global_expr_2093.
 rewrite instance_36_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2093.
Transparent Child0Stable.word_12 global_word_2094.
Lemma instance_36_word_12 v : Child0Stable.word_12 (instance_36_leaves v) = global_word_2094 v.
Proof. unfold Child0Stable.word_12, global_word_2094, Child0Stable.closed_word_12, global_closed_2094, Child0Stable.expr_word_12, global_expr_2094.
 rewrite instance_36_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2094.
Transparent Child0Stable.word_13 global_word_2095.
Lemma instance_36_word_13 v : Child0Stable.word_13 (instance_36_leaves v) = global_word_2095 v.
Proof. unfold Child0Stable.word_13, global_word_2095, Child0Stable.closed_word_13, global_closed_2095, Child0Stable.expr_word_13, global_expr_2095.
 rewrite instance_36_word_10 instance_36_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2095.
Transparent Child0Stable.word_14 global_word_2096.
Lemma instance_36_word_14 v : Child0Stable.word_14 (instance_36_leaves v) = global_word_2096 v.
Proof. unfold Child0Stable.word_14, global_word_2096, Child0Stable.closed_word_14, global_closed_2096, Child0Stable.expr_word_14, global_expr_2096.
 rewrite instance_36_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2096.
Transparent Child0Stable.word_15 global_word_2097.
Lemma instance_36_word_15 v : Child0Stable.word_15 (instance_36_leaves v) = global_word_2097 v.
Proof. unfold Child0Stable.word_15, global_word_2097, Child0Stable.closed_word_15, global_closed_2097, Child0Stable.expr_word_15, global_expr_2097.
 rewrite instance_36_word_9 instance_36_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2097.
Transparent Child0Stable.word_16 global_word_2099.
Lemma instance_36_word_16 v : Child0Stable.word_16 (instance_36_leaves v) = global_word_2099 v.
Proof. unfold Child0Stable.word_16, global_word_2099, Child0Stable.closed_word_16, global_closed_2099, Child0Stable.expr_word_16, global_expr_2099.
 rewrite instance_36_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2099.
Transparent Child0Stable.word_17 global_word_2100.
Lemma instance_36_word_17 v : Child0Stable.word_17 (instance_36_leaves v) = global_word_2100 v.
Proof. unfold Child0Stable.word_17, global_word_2100, Child0Stable.closed_word_17, global_closed_2100, Child0Stable.expr_word_17, global_expr_2100.
 rewrite instance_36_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2100.
Transparent Child0Stable.word_18 global_word_2101.
Lemma instance_36_word_18 v : Child0Stable.word_18 (instance_36_leaves v) = global_word_2101 v.
Proof. unfold Child0Stable.word_18, global_word_2101, Child0Stable.closed_word_18, global_closed_2101, Child0Stable.expr_word_18, global_expr_2101.
 rewrite instance_36_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2101.
Definition instance_37_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2120 v
| 0, 1 => global_word_2116 v
| 0, 2 => global_word_1068 v
| 0, 3 => global_word_1071 v
| 0, 4 => global_word_1065 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_2120.
Lemma instance_37_word_0 v : Child1Stable.word_0 (instance_37_leaves v) = global_word_2120 v.
Proof. unfold Child1Stable.word_0, instance_37_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_2120.
Transparent Child1Stable.word_1 global_word_2116.
Lemma instance_37_word_1 v : Child1Stable.word_1 (instance_37_leaves v) = global_word_2116 v.
Proof. unfold Child1Stable.word_1, instance_37_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_2116.
Transparent Child1Stable.word_2 global_word_1068.
Lemma instance_37_word_2 v : Child1Stable.word_2 (instance_37_leaves v) = global_word_1068 v.
Proof. unfold Child1Stable.word_2, instance_37_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_1068.
Transparent Child1Stable.word_3 global_word_1071.
Lemma instance_37_word_3 v : Child1Stable.word_3 (instance_37_leaves v) = global_word_1071 v.
Proof. unfold Child1Stable.word_3, instance_37_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_1071.
Transparent Child1Stable.word_4 global_word_1065.
Lemma instance_37_word_4 v : Child1Stable.word_4 (instance_37_leaves v) = global_word_1065 v.
Proof. unfold Child1Stable.word_4, instance_37_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_1065.
Transparent Child1Stable.word_7 global_word_2103.
Lemma instance_37_word_7 v : Child1Stable.word_7 (instance_37_leaves v) = global_word_2103 v.
Proof. unfold Child1Stable.word_7, global_word_2103, Child1Stable.closed_word_7, global_closed_2103, Child1Stable.expr_word_7, global_expr_2103.
 rewrite instance_37_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_2103.
Transparent Child1Stable.word_8 global_word_2104.
Lemma instance_37_word_8 v : Child1Stable.word_8 (instance_37_leaves v) = global_word_2104 v.
Proof. unfold Child1Stable.word_8, global_word_2104, Child1Stable.closed_word_8, global_closed_2104, Child1Stable.expr_word_8, global_expr_2104.
 rewrite instance_37_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_2104.
Transparent Child1Stable.word_9 global_word_2105.
Lemma instance_37_word_9 v : Child1Stable.word_9 (instance_37_leaves v) = global_word_2105 v.
Proof. unfold Child1Stable.word_9, global_word_2105, Child1Stable.closed_word_9, global_closed_2105, Child1Stable.expr_word_9, global_expr_2105.
 rewrite instance_37_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_2105.
Transparent Child1Stable.word_10 global_word_2106.
Lemma instance_37_word_10 v : Child1Stable.word_10 (instance_37_leaves v) = global_word_2106 v.
Proof. unfold Child1Stable.word_10, global_word_2106, Child1Stable.closed_word_10, global_closed_2106, Child1Stable.expr_word_10, global_expr_2106.
 rewrite instance_37_word_7 instance_37_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_2106.
Transparent Child1Stable.word_11 global_word_2107.
Lemma instance_37_word_11 v : Child1Stable.word_11 (instance_37_leaves v) = global_word_2107 v.
Proof. unfold Child1Stable.word_11, global_word_2107, Child1Stable.closed_word_11, global_closed_2107, Child1Stable.expr_word_11, global_expr_2107.
 rewrite instance_37_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_2107.
Transparent Child1Stable.word_12 global_word_2108.
Lemma instance_37_word_12 v : Child1Stable.word_12 (instance_37_leaves v) = global_word_2108 v.
Proof. unfold Child1Stable.word_12, global_word_2108, Child1Stable.closed_word_12, global_closed_2108, Child1Stable.expr_word_12, global_expr_2108.
 rewrite instance_37_word_9 instance_37_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_2108.
Transparent Child1Stable.word_13 global_word_2109.
Lemma instance_37_word_13 v : Child1Stable.word_13 (instance_37_leaves v) = global_word_2109 v.
Proof. unfold Child1Stable.word_13, global_word_2109, Child1Stable.closed_word_13, global_closed_2109, Child1Stable.expr_word_13, global_expr_2109.
 rewrite instance_37_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_2109.
Transparent Child1Stable.word_25 global_word_1066.
Lemma instance_37_word_25 v : Child1Stable.word_25 (instance_37_leaves v) = global_word_1066 v.
Proof. unfold Child1Stable.word_25, global_word_1066, Child1Stable.closed_word_25, global_closed_1066, Child1Stable.expr_word_25, global_expr_1066.
 rewrite instance_37_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_1066.
Transparent Child1Stable.word_23 global_word_1069.
Lemma instance_37_word_23 v : Child1Stable.word_23 (instance_37_leaves v) = global_word_1069 v.
Proof. unfold Child1Stable.word_23, global_word_1069, Child1Stable.closed_word_23, global_closed_1069, Child1Stable.expr_word_23, global_expr_1069.
 rewrite instance_37_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_1069.
Transparent Child1Stable.word_24 global_word_1072.
Lemma instance_37_word_24 v : Child1Stable.word_24 (instance_37_leaves v) = global_word_1072 v.
Proof. unfold Child1Stable.word_24, global_word_1072, Child1Stable.closed_word_24, global_closed_1072, Child1Stable.expr_word_24, global_expr_1072.
 rewrite instance_37_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_1072.
Transparent Child1Stable.word_26 global_word_1073.
Lemma instance_37_word_26 v : Child1Stable.word_26 (instance_37_leaves v) = global_word_1073 v.
Proof. unfold Child1Stable.word_26, global_word_1073, Child1Stable.closed_word_26, global_closed_1073, Child1Stable.expr_word_26, global_expr_1073.
 rewrite instance_37_word_23 instance_37_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_1073.
Transparent Child1Stable.word_28 global_word_1074.
Lemma instance_37_word_28 v : Child1Stable.word_28 (instance_37_leaves v) = global_word_1074 v.
Proof. unfold Child1Stable.word_28, global_word_1074, Child1Stable.closed_word_28, global_closed_1074, Child1Stable.expr_word_28, global_expr_1074.
 rewrite instance_37_word_25 instance_37_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_1074.
Transparent Child1Stable.word_27 global_word_1075.
Lemma instance_37_word_27 v : Child1Stable.word_27 (instance_37_leaves v) = global_word_1075 v.
Proof. unfold Child1Stable.word_27, global_word_1075, Child1Stable.closed_word_27, global_closed_1075, Child1Stable.expr_word_27, global_expr_1075.
 rewrite instance_37_word_23 instance_37_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_1075.
Transparent Child1Stable.word_29 global_word_1076.
Lemma instance_37_word_29 v : Child1Stable.word_29 (instance_37_leaves v) = global_word_1076 v.
Proof. unfold Child1Stable.word_29, global_word_1076, Child1Stable.closed_word_29, global_closed_1076, Child1Stable.expr_word_29, global_expr_1076.
 rewrite instance_37_word_25 instance_37_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_1076.
Transparent Child1Stable.word_30 global_word_1077.
Lemma instance_37_word_30 v : Child1Stable.word_30 (instance_37_leaves v) = global_word_1077 v.
Proof. unfold Child1Stable.word_30, global_word_1077, Child1Stable.closed_word_30, global_closed_1077, Child1Stable.expr_word_30, global_expr_1077.
 rewrite instance_37_word_27 instance_37_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_1077.
Transparent Child1Stable.word_31 global_word_1078.
Lemma instance_37_word_31 v : Child1Stable.word_31 (instance_37_leaves v) = global_word_1078 v.
Proof. unfold Child1Stable.word_31, global_word_1078, Child1Stable.closed_word_31, global_closed_1078, Child1Stable.expr_word_31, global_expr_1078.
 rewrite instance_37_word_28 instance_37_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_1078.
Transparent Child1Stable.word_32 global_word_1079.
Lemma instance_37_word_32 v : Child1Stable.word_32 (instance_37_leaves v) = global_word_1079 v.
Proof. unfold Child1Stable.word_32, global_word_1079, Child1Stable.closed_word_32, global_closed_1079, Child1Stable.expr_word_32, global_expr_1079.
 rewrite instance_37_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_1079.
Transparent Child1Stable.word_33 global_word_1080.
Lemma instance_37_word_33 v : Child1Stable.word_33 (instance_37_leaves v) = global_word_1080 v.
Proof. unfold Child1Stable.word_33, global_word_1080, Child1Stable.closed_word_33, global_closed_1080, Child1Stable.expr_word_33, global_expr_1080.
 rewrite instance_37_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_1080.
Transparent Child1Stable.word_5 global_word_1081.
Lemma instance_37_word_5 v : Child1Stable.word_5 (instance_37_leaves v) = global_word_1081 v.
Proof. unfold Child1Stable.word_5, global_word_1081, Child1Stable.closed_word_5, global_closed_1081, Child1Stable.expr_word_5, global_expr_1081.
 rewrite instance_37_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_1081.
Transparent Child1Stable.word_14 global_word_2110.
Lemma instance_37_word_14 v : Child1Stable.word_14 (instance_37_leaves v) = global_word_2110 v.
Proof. unfold Child1Stable.word_14, global_word_2110, Child1Stable.closed_word_14, global_closed_2110, Child1Stable.expr_word_14, global_expr_2110.
 rewrite instance_37_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_2110.
Transparent Child1Stable.word_34 global_word_1084.
Lemma instance_37_word_34 v : Child1Stable.word_34 (instance_37_leaves v) = global_word_1084 v.
Proof. unfold Child1Stable.word_34, global_word_1084, Child1Stable.closed_word_34, global_closed_1084, Child1Stable.expr_word_34, global_expr_1084.
 rewrite instance_37_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_1084.
Transparent Child1Stable.word_6 global_word_1085.
Lemma instance_37_word_6 v : Child1Stable.word_6 (instance_37_leaves v) = global_word_1085 v.
Proof. unfold Child1Stable.word_6, global_word_1085, Child1Stable.closed_word_6, global_closed_1085, Child1Stable.expr_word_6, global_expr_1085.
 rewrite instance_37_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_1085.
Transparent Child1Stable.word_15 global_word_2111.
Lemma instance_37_word_15 v : Child1Stable.word_15 (instance_37_leaves v) = global_word_2111 v.
Proof. unfold Child1Stable.word_15, global_word_2111, Child1Stable.closed_word_15, global_closed_2111, Child1Stable.expr_word_15, global_expr_2111.
 rewrite instance_37_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_2111.
Transparent Child1Stable.word_16 global_word_2112.
Lemma instance_37_word_16 v : Child1Stable.word_16 (instance_37_leaves v) = global_word_2112 v.
Proof. unfold Child1Stable.word_16, global_word_2112, Child1Stable.closed_word_16, global_closed_2112, Child1Stable.expr_word_16, global_expr_2112.
 rewrite instance_37_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_2112.
Transparent Child1Stable.word_17 global_word_2113.
Lemma instance_37_word_17 v : Child1Stable.word_17 (instance_37_leaves v) = global_word_2113 v.
Proof. unfold Child1Stable.word_17, global_word_2113, Child1Stable.closed_word_17, global_closed_2113, Child1Stable.expr_word_17, global_expr_2113.
 rewrite instance_37_word_14 instance_37_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_2113.
Transparent Child1Stable.word_18 global_word_2114.
Lemma instance_37_word_18 v : Child1Stable.word_18 (instance_37_leaves v) = global_word_2114 v.
Proof. unfold Child1Stable.word_18, global_word_2114, Child1Stable.closed_word_18, global_closed_2114, Child1Stable.expr_word_18, global_expr_2114.
 rewrite instance_37_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_2114.
Transparent Child1Stable.word_19 global_word_2115.
Lemma instance_37_word_19 v : Child1Stable.word_19 (instance_37_leaves v) = global_word_2115 v.
Proof. unfold Child1Stable.word_19, global_word_2115, Child1Stable.closed_word_19, global_closed_2115, Child1Stable.expr_word_19, global_expr_2115.
 rewrite instance_37_word_13 instance_37_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_2115.
Transparent Child1Stable.word_20 global_word_2117.
Lemma instance_37_word_20 v : Child1Stable.word_20 (instance_37_leaves v) = global_word_2117 v.
Proof. unfold Child1Stable.word_20, global_word_2117, Child1Stable.closed_word_20, global_closed_2117, Child1Stable.expr_word_20, global_expr_2117.
 rewrite instance_37_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_2117.
Transparent Child1Stable.word_21 global_word_2118.
Lemma instance_37_word_21 v : Child1Stable.word_21 (instance_37_leaves v) = global_word_2118 v.
Proof. unfold Child1Stable.word_21, global_word_2118, Child1Stable.closed_word_21, global_closed_2118, Child1Stable.expr_word_21, global_expr_2118.
 rewrite instance_37_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_2118.
Transparent Child1Stable.word_22 global_word_2119.
Lemma instance_37_word_22 v : Child1Stable.word_22 (instance_37_leaves v) = global_word_2119 v.
Proof. unfold Child1Stable.word_22, global_word_2119, Child1Stable.closed_word_22, global_closed_2119, Child1Stable.expr_word_22, global_expr_2119.
 rewrite instance_37_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_2119.
Definition instance_38_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2138 v
| 0, 1 => global_word_2134 v
| 0, 2 => global_word_1092 v
| 0, 3 => global_word_1095 v
| 0, 4 => global_word_1089 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_2138.
Lemma instance_38_word_0 v : Child1Stable.word_0 (instance_38_leaves v) = global_word_2138 v.
Proof. unfold Child1Stable.word_0, instance_38_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_2138.
Transparent Child1Stable.word_1 global_word_2134.
Lemma instance_38_word_1 v : Child1Stable.word_1 (instance_38_leaves v) = global_word_2134 v.
Proof. unfold Child1Stable.word_1, instance_38_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_2134.
Transparent Child1Stable.word_2 global_word_1092.
Lemma instance_38_word_2 v : Child1Stable.word_2 (instance_38_leaves v) = global_word_1092 v.
Proof. unfold Child1Stable.word_2, instance_38_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_1092.
Transparent Child1Stable.word_3 global_word_1095.
Lemma instance_38_word_3 v : Child1Stable.word_3 (instance_38_leaves v) = global_word_1095 v.
Proof. unfold Child1Stable.word_3, instance_38_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_1095.
Transparent Child1Stable.word_4 global_word_1089.
Lemma instance_38_word_4 v : Child1Stable.word_4 (instance_38_leaves v) = global_word_1089 v.
Proof. unfold Child1Stable.word_4, instance_38_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_1089.
Transparent Child1Stable.word_7 global_word_2121.
Lemma instance_38_word_7 v : Child1Stable.word_7 (instance_38_leaves v) = global_word_2121 v.
Proof. unfold Child1Stable.word_7, global_word_2121, Child1Stable.closed_word_7, global_closed_2121, Child1Stable.expr_word_7, global_expr_2121.
 rewrite instance_38_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_2121.
Transparent Child1Stable.word_8 global_word_2122.
Lemma instance_38_word_8 v : Child1Stable.word_8 (instance_38_leaves v) = global_word_2122 v.
Proof. unfold Child1Stable.word_8, global_word_2122, Child1Stable.closed_word_8, global_closed_2122, Child1Stable.expr_word_8, global_expr_2122.
 rewrite instance_38_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_2122.
Transparent Child1Stable.word_9 global_word_2123.
Lemma instance_38_word_9 v : Child1Stable.word_9 (instance_38_leaves v) = global_word_2123 v.
Proof. unfold Child1Stable.word_9, global_word_2123, Child1Stable.closed_word_9, global_closed_2123, Child1Stable.expr_word_9, global_expr_2123.
 rewrite instance_38_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_2123.
Transparent Child1Stable.word_10 global_word_2124.
Lemma instance_38_word_10 v : Child1Stable.word_10 (instance_38_leaves v) = global_word_2124 v.
Proof. unfold Child1Stable.word_10, global_word_2124, Child1Stable.closed_word_10, global_closed_2124, Child1Stable.expr_word_10, global_expr_2124.
 rewrite instance_38_word_7 instance_38_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_2124.
Transparent Child1Stable.word_11 global_word_2125.
Lemma instance_38_word_11 v : Child1Stable.word_11 (instance_38_leaves v) = global_word_2125 v.
Proof. unfold Child1Stable.word_11, global_word_2125, Child1Stable.closed_word_11, global_closed_2125, Child1Stable.expr_word_11, global_expr_2125.
 rewrite instance_38_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_2125.
Transparent Child1Stable.word_12 global_word_2126.
Lemma instance_38_word_12 v : Child1Stable.word_12 (instance_38_leaves v) = global_word_2126 v.
Proof. unfold Child1Stable.word_12, global_word_2126, Child1Stable.closed_word_12, global_closed_2126, Child1Stable.expr_word_12, global_expr_2126.
 rewrite instance_38_word_9 instance_38_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_2126.
Transparent Child1Stable.word_13 global_word_2127.
Lemma instance_38_word_13 v : Child1Stable.word_13 (instance_38_leaves v) = global_word_2127 v.
Proof. unfold Child1Stable.word_13, global_word_2127, Child1Stable.closed_word_13, global_closed_2127, Child1Stable.expr_word_13, global_expr_2127.
 rewrite instance_38_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_2127.
Transparent Child1Stable.word_25 global_word_1090.
Lemma instance_38_word_25 v : Child1Stable.word_25 (instance_38_leaves v) = global_word_1090 v.
Proof. unfold Child1Stable.word_25, global_word_1090, Child1Stable.closed_word_25, global_closed_1090, Child1Stable.expr_word_25, global_expr_1090.
 rewrite instance_38_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_1090.
Transparent Child1Stable.word_23 global_word_1093.
Lemma instance_38_word_23 v : Child1Stable.word_23 (instance_38_leaves v) = global_word_1093 v.
Proof. unfold Child1Stable.word_23, global_word_1093, Child1Stable.closed_word_23, global_closed_1093, Child1Stable.expr_word_23, global_expr_1093.
 rewrite instance_38_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_1093.
Transparent Child1Stable.word_24 global_word_1096.
Lemma instance_38_word_24 v : Child1Stable.word_24 (instance_38_leaves v) = global_word_1096 v.
Proof. unfold Child1Stable.word_24, global_word_1096, Child1Stable.closed_word_24, global_closed_1096, Child1Stable.expr_word_24, global_expr_1096.
 rewrite instance_38_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_1096.
Transparent Child1Stable.word_26 global_word_1097.
Lemma instance_38_word_26 v : Child1Stable.word_26 (instance_38_leaves v) = global_word_1097 v.
Proof. unfold Child1Stable.word_26, global_word_1097, Child1Stable.closed_word_26, global_closed_1097, Child1Stable.expr_word_26, global_expr_1097.
 rewrite instance_38_word_23 instance_38_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_1097.
Transparent Child1Stable.word_28 global_word_1098.
Lemma instance_38_word_28 v : Child1Stable.word_28 (instance_38_leaves v) = global_word_1098 v.
Proof. unfold Child1Stable.word_28, global_word_1098, Child1Stable.closed_word_28, global_closed_1098, Child1Stable.expr_word_28, global_expr_1098.
 rewrite instance_38_word_25 instance_38_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_1098.
Transparent Child1Stable.word_27 global_word_1099.
Lemma instance_38_word_27 v : Child1Stable.word_27 (instance_38_leaves v) = global_word_1099 v.
Proof. unfold Child1Stable.word_27, global_word_1099, Child1Stable.closed_word_27, global_closed_1099, Child1Stable.expr_word_27, global_expr_1099.
 rewrite instance_38_word_23 instance_38_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_1099.
Transparent Child1Stable.word_29 global_word_1100.
Lemma instance_38_word_29 v : Child1Stable.word_29 (instance_38_leaves v) = global_word_1100 v.
Proof. unfold Child1Stable.word_29, global_word_1100, Child1Stable.closed_word_29, global_closed_1100, Child1Stable.expr_word_29, global_expr_1100.
 rewrite instance_38_word_25 instance_38_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_1100.
Transparent Child1Stable.word_30 global_word_1101.
Lemma instance_38_word_30 v : Child1Stable.word_30 (instance_38_leaves v) = global_word_1101 v.
Proof. unfold Child1Stable.word_30, global_word_1101, Child1Stable.closed_word_30, global_closed_1101, Child1Stable.expr_word_30, global_expr_1101.
 rewrite instance_38_word_27 instance_38_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_1101.
Transparent Child1Stable.word_31 global_word_1102.
Lemma instance_38_word_31 v : Child1Stable.word_31 (instance_38_leaves v) = global_word_1102 v.
Proof. unfold Child1Stable.word_31, global_word_1102, Child1Stable.closed_word_31, global_closed_1102, Child1Stable.expr_word_31, global_expr_1102.
 rewrite instance_38_word_28 instance_38_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_1102.
Transparent Child1Stable.word_32 global_word_1103.
Lemma instance_38_word_32 v : Child1Stable.word_32 (instance_38_leaves v) = global_word_1103 v.
Proof. unfold Child1Stable.word_32, global_word_1103, Child1Stable.closed_word_32, global_closed_1103, Child1Stable.expr_word_32, global_expr_1103.
 rewrite instance_38_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_1103.
Transparent Child1Stable.word_33 global_word_1104.
Lemma instance_38_word_33 v : Child1Stable.word_33 (instance_38_leaves v) = global_word_1104 v.
Proof. unfold Child1Stable.word_33, global_word_1104, Child1Stable.closed_word_33, global_closed_1104, Child1Stable.expr_word_33, global_expr_1104.
 rewrite instance_38_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_1104.
Transparent Child1Stable.word_5 global_word_1105.
Lemma instance_38_word_5 v : Child1Stable.word_5 (instance_38_leaves v) = global_word_1105 v.
Proof. unfold Child1Stable.word_5, global_word_1105, Child1Stable.closed_word_5, global_closed_1105, Child1Stable.expr_word_5, global_expr_1105.
 rewrite instance_38_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_1105.
Transparent Child1Stable.word_14 global_word_2128.
Lemma instance_38_word_14 v : Child1Stable.word_14 (instance_38_leaves v) = global_word_2128 v.
Proof. unfold Child1Stable.word_14, global_word_2128, Child1Stable.closed_word_14, global_closed_2128, Child1Stable.expr_word_14, global_expr_2128.
 rewrite instance_38_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_2128.
Transparent Child1Stable.word_34 global_word_1108.
Lemma instance_38_word_34 v : Child1Stable.word_34 (instance_38_leaves v) = global_word_1108 v.
Proof. unfold Child1Stable.word_34, global_word_1108, Child1Stable.closed_word_34, global_closed_1108, Child1Stable.expr_word_34, global_expr_1108.
 rewrite instance_38_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_1108.
Transparent Child1Stable.word_6 global_word_1109.
Lemma instance_38_word_6 v : Child1Stable.word_6 (instance_38_leaves v) = global_word_1109 v.
Proof. unfold Child1Stable.word_6, global_word_1109, Child1Stable.closed_word_6, global_closed_1109, Child1Stable.expr_word_6, global_expr_1109.
 rewrite instance_38_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_1109.
Transparent Child1Stable.word_15 global_word_2129.
Lemma instance_38_word_15 v : Child1Stable.word_15 (instance_38_leaves v) = global_word_2129 v.
Proof. unfold Child1Stable.word_15, global_word_2129, Child1Stable.closed_word_15, global_closed_2129, Child1Stable.expr_word_15, global_expr_2129.
 rewrite instance_38_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_2129.
Transparent Child1Stable.word_16 global_word_2130.
Lemma instance_38_word_16 v : Child1Stable.word_16 (instance_38_leaves v) = global_word_2130 v.
Proof. unfold Child1Stable.word_16, global_word_2130, Child1Stable.closed_word_16, global_closed_2130, Child1Stable.expr_word_16, global_expr_2130.
 rewrite instance_38_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_2130.
Transparent Child1Stable.word_17 global_word_2131.
Lemma instance_38_word_17 v : Child1Stable.word_17 (instance_38_leaves v) = global_word_2131 v.
Proof. unfold Child1Stable.word_17, global_word_2131, Child1Stable.closed_word_17, global_closed_2131, Child1Stable.expr_word_17, global_expr_2131.
 rewrite instance_38_word_14 instance_38_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_2131.
Transparent Child1Stable.word_18 global_word_2132.
Lemma instance_38_word_18 v : Child1Stable.word_18 (instance_38_leaves v) = global_word_2132 v.
Proof. unfold Child1Stable.word_18, global_word_2132, Child1Stable.closed_word_18, global_closed_2132, Child1Stable.expr_word_18, global_expr_2132.
 rewrite instance_38_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_2132.
Transparent Child1Stable.word_19 global_word_2133.
Lemma instance_38_word_19 v : Child1Stable.word_19 (instance_38_leaves v) = global_word_2133 v.
Proof. unfold Child1Stable.word_19, global_word_2133, Child1Stable.closed_word_19, global_closed_2133, Child1Stable.expr_word_19, global_expr_2133.
 rewrite instance_38_word_13 instance_38_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_2133.
Transparent Child1Stable.word_20 global_word_2135.
Lemma instance_38_word_20 v : Child1Stable.word_20 (instance_38_leaves v) = global_word_2135 v.
Proof. unfold Child1Stable.word_20, global_word_2135, Child1Stable.closed_word_20, global_closed_2135, Child1Stable.expr_word_20, global_expr_2135.
 rewrite instance_38_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_2135.
Transparent Child1Stable.word_21 global_word_2136.
Lemma instance_38_word_21 v : Child1Stable.word_21 (instance_38_leaves v) = global_word_2136 v.
Proof. unfold Child1Stable.word_21, global_word_2136, Child1Stable.closed_word_21, global_closed_2136, Child1Stable.expr_word_21, global_expr_2136.
 rewrite instance_38_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_2136.
Transparent Child1Stable.word_22 global_word_2137.
Lemma instance_38_word_22 v : Child1Stable.word_22 (instance_38_leaves v) = global_word_2137 v.
Proof. unfold Child1Stable.word_22, global_word_2137, Child1Stable.closed_word_22, global_closed_2137, Child1Stable.expr_word_22, global_expr_2137.
 rewrite instance_38_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_2137.
Definition instance_39_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2153 v
| 0, 1 => global_word_2149 v
| 0, 2 => global_word_1113 v
| 0, 3 => global_word_1116 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2153.
Lemma instance_39_word_0 v : Child0Stable.word_0 (instance_39_leaves v) = global_word_2153 v.
Proof. unfold Child0Stable.word_0, instance_39_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2153.
Transparent Child0Stable.word_1 global_word_2149.
Lemma instance_39_word_1 v : Child0Stable.word_1 (instance_39_leaves v) = global_word_2149 v.
Proof. unfold Child0Stable.word_1, instance_39_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2149.
Transparent Child0Stable.word_2 global_word_1113.
Lemma instance_39_word_2 v : Child0Stable.word_2 (instance_39_leaves v) = global_word_1113 v.
Proof. unfold Child0Stable.word_2, instance_39_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1113.
Transparent Child0Stable.word_3 global_word_1116.
Lemma instance_39_word_3 v : Child0Stable.word_3 (instance_39_leaves v) = global_word_1116 v.
Proof. unfold Child0Stable.word_3, instance_39_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1116.
Transparent Child0Stable.word_6 global_word_2139.
Lemma instance_39_word_6 v : Child0Stable.word_6 (instance_39_leaves v) = global_word_2139 v.
Proof. unfold Child0Stable.word_6, global_word_2139, Child0Stable.closed_word_6, global_closed_2139, Child0Stable.expr_word_6, global_expr_2139.
 rewrite instance_39_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2139.
Transparent Child0Stable.word_7 global_word_2140.
Lemma instance_39_word_7 v : Child0Stable.word_7 (instance_39_leaves v) = global_word_2140 v.
Proof. unfold Child0Stable.word_7, global_word_2140, Child0Stable.closed_word_7, global_closed_2140, Child0Stable.expr_word_7, global_expr_2140.
 rewrite instance_39_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2140.
Transparent Child0Stable.word_8 global_word_2141.
Lemma instance_39_word_8 v : Child0Stable.word_8 (instance_39_leaves v) = global_word_2141 v.
Proof. unfold Child0Stable.word_8, global_word_2141, Child0Stable.closed_word_8, global_closed_2141, Child0Stable.expr_word_8, global_expr_2141.
 rewrite instance_39_word_6 instance_39_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2141.
Transparent Child0Stable.word_9 global_word_2142.
Lemma instance_39_word_9 v : Child0Stable.word_9 (instance_39_leaves v) = global_word_2142 v.
Proof. unfold Child0Stable.word_9, global_word_2142, Child0Stable.closed_word_9, global_closed_2142, Child0Stable.expr_word_9, global_expr_2142.
 rewrite instance_39_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2142.
Transparent Child0Stable.word_19 global_word_1114.
Lemma instance_39_word_19 v : Child0Stable.word_19 (instance_39_leaves v) = global_word_1114 v.
Proof. unfold Child0Stable.word_19, global_word_1114, Child0Stable.closed_word_19, global_closed_1114, Child0Stable.expr_word_19, global_expr_1114.
 rewrite instance_39_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1114.
Transparent Child0Stable.word_20 global_word_1117.
Lemma instance_39_word_20 v : Child0Stable.word_20 (instance_39_leaves v) = global_word_1117 v.
Proof. unfold Child0Stable.word_20, global_word_1117, Child0Stable.closed_word_20, global_closed_1117, Child0Stable.expr_word_20, global_expr_1117.
 rewrite instance_39_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1117.
Transparent Child0Stable.word_21 global_word_1118.
Lemma instance_39_word_21 v : Child0Stable.word_21 (instance_39_leaves v) = global_word_1118 v.
Proof. unfold Child0Stable.word_21, global_word_1118, Child0Stable.closed_word_21, global_closed_1118, Child0Stable.expr_word_21, global_expr_1118.
 rewrite instance_39_word_19 instance_39_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1118.
Transparent Child0Stable.word_22 global_word_1119.
Lemma instance_39_word_22 v : Child0Stable.word_22 (instance_39_leaves v) = global_word_1119 v.
Proof. unfold Child0Stable.word_22, global_word_1119, Child0Stable.closed_word_22, global_closed_1119, Child0Stable.expr_word_22, global_expr_1119.
 rewrite instance_39_word_19 instance_39_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1119.
Transparent Child0Stable.word_23 global_word_1120.
Lemma instance_39_word_23 v : Child0Stable.word_23 (instance_39_leaves v) = global_word_1120 v.
Proof. unfold Child0Stable.word_23, global_word_1120, Child0Stable.closed_word_23, global_closed_1120, Child0Stable.expr_word_23, global_expr_1120.
 rewrite instance_39_word_21 instance_39_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1120.
Transparent Child0Stable.word_24 global_word_1121.
Lemma instance_39_word_24 v : Child0Stable.word_24 (instance_39_leaves v) = global_word_1121 v.
Proof. unfold Child0Stable.word_24, global_word_1121, Child0Stable.closed_word_24, global_closed_1121, Child0Stable.expr_word_24, global_expr_1121.
 rewrite instance_39_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1121.
Transparent Child0Stable.word_25 global_word_1122.
Lemma instance_39_word_25 v : Child0Stable.word_25 (instance_39_leaves v) = global_word_1122 v.
Proof. unfold Child0Stable.word_25, global_word_1122, Child0Stable.closed_word_25, global_closed_1122, Child0Stable.expr_word_25, global_expr_1122.
 rewrite instance_39_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1122.
Transparent Child0Stable.word_4 global_word_1123.
Lemma instance_39_word_4 v : Child0Stable.word_4 (instance_39_leaves v) = global_word_1123 v.
Proof. unfold Child0Stable.word_4, global_word_1123, Child0Stable.closed_word_4, global_closed_1123, Child0Stable.expr_word_4, global_expr_1123.
 rewrite instance_39_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1123.
Transparent Child0Stable.word_10 global_word_2143.
Lemma instance_39_word_10 v : Child0Stable.word_10 (instance_39_leaves v) = global_word_2143 v.
Proof. unfold Child0Stable.word_10, global_word_2143, Child0Stable.closed_word_10, global_closed_2143, Child0Stable.expr_word_10, global_expr_2143.
 rewrite instance_39_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2143.
Transparent Child0Stable.word_26 global_word_1126.
Lemma instance_39_word_26 v : Child0Stable.word_26 (instance_39_leaves v) = global_word_1126 v.
Proof. unfold Child0Stable.word_26, global_word_1126, Child0Stable.closed_word_26, global_closed_1126, Child0Stable.expr_word_26, global_expr_1126.
 rewrite instance_39_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1126.
Transparent Child0Stable.word_5 global_word_1127.
Lemma instance_39_word_5 v : Child0Stable.word_5 (instance_39_leaves v) = global_word_1127 v.
Proof. unfold Child0Stable.word_5, global_word_1127, Child0Stable.closed_word_5, global_closed_1127, Child0Stable.expr_word_5, global_expr_1127.
 rewrite instance_39_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1127.
Transparent Child0Stable.word_11 global_word_2144.
Lemma instance_39_word_11 v : Child0Stable.word_11 (instance_39_leaves v) = global_word_2144 v.
Proof. unfold Child0Stable.word_11, global_word_2144, Child0Stable.closed_word_11, global_closed_2144, Child0Stable.expr_word_11, global_expr_2144.
 rewrite instance_39_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2144.
Transparent Child0Stable.word_12 global_word_2145.
Lemma instance_39_word_12 v : Child0Stable.word_12 (instance_39_leaves v) = global_word_2145 v.
Proof. unfold Child0Stable.word_12, global_word_2145, Child0Stable.closed_word_12, global_closed_2145, Child0Stable.expr_word_12, global_expr_2145.
 rewrite instance_39_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2145.
Transparent Child0Stable.word_13 global_word_2146.
Lemma instance_39_word_13 v : Child0Stable.word_13 (instance_39_leaves v) = global_word_2146 v.
Proof. unfold Child0Stable.word_13, global_word_2146, Child0Stable.closed_word_13, global_closed_2146, Child0Stable.expr_word_13, global_expr_2146.
 rewrite instance_39_word_10 instance_39_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2146.
Transparent Child0Stable.word_14 global_word_2147.
Lemma instance_39_word_14 v : Child0Stable.word_14 (instance_39_leaves v) = global_word_2147 v.
Proof. unfold Child0Stable.word_14, global_word_2147, Child0Stable.closed_word_14, global_closed_2147, Child0Stable.expr_word_14, global_expr_2147.
 rewrite instance_39_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2147.
Transparent Child0Stable.word_15 global_word_2148.
Lemma instance_39_word_15 v : Child0Stable.word_15 (instance_39_leaves v) = global_word_2148 v.
Proof. unfold Child0Stable.word_15, global_word_2148, Child0Stable.closed_word_15, global_closed_2148, Child0Stable.expr_word_15, global_expr_2148.
 rewrite instance_39_word_9 instance_39_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2148.
Transparent Child0Stable.word_16 global_word_2150.
Lemma instance_39_word_16 v : Child0Stable.word_16 (instance_39_leaves v) = global_word_2150 v.
Proof. unfold Child0Stable.word_16, global_word_2150, Child0Stable.closed_word_16, global_closed_2150, Child0Stable.expr_word_16, global_expr_2150.
 rewrite instance_39_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2150.
Transparent Child0Stable.word_17 global_word_2151.
Lemma instance_39_word_17 v : Child0Stable.word_17 (instance_39_leaves v) = global_word_2151 v.
Proof. unfold Child0Stable.word_17, global_word_2151, Child0Stable.closed_word_17, global_closed_2151, Child0Stable.expr_word_17, global_expr_2151.
 rewrite instance_39_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2151.
Transparent Child0Stable.word_18 global_word_2152.
Lemma instance_39_word_18 v : Child0Stable.word_18 (instance_39_leaves v) = global_word_2152 v.
Proof. unfold Child0Stable.word_18, global_word_2152, Child0Stable.closed_word_18, global_closed_2152, Child0Stable.expr_word_18, global_expr_2152.
 rewrite instance_39_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2152.
Definition instance_40_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2168 v
| 0, 1 => global_word_2164 v
| 0, 2 => global_word_1131 v
| 0, 3 => global_word_1134 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2168.
Lemma instance_40_word_0 v : Child0Stable.word_0 (instance_40_leaves v) = global_word_2168 v.
Proof. unfold Child0Stable.word_0, instance_40_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2168.
Transparent Child0Stable.word_1 global_word_2164.
Lemma instance_40_word_1 v : Child0Stable.word_1 (instance_40_leaves v) = global_word_2164 v.
Proof. unfold Child0Stable.word_1, instance_40_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2164.
Transparent Child0Stable.word_2 global_word_1131.
Lemma instance_40_word_2 v : Child0Stable.word_2 (instance_40_leaves v) = global_word_1131 v.
Proof. unfold Child0Stable.word_2, instance_40_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1131.
Transparent Child0Stable.word_3 global_word_1134.
Lemma instance_40_word_3 v : Child0Stable.word_3 (instance_40_leaves v) = global_word_1134 v.
Proof. unfold Child0Stable.word_3, instance_40_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1134.
Transparent Child0Stable.word_6 global_word_2154.
Lemma instance_40_word_6 v : Child0Stable.word_6 (instance_40_leaves v) = global_word_2154 v.
Proof. unfold Child0Stable.word_6, global_word_2154, Child0Stable.closed_word_6, global_closed_2154, Child0Stable.expr_word_6, global_expr_2154.
 rewrite instance_40_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2154.
Transparent Child0Stable.word_7 global_word_2155.
Lemma instance_40_word_7 v : Child0Stable.word_7 (instance_40_leaves v) = global_word_2155 v.
Proof. unfold Child0Stable.word_7, global_word_2155, Child0Stable.closed_word_7, global_closed_2155, Child0Stable.expr_word_7, global_expr_2155.
 rewrite instance_40_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2155.
Transparent Child0Stable.word_8 global_word_2156.
Lemma instance_40_word_8 v : Child0Stable.word_8 (instance_40_leaves v) = global_word_2156 v.
Proof. unfold Child0Stable.word_8, global_word_2156, Child0Stable.closed_word_8, global_closed_2156, Child0Stable.expr_word_8, global_expr_2156.
 rewrite instance_40_word_6 instance_40_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2156.
Transparent Child0Stable.word_9 global_word_2157.
Lemma instance_40_word_9 v : Child0Stable.word_9 (instance_40_leaves v) = global_word_2157 v.
Proof. unfold Child0Stable.word_9, global_word_2157, Child0Stable.closed_word_9, global_closed_2157, Child0Stable.expr_word_9, global_expr_2157.
 rewrite instance_40_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2157.
Transparent Child0Stable.word_19 global_word_1132.
Lemma instance_40_word_19 v : Child0Stable.word_19 (instance_40_leaves v) = global_word_1132 v.
Proof. unfold Child0Stable.word_19, global_word_1132, Child0Stable.closed_word_19, global_closed_1132, Child0Stable.expr_word_19, global_expr_1132.
 rewrite instance_40_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1132.
Transparent Child0Stable.word_20 global_word_1135.
Lemma instance_40_word_20 v : Child0Stable.word_20 (instance_40_leaves v) = global_word_1135 v.
Proof. unfold Child0Stable.word_20, global_word_1135, Child0Stable.closed_word_20, global_closed_1135, Child0Stable.expr_word_20, global_expr_1135.
 rewrite instance_40_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1135.
Transparent Child0Stable.word_21 global_word_1136.
Lemma instance_40_word_21 v : Child0Stable.word_21 (instance_40_leaves v) = global_word_1136 v.
Proof. unfold Child0Stable.word_21, global_word_1136, Child0Stable.closed_word_21, global_closed_1136, Child0Stable.expr_word_21, global_expr_1136.
 rewrite instance_40_word_19 instance_40_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1136.
Transparent Child0Stable.word_22 global_word_1137.
Lemma instance_40_word_22 v : Child0Stable.word_22 (instance_40_leaves v) = global_word_1137 v.
Proof. unfold Child0Stable.word_22, global_word_1137, Child0Stable.closed_word_22, global_closed_1137, Child0Stable.expr_word_22, global_expr_1137.
 rewrite instance_40_word_19 instance_40_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1137.
Transparent Child0Stable.word_23 global_word_1138.
Lemma instance_40_word_23 v : Child0Stable.word_23 (instance_40_leaves v) = global_word_1138 v.
Proof. unfold Child0Stable.word_23, global_word_1138, Child0Stable.closed_word_23, global_closed_1138, Child0Stable.expr_word_23, global_expr_1138.
 rewrite instance_40_word_21 instance_40_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1138.
Transparent Child0Stable.word_24 global_word_1139.
Lemma instance_40_word_24 v : Child0Stable.word_24 (instance_40_leaves v) = global_word_1139 v.
Proof. unfold Child0Stable.word_24, global_word_1139, Child0Stable.closed_word_24, global_closed_1139, Child0Stable.expr_word_24, global_expr_1139.
 rewrite instance_40_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1139.
Transparent Child0Stable.word_25 global_word_1140.
Lemma instance_40_word_25 v : Child0Stable.word_25 (instance_40_leaves v) = global_word_1140 v.
Proof. unfold Child0Stable.word_25, global_word_1140, Child0Stable.closed_word_25, global_closed_1140, Child0Stable.expr_word_25, global_expr_1140.
 rewrite instance_40_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1140.
Transparent Child0Stable.word_4 global_word_1141.
Lemma instance_40_word_4 v : Child0Stable.word_4 (instance_40_leaves v) = global_word_1141 v.
Proof. unfold Child0Stable.word_4, global_word_1141, Child0Stable.closed_word_4, global_closed_1141, Child0Stable.expr_word_4, global_expr_1141.
 rewrite instance_40_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1141.
Transparent Child0Stable.word_10 global_word_2158.
Lemma instance_40_word_10 v : Child0Stable.word_10 (instance_40_leaves v) = global_word_2158 v.
Proof. unfold Child0Stable.word_10, global_word_2158, Child0Stable.closed_word_10, global_closed_2158, Child0Stable.expr_word_10, global_expr_2158.
 rewrite instance_40_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2158.
Transparent Child0Stable.word_26 global_word_1144.
Lemma instance_40_word_26 v : Child0Stable.word_26 (instance_40_leaves v) = global_word_1144 v.
Proof. unfold Child0Stable.word_26, global_word_1144, Child0Stable.closed_word_26, global_closed_1144, Child0Stable.expr_word_26, global_expr_1144.
 rewrite instance_40_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1144.
Transparent Child0Stable.word_5 global_word_1145.
Lemma instance_40_word_5 v : Child0Stable.word_5 (instance_40_leaves v) = global_word_1145 v.
Proof. unfold Child0Stable.word_5, global_word_1145, Child0Stable.closed_word_5, global_closed_1145, Child0Stable.expr_word_5, global_expr_1145.
 rewrite instance_40_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1145.
Transparent Child0Stable.word_11 global_word_2159.
Lemma instance_40_word_11 v : Child0Stable.word_11 (instance_40_leaves v) = global_word_2159 v.
Proof. unfold Child0Stable.word_11, global_word_2159, Child0Stable.closed_word_11, global_closed_2159, Child0Stable.expr_word_11, global_expr_2159.
 rewrite instance_40_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2159.
Transparent Child0Stable.word_12 global_word_2160.
Lemma instance_40_word_12 v : Child0Stable.word_12 (instance_40_leaves v) = global_word_2160 v.
Proof. unfold Child0Stable.word_12, global_word_2160, Child0Stable.closed_word_12, global_closed_2160, Child0Stable.expr_word_12, global_expr_2160.
 rewrite instance_40_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2160.
Transparent Child0Stable.word_13 global_word_2161.
Lemma instance_40_word_13 v : Child0Stable.word_13 (instance_40_leaves v) = global_word_2161 v.
Proof. unfold Child0Stable.word_13, global_word_2161, Child0Stable.closed_word_13, global_closed_2161, Child0Stable.expr_word_13, global_expr_2161.
 rewrite instance_40_word_10 instance_40_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2161.
Transparent Child0Stable.word_14 global_word_2162.
Lemma instance_40_word_14 v : Child0Stable.word_14 (instance_40_leaves v) = global_word_2162 v.
Proof. unfold Child0Stable.word_14, global_word_2162, Child0Stable.closed_word_14, global_closed_2162, Child0Stable.expr_word_14, global_expr_2162.
 rewrite instance_40_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2162.
Transparent Child0Stable.word_15 global_word_2163.
Lemma instance_40_word_15 v : Child0Stable.word_15 (instance_40_leaves v) = global_word_2163 v.
Proof. unfold Child0Stable.word_15, global_word_2163, Child0Stable.closed_word_15, global_closed_2163, Child0Stable.expr_word_15, global_expr_2163.
 rewrite instance_40_word_9 instance_40_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2163.
Transparent Child0Stable.word_16 global_word_2165.
Lemma instance_40_word_16 v : Child0Stable.word_16 (instance_40_leaves v) = global_word_2165 v.
Proof. unfold Child0Stable.word_16, global_word_2165, Child0Stable.closed_word_16, global_closed_2165, Child0Stable.expr_word_16, global_expr_2165.
 rewrite instance_40_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2165.
Transparent Child0Stable.word_17 global_word_2166.
Lemma instance_40_word_17 v : Child0Stable.word_17 (instance_40_leaves v) = global_word_2166 v.
Proof. unfold Child0Stable.word_17, global_word_2166, Child0Stable.closed_word_17, global_closed_2166, Child0Stable.expr_word_17, global_expr_2166.
 rewrite instance_40_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2166.
Transparent Child0Stable.word_18 global_word_2167.
Lemma instance_40_word_18 v : Child0Stable.word_18 (instance_40_leaves v) = global_word_2167 v.
Proof. unfold Child0Stable.word_18, global_word_2167, Child0Stable.closed_word_18, global_closed_2167, Child0Stable.expr_word_18, global_expr_2167.
 rewrite instance_40_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2167.
Definition instance_41_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2183 v
| 0, 1 => global_word_2179 v
| 0, 2 => global_word_1149 v
| 0, 3 => global_word_1152 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2183.
Lemma instance_41_word_0 v : Child0Stable.word_0 (instance_41_leaves v) = global_word_2183 v.
Proof. unfold Child0Stable.word_0, instance_41_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2183.
Transparent Child0Stable.word_1 global_word_2179.
Lemma instance_41_word_1 v : Child0Stable.word_1 (instance_41_leaves v) = global_word_2179 v.
Proof. unfold Child0Stable.word_1, instance_41_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2179.
Transparent Child0Stable.word_2 global_word_1149.
Lemma instance_41_word_2 v : Child0Stable.word_2 (instance_41_leaves v) = global_word_1149 v.
Proof. unfold Child0Stable.word_2, instance_41_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1149.
Transparent Child0Stable.word_3 global_word_1152.
Lemma instance_41_word_3 v : Child0Stable.word_3 (instance_41_leaves v) = global_word_1152 v.
Proof. unfold Child0Stable.word_3, instance_41_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1152.
Transparent Child0Stable.word_6 global_word_2169.
Lemma instance_41_word_6 v : Child0Stable.word_6 (instance_41_leaves v) = global_word_2169 v.
Proof. unfold Child0Stable.word_6, global_word_2169, Child0Stable.closed_word_6, global_closed_2169, Child0Stable.expr_word_6, global_expr_2169.
 rewrite instance_41_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2169.
Transparent Child0Stable.word_7 global_word_2170.
Lemma instance_41_word_7 v : Child0Stable.word_7 (instance_41_leaves v) = global_word_2170 v.
Proof. unfold Child0Stable.word_7, global_word_2170, Child0Stable.closed_word_7, global_closed_2170, Child0Stable.expr_word_7, global_expr_2170.
 rewrite instance_41_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2170.
Transparent Child0Stable.word_8 global_word_2171.
Lemma instance_41_word_8 v : Child0Stable.word_8 (instance_41_leaves v) = global_word_2171 v.
Proof. unfold Child0Stable.word_8, global_word_2171, Child0Stable.closed_word_8, global_closed_2171, Child0Stable.expr_word_8, global_expr_2171.
 rewrite instance_41_word_6 instance_41_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2171.
Transparent Child0Stable.word_9 global_word_2172.
Lemma instance_41_word_9 v : Child0Stable.word_9 (instance_41_leaves v) = global_word_2172 v.
Proof. unfold Child0Stable.word_9, global_word_2172, Child0Stable.closed_word_9, global_closed_2172, Child0Stable.expr_word_9, global_expr_2172.
 rewrite instance_41_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2172.
Transparent Child0Stable.word_19 global_word_1150.
Lemma instance_41_word_19 v : Child0Stable.word_19 (instance_41_leaves v) = global_word_1150 v.
Proof. unfold Child0Stable.word_19, global_word_1150, Child0Stable.closed_word_19, global_closed_1150, Child0Stable.expr_word_19, global_expr_1150.
 rewrite instance_41_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1150.
Transparent Child0Stable.word_20 global_word_1153.
Lemma instance_41_word_20 v : Child0Stable.word_20 (instance_41_leaves v) = global_word_1153 v.
Proof. unfold Child0Stable.word_20, global_word_1153, Child0Stable.closed_word_20, global_closed_1153, Child0Stable.expr_word_20, global_expr_1153.
 rewrite instance_41_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1153.
Transparent Child0Stable.word_21 global_word_1154.
Lemma instance_41_word_21 v : Child0Stable.word_21 (instance_41_leaves v) = global_word_1154 v.
Proof. unfold Child0Stable.word_21, global_word_1154, Child0Stable.closed_word_21, global_closed_1154, Child0Stable.expr_word_21, global_expr_1154.
 rewrite instance_41_word_19 instance_41_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1154.
Transparent Child0Stable.word_22 global_word_1155.
Lemma instance_41_word_22 v : Child0Stable.word_22 (instance_41_leaves v) = global_word_1155 v.
Proof. unfold Child0Stable.word_22, global_word_1155, Child0Stable.closed_word_22, global_closed_1155, Child0Stable.expr_word_22, global_expr_1155.
 rewrite instance_41_word_19 instance_41_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1155.
Transparent Child0Stable.word_23 global_word_1156.
Lemma instance_41_word_23 v : Child0Stable.word_23 (instance_41_leaves v) = global_word_1156 v.
Proof. unfold Child0Stable.word_23, global_word_1156, Child0Stable.closed_word_23, global_closed_1156, Child0Stable.expr_word_23, global_expr_1156.
 rewrite instance_41_word_21 instance_41_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1156.
Transparent Child0Stable.word_24 global_word_1157.
Lemma instance_41_word_24 v : Child0Stable.word_24 (instance_41_leaves v) = global_word_1157 v.
Proof. unfold Child0Stable.word_24, global_word_1157, Child0Stable.closed_word_24, global_closed_1157, Child0Stable.expr_word_24, global_expr_1157.
 rewrite instance_41_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1157.
Transparent Child0Stable.word_25 global_word_1158.
Lemma instance_41_word_25 v : Child0Stable.word_25 (instance_41_leaves v) = global_word_1158 v.
Proof. unfold Child0Stable.word_25, global_word_1158, Child0Stable.closed_word_25, global_closed_1158, Child0Stable.expr_word_25, global_expr_1158.
 rewrite instance_41_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1158.
Transparent Child0Stable.word_4 global_word_1159.
Lemma instance_41_word_4 v : Child0Stable.word_4 (instance_41_leaves v) = global_word_1159 v.
Proof. unfold Child0Stable.word_4, global_word_1159, Child0Stable.closed_word_4, global_closed_1159, Child0Stable.expr_word_4, global_expr_1159.
 rewrite instance_41_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1159.
Transparent Child0Stable.word_10 global_word_2173.
Lemma instance_41_word_10 v : Child0Stable.word_10 (instance_41_leaves v) = global_word_2173 v.
Proof. unfold Child0Stable.word_10, global_word_2173, Child0Stable.closed_word_10, global_closed_2173, Child0Stable.expr_word_10, global_expr_2173.
 rewrite instance_41_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2173.
Transparent Child0Stable.word_26 global_word_1162.
Lemma instance_41_word_26 v : Child0Stable.word_26 (instance_41_leaves v) = global_word_1162 v.
Proof. unfold Child0Stable.word_26, global_word_1162, Child0Stable.closed_word_26, global_closed_1162, Child0Stable.expr_word_26, global_expr_1162.
 rewrite instance_41_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1162.
Transparent Child0Stable.word_5 global_word_1163.
Lemma instance_41_word_5 v : Child0Stable.word_5 (instance_41_leaves v) = global_word_1163 v.
Proof. unfold Child0Stable.word_5, global_word_1163, Child0Stable.closed_word_5, global_closed_1163, Child0Stable.expr_word_5, global_expr_1163.
 rewrite instance_41_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1163.
Transparent Child0Stable.word_11 global_word_2174.
Lemma instance_41_word_11 v : Child0Stable.word_11 (instance_41_leaves v) = global_word_2174 v.
Proof. unfold Child0Stable.word_11, global_word_2174, Child0Stable.closed_word_11, global_closed_2174, Child0Stable.expr_word_11, global_expr_2174.
 rewrite instance_41_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2174.
Transparent Child0Stable.word_12 global_word_2175.
Lemma instance_41_word_12 v : Child0Stable.word_12 (instance_41_leaves v) = global_word_2175 v.
Proof. unfold Child0Stable.word_12, global_word_2175, Child0Stable.closed_word_12, global_closed_2175, Child0Stable.expr_word_12, global_expr_2175.
 rewrite instance_41_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2175.
Transparent Child0Stable.word_13 global_word_2176.
Lemma instance_41_word_13 v : Child0Stable.word_13 (instance_41_leaves v) = global_word_2176 v.
Proof. unfold Child0Stable.word_13, global_word_2176, Child0Stable.closed_word_13, global_closed_2176, Child0Stable.expr_word_13, global_expr_2176.
 rewrite instance_41_word_10 instance_41_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2176.
Transparent Child0Stable.word_14 global_word_2177.
Lemma instance_41_word_14 v : Child0Stable.word_14 (instance_41_leaves v) = global_word_2177 v.
Proof. unfold Child0Stable.word_14, global_word_2177, Child0Stable.closed_word_14, global_closed_2177, Child0Stable.expr_word_14, global_expr_2177.
 rewrite instance_41_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2177.
Transparent Child0Stable.word_15 global_word_2178.
Lemma instance_41_word_15 v : Child0Stable.word_15 (instance_41_leaves v) = global_word_2178 v.
Proof. unfold Child0Stable.word_15, global_word_2178, Child0Stable.closed_word_15, global_closed_2178, Child0Stable.expr_word_15, global_expr_2178.
 rewrite instance_41_word_9 instance_41_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2178.
Transparent Child0Stable.word_16 global_word_2180.
Lemma instance_41_word_16 v : Child0Stable.word_16 (instance_41_leaves v) = global_word_2180 v.
Proof. unfold Child0Stable.word_16, global_word_2180, Child0Stable.closed_word_16, global_closed_2180, Child0Stable.expr_word_16, global_expr_2180.
 rewrite instance_41_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2180.
Transparent Child0Stable.word_17 global_word_2181.
Lemma instance_41_word_17 v : Child0Stable.word_17 (instance_41_leaves v) = global_word_2181 v.
Proof. unfold Child0Stable.word_17, global_word_2181, Child0Stable.closed_word_17, global_closed_2181, Child0Stable.expr_word_17, global_expr_2181.
 rewrite instance_41_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2181.
Transparent Child0Stable.word_18 global_word_2182.
Lemma instance_41_word_18 v : Child0Stable.word_18 (instance_41_leaves v) = global_word_2182 v.
Proof. unfold Child0Stable.word_18, global_word_2182, Child0Stable.closed_word_18, global_closed_2182, Child0Stable.expr_word_18, global_expr_2182.
 rewrite instance_41_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2182.
Definition instance_42_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2198 v
| 0, 1 => global_word_2194 v
| 0, 2 => global_word_1167 v
| 0, 3 => global_word_1170 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2198.
Lemma instance_42_word_0 v : Child0Stable.word_0 (instance_42_leaves v) = global_word_2198 v.
Proof. unfold Child0Stable.word_0, instance_42_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2198.
Transparent Child0Stable.word_1 global_word_2194.
Lemma instance_42_word_1 v : Child0Stable.word_1 (instance_42_leaves v) = global_word_2194 v.
Proof. unfold Child0Stable.word_1, instance_42_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2194.
Transparent Child0Stable.word_2 global_word_1167.
Lemma instance_42_word_2 v : Child0Stable.word_2 (instance_42_leaves v) = global_word_1167 v.
Proof. unfold Child0Stable.word_2, instance_42_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1167.
Transparent Child0Stable.word_3 global_word_1170.
Lemma instance_42_word_3 v : Child0Stable.word_3 (instance_42_leaves v) = global_word_1170 v.
Proof. unfold Child0Stable.word_3, instance_42_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1170.
Transparent Child0Stable.word_6 global_word_2184.
Lemma instance_42_word_6 v : Child0Stable.word_6 (instance_42_leaves v) = global_word_2184 v.
Proof. unfold Child0Stable.word_6, global_word_2184, Child0Stable.closed_word_6, global_closed_2184, Child0Stable.expr_word_6, global_expr_2184.
 rewrite instance_42_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2184.
Transparent Child0Stable.word_7 global_word_2185.
Lemma instance_42_word_7 v : Child0Stable.word_7 (instance_42_leaves v) = global_word_2185 v.
Proof. unfold Child0Stable.word_7, global_word_2185, Child0Stable.closed_word_7, global_closed_2185, Child0Stable.expr_word_7, global_expr_2185.
 rewrite instance_42_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2185.
Transparent Child0Stable.word_8 global_word_2186.
Lemma instance_42_word_8 v : Child0Stable.word_8 (instance_42_leaves v) = global_word_2186 v.
Proof. unfold Child0Stable.word_8, global_word_2186, Child0Stable.closed_word_8, global_closed_2186, Child0Stable.expr_word_8, global_expr_2186.
 rewrite instance_42_word_6 instance_42_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2186.
Transparent Child0Stable.word_9 global_word_2187.
Lemma instance_42_word_9 v : Child0Stable.word_9 (instance_42_leaves v) = global_word_2187 v.
Proof. unfold Child0Stable.word_9, global_word_2187, Child0Stable.closed_word_9, global_closed_2187, Child0Stable.expr_word_9, global_expr_2187.
 rewrite instance_42_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2187.
Transparent Child0Stable.word_19 global_word_1168.
Lemma instance_42_word_19 v : Child0Stable.word_19 (instance_42_leaves v) = global_word_1168 v.
Proof. unfold Child0Stable.word_19, global_word_1168, Child0Stable.closed_word_19, global_closed_1168, Child0Stable.expr_word_19, global_expr_1168.
 rewrite instance_42_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1168.
Transparent Child0Stable.word_20 global_word_1171.
Lemma instance_42_word_20 v : Child0Stable.word_20 (instance_42_leaves v) = global_word_1171 v.
Proof. unfold Child0Stable.word_20, global_word_1171, Child0Stable.closed_word_20, global_closed_1171, Child0Stable.expr_word_20, global_expr_1171.
 rewrite instance_42_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1171.
Transparent Child0Stable.word_21 global_word_1172.
Lemma instance_42_word_21 v : Child0Stable.word_21 (instance_42_leaves v) = global_word_1172 v.
Proof. unfold Child0Stable.word_21, global_word_1172, Child0Stable.closed_word_21, global_closed_1172, Child0Stable.expr_word_21, global_expr_1172.
 rewrite instance_42_word_19 instance_42_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1172.
Transparent Child0Stable.word_22 global_word_1173.
Lemma instance_42_word_22 v : Child0Stable.word_22 (instance_42_leaves v) = global_word_1173 v.
Proof. unfold Child0Stable.word_22, global_word_1173, Child0Stable.closed_word_22, global_closed_1173, Child0Stable.expr_word_22, global_expr_1173.
 rewrite instance_42_word_19 instance_42_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1173.
Transparent Child0Stable.word_23 global_word_1174.
Lemma instance_42_word_23 v : Child0Stable.word_23 (instance_42_leaves v) = global_word_1174 v.
Proof. unfold Child0Stable.word_23, global_word_1174, Child0Stable.closed_word_23, global_closed_1174, Child0Stable.expr_word_23, global_expr_1174.
 rewrite instance_42_word_21 instance_42_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1174.
Transparent Child0Stable.word_24 global_word_1175.
Lemma instance_42_word_24 v : Child0Stable.word_24 (instance_42_leaves v) = global_word_1175 v.
Proof. unfold Child0Stable.word_24, global_word_1175, Child0Stable.closed_word_24, global_closed_1175, Child0Stable.expr_word_24, global_expr_1175.
 rewrite instance_42_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1175.
Transparent Child0Stable.word_25 global_word_1176.
Lemma instance_42_word_25 v : Child0Stable.word_25 (instance_42_leaves v) = global_word_1176 v.
Proof. unfold Child0Stable.word_25, global_word_1176, Child0Stable.closed_word_25, global_closed_1176, Child0Stable.expr_word_25, global_expr_1176.
 rewrite instance_42_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1176.
Transparent Child0Stable.word_4 global_word_1177.
Lemma instance_42_word_4 v : Child0Stable.word_4 (instance_42_leaves v) = global_word_1177 v.
Proof. unfold Child0Stable.word_4, global_word_1177, Child0Stable.closed_word_4, global_closed_1177, Child0Stable.expr_word_4, global_expr_1177.
 rewrite instance_42_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1177.
Transparent Child0Stable.word_10 global_word_2188.
Lemma instance_42_word_10 v : Child0Stable.word_10 (instance_42_leaves v) = global_word_2188 v.
Proof. unfold Child0Stable.word_10, global_word_2188, Child0Stable.closed_word_10, global_closed_2188, Child0Stable.expr_word_10, global_expr_2188.
 rewrite instance_42_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2188.
Transparent Child0Stable.word_26 global_word_1180.
Lemma instance_42_word_26 v : Child0Stable.word_26 (instance_42_leaves v) = global_word_1180 v.
Proof. unfold Child0Stable.word_26, global_word_1180, Child0Stable.closed_word_26, global_closed_1180, Child0Stable.expr_word_26, global_expr_1180.
 rewrite instance_42_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1180.
Transparent Child0Stable.word_5 global_word_1181.
Lemma instance_42_word_5 v : Child0Stable.word_5 (instance_42_leaves v) = global_word_1181 v.
Proof. unfold Child0Stable.word_5, global_word_1181, Child0Stable.closed_word_5, global_closed_1181, Child0Stable.expr_word_5, global_expr_1181.
 rewrite instance_42_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1181.
Transparent Child0Stable.word_11 global_word_2189.
Lemma instance_42_word_11 v : Child0Stable.word_11 (instance_42_leaves v) = global_word_2189 v.
Proof. unfold Child0Stable.word_11, global_word_2189, Child0Stable.closed_word_11, global_closed_2189, Child0Stable.expr_word_11, global_expr_2189.
 rewrite instance_42_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2189.
Transparent Child0Stable.word_12 global_word_2190.
Lemma instance_42_word_12 v : Child0Stable.word_12 (instance_42_leaves v) = global_word_2190 v.
Proof. unfold Child0Stable.word_12, global_word_2190, Child0Stable.closed_word_12, global_closed_2190, Child0Stable.expr_word_12, global_expr_2190.
 rewrite instance_42_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2190.
Transparent Child0Stable.word_13 global_word_2191.
Lemma instance_42_word_13 v : Child0Stable.word_13 (instance_42_leaves v) = global_word_2191 v.
Proof. unfold Child0Stable.word_13, global_word_2191, Child0Stable.closed_word_13, global_closed_2191, Child0Stable.expr_word_13, global_expr_2191.
 rewrite instance_42_word_10 instance_42_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2191.
Transparent Child0Stable.word_14 global_word_2192.
Lemma instance_42_word_14 v : Child0Stable.word_14 (instance_42_leaves v) = global_word_2192 v.
Proof. unfold Child0Stable.word_14, global_word_2192, Child0Stable.closed_word_14, global_closed_2192, Child0Stable.expr_word_14, global_expr_2192.
 rewrite instance_42_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2192.
Transparent Child0Stable.word_15 global_word_2193.
Lemma instance_42_word_15 v : Child0Stable.word_15 (instance_42_leaves v) = global_word_2193 v.
Proof. unfold Child0Stable.word_15, global_word_2193, Child0Stable.closed_word_15, global_closed_2193, Child0Stable.expr_word_15, global_expr_2193.
 rewrite instance_42_word_9 instance_42_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2193.
Transparent Child0Stable.word_16 global_word_2195.
Lemma instance_42_word_16 v : Child0Stable.word_16 (instance_42_leaves v) = global_word_2195 v.
Proof. unfold Child0Stable.word_16, global_word_2195, Child0Stable.closed_word_16, global_closed_2195, Child0Stable.expr_word_16, global_expr_2195.
 rewrite instance_42_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2195.
Transparent Child0Stable.word_17 global_word_2196.
Lemma instance_42_word_17 v : Child0Stable.word_17 (instance_42_leaves v) = global_word_2196 v.
Proof. unfold Child0Stable.word_17, global_word_2196, Child0Stable.closed_word_17, global_closed_2196, Child0Stable.expr_word_17, global_expr_2196.
 rewrite instance_42_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2196.
Transparent Child0Stable.word_18 global_word_2197.
Lemma instance_42_word_18 v : Child0Stable.word_18 (instance_42_leaves v) = global_word_2197 v.
Proof. unfold Child0Stable.word_18, global_word_2197, Child0Stable.closed_word_18, global_closed_2197, Child0Stable.expr_word_18, global_expr_2197.
 rewrite instance_42_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2197.
Definition instance_43_leaves (v:global_leaves) : Child1Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2216 v
| 0, 1 => global_word_2212 v
| 0, 2 => global_word_1188 v
| 0, 3 => global_word_1191 v
| 0, 4 => global_word_1185 v
| _,_ => [::] end.
Transparent Child1Stable.word_0 global_word_2216.
Lemma instance_43_word_0 v : Child1Stable.word_0 (instance_43_leaves v) = global_word_2216 v.
Proof. unfold Child1Stable.word_0, instance_43_leaves. reflexivity. Qed.
Opaque Child1Stable.word_0 global_word_2216.
Transparent Child1Stable.word_1 global_word_2212.
Lemma instance_43_word_1 v : Child1Stable.word_1 (instance_43_leaves v) = global_word_2212 v.
Proof. unfold Child1Stable.word_1, instance_43_leaves. reflexivity. Qed.
Opaque Child1Stable.word_1 global_word_2212.
Transparent Child1Stable.word_2 global_word_1188.
Lemma instance_43_word_2 v : Child1Stable.word_2 (instance_43_leaves v) = global_word_1188 v.
Proof. unfold Child1Stable.word_2, instance_43_leaves. reflexivity. Qed.
Opaque Child1Stable.word_2 global_word_1188.
Transparent Child1Stable.word_3 global_word_1191.
Lemma instance_43_word_3 v : Child1Stable.word_3 (instance_43_leaves v) = global_word_1191 v.
Proof. unfold Child1Stable.word_3, instance_43_leaves. reflexivity. Qed.
Opaque Child1Stable.word_3 global_word_1191.
Transparent Child1Stable.word_4 global_word_1185.
Lemma instance_43_word_4 v : Child1Stable.word_4 (instance_43_leaves v) = global_word_1185 v.
Proof. unfold Child1Stable.word_4, instance_43_leaves. reflexivity. Qed.
Opaque Child1Stable.word_4 global_word_1185.
Transparent Child1Stable.word_7 global_word_2199.
Lemma instance_43_word_7 v : Child1Stable.word_7 (instance_43_leaves v) = global_word_2199 v.
Proof. unfold Child1Stable.word_7, global_word_2199, Child1Stable.closed_word_7, global_closed_2199, Child1Stable.expr_word_7, global_expr_2199.
 rewrite instance_43_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_7 global_word_2199.
Transparent Child1Stable.word_8 global_word_2200.
Lemma instance_43_word_8 v : Child1Stable.word_8 (instance_43_leaves v) = global_word_2200 v.
Proof. unfold Child1Stable.word_8, global_word_2200, Child1Stable.closed_word_8, global_closed_2200, Child1Stable.expr_word_8, global_expr_2200.
 rewrite instance_43_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_8 global_word_2200.
Transparent Child1Stable.word_9 global_word_2201.
Lemma instance_43_word_9 v : Child1Stable.word_9 (instance_43_leaves v) = global_word_2201 v.
Proof. unfold Child1Stable.word_9, global_word_2201, Child1Stable.closed_word_9, global_closed_2201, Child1Stable.expr_word_9, global_expr_2201.
 rewrite instance_43_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_9 global_word_2201.
Transparent Child1Stable.word_10 global_word_2202.
Lemma instance_43_word_10 v : Child1Stable.word_10 (instance_43_leaves v) = global_word_2202 v.
Proof. unfold Child1Stable.word_10, global_word_2202, Child1Stable.closed_word_10, global_closed_2202, Child1Stable.expr_word_10, global_expr_2202.
 rewrite instance_43_word_7 instance_43_word_8.
 reflexivity. Qed. Opaque Child1Stable.word_10 global_word_2202.
Transparent Child1Stable.word_11 global_word_2203.
Lemma instance_43_word_11 v : Child1Stable.word_11 (instance_43_leaves v) = global_word_2203 v.
Proof. unfold Child1Stable.word_11, global_word_2203, Child1Stable.closed_word_11, global_closed_2203, Child1Stable.expr_word_11, global_expr_2203.
 rewrite instance_43_word_10.
 reflexivity. Qed. Opaque Child1Stable.word_11 global_word_2203.
Transparent Child1Stable.word_12 global_word_2204.
Lemma instance_43_word_12 v : Child1Stable.word_12 (instance_43_leaves v) = global_word_2204 v.
Proof. unfold Child1Stable.word_12, global_word_2204, Child1Stable.closed_word_12, global_closed_2204, Child1Stable.expr_word_12, global_expr_2204.
 rewrite instance_43_word_9 instance_43_word_11.
 reflexivity. Qed. Opaque Child1Stable.word_12 global_word_2204.
Transparent Child1Stable.word_13 global_word_2205.
Lemma instance_43_word_13 v : Child1Stable.word_13 (instance_43_leaves v) = global_word_2205 v.
Proof. unfold Child1Stable.word_13, global_word_2205, Child1Stable.closed_word_13, global_closed_2205, Child1Stable.expr_word_13, global_expr_2205.
 rewrite instance_43_word_12.
 reflexivity. Qed. Opaque Child1Stable.word_13 global_word_2205.
Transparent Child1Stable.word_25 global_word_1186.
Lemma instance_43_word_25 v : Child1Stable.word_25 (instance_43_leaves v) = global_word_1186 v.
Proof. unfold Child1Stable.word_25, global_word_1186, Child1Stable.closed_word_25, global_closed_1186, Child1Stable.expr_word_25, global_expr_1186.
 rewrite instance_43_word_4.
 reflexivity. Qed. Opaque Child1Stable.word_25 global_word_1186.
Transparent Child1Stable.word_23 global_word_1189.
Lemma instance_43_word_23 v : Child1Stable.word_23 (instance_43_leaves v) = global_word_1189 v.
Proof. unfold Child1Stable.word_23, global_word_1189, Child1Stable.closed_word_23, global_closed_1189, Child1Stable.expr_word_23, global_expr_1189.
 rewrite instance_43_word_2.
 reflexivity. Qed. Opaque Child1Stable.word_23 global_word_1189.
Transparent Child1Stable.word_24 global_word_1192.
Lemma instance_43_word_24 v : Child1Stable.word_24 (instance_43_leaves v) = global_word_1192 v.
Proof. unfold Child1Stable.word_24, global_word_1192, Child1Stable.closed_word_24, global_closed_1192, Child1Stable.expr_word_24, global_expr_1192.
 rewrite instance_43_word_3.
 reflexivity. Qed. Opaque Child1Stable.word_24 global_word_1192.
Transparent Child1Stable.word_26 global_word_1193.
Lemma instance_43_word_26 v : Child1Stable.word_26 (instance_43_leaves v) = global_word_1193 v.
Proof. unfold Child1Stable.word_26, global_word_1193, Child1Stable.closed_word_26, global_closed_1193, Child1Stable.expr_word_26, global_expr_1193.
 rewrite instance_43_word_23 instance_43_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_26 global_word_1193.
Transparent Child1Stable.word_28 global_word_1194.
Lemma instance_43_word_28 v : Child1Stable.word_28 (instance_43_leaves v) = global_word_1194 v.
Proof. unfold Child1Stable.word_28, global_word_1194, Child1Stable.closed_word_28, global_closed_1194, Child1Stable.expr_word_28, global_expr_1194.
 rewrite instance_43_word_25 instance_43_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_28 global_word_1194.
Transparent Child1Stable.word_27 global_word_1195.
Lemma instance_43_word_27 v : Child1Stable.word_27 (instance_43_leaves v) = global_word_1195 v.
Proof. unfold Child1Stable.word_27, global_word_1195, Child1Stable.closed_word_27, global_closed_1195, Child1Stable.expr_word_27, global_expr_1195.
 rewrite instance_43_word_23 instance_43_word_24.
 reflexivity. Qed. Opaque Child1Stable.word_27 global_word_1195.
Transparent Child1Stable.word_29 global_word_1196.
Lemma instance_43_word_29 v : Child1Stable.word_29 (instance_43_leaves v) = global_word_1196 v.
Proof. unfold Child1Stable.word_29, global_word_1196, Child1Stable.closed_word_29, global_closed_1196, Child1Stable.expr_word_29, global_expr_1196.
 rewrite instance_43_word_25 instance_43_word_26.
 reflexivity. Qed. Opaque Child1Stable.word_29 global_word_1196.
Transparent Child1Stable.word_30 global_word_1197.
Lemma instance_43_word_30 v : Child1Stable.word_30 (instance_43_leaves v) = global_word_1197 v.
Proof. unfold Child1Stable.word_30, global_word_1197, Child1Stable.closed_word_30, global_closed_1197, Child1Stable.expr_word_30, global_expr_1197.
 rewrite instance_43_word_27 instance_43_word_29.
 reflexivity. Qed. Opaque Child1Stable.word_30 global_word_1197.
Transparent Child1Stable.word_31 global_word_1198.
Lemma instance_43_word_31 v : Child1Stable.word_31 (instance_43_leaves v) = global_word_1198 v.
Proof. unfold Child1Stable.word_31, global_word_1198, Child1Stable.closed_word_31, global_closed_1198, Child1Stable.expr_word_31, global_expr_1198.
 rewrite instance_43_word_28 instance_43_word_30.
 reflexivity. Qed. Opaque Child1Stable.word_31 global_word_1198.
Transparent Child1Stable.word_32 global_word_1199.
Lemma instance_43_word_32 v : Child1Stable.word_32 (instance_43_leaves v) = global_word_1199 v.
Proof. unfold Child1Stable.word_32, global_word_1199, Child1Stable.closed_word_32, global_closed_1199, Child1Stable.expr_word_32, global_expr_1199.
 rewrite instance_43_word_31.
 reflexivity. Qed. Opaque Child1Stable.word_32 global_word_1199.
Transparent Child1Stable.word_33 global_word_1200.
Lemma instance_43_word_33 v : Child1Stable.word_33 (instance_43_leaves v) = global_word_1200 v.
Proof. unfold Child1Stable.word_33, global_word_1200, Child1Stable.closed_word_33, global_closed_1200, Child1Stable.expr_word_33, global_expr_1200.
 rewrite instance_43_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_33 global_word_1200.
Transparent Child1Stable.word_5 global_word_1201.
Lemma instance_43_word_5 v : Child1Stable.word_5 (instance_43_leaves v) = global_word_1201 v.
Proof. unfold Child1Stable.word_5, global_word_1201, Child1Stable.closed_word_5, global_closed_1201, Child1Stable.expr_word_5, global_expr_1201.
 rewrite instance_43_word_33.
 reflexivity. Qed. Opaque Child1Stable.word_5 global_word_1201.
Transparent Child1Stable.word_14 global_word_2206.
Lemma instance_43_word_14 v : Child1Stable.word_14 (instance_43_leaves v) = global_word_2206 v.
Proof. unfold Child1Stable.word_14, global_word_2206, Child1Stable.closed_word_14, global_closed_2206, Child1Stable.expr_word_14, global_expr_2206.
 rewrite instance_43_word_5.
 reflexivity. Qed. Opaque Child1Stable.word_14 global_word_2206.
Transparent Child1Stable.word_34 global_word_1204.
Lemma instance_43_word_34 v : Child1Stable.word_34 (instance_43_leaves v) = global_word_1204 v.
Proof. unfold Child1Stable.word_34, global_word_1204, Child1Stable.closed_word_34, global_closed_1204, Child1Stable.expr_word_34, global_expr_1204.
 rewrite instance_43_word_32.
 reflexivity. Qed. Opaque Child1Stable.word_34 global_word_1204.
Transparent Child1Stable.word_6 global_word_1205.
Lemma instance_43_word_6 v : Child1Stable.word_6 (instance_43_leaves v) = global_word_1205 v.
Proof. unfold Child1Stable.word_6, global_word_1205, Child1Stable.closed_word_6, global_closed_1205, Child1Stable.expr_word_6, global_expr_1205.
 rewrite instance_43_word_34.
 reflexivity. Qed. Opaque Child1Stable.word_6 global_word_1205.
Transparent Child1Stable.word_15 global_word_2207.
Lemma instance_43_word_15 v : Child1Stable.word_15 (instance_43_leaves v) = global_word_2207 v.
Proof. unfold Child1Stable.word_15, global_word_2207, Child1Stable.closed_word_15, global_closed_2207, Child1Stable.expr_word_15, global_expr_2207.
 rewrite instance_43_word_6.
 reflexivity. Qed. Opaque Child1Stable.word_15 global_word_2207.
Transparent Child1Stable.word_16 global_word_2208.
Lemma instance_43_word_16 v : Child1Stable.word_16 (instance_43_leaves v) = global_word_2208 v.
Proof. unfold Child1Stable.word_16, global_word_2208, Child1Stable.closed_word_16, global_closed_2208, Child1Stable.expr_word_16, global_expr_2208.
 rewrite instance_43_word_15.
 reflexivity. Qed. Opaque Child1Stable.word_16 global_word_2208.
Transparent Child1Stable.word_17 global_word_2209.
Lemma instance_43_word_17 v : Child1Stable.word_17 (instance_43_leaves v) = global_word_2209 v.
Proof. unfold Child1Stable.word_17, global_word_2209, Child1Stable.closed_word_17, global_closed_2209, Child1Stable.expr_word_17, global_expr_2209.
 rewrite instance_43_word_14 instance_43_word_16.
 reflexivity. Qed. Opaque Child1Stable.word_17 global_word_2209.
Transparent Child1Stable.word_18 global_word_2210.
Lemma instance_43_word_18 v : Child1Stable.word_18 (instance_43_leaves v) = global_word_2210 v.
Proof. unfold Child1Stable.word_18, global_word_2210, Child1Stable.closed_word_18, global_closed_2210, Child1Stable.expr_word_18, global_expr_2210.
 rewrite instance_43_word_17.
 reflexivity. Qed. Opaque Child1Stable.word_18 global_word_2210.
Transparent Child1Stable.word_19 global_word_2211.
Lemma instance_43_word_19 v : Child1Stable.word_19 (instance_43_leaves v) = global_word_2211 v.
Proof. unfold Child1Stable.word_19, global_word_2211, Child1Stable.closed_word_19, global_closed_2211, Child1Stable.expr_word_19, global_expr_2211.
 rewrite instance_43_word_13 instance_43_word_18.
 reflexivity. Qed. Opaque Child1Stable.word_19 global_word_2211.
Transparent Child1Stable.word_20 global_word_2213.
Lemma instance_43_word_20 v : Child1Stable.word_20 (instance_43_leaves v) = global_word_2213 v.
Proof. unfold Child1Stable.word_20, global_word_2213, Child1Stable.closed_word_20, global_closed_2213, Child1Stable.expr_word_20, global_expr_2213.
 rewrite instance_43_word_1.
 reflexivity. Qed. Opaque Child1Stable.word_20 global_word_2213.
Transparent Child1Stable.word_21 global_word_2214.
Lemma instance_43_word_21 v : Child1Stable.word_21 (instance_43_leaves v) = global_word_2214 v.
Proof. unfold Child1Stable.word_21, global_word_2214, Child1Stable.closed_word_21, global_closed_2214, Child1Stable.expr_word_21, global_expr_2214.
 rewrite instance_43_word_20.
 reflexivity. Qed. Opaque Child1Stable.word_21 global_word_2214.
Transparent Child1Stable.word_22 global_word_2215.
Lemma instance_43_word_22 v : Child1Stable.word_22 (instance_43_leaves v) = global_word_2215 v.
Proof. unfold Child1Stable.word_22, global_word_2215, Child1Stable.closed_word_22, global_closed_2215, Child1Stable.expr_word_22, global_expr_2215.
 rewrite instance_43_word_19.
 reflexivity. Qed. Opaque Child1Stable.word_22 global_word_2215.
Definition instance_44_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2231 v
| 0, 1 => global_word_2227 v
| 0, 2 => global_word_1209 v
| 0, 3 => global_word_1212 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2231.
Lemma instance_44_word_0 v : Child0Stable.word_0 (instance_44_leaves v) = global_word_2231 v.
Proof. unfold Child0Stable.word_0, instance_44_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2231.
Transparent Child0Stable.word_1 global_word_2227.
Lemma instance_44_word_1 v : Child0Stable.word_1 (instance_44_leaves v) = global_word_2227 v.
Proof. unfold Child0Stable.word_1, instance_44_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2227.
Transparent Child0Stable.word_2 global_word_1209.
Lemma instance_44_word_2 v : Child0Stable.word_2 (instance_44_leaves v) = global_word_1209 v.
Proof. unfold Child0Stable.word_2, instance_44_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1209.
Transparent Child0Stable.word_3 global_word_1212.
Lemma instance_44_word_3 v : Child0Stable.word_3 (instance_44_leaves v) = global_word_1212 v.
Proof. unfold Child0Stable.word_3, instance_44_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1212.
Transparent Child0Stable.word_6 global_word_2217.
Lemma instance_44_word_6 v : Child0Stable.word_6 (instance_44_leaves v) = global_word_2217 v.
Proof. unfold Child0Stable.word_6, global_word_2217, Child0Stable.closed_word_6, global_closed_2217, Child0Stable.expr_word_6, global_expr_2217.
 rewrite instance_44_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2217.
Transparent Child0Stable.word_7 global_word_2218.
Lemma instance_44_word_7 v : Child0Stable.word_7 (instance_44_leaves v) = global_word_2218 v.
Proof. unfold Child0Stable.word_7, global_word_2218, Child0Stable.closed_word_7, global_closed_2218, Child0Stable.expr_word_7, global_expr_2218.
 rewrite instance_44_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2218.
Transparent Child0Stable.word_8 global_word_2219.
Lemma instance_44_word_8 v : Child0Stable.word_8 (instance_44_leaves v) = global_word_2219 v.
Proof. unfold Child0Stable.word_8, global_word_2219, Child0Stable.closed_word_8, global_closed_2219, Child0Stable.expr_word_8, global_expr_2219.
 rewrite instance_44_word_6 instance_44_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2219.
Transparent Child0Stable.word_9 global_word_2220.
Lemma instance_44_word_9 v : Child0Stable.word_9 (instance_44_leaves v) = global_word_2220 v.
Proof. unfold Child0Stable.word_9, global_word_2220, Child0Stable.closed_word_9, global_closed_2220, Child0Stable.expr_word_9, global_expr_2220.
 rewrite instance_44_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2220.
Transparent Child0Stable.word_19 global_word_1210.
Lemma instance_44_word_19 v : Child0Stable.word_19 (instance_44_leaves v) = global_word_1210 v.
Proof. unfold Child0Stable.word_19, global_word_1210, Child0Stable.closed_word_19, global_closed_1210, Child0Stable.expr_word_19, global_expr_1210.
 rewrite instance_44_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1210.
Transparent Child0Stable.word_20 global_word_1213.
Lemma instance_44_word_20 v : Child0Stable.word_20 (instance_44_leaves v) = global_word_1213 v.
Proof. unfold Child0Stable.word_20, global_word_1213, Child0Stable.closed_word_20, global_closed_1213, Child0Stable.expr_word_20, global_expr_1213.
 rewrite instance_44_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1213.
Transparent Child0Stable.word_21 global_word_1214.
Lemma instance_44_word_21 v : Child0Stable.word_21 (instance_44_leaves v) = global_word_1214 v.
Proof. unfold Child0Stable.word_21, global_word_1214, Child0Stable.closed_word_21, global_closed_1214, Child0Stable.expr_word_21, global_expr_1214.
 rewrite instance_44_word_19 instance_44_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1214.
Transparent Child0Stable.word_22 global_word_1215.
Lemma instance_44_word_22 v : Child0Stable.word_22 (instance_44_leaves v) = global_word_1215 v.
Proof. unfold Child0Stable.word_22, global_word_1215, Child0Stable.closed_word_22, global_closed_1215, Child0Stable.expr_word_22, global_expr_1215.
 rewrite instance_44_word_19 instance_44_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1215.
Transparent Child0Stable.word_23 global_word_1216.
Lemma instance_44_word_23 v : Child0Stable.word_23 (instance_44_leaves v) = global_word_1216 v.
Proof. unfold Child0Stable.word_23, global_word_1216, Child0Stable.closed_word_23, global_closed_1216, Child0Stable.expr_word_23, global_expr_1216.
 rewrite instance_44_word_21 instance_44_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1216.
Transparent Child0Stable.word_24 global_word_1217.
Lemma instance_44_word_24 v : Child0Stable.word_24 (instance_44_leaves v) = global_word_1217 v.
Proof. unfold Child0Stable.word_24, global_word_1217, Child0Stable.closed_word_24, global_closed_1217, Child0Stable.expr_word_24, global_expr_1217.
 rewrite instance_44_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1217.
Transparent Child0Stable.word_25 global_word_1218.
Lemma instance_44_word_25 v : Child0Stable.word_25 (instance_44_leaves v) = global_word_1218 v.
Proof. unfold Child0Stable.word_25, global_word_1218, Child0Stable.closed_word_25, global_closed_1218, Child0Stable.expr_word_25, global_expr_1218.
 rewrite instance_44_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1218.
Transparent Child0Stable.word_4 global_word_1219.
Lemma instance_44_word_4 v : Child0Stable.word_4 (instance_44_leaves v) = global_word_1219 v.
Proof. unfold Child0Stable.word_4, global_word_1219, Child0Stable.closed_word_4, global_closed_1219, Child0Stable.expr_word_4, global_expr_1219.
 rewrite instance_44_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1219.
Transparent Child0Stable.word_10 global_word_2221.
Lemma instance_44_word_10 v : Child0Stable.word_10 (instance_44_leaves v) = global_word_2221 v.
Proof. unfold Child0Stable.word_10, global_word_2221, Child0Stable.closed_word_10, global_closed_2221, Child0Stable.expr_word_10, global_expr_2221.
 rewrite instance_44_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2221.
Transparent Child0Stable.word_26 global_word_1222.
Lemma instance_44_word_26 v : Child0Stable.word_26 (instance_44_leaves v) = global_word_1222 v.
Proof. unfold Child0Stable.word_26, global_word_1222, Child0Stable.closed_word_26, global_closed_1222, Child0Stable.expr_word_26, global_expr_1222.
 rewrite instance_44_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1222.
Transparent Child0Stable.word_5 global_word_1223.
Lemma instance_44_word_5 v : Child0Stable.word_5 (instance_44_leaves v) = global_word_1223 v.
Proof. unfold Child0Stable.word_5, global_word_1223, Child0Stable.closed_word_5, global_closed_1223, Child0Stable.expr_word_5, global_expr_1223.
 rewrite instance_44_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1223.
Transparent Child0Stable.word_11 global_word_2222.
Lemma instance_44_word_11 v : Child0Stable.word_11 (instance_44_leaves v) = global_word_2222 v.
Proof. unfold Child0Stable.word_11, global_word_2222, Child0Stable.closed_word_11, global_closed_2222, Child0Stable.expr_word_11, global_expr_2222.
 rewrite instance_44_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2222.
Transparent Child0Stable.word_12 global_word_2223.
Lemma instance_44_word_12 v : Child0Stable.word_12 (instance_44_leaves v) = global_word_2223 v.
Proof. unfold Child0Stable.word_12, global_word_2223, Child0Stable.closed_word_12, global_closed_2223, Child0Stable.expr_word_12, global_expr_2223.
 rewrite instance_44_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2223.
Transparent Child0Stable.word_13 global_word_2224.
Lemma instance_44_word_13 v : Child0Stable.word_13 (instance_44_leaves v) = global_word_2224 v.
Proof. unfold Child0Stable.word_13, global_word_2224, Child0Stable.closed_word_13, global_closed_2224, Child0Stable.expr_word_13, global_expr_2224.
 rewrite instance_44_word_10 instance_44_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2224.
Transparent Child0Stable.word_14 global_word_2225.
Lemma instance_44_word_14 v : Child0Stable.word_14 (instance_44_leaves v) = global_word_2225 v.
Proof. unfold Child0Stable.word_14, global_word_2225, Child0Stable.closed_word_14, global_closed_2225, Child0Stable.expr_word_14, global_expr_2225.
 rewrite instance_44_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2225.
Transparent Child0Stable.word_15 global_word_2226.
Lemma instance_44_word_15 v : Child0Stable.word_15 (instance_44_leaves v) = global_word_2226 v.
Proof. unfold Child0Stable.word_15, global_word_2226, Child0Stable.closed_word_15, global_closed_2226, Child0Stable.expr_word_15, global_expr_2226.
 rewrite instance_44_word_9 instance_44_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2226.
Transparent Child0Stable.word_16 global_word_2228.
Lemma instance_44_word_16 v : Child0Stable.word_16 (instance_44_leaves v) = global_word_2228 v.
Proof. unfold Child0Stable.word_16, global_word_2228, Child0Stable.closed_word_16, global_closed_2228, Child0Stable.expr_word_16, global_expr_2228.
 rewrite instance_44_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2228.
Transparent Child0Stable.word_17 global_word_2229.
Lemma instance_44_word_17 v : Child0Stable.word_17 (instance_44_leaves v) = global_word_2229 v.
Proof. unfold Child0Stable.word_17, global_word_2229, Child0Stable.closed_word_17, global_closed_2229, Child0Stable.expr_word_17, global_expr_2229.
 rewrite instance_44_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2229.
Transparent Child0Stable.word_18 global_word_2230.
Lemma instance_44_word_18 v : Child0Stable.word_18 (instance_44_leaves v) = global_word_2230 v.
Proof. unfold Child0Stable.word_18, global_word_2230, Child0Stable.closed_word_18, global_closed_2230, Child0Stable.expr_word_18, global_expr_2230.
 rewrite instance_44_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2230.
Definition instance_45_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2246 v
| 0, 1 => global_word_2242 v
| 0, 2 => global_word_1227 v
| 0, 3 => global_word_1230 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2246.
Lemma instance_45_word_0 v : Child0Stable.word_0 (instance_45_leaves v) = global_word_2246 v.
Proof. unfold Child0Stable.word_0, instance_45_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2246.
Transparent Child0Stable.word_1 global_word_2242.
Lemma instance_45_word_1 v : Child0Stable.word_1 (instance_45_leaves v) = global_word_2242 v.
Proof. unfold Child0Stable.word_1, instance_45_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2242.
Transparent Child0Stable.word_2 global_word_1227.
Lemma instance_45_word_2 v : Child0Stable.word_2 (instance_45_leaves v) = global_word_1227 v.
Proof. unfold Child0Stable.word_2, instance_45_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1227.
Transparent Child0Stable.word_3 global_word_1230.
Lemma instance_45_word_3 v : Child0Stable.word_3 (instance_45_leaves v) = global_word_1230 v.
Proof. unfold Child0Stable.word_3, instance_45_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1230.
Transparent Child0Stable.word_6 global_word_2232.
Lemma instance_45_word_6 v : Child0Stable.word_6 (instance_45_leaves v) = global_word_2232 v.
Proof. unfold Child0Stable.word_6, global_word_2232, Child0Stable.closed_word_6, global_closed_2232, Child0Stable.expr_word_6, global_expr_2232.
 rewrite instance_45_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2232.
Transparent Child0Stable.word_7 global_word_2233.
Lemma instance_45_word_7 v : Child0Stable.word_7 (instance_45_leaves v) = global_word_2233 v.
Proof. unfold Child0Stable.word_7, global_word_2233, Child0Stable.closed_word_7, global_closed_2233, Child0Stable.expr_word_7, global_expr_2233.
 rewrite instance_45_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2233.
Transparent Child0Stable.word_8 global_word_2234.
Lemma instance_45_word_8 v : Child0Stable.word_8 (instance_45_leaves v) = global_word_2234 v.
Proof. unfold Child0Stable.word_8, global_word_2234, Child0Stable.closed_word_8, global_closed_2234, Child0Stable.expr_word_8, global_expr_2234.
 rewrite instance_45_word_6 instance_45_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2234.
Transparent Child0Stable.word_9 global_word_2235.
Lemma instance_45_word_9 v : Child0Stable.word_9 (instance_45_leaves v) = global_word_2235 v.
Proof. unfold Child0Stable.word_9, global_word_2235, Child0Stable.closed_word_9, global_closed_2235, Child0Stable.expr_word_9, global_expr_2235.
 rewrite instance_45_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2235.
Transparent Child0Stable.word_19 global_word_1228.
Lemma instance_45_word_19 v : Child0Stable.word_19 (instance_45_leaves v) = global_word_1228 v.
Proof. unfold Child0Stable.word_19, global_word_1228, Child0Stable.closed_word_19, global_closed_1228, Child0Stable.expr_word_19, global_expr_1228.
 rewrite instance_45_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1228.
Transparent Child0Stable.word_20 global_word_1231.
Lemma instance_45_word_20 v : Child0Stable.word_20 (instance_45_leaves v) = global_word_1231 v.
Proof. unfold Child0Stable.word_20, global_word_1231, Child0Stable.closed_word_20, global_closed_1231, Child0Stable.expr_word_20, global_expr_1231.
 rewrite instance_45_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1231.
Transparent Child0Stable.word_21 global_word_1232.
Lemma instance_45_word_21 v : Child0Stable.word_21 (instance_45_leaves v) = global_word_1232 v.
Proof. unfold Child0Stable.word_21, global_word_1232, Child0Stable.closed_word_21, global_closed_1232, Child0Stable.expr_word_21, global_expr_1232.
 rewrite instance_45_word_19 instance_45_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1232.
Transparent Child0Stable.word_22 global_word_1233.
Lemma instance_45_word_22 v : Child0Stable.word_22 (instance_45_leaves v) = global_word_1233 v.
Proof. unfold Child0Stable.word_22, global_word_1233, Child0Stable.closed_word_22, global_closed_1233, Child0Stable.expr_word_22, global_expr_1233.
 rewrite instance_45_word_19 instance_45_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1233.
Transparent Child0Stable.word_23 global_word_1234.
Lemma instance_45_word_23 v : Child0Stable.word_23 (instance_45_leaves v) = global_word_1234 v.
Proof. unfold Child0Stable.word_23, global_word_1234, Child0Stable.closed_word_23, global_closed_1234, Child0Stable.expr_word_23, global_expr_1234.
 rewrite instance_45_word_21 instance_45_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1234.
Transparent Child0Stable.word_24 global_word_1235.
Lemma instance_45_word_24 v : Child0Stable.word_24 (instance_45_leaves v) = global_word_1235 v.
Proof. unfold Child0Stable.word_24, global_word_1235, Child0Stable.closed_word_24, global_closed_1235, Child0Stable.expr_word_24, global_expr_1235.
 rewrite instance_45_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1235.
Transparent Child0Stable.word_25 global_word_1236.
Lemma instance_45_word_25 v : Child0Stable.word_25 (instance_45_leaves v) = global_word_1236 v.
Proof. unfold Child0Stable.word_25, global_word_1236, Child0Stable.closed_word_25, global_closed_1236, Child0Stable.expr_word_25, global_expr_1236.
 rewrite instance_45_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1236.
Transparent Child0Stable.word_4 global_word_1237.
Lemma instance_45_word_4 v : Child0Stable.word_4 (instance_45_leaves v) = global_word_1237 v.
Proof. unfold Child0Stable.word_4, global_word_1237, Child0Stable.closed_word_4, global_closed_1237, Child0Stable.expr_word_4, global_expr_1237.
 rewrite instance_45_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1237.
Transparent Child0Stable.word_10 global_word_2236.
Lemma instance_45_word_10 v : Child0Stable.word_10 (instance_45_leaves v) = global_word_2236 v.
Proof. unfold Child0Stable.word_10, global_word_2236, Child0Stable.closed_word_10, global_closed_2236, Child0Stable.expr_word_10, global_expr_2236.
 rewrite instance_45_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2236.
Transparent Child0Stable.word_26 global_word_1240.
Lemma instance_45_word_26 v : Child0Stable.word_26 (instance_45_leaves v) = global_word_1240 v.
Proof. unfold Child0Stable.word_26, global_word_1240, Child0Stable.closed_word_26, global_closed_1240, Child0Stable.expr_word_26, global_expr_1240.
 rewrite instance_45_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1240.
Transparent Child0Stable.word_5 global_word_1241.
Lemma instance_45_word_5 v : Child0Stable.word_5 (instance_45_leaves v) = global_word_1241 v.
Proof. unfold Child0Stable.word_5, global_word_1241, Child0Stable.closed_word_5, global_closed_1241, Child0Stable.expr_word_5, global_expr_1241.
 rewrite instance_45_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1241.
Transparent Child0Stable.word_11 global_word_2237.
Lemma instance_45_word_11 v : Child0Stable.word_11 (instance_45_leaves v) = global_word_2237 v.
Proof. unfold Child0Stable.word_11, global_word_2237, Child0Stable.closed_word_11, global_closed_2237, Child0Stable.expr_word_11, global_expr_2237.
 rewrite instance_45_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2237.
Transparent Child0Stable.word_12 global_word_2238.
Lemma instance_45_word_12 v : Child0Stable.word_12 (instance_45_leaves v) = global_word_2238 v.
Proof. unfold Child0Stable.word_12, global_word_2238, Child0Stable.closed_word_12, global_closed_2238, Child0Stable.expr_word_12, global_expr_2238.
 rewrite instance_45_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2238.
Transparent Child0Stable.word_13 global_word_2239.
Lemma instance_45_word_13 v : Child0Stable.word_13 (instance_45_leaves v) = global_word_2239 v.
Proof. unfold Child0Stable.word_13, global_word_2239, Child0Stable.closed_word_13, global_closed_2239, Child0Stable.expr_word_13, global_expr_2239.
 rewrite instance_45_word_10 instance_45_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2239.
Transparent Child0Stable.word_14 global_word_2240.
Lemma instance_45_word_14 v : Child0Stable.word_14 (instance_45_leaves v) = global_word_2240 v.
Proof. unfold Child0Stable.word_14, global_word_2240, Child0Stable.closed_word_14, global_closed_2240, Child0Stable.expr_word_14, global_expr_2240.
 rewrite instance_45_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2240.
Transparent Child0Stable.word_15 global_word_2241.
Lemma instance_45_word_15 v : Child0Stable.word_15 (instance_45_leaves v) = global_word_2241 v.
Proof. unfold Child0Stable.word_15, global_word_2241, Child0Stable.closed_word_15, global_closed_2241, Child0Stable.expr_word_15, global_expr_2241.
 rewrite instance_45_word_9 instance_45_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2241.
Transparent Child0Stable.word_16 global_word_2243.
Lemma instance_45_word_16 v : Child0Stable.word_16 (instance_45_leaves v) = global_word_2243 v.
Proof. unfold Child0Stable.word_16, global_word_2243, Child0Stable.closed_word_16, global_closed_2243, Child0Stable.expr_word_16, global_expr_2243.
 rewrite instance_45_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2243.
Transparent Child0Stable.word_17 global_word_2244.
Lemma instance_45_word_17 v : Child0Stable.word_17 (instance_45_leaves v) = global_word_2244 v.
Proof. unfold Child0Stable.word_17, global_word_2244, Child0Stable.closed_word_17, global_closed_2244, Child0Stable.expr_word_17, global_expr_2244.
 rewrite instance_45_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2244.
Transparent Child0Stable.word_18 global_word_2245.
Lemma instance_45_word_18 v : Child0Stable.word_18 (instance_45_leaves v) = global_word_2245 v.
Proof. unfold Child0Stable.word_18, global_word_2245, Child0Stable.closed_word_18, global_closed_2245, Child0Stable.expr_word_18, global_expr_2245.
 rewrite instance_45_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2245.
Definition instance_46_leaves (v:global_leaves) : Child0Stable.leaf_values := fun scope id => match scope,id with
| 0, 0 => global_word_2261 v
| 0, 1 => global_word_2257 v
| 0, 2 => global_word_1245 v
| 0, 3 => global_word_1248 v
| _,_ => [::] end.
Transparent Child0Stable.word_0 global_word_2261.
Lemma instance_46_word_0 v : Child0Stable.word_0 (instance_46_leaves v) = global_word_2261 v.
Proof. unfold Child0Stable.word_0, instance_46_leaves. reflexivity. Qed.
Opaque Child0Stable.word_0 global_word_2261.
Transparent Child0Stable.word_1 global_word_2257.
Lemma instance_46_word_1 v : Child0Stable.word_1 (instance_46_leaves v) = global_word_2257 v.
Proof. unfold Child0Stable.word_1, instance_46_leaves. reflexivity. Qed.
Opaque Child0Stable.word_1 global_word_2257.
Transparent Child0Stable.word_2 global_word_1245.
Lemma instance_46_word_2 v : Child0Stable.word_2 (instance_46_leaves v) = global_word_1245 v.
Proof. unfold Child0Stable.word_2, instance_46_leaves. reflexivity. Qed.
Opaque Child0Stable.word_2 global_word_1245.
Transparent Child0Stable.word_3 global_word_1248.
Lemma instance_46_word_3 v : Child0Stable.word_3 (instance_46_leaves v) = global_word_1248 v.
Proof. unfold Child0Stable.word_3, instance_46_leaves. reflexivity. Qed.
Opaque Child0Stable.word_3 global_word_1248.
Transparent Child0Stable.word_6 global_word_2247.
Lemma instance_46_word_6 v : Child0Stable.word_6 (instance_46_leaves v) = global_word_2247 v.
Proof. unfold Child0Stable.word_6, global_word_2247, Child0Stable.closed_word_6, global_closed_2247, Child0Stable.expr_word_6, global_expr_2247.
 rewrite instance_46_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_6 global_word_2247.
Transparent Child0Stable.word_7 global_word_2248.
Lemma instance_46_word_7 v : Child0Stable.word_7 (instance_46_leaves v) = global_word_2248 v.
Proof. unfold Child0Stable.word_7, global_word_2248, Child0Stable.closed_word_7, global_closed_2248, Child0Stable.expr_word_7, global_expr_2248.
 rewrite instance_46_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_7 global_word_2248.
Transparent Child0Stable.word_8 global_word_2249.
Lemma instance_46_word_8 v : Child0Stable.word_8 (instance_46_leaves v) = global_word_2249 v.
Proof. unfold Child0Stable.word_8, global_word_2249, Child0Stable.closed_word_8, global_closed_2249, Child0Stable.expr_word_8, global_expr_2249.
 rewrite instance_46_word_6 instance_46_word_7.
 reflexivity. Qed. Opaque Child0Stable.word_8 global_word_2249.
Transparent Child0Stable.word_9 global_word_2250.
Lemma instance_46_word_9 v : Child0Stable.word_9 (instance_46_leaves v) = global_word_2250 v.
Proof. unfold Child0Stable.word_9, global_word_2250, Child0Stable.closed_word_9, global_closed_2250, Child0Stable.expr_word_9, global_expr_2250.
 rewrite instance_46_word_8.
 reflexivity. Qed. Opaque Child0Stable.word_9 global_word_2250.
Transparent Child0Stable.word_19 global_word_1246.
Lemma instance_46_word_19 v : Child0Stable.word_19 (instance_46_leaves v) = global_word_1246 v.
Proof. unfold Child0Stable.word_19, global_word_1246, Child0Stable.closed_word_19, global_closed_1246, Child0Stable.expr_word_19, global_expr_1246.
 rewrite instance_46_word_2.
 reflexivity. Qed. Opaque Child0Stable.word_19 global_word_1246.
Transparent Child0Stable.word_20 global_word_1249.
Lemma instance_46_word_20 v : Child0Stable.word_20 (instance_46_leaves v) = global_word_1249 v.
Proof. unfold Child0Stable.word_20, global_word_1249, Child0Stable.closed_word_20, global_closed_1249, Child0Stable.expr_word_20, global_expr_1249.
 rewrite instance_46_word_3.
 reflexivity. Qed. Opaque Child0Stable.word_20 global_word_1249.
Transparent Child0Stable.word_21 global_word_1250.
Lemma instance_46_word_21 v : Child0Stable.word_21 (instance_46_leaves v) = global_word_1250 v.
Proof. unfold Child0Stable.word_21, global_word_1250, Child0Stable.closed_word_21, global_closed_1250, Child0Stable.expr_word_21, global_expr_1250.
 rewrite instance_46_word_19 instance_46_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_21 global_word_1250.
Transparent Child0Stable.word_22 global_word_1251.
Lemma instance_46_word_22 v : Child0Stable.word_22 (instance_46_leaves v) = global_word_1251 v.
Proof. unfold Child0Stable.word_22, global_word_1251, Child0Stable.closed_word_22, global_closed_1251, Child0Stable.expr_word_22, global_expr_1251.
 rewrite instance_46_word_19 instance_46_word_20.
 reflexivity. Qed. Opaque Child0Stable.word_22 global_word_1251.
Transparent Child0Stable.word_23 global_word_1252.
Lemma instance_46_word_23 v : Child0Stable.word_23 (instance_46_leaves v) = global_word_1252 v.
Proof. unfold Child0Stable.word_23, global_word_1252, Child0Stable.closed_word_23, global_closed_1252, Child0Stable.expr_word_23, global_expr_1252.
 rewrite instance_46_word_21 instance_46_word_22.
 reflexivity. Qed. Opaque Child0Stable.word_23 global_word_1252.
Transparent Child0Stable.word_24 global_word_1253.
Lemma instance_46_word_24 v : Child0Stable.word_24 (instance_46_leaves v) = global_word_1253 v.
Proof. unfold Child0Stable.word_24, global_word_1253, Child0Stable.closed_word_24, global_closed_1253, Child0Stable.expr_word_24, global_expr_1253.
 rewrite instance_46_word_23.
 reflexivity. Qed. Opaque Child0Stable.word_24 global_word_1253.
Transparent Child0Stable.word_25 global_word_1254.
Lemma instance_46_word_25 v : Child0Stable.word_25 (instance_46_leaves v) = global_word_1254 v.
Proof. unfold Child0Stable.word_25, global_word_1254, Child0Stable.closed_word_25, global_closed_1254, Child0Stable.expr_word_25, global_expr_1254.
 rewrite instance_46_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_25 global_word_1254.
Transparent Child0Stable.word_4 global_word_1255.
Lemma instance_46_word_4 v : Child0Stable.word_4 (instance_46_leaves v) = global_word_1255 v.
Proof. unfold Child0Stable.word_4, global_word_1255, Child0Stable.closed_word_4, global_closed_1255, Child0Stable.expr_word_4, global_expr_1255.
 rewrite instance_46_word_25.
 reflexivity. Qed. Opaque Child0Stable.word_4 global_word_1255.
Transparent Child0Stable.word_10 global_word_2251.
Lemma instance_46_word_10 v : Child0Stable.word_10 (instance_46_leaves v) = global_word_2251 v.
Proof. unfold Child0Stable.word_10, global_word_2251, Child0Stable.closed_word_10, global_closed_2251, Child0Stable.expr_word_10, global_expr_2251.
 rewrite instance_46_word_4.
 reflexivity. Qed. Opaque Child0Stable.word_10 global_word_2251.
Transparent Child0Stable.word_26 global_word_1258.
Lemma instance_46_word_26 v : Child0Stable.word_26 (instance_46_leaves v) = global_word_1258 v.
Proof. unfold Child0Stable.word_26, global_word_1258, Child0Stable.closed_word_26, global_closed_1258, Child0Stable.expr_word_26, global_expr_1258.
 rewrite instance_46_word_24.
 reflexivity. Qed. Opaque Child0Stable.word_26 global_word_1258.
Transparent Child0Stable.word_5 global_word_1259.
Lemma instance_46_word_5 v : Child0Stable.word_5 (instance_46_leaves v) = global_word_1259 v.
Proof. unfold Child0Stable.word_5, global_word_1259, Child0Stable.closed_word_5, global_closed_1259, Child0Stable.expr_word_5, global_expr_1259.
 rewrite instance_46_word_26.
 reflexivity. Qed. Opaque Child0Stable.word_5 global_word_1259.
Transparent Child0Stable.word_11 global_word_2252.
Lemma instance_46_word_11 v : Child0Stable.word_11 (instance_46_leaves v) = global_word_2252 v.
Proof. unfold Child0Stable.word_11, global_word_2252, Child0Stable.closed_word_11, global_closed_2252, Child0Stable.expr_word_11, global_expr_2252.
 rewrite instance_46_word_5.
 reflexivity. Qed. Opaque Child0Stable.word_11 global_word_2252.
Transparent Child0Stable.word_12 global_word_2253.
Lemma instance_46_word_12 v : Child0Stable.word_12 (instance_46_leaves v) = global_word_2253 v.
Proof. unfold Child0Stable.word_12, global_word_2253, Child0Stable.closed_word_12, global_closed_2253, Child0Stable.expr_word_12, global_expr_2253.
 rewrite instance_46_word_11.
 reflexivity. Qed. Opaque Child0Stable.word_12 global_word_2253.
Transparent Child0Stable.word_13 global_word_2254.
Lemma instance_46_word_13 v : Child0Stable.word_13 (instance_46_leaves v) = global_word_2254 v.
Proof. unfold Child0Stable.word_13, global_word_2254, Child0Stable.closed_word_13, global_closed_2254, Child0Stable.expr_word_13, global_expr_2254.
 rewrite instance_46_word_10 instance_46_word_12.
 reflexivity. Qed. Opaque Child0Stable.word_13 global_word_2254.
Transparent Child0Stable.word_14 global_word_2255.
Lemma instance_46_word_14 v : Child0Stable.word_14 (instance_46_leaves v) = global_word_2255 v.
Proof. unfold Child0Stable.word_14, global_word_2255, Child0Stable.closed_word_14, global_closed_2255, Child0Stable.expr_word_14, global_expr_2255.
 rewrite instance_46_word_13.
 reflexivity. Qed. Opaque Child0Stable.word_14 global_word_2255.
Transparent Child0Stable.word_15 global_word_2256.
Lemma instance_46_word_15 v : Child0Stable.word_15 (instance_46_leaves v) = global_word_2256 v.
Proof. unfold Child0Stable.word_15, global_word_2256, Child0Stable.closed_word_15, global_closed_2256, Child0Stable.expr_word_15, global_expr_2256.
 rewrite instance_46_word_9 instance_46_word_14.
 reflexivity. Qed. Opaque Child0Stable.word_15 global_word_2256.
Transparent Child0Stable.word_16 global_word_2258.
Lemma instance_46_word_16 v : Child0Stable.word_16 (instance_46_leaves v) = global_word_2258 v.
Proof. unfold Child0Stable.word_16, global_word_2258, Child0Stable.closed_word_16, global_closed_2258, Child0Stable.expr_word_16, global_expr_2258.
 rewrite instance_46_word_1.
 reflexivity. Qed. Opaque Child0Stable.word_16 global_word_2258.
Transparent Child0Stable.word_17 global_word_2259.
Lemma instance_46_word_17 v : Child0Stable.word_17 (instance_46_leaves v) = global_word_2259 v.
Proof. unfold Child0Stable.word_17, global_word_2259, Child0Stable.closed_word_17, global_closed_2259, Child0Stable.expr_word_17, global_expr_2259.
 rewrite instance_46_word_16.
 reflexivity. Qed. Opaque Child0Stable.word_17 global_word_2259.
Transparent Child0Stable.word_18 global_word_2260.
Lemma instance_46_word_18 v : Child0Stable.word_18 (instance_46_leaves v) = global_word_2260 v.
Proof. unfold Child0Stable.word_18, global_word_2260, Child0Stable.closed_word_18, global_closed_2260, Child0Stable.expr_word_18, global_expr_2260.
 rewrite instance_46_word_15.
 reflexivity. Qed. Opaque Child0Stable.word_18 global_word_2260.

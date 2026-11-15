From Coq Require Import ZArith NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalChildren Child0Stable Child1Stable Child2Stable ChildAbstract Compressors.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalAliases.
Lemma instance_6_bits v (a b c:bool)
 (E2:global_word_376 v=[::a])
 (E3:global_word_381 v=[::b])
 (E4:global_word_371 v=[::c])
 : global_word_391 v=[::fa_sum a b c] /\ global_word_418 v=[::fa_carry a b c] /\ global_word_1480 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_6_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_6_leaves]. exact E2.
   + cbn [instance_6_leaves]. exact E3.
   + cbn [instance_6_leaves]. exact E4.
 - rewrite -instance_6_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_6_leaves]. exact E2.
   + cbn [instance_6_leaves]. exact E3.
   + cbn [instance_6_leaves]. exact E4.
 - rewrite -instance_6_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_6_leaves]. exact E2.
   + cbn [instance_6_leaves]. exact E3.
   + cbn [instance_6_leaves]. exact E4.
Qed.
Lemma instance_7_bits v (a b c:bool)
 (E2:global_word_395 v=[::a])
 (E3:global_word_401 v=[::b])
 (E4:global_word_366 v=[::c])
 : global_word_411 v=[::fa_sum a b c] /\ global_word_425 v=[::fa_carry a b c] /\ global_word_1498 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_7_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_7_leaves]. exact E2.
   + cbn [instance_7_leaves]. exact E3.
   + cbn [instance_7_leaves]. exact E4.
 - rewrite -instance_7_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_7_leaves]. exact E2.
   + cbn [instance_7_leaves]. exact E3.
   + cbn [instance_7_leaves]. exact E4.
 - rewrite -instance_7_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_7_leaves]. exact E2.
   + cbn [instance_7_leaves]. exact E3.
   + cbn [instance_7_leaves]. exact E4.
Qed.
Lemma instance_9_bits v (a b c:bool)
 (E2:global_word_445 v=[::a])
 (E3:global_word_450 v=[::b])
 (E4:global_word_440 v=[::c])
 : global_word_460 v=[::fa_sum a b c] /\ global_word_487 v=[::fa_carry a b c] /\ global_word_1548 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_9_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_9_leaves]. exact E2.
   + cbn [instance_9_leaves]. exact E3.
   + cbn [instance_9_leaves]. exact E4.
 - rewrite -instance_9_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_9_leaves]. exact E2.
   + cbn [instance_9_leaves]. exact E3.
   + cbn [instance_9_leaves]. exact E4.
 - rewrite -instance_9_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_9_leaves]. exact E2.
   + cbn [instance_9_leaves]. exact E3.
   + cbn [instance_9_leaves]. exact E4.
Qed.
Lemma instance_10_bits v (a b c:bool)
 (E2:global_word_464 v=[::a])
 (E3:global_word_470 v=[::b])
 (E4:global_word_435 v=[::c])
 : global_word_480 v=[::fa_sum a b c] /\ global_word_494 v=[::fa_carry a b c] /\ global_word_1566 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_10_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_10_leaves]. exact E2.
   + cbn [instance_10_leaves]. exact E3.
   + cbn [instance_10_leaves]. exact E4.
 - rewrite -instance_10_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_10_leaves]. exact E2.
   + cbn [instance_10_leaves]. exact E3.
   + cbn [instance_10_leaves]. exact E4.
 - rewrite -instance_10_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_10_leaves]. exact E2.
   + cbn [instance_10_leaves]. exact E3.
   + cbn [instance_10_leaves]. exact E4.
Qed.
Lemma instance_12_bits v (a b c:bool)
 (E2:global_word_514 v=[::a])
 (E3:global_word_519 v=[::b])
 (E4:global_word_509 v=[::c])
 : global_word_529 v=[::fa_sum a b c] /\ global_word_556 v=[::fa_carry a b c] /\ global_word_1616 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_12_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_12_leaves]. exact E2.
   + cbn [instance_12_leaves]. exact E3.
   + cbn [instance_12_leaves]. exact E4.
 - rewrite -instance_12_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_12_leaves]. exact E2.
   + cbn [instance_12_leaves]. exact E3.
   + cbn [instance_12_leaves]. exact E4.
 - rewrite -instance_12_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_12_leaves]. exact E2.
   + cbn [instance_12_leaves]. exact E3.
   + cbn [instance_12_leaves]. exact E4.
Qed.
Lemma instance_13_bits v (a b c:bool)
 (E2:global_word_533 v=[::a])
 (E3:global_word_539 v=[::b])
 (E4:global_word_504 v=[::c])
 : global_word_549 v=[::fa_sum a b c] /\ global_word_563 v=[::fa_carry a b c] /\ global_word_1634 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_13_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_13_leaves]. exact E2.
   + cbn [instance_13_leaves]. exact E3.
   + cbn [instance_13_leaves]. exact E4.
 - rewrite -instance_13_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_13_leaves]. exact E2.
   + cbn [instance_13_leaves]. exact E3.
   + cbn [instance_13_leaves]. exact E4.
 - rewrite -instance_13_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_13_leaves]. exact E2.
   + cbn [instance_13_leaves]. exact E3.
   + cbn [instance_13_leaves]. exact E4.
Qed.
Lemma instance_15_bits v (a b c:bool)
 (E2:global_word_583 v=[::a])
 (E3:global_word_588 v=[::b])
 (E4:global_word_578 v=[::c])
 : global_word_598 v=[::fa_sum a b c] /\ global_word_625 v=[::fa_carry a b c] /\ global_word_1684 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_15_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_15_leaves]. exact E2.
   + cbn [instance_15_leaves]. exact E3.
   + cbn [instance_15_leaves]. exact E4.
 - rewrite -instance_15_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_15_leaves]. exact E2.
   + cbn [instance_15_leaves]. exact E3.
   + cbn [instance_15_leaves]. exact E4.
 - rewrite -instance_15_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_15_leaves]. exact E2.
   + cbn [instance_15_leaves]. exact E3.
   + cbn [instance_15_leaves]. exact E4.
Qed.
Lemma instance_16_bits v (a b c:bool)
 (E2:global_word_602 v=[::a])
 (E3:global_word_608 v=[::b])
 (E4:global_word_573 v=[::c])
 : global_word_618 v=[::fa_sum a b c] /\ global_word_632 v=[::fa_carry a b c] /\ global_word_1702 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_16_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_16_leaves]. exact E2.
   + cbn [instance_16_leaves]. exact E3.
   + cbn [instance_16_leaves]. exact E4.
 - rewrite -instance_16_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_16_leaves]. exact E2.
   + cbn [instance_16_leaves]. exact E3.
   + cbn [instance_16_leaves]. exact E4.
 - rewrite -instance_16_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_16_leaves]. exact E2.
   + cbn [instance_16_leaves]. exact E3.
   + cbn [instance_16_leaves]. exact E4.
Qed.
Lemma instance_18_bits v (a b c:bool)
 (E2:global_word_652 v=[::a])
 (E3:global_word_657 v=[::b])
 (E4:global_word_647 v=[::c])
 : global_word_667 v=[::fa_sum a b c] /\ global_word_694 v=[::fa_carry a b c] /\ global_word_1752 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_18_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_18_leaves]. exact E2.
   + cbn [instance_18_leaves]. exact E3.
   + cbn [instance_18_leaves]. exact E4.
 - rewrite -instance_18_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_18_leaves]. exact E2.
   + cbn [instance_18_leaves]. exact E3.
   + cbn [instance_18_leaves]. exact E4.
 - rewrite -instance_18_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_18_leaves]. exact E2.
   + cbn [instance_18_leaves]. exact E3.
   + cbn [instance_18_leaves]. exact E4.
Qed.
Lemma instance_19_bits v (a b c:bool)
 (E2:global_word_671 v=[::a])
 (E3:global_word_677 v=[::b])
 (E4:global_word_642 v=[::c])
 : global_word_687 v=[::fa_sum a b c] /\ global_word_701 v=[::fa_carry a b c] /\ global_word_1770 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_19_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_19_leaves]. exact E2.
   + cbn [instance_19_leaves]. exact E3.
   + cbn [instance_19_leaves]. exact E4.
 - rewrite -instance_19_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_19_leaves]. exact E2.
   + cbn [instance_19_leaves]. exact E3.
   + cbn [instance_19_leaves]. exact E4.
 - rewrite -instance_19_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_19_leaves]. exact E2.
   + cbn [instance_19_leaves]. exact E3.
   + cbn [instance_19_leaves]. exact E4.
Qed.
Lemma instance_21_bits v (a b c:bool)
 (E2:global_word_721 v=[::a])
 (E3:global_word_726 v=[::b])
 (E4:global_word_716 v=[::c])
 : global_word_736 v=[::fa_sum a b c] /\ global_word_763 v=[::fa_carry a b c] /\ global_word_1820 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_21_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_21_leaves]. exact E2.
   + cbn [instance_21_leaves]. exact E3.
   + cbn [instance_21_leaves]. exact E4.
 - rewrite -instance_21_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_21_leaves]. exact E2.
   + cbn [instance_21_leaves]. exact E3.
   + cbn [instance_21_leaves]. exact E4.
 - rewrite -instance_21_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_21_leaves]. exact E2.
   + cbn [instance_21_leaves]. exact E3.
   + cbn [instance_21_leaves]. exact E4.
Qed.
Lemma instance_22_bits v (a b c:bool)
 (E2:global_word_740 v=[::a])
 (E3:global_word_746 v=[::b])
 (E4:global_word_711 v=[::c])
 : global_word_756 v=[::fa_sum a b c] /\ global_word_770 v=[::fa_carry a b c] /\ global_word_1838 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_22_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_22_leaves]. exact E2.
   + cbn [instance_22_leaves]. exact E3.
   + cbn [instance_22_leaves]. exact E4.
 - rewrite -instance_22_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_22_leaves]. exact E2.
   + cbn [instance_22_leaves]. exact E3.
   + cbn [instance_22_leaves]. exact E4.
 - rewrite -instance_22_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_22_leaves]. exact E2.
   + cbn [instance_22_leaves]. exact E3.
   + cbn [instance_22_leaves]. exact E4.
Qed.
Lemma instance_24_bits v (a b c:bool)
 (E2:global_word_790 v=[::a])
 (E3:global_word_795 v=[::b])
 (E4:global_word_785 v=[::c])
 : global_word_805 v=[::fa_sum a b c] /\ global_word_832 v=[::fa_carry a b c] /\ global_word_1888 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_24_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_24_leaves]. exact E2.
   + cbn [instance_24_leaves]. exact E3.
   + cbn [instance_24_leaves]. exact E4.
 - rewrite -instance_24_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_24_leaves]. exact E2.
   + cbn [instance_24_leaves]. exact E3.
   + cbn [instance_24_leaves]. exact E4.
 - rewrite -instance_24_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_24_leaves]. exact E2.
   + cbn [instance_24_leaves]. exact E3.
   + cbn [instance_24_leaves]. exact E4.
Qed.
Lemma instance_25_bits v (a b c:bool)
 (E2:global_word_809 v=[::a])
 (E3:global_word_815 v=[::b])
 (E4:global_word_780 v=[::c])
 : global_word_825 v=[::fa_sum a b c] /\ global_word_839 v=[::fa_carry a b c] /\ global_word_1906 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_25_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_25_leaves]. exact E2.
   + cbn [instance_25_leaves]. exact E3.
   + cbn [instance_25_leaves]. exact E4.
 - rewrite -instance_25_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_25_leaves]. exact E2.
   + cbn [instance_25_leaves]. exact E3.
   + cbn [instance_25_leaves]. exact E4.
 - rewrite -instance_25_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_25_leaves]. exact E2.
   + cbn [instance_25_leaves]. exact E3.
   + cbn [instance_25_leaves]. exact E4.
Qed.
Lemma instance_27_bits v (a b c:bool)
 (E2:global_word_859 v=[::a])
 (E3:global_word_864 v=[::b])
 (E4:global_word_854 v=[::c])
 : global_word_874 v=[::fa_sum a b c] /\ global_word_901 v=[::fa_carry a b c] /\ global_word_1956 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_27_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_27_leaves]. exact E2.
   + cbn [instance_27_leaves]. exact E3.
   + cbn [instance_27_leaves]. exact E4.
 - rewrite -instance_27_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_27_leaves]. exact E2.
   + cbn [instance_27_leaves]. exact E3.
   + cbn [instance_27_leaves]. exact E4.
 - rewrite -instance_27_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_27_leaves]. exact E2.
   + cbn [instance_27_leaves]. exact E3.
   + cbn [instance_27_leaves]. exact E4.
Qed.
Lemma instance_28_bits v (a b c:bool)
 (E2:global_word_878 v=[::a])
 (E3:global_word_884 v=[::b])
 (E4:global_word_849 v=[::c])
 : global_word_894 v=[::fa_sum a b c] /\ global_word_908 v=[::fa_carry a b c] /\ global_word_1974 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_28_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_28_leaves]. exact E2.
   + cbn [instance_28_leaves]. exact E3.
   + cbn [instance_28_leaves]. exact E4.
 - rewrite -instance_28_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_28_leaves]. exact E2.
   + cbn [instance_28_leaves]. exact E3.
   + cbn [instance_28_leaves]. exact E4.
 - rewrite -instance_28_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_28_leaves]. exact E2.
   + cbn [instance_28_leaves]. exact E3.
   + cbn [instance_28_leaves]. exact E4.
Qed.
Lemma instance_1_bits v (a b:bool)
 (E2:global_word_279 v=[::a])
 (E3:global_word_282 v=[::b])
 : global_word_289 v=[::xorb a b] /\ global_word_293 v=[::andb a b] /\ global_word_1379 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_1_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_1_leaves]. exact E2.
   + cbn [instance_1_leaves]. exact E3.
 - rewrite -instance_1_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_1_leaves]. exact E2.
   + cbn [instance_1_leaves]. exact E3.
 - rewrite -instance_1_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_1_leaves]. exact E2.
   + cbn [instance_1_leaves]. exact E3.
Qed.
Lemma instance_2_bits v (a b:bool)
 (E2:global_word_297 v=[::a])
 (E3:global_word_300 v=[::b])
 : global_word_307 v=[::xorb a b] /\ global_word_311 v=[::andb a b] /\ global_word_1394 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_2_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_2_leaves]. exact E2.
   + cbn [instance_2_leaves]. exact E3.
 - rewrite -instance_2_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_2_leaves]. exact E2.
   + cbn [instance_2_leaves]. exact E3.
 - rewrite -instance_2_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_2_leaves]. exact E2.
   + cbn [instance_2_leaves]. exact E3.
Qed.
Lemma instance_3_bits v (a b c:bool)
 (E2:global_word_318 v=[::a])
 (E3:global_word_321 v=[::b])
 (E4:global_word_315 v=[::c])
 : global_word_331 v=[::fa_sum a b c] /\ global_word_335 v=[::fa_carry a b c] /\ global_word_1412 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_3_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_3_leaves]. exact E2.
   + cbn [instance_3_leaves]. exact E3.
   + cbn [instance_3_leaves]. exact E4.
 - rewrite -instance_3_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_3_leaves]. exact E2.
   + cbn [instance_3_leaves]. exact E3.
   + cbn [instance_3_leaves]. exact E4.
 - rewrite -instance_3_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_3_leaves]. exact E2.
   + cbn [instance_3_leaves]. exact E3.
   + cbn [instance_3_leaves]. exact E4.
Qed.
Lemma instance_4_bits v (a b c:bool)
 (E2:global_word_342 v=[::a])
 (E3:global_word_345 v=[::b])
 (E4:global_word_339 v=[::c])
 : global_word_355 v=[::fa_sum a b c] /\ global_word_359 v=[::fa_carry a b c] /\ global_word_1430 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_4_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_4_leaves]. exact E2.
   + cbn [instance_4_leaves]. exact E3.
   + cbn [instance_4_leaves]. exact E4.
 - rewrite -instance_4_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_4_leaves]. exact E2.
   + cbn [instance_4_leaves]. exact E3.
   + cbn [instance_4_leaves]. exact E4.
 - rewrite -instance_4_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_4_leaves]. exact E2.
   + cbn [instance_4_leaves]. exact E3.
   + cbn [instance_4_leaves]. exact E4.
Qed.
Lemma instance_5_bits v (a b c d e:bool)
 (E2:global_word_374 v=[::a])
 (E3:global_word_379 v=[::b])
 (E4:global_word_369 v=[::c])
 (E5:global_word_398 v=[::d])
 (E6:global_word_363 v=[::e])
 : global_word_414 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_421 v=[::fa_carry a b c] /\ global_word_428 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1458 v=[::true].
Proof.
 have C10: global_word_391 v=[::fa_sum a b c] /\ global_word_418 v=[::fa_carry a b c] /\ global_word_1480 v=[::true].
 { apply instance_6_bits.
   - rewrite wire_alias_376 wire_alias_375. exact E2.
   - rewrite wire_alias_381 wire_alias_380. exact E3.
   - rewrite wire_alias_371 wire_alias_370. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_411 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_425 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1498 v=[::true].
 { apply instance_7_bits.
   - rewrite wire_alias_395 wire_alias_394 wire_alias_393 wire_alias_392. exact S10.
   - rewrite wire_alias_401 wire_alias_400 wire_alias_399. exact E5.
   - rewrite wire_alias_366 wire_alias_365 wire_alias_364. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_5_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_5_leaves]. rewrite wire_alias_412. exact S11.
 - rewrite -instance_5_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_5_leaves]. rewrite wire_alias_419. exact C10.
 - rewrite -instance_5_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_5_leaves]. rewrite wire_alias_426. exact C11.
 - rewrite -instance_5_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_5_leaves]. exact E2.
   + cbn [instance_5_leaves]. exact E3.
   + cbn [instance_5_leaves]. exact E4.
   + cbn [instance_5_leaves]. exact E5.
   + cbn [instance_5_leaves]. exact E6.
   + cbn [instance_5_leaves]. rewrite wire_alias_419. exact C10.
   + cbn [instance_5_leaves]. rewrite wire_alias_412. exact S11.
   + cbn [instance_5_leaves]. rewrite wire_alias_426. exact C11.
Qed.
Lemma instance_8_bits v (a b c d e:bool)
 (E2:global_word_443 v=[::a])
 (E3:global_word_448 v=[::b])
 (E4:global_word_438 v=[::c])
 (E5:global_word_467 v=[::d])
 (E6:global_word_432 v=[::e])
 : global_word_483 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_490 v=[::fa_carry a b c] /\ global_word_497 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1526 v=[::true].
Proof.
 have C10: global_word_460 v=[::fa_sum a b c] /\ global_word_487 v=[::fa_carry a b c] /\ global_word_1548 v=[::true].
 { apply instance_9_bits.
   - rewrite wire_alias_445 wire_alias_444. exact E2.
   - rewrite wire_alias_450 wire_alias_449. exact E3.
   - rewrite wire_alias_440 wire_alias_439. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_480 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_494 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1566 v=[::true].
 { apply instance_10_bits.
   - rewrite wire_alias_464 wire_alias_463 wire_alias_462 wire_alias_461. exact S10.
   - rewrite wire_alias_470 wire_alias_469 wire_alias_468. exact E5.
   - rewrite wire_alias_435 wire_alias_434 wire_alias_433. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_8_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_8_leaves]. rewrite wire_alias_481. exact S11.
 - rewrite -instance_8_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_8_leaves]. rewrite wire_alias_488. exact C10.
 - rewrite -instance_8_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_8_leaves]. rewrite wire_alias_495. exact C11.
 - rewrite -instance_8_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_8_leaves]. exact E2.
   + cbn [instance_8_leaves]. exact E3.
   + cbn [instance_8_leaves]. exact E4.
   + cbn [instance_8_leaves]. exact E5.
   + cbn [instance_8_leaves]. exact E6.
   + cbn [instance_8_leaves]. rewrite wire_alias_488. exact C10.
   + cbn [instance_8_leaves]. rewrite wire_alias_481. exact S11.
   + cbn [instance_8_leaves]. rewrite wire_alias_495. exact C11.
Qed.
Lemma instance_11_bits v (a b c d e:bool)
 (E2:global_word_512 v=[::a])
 (E3:global_word_517 v=[::b])
 (E4:global_word_507 v=[::c])
 (E5:global_word_536 v=[::d])
 (E6:global_word_501 v=[::e])
 : global_word_552 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_559 v=[::fa_carry a b c] /\ global_word_566 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1594 v=[::true].
Proof.
 have C10: global_word_529 v=[::fa_sum a b c] /\ global_word_556 v=[::fa_carry a b c] /\ global_word_1616 v=[::true].
 { apply instance_12_bits.
   - rewrite wire_alias_514 wire_alias_513. exact E2.
   - rewrite wire_alias_519 wire_alias_518. exact E3.
   - rewrite wire_alias_509 wire_alias_508. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_549 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_563 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1634 v=[::true].
 { apply instance_13_bits.
   - rewrite wire_alias_533 wire_alias_532 wire_alias_531 wire_alias_530. exact S10.
   - rewrite wire_alias_539 wire_alias_538 wire_alias_537. exact E5.
   - rewrite wire_alias_504 wire_alias_503 wire_alias_502. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_11_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_11_leaves]. rewrite wire_alias_550. exact S11.
 - rewrite -instance_11_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_11_leaves]. rewrite wire_alias_557. exact C10.
 - rewrite -instance_11_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_11_leaves]. rewrite wire_alias_564. exact C11.
 - rewrite -instance_11_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_11_leaves]. exact E2.
   + cbn [instance_11_leaves]. exact E3.
   + cbn [instance_11_leaves]. exact E4.
   + cbn [instance_11_leaves]. exact E5.
   + cbn [instance_11_leaves]. exact E6.
   + cbn [instance_11_leaves]. rewrite wire_alias_557. exact C10.
   + cbn [instance_11_leaves]. rewrite wire_alias_550. exact S11.
   + cbn [instance_11_leaves]. rewrite wire_alias_564. exact C11.
Qed.
Lemma instance_14_bits v (a b c d e:bool)
 (E2:global_word_581 v=[::a])
 (E3:global_word_586 v=[::b])
 (E4:global_word_576 v=[::c])
 (E5:global_word_605 v=[::d])
 (E6:global_word_570 v=[::e])
 : global_word_621 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_628 v=[::fa_carry a b c] /\ global_word_635 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1662 v=[::true].
Proof.
 have C10: global_word_598 v=[::fa_sum a b c] /\ global_word_625 v=[::fa_carry a b c] /\ global_word_1684 v=[::true].
 { apply instance_15_bits.
   - rewrite wire_alias_583 wire_alias_582. exact E2.
   - rewrite wire_alias_588 wire_alias_587. exact E3.
   - rewrite wire_alias_578 wire_alias_577. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_618 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_632 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1702 v=[::true].
 { apply instance_16_bits.
   - rewrite wire_alias_602 wire_alias_601 wire_alias_600 wire_alias_599. exact S10.
   - rewrite wire_alias_608 wire_alias_607 wire_alias_606. exact E5.
   - rewrite wire_alias_573 wire_alias_572 wire_alias_571. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_14_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_14_leaves]. rewrite wire_alias_619. exact S11.
 - rewrite -instance_14_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_14_leaves]. rewrite wire_alias_626. exact C10.
 - rewrite -instance_14_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_14_leaves]. rewrite wire_alias_633. exact C11.
 - rewrite -instance_14_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_14_leaves]. exact E2.
   + cbn [instance_14_leaves]. exact E3.
   + cbn [instance_14_leaves]. exact E4.
   + cbn [instance_14_leaves]. exact E5.
   + cbn [instance_14_leaves]. exact E6.
   + cbn [instance_14_leaves]. rewrite wire_alias_626. exact C10.
   + cbn [instance_14_leaves]. rewrite wire_alias_619. exact S11.
   + cbn [instance_14_leaves]. rewrite wire_alias_633. exact C11.
Qed.
Lemma instance_17_bits v (a b c d e:bool)
 (E2:global_word_650 v=[::a])
 (E3:global_word_655 v=[::b])
 (E4:global_word_645 v=[::c])
 (E5:global_word_674 v=[::d])
 (E6:global_word_639 v=[::e])
 : global_word_690 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_697 v=[::fa_carry a b c] /\ global_word_704 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1730 v=[::true].
Proof.
 have C10: global_word_667 v=[::fa_sum a b c] /\ global_word_694 v=[::fa_carry a b c] /\ global_word_1752 v=[::true].
 { apply instance_18_bits.
   - rewrite wire_alias_652 wire_alias_651. exact E2.
   - rewrite wire_alias_657 wire_alias_656. exact E3.
   - rewrite wire_alias_647 wire_alias_646. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_687 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_701 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1770 v=[::true].
 { apply instance_19_bits.
   - rewrite wire_alias_671 wire_alias_670 wire_alias_669 wire_alias_668. exact S10.
   - rewrite wire_alias_677 wire_alias_676 wire_alias_675. exact E5.
   - rewrite wire_alias_642 wire_alias_641 wire_alias_640. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_17_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_17_leaves]. rewrite wire_alias_688. exact S11.
 - rewrite -instance_17_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_17_leaves]. rewrite wire_alias_695. exact C10.
 - rewrite -instance_17_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_17_leaves]. rewrite wire_alias_702. exact C11.
 - rewrite -instance_17_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_17_leaves]. exact E2.
   + cbn [instance_17_leaves]. exact E3.
   + cbn [instance_17_leaves]. exact E4.
   + cbn [instance_17_leaves]. exact E5.
   + cbn [instance_17_leaves]. exact E6.
   + cbn [instance_17_leaves]. rewrite wire_alias_695. exact C10.
   + cbn [instance_17_leaves]. rewrite wire_alias_688. exact S11.
   + cbn [instance_17_leaves]. rewrite wire_alias_702. exact C11.
Qed.
Lemma instance_20_bits v (a b c d e:bool)
 (E2:global_word_719 v=[::a])
 (E3:global_word_724 v=[::b])
 (E4:global_word_714 v=[::c])
 (E5:global_word_743 v=[::d])
 (E6:global_word_708 v=[::e])
 : global_word_759 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_766 v=[::fa_carry a b c] /\ global_word_773 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1798 v=[::true].
Proof.
 have C10: global_word_736 v=[::fa_sum a b c] /\ global_word_763 v=[::fa_carry a b c] /\ global_word_1820 v=[::true].
 { apply instance_21_bits.
   - rewrite wire_alias_721 wire_alias_720. exact E2.
   - rewrite wire_alias_726 wire_alias_725. exact E3.
   - rewrite wire_alias_716 wire_alias_715. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_756 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_770 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1838 v=[::true].
 { apply instance_22_bits.
   - rewrite wire_alias_740 wire_alias_739 wire_alias_738 wire_alias_737. exact S10.
   - rewrite wire_alias_746 wire_alias_745 wire_alias_744. exact E5.
   - rewrite wire_alias_711 wire_alias_710 wire_alias_709. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_20_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_20_leaves]. rewrite wire_alias_757. exact S11.
 - rewrite -instance_20_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_20_leaves]. rewrite wire_alias_764. exact C10.
 - rewrite -instance_20_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_20_leaves]. rewrite wire_alias_771. exact C11.
 - rewrite -instance_20_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_20_leaves]. exact E2.
   + cbn [instance_20_leaves]. exact E3.
   + cbn [instance_20_leaves]. exact E4.
   + cbn [instance_20_leaves]. exact E5.
   + cbn [instance_20_leaves]. exact E6.
   + cbn [instance_20_leaves]. rewrite wire_alias_764. exact C10.
   + cbn [instance_20_leaves]. rewrite wire_alias_757. exact S11.
   + cbn [instance_20_leaves]. rewrite wire_alias_771. exact C11.
Qed.
Lemma instance_23_bits v (a b c d e:bool)
 (E2:global_word_788 v=[::a])
 (E3:global_word_793 v=[::b])
 (E4:global_word_783 v=[::c])
 (E5:global_word_812 v=[::d])
 (E6:global_word_777 v=[::e])
 : global_word_828 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_835 v=[::fa_carry a b c] /\ global_word_842 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1866 v=[::true].
Proof.
 have C10: global_word_805 v=[::fa_sum a b c] /\ global_word_832 v=[::fa_carry a b c] /\ global_word_1888 v=[::true].
 { apply instance_24_bits.
   - rewrite wire_alias_790 wire_alias_789. exact E2.
   - rewrite wire_alias_795 wire_alias_794. exact E3.
   - rewrite wire_alias_785 wire_alias_784. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_825 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_839 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1906 v=[::true].
 { apply instance_25_bits.
   - rewrite wire_alias_809 wire_alias_808 wire_alias_807 wire_alias_806. exact S10.
   - rewrite wire_alias_815 wire_alias_814 wire_alias_813. exact E5.
   - rewrite wire_alias_780 wire_alias_779 wire_alias_778. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_23_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_23_leaves]. rewrite wire_alias_826. exact S11.
 - rewrite -instance_23_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_23_leaves]. rewrite wire_alias_833. exact C10.
 - rewrite -instance_23_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_23_leaves]. rewrite wire_alias_840. exact C11.
 - rewrite -instance_23_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_23_leaves]. exact E2.
   + cbn [instance_23_leaves]. exact E3.
   + cbn [instance_23_leaves]. exact E4.
   + cbn [instance_23_leaves]. exact E5.
   + cbn [instance_23_leaves]. exact E6.
   + cbn [instance_23_leaves]. rewrite wire_alias_833. exact C10.
   + cbn [instance_23_leaves]. rewrite wire_alias_826. exact S11.
   + cbn [instance_23_leaves]. rewrite wire_alias_840. exact C11.
Qed.
Lemma instance_26_bits v (a b c d e:bool)
 (E2:global_word_857 v=[::a])
 (E3:global_word_862 v=[::b])
 (E4:global_word_852 v=[::c])
 (E5:global_word_881 v=[::d])
 (E6:global_word_846 v=[::e])
 : global_word_897 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_904 v=[::fa_carry a b c] /\ global_word_911 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1934 v=[::true].
Proof.
 have C10: global_word_874 v=[::fa_sum a b c] /\ global_word_901 v=[::fa_carry a b c] /\ global_word_1956 v=[::true].
 { apply instance_27_bits.
   - rewrite wire_alias_859 wire_alias_858. exact E2.
   - rewrite wire_alias_864 wire_alias_863. exact E3.
   - rewrite wire_alias_854 wire_alias_853. exact E4.
 }
 destruct C10 as [S10 [C10 A10]].
 have C11: global_word_894 v=[::fa_sum (fa_sum a b c) d e] /\ global_word_908 v=[::fa_carry (fa_sum a b c) d e] /\ global_word_1974 v=[::true].
 { apply instance_28_bits.
   - rewrite wire_alias_878 wire_alias_877 wire_alias_876 wire_alias_875. exact S10.
   - rewrite wire_alias_884 wire_alias_883 wire_alias_882. exact E5.
   - rewrite wire_alias_849 wire_alias_848 wire_alias_847. exact E6.
 }
 destruct C11 as [S11 [C11 A11]].
 repeat split.
 - rewrite -instance_26_word_7.
   apply (abstract_child2_7 _ a b c d e).
   + cbn [instance_26_leaves]. rewrite wire_alias_895. exact S11.
 - rewrite -instance_26_word_8.
   apply (abstract_child2_8 _ a b c d e).
   + cbn [instance_26_leaves]. rewrite wire_alias_902. exact C10.
 - rewrite -instance_26_word_9.
   apply (abstract_child2_9 _ a b c d e).
   + cbn [instance_26_leaves]. rewrite wire_alias_909. exact C11.
 - rewrite -instance_26_word_34.
   apply (abstract_child2_34 _ a b c d e).
   + cbn [instance_26_leaves]. exact E2.
   + cbn [instance_26_leaves]. exact E3.
   + cbn [instance_26_leaves]. exact E4.
   + cbn [instance_26_leaves]. exact E5.
   + cbn [instance_26_leaves]. exact E6.
   + cbn [instance_26_leaves]. rewrite wire_alias_902. exact C10.
   + cbn [instance_26_leaves]. rewrite wire_alias_895. exact S11.
   + cbn [instance_26_leaves]. rewrite wire_alias_909. exact C11.
Qed.
Lemma instance_29_bits v (a b c:bool)
 (E2:global_word_918 v=[::a])
 (E3:global_word_921 v=[::b])
 (E4:global_word_915 v=[::c])
 : global_word_931 v=[::fa_sum a b c] /\ global_word_935 v=[::fa_carry a b c] /\ global_word_1992 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_29_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_29_leaves]. exact E2.
   + cbn [instance_29_leaves]. exact E3.
   + cbn [instance_29_leaves]. exact E4.
 - rewrite -instance_29_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_29_leaves]. exact E2.
   + cbn [instance_29_leaves]. exact E3.
   + cbn [instance_29_leaves]. exact E4.
 - rewrite -instance_29_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_29_leaves]. exact E2.
   + cbn [instance_29_leaves]. exact E3.
   + cbn [instance_29_leaves]. exact E4.
Qed.
Lemma instance_30_bits v (a b:bool)
 (E2:global_word_939 v=[::a])
 (E3:global_word_942 v=[::b])
 : global_word_949 v=[::xorb a b] /\ global_word_953 v=[::andb a b] /\ global_word_2007 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_30_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_30_leaves]. exact E2.
   + cbn [instance_30_leaves]. exact E3.
 - rewrite -instance_30_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_30_leaves]. exact E2.
   + cbn [instance_30_leaves]. exact E3.
 - rewrite -instance_30_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_30_leaves]. exact E2.
   + cbn [instance_30_leaves]. exact E3.
Qed.
Lemma instance_31_bits v (a b:bool)
 (E2:global_word_957 v=[::a])
 (E3:global_word_960 v=[::b])
 : global_word_967 v=[::xorb a b] /\ global_word_971 v=[::andb a b] /\ global_word_2022 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_31_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_31_leaves]. exact E2.
   + cbn [instance_31_leaves]. exact E3.
 - rewrite -instance_31_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_31_leaves]. exact E2.
   + cbn [instance_31_leaves]. exact E3.
 - rewrite -instance_31_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_31_leaves]. exact E2.
   + cbn [instance_31_leaves]. exact E3.
Qed.
Lemma instance_32_bits v (a b:bool)
 (E2:global_word_975 v=[::a])
 (E3:global_word_978 v=[::b])
 : global_word_985 v=[::xorb a b] /\ global_word_989 v=[::andb a b] /\ global_word_2037 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_32_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_32_leaves]. exact E2.
   + cbn [instance_32_leaves]. exact E3.
 - rewrite -instance_32_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_32_leaves]. exact E2.
   + cbn [instance_32_leaves]. exact E3.
 - rewrite -instance_32_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_32_leaves]. exact E2.
   + cbn [instance_32_leaves]. exact E3.
Qed.
Lemma instance_33_bits v (a b:bool)
 (E2:global_word_993 v=[::a])
 (E3:global_word_996 v=[::b])
 : global_word_1003 v=[::xorb a b] /\ global_word_1007 v=[::andb a b] /\ global_word_2052 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_33_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_33_leaves]. exact E2.
   + cbn [instance_33_leaves]. exact E3.
 - rewrite -instance_33_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_33_leaves]. exact E2.
   + cbn [instance_33_leaves]. exact E3.
 - rewrite -instance_33_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_33_leaves]. exact E2.
   + cbn [instance_33_leaves]. exact E3.
Qed.
Lemma instance_34_bits v (a b:bool)
 (E2:global_word_1011 v=[::a])
 (E3:global_word_1014 v=[::b])
 : global_word_1021 v=[::xorb a b] /\ global_word_1025 v=[::andb a b] /\ global_word_2067 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_34_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_34_leaves]. exact E2.
   + cbn [instance_34_leaves]. exact E3.
 - rewrite -instance_34_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_34_leaves]. exact E2.
   + cbn [instance_34_leaves]. exact E3.
 - rewrite -instance_34_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_34_leaves]. exact E2.
   + cbn [instance_34_leaves]. exact E3.
Qed.
Lemma instance_35_bits v (a b:bool)
 (E2:global_word_1029 v=[::a])
 (E3:global_word_1032 v=[::b])
 : global_word_1039 v=[::xorb a b] /\ global_word_1043 v=[::andb a b] /\ global_word_2082 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_35_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_35_leaves]. exact E2.
   + cbn [instance_35_leaves]. exact E3.
 - rewrite -instance_35_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_35_leaves]. exact E2.
   + cbn [instance_35_leaves]. exact E3.
 - rewrite -instance_35_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_35_leaves]. exact E2.
   + cbn [instance_35_leaves]. exact E3.
Qed.
Lemma instance_36_bits v (a b:bool)
 (E2:global_word_1047 v=[::a])
 (E3:global_word_1050 v=[::b])
 : global_word_1057 v=[::xorb a b] /\ global_word_1061 v=[::andb a b] /\ global_word_2097 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_36_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_36_leaves]. exact E2.
   + cbn [instance_36_leaves]. exact E3.
 - rewrite -instance_36_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_36_leaves]. exact E2.
   + cbn [instance_36_leaves]. exact E3.
 - rewrite -instance_36_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_36_leaves]. exact E2.
   + cbn [instance_36_leaves]. exact E3.
Qed.
Lemma instance_37_bits v (a b c:bool)
 (E2:global_word_1068 v=[::a])
 (E3:global_word_1071 v=[::b])
 (E4:global_word_1065 v=[::c])
 : global_word_1081 v=[::fa_sum a b c] /\ global_word_1085 v=[::fa_carry a b c] /\ global_word_2115 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_37_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_37_leaves]. exact E2.
   + cbn [instance_37_leaves]. exact E3.
   + cbn [instance_37_leaves]. exact E4.
 - rewrite -instance_37_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_37_leaves]. exact E2.
   + cbn [instance_37_leaves]. exact E3.
   + cbn [instance_37_leaves]. exact E4.
 - rewrite -instance_37_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_37_leaves]. exact E2.
   + cbn [instance_37_leaves]. exact E3.
   + cbn [instance_37_leaves]. exact E4.
Qed.
Lemma instance_38_bits v (a b c:bool)
 (E2:global_word_1092 v=[::a])
 (E3:global_word_1095 v=[::b])
 (E4:global_word_1089 v=[::c])
 : global_word_1105 v=[::fa_sum a b c] /\ global_word_1109 v=[::fa_carry a b c] /\ global_word_2133 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_38_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_38_leaves]. exact E2.
   + cbn [instance_38_leaves]. exact E3.
   + cbn [instance_38_leaves]. exact E4.
 - rewrite -instance_38_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_38_leaves]. exact E2.
   + cbn [instance_38_leaves]. exact E3.
   + cbn [instance_38_leaves]. exact E4.
 - rewrite -instance_38_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_38_leaves]. exact E2.
   + cbn [instance_38_leaves]. exact E3.
   + cbn [instance_38_leaves]. exact E4.
Qed.
Lemma instance_39_bits v (a b:bool)
 (E2:global_word_1113 v=[::a])
 (E3:global_word_1116 v=[::b])
 : global_word_1123 v=[::xorb a b] /\ global_word_1127 v=[::andb a b] /\ global_word_2148 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_39_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_39_leaves]. exact E2.
   + cbn [instance_39_leaves]. exact E3.
 - rewrite -instance_39_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_39_leaves]. exact E2.
   + cbn [instance_39_leaves]. exact E3.
 - rewrite -instance_39_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_39_leaves]. exact E2.
   + cbn [instance_39_leaves]. exact E3.
Qed.
Lemma instance_40_bits v (a b:bool)
 (E2:global_word_1131 v=[::a])
 (E3:global_word_1134 v=[::b])
 : global_word_1141 v=[::xorb a b] /\ global_word_1145 v=[::andb a b] /\ global_word_2163 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_40_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_40_leaves]. exact E2.
   + cbn [instance_40_leaves]. exact E3.
 - rewrite -instance_40_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_40_leaves]. exact E2.
   + cbn [instance_40_leaves]. exact E3.
 - rewrite -instance_40_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_40_leaves]. exact E2.
   + cbn [instance_40_leaves]. exact E3.
Qed.
Lemma instance_41_bits v (a b:bool)
 (E2:global_word_1149 v=[::a])
 (E3:global_word_1152 v=[::b])
 : global_word_1159 v=[::xorb a b] /\ global_word_1163 v=[::andb a b] /\ global_word_2178 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_41_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_41_leaves]. exact E2.
   + cbn [instance_41_leaves]. exact E3.
 - rewrite -instance_41_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_41_leaves]. exact E2.
   + cbn [instance_41_leaves]. exact E3.
 - rewrite -instance_41_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_41_leaves]. exact E2.
   + cbn [instance_41_leaves]. exact E3.
Qed.
Lemma instance_42_bits v (a b:bool)
 (E2:global_word_1167 v=[::a])
 (E3:global_word_1170 v=[::b])
 : global_word_1177 v=[::xorb a b] /\ global_word_1181 v=[::andb a b] /\ global_word_2193 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_42_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_42_leaves]. exact E2.
   + cbn [instance_42_leaves]. exact E3.
 - rewrite -instance_42_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_42_leaves]. exact E2.
   + cbn [instance_42_leaves]. exact E3.
 - rewrite -instance_42_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_42_leaves]. exact E2.
   + cbn [instance_42_leaves]. exact E3.
Qed.
Lemma instance_43_bits v (a b c:bool)
 (E2:global_word_1188 v=[::a])
 (E3:global_word_1191 v=[::b])
 (E4:global_word_1185 v=[::c])
 : global_word_1201 v=[::fa_sum a b c] /\ global_word_1205 v=[::fa_carry a b c] /\ global_word_2211 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_43_word_5.
   apply (abstract_child1_5 _ a b c).
   + cbn [instance_43_leaves]. exact E2.
   + cbn [instance_43_leaves]. exact E3.
   + cbn [instance_43_leaves]. exact E4.
 - rewrite -instance_43_word_6.
   apply (abstract_child1_6 _ a b c).
   + cbn [instance_43_leaves]. exact E2.
   + cbn [instance_43_leaves]. exact E3.
   + cbn [instance_43_leaves]. exact E4.
 - rewrite -instance_43_word_19.
   apply (abstract_child1_19 _ a b c).
   + cbn [instance_43_leaves]. exact E2.
   + cbn [instance_43_leaves]. exact E3.
   + cbn [instance_43_leaves]. exact E4.
Qed.
Lemma instance_44_bits v (a b:bool)
 (E2:global_word_1209 v=[::a])
 (E3:global_word_1212 v=[::b])
 : global_word_1219 v=[::xorb a b] /\ global_word_1223 v=[::andb a b] /\ global_word_2226 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_44_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_44_leaves]. exact E2.
   + cbn [instance_44_leaves]. exact E3.
 - rewrite -instance_44_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_44_leaves]. exact E2.
   + cbn [instance_44_leaves]. exact E3.
 - rewrite -instance_44_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_44_leaves]. exact E2.
   + cbn [instance_44_leaves]. exact E3.
Qed.
Lemma instance_45_bits v (a b:bool)
 (E2:global_word_1227 v=[::a])
 (E3:global_word_1230 v=[::b])
 : global_word_1237 v=[::xorb a b] /\ global_word_1241 v=[::andb a b] /\ global_word_2241 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_45_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_45_leaves]. exact E2.
   + cbn [instance_45_leaves]. exact E3.
 - rewrite -instance_45_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_45_leaves]. exact E2.
   + cbn [instance_45_leaves]. exact E3.
 - rewrite -instance_45_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_45_leaves]. exact E2.
   + cbn [instance_45_leaves]. exact E3.
Qed.
Lemma instance_46_bits v (a b:bool)
 (E2:global_word_1245 v=[::a])
 (E3:global_word_1248 v=[::b])
 : global_word_1255 v=[::xorb a b] /\ global_word_1259 v=[::andb a b] /\ global_word_2256 v=[::true].
Proof.
 repeat split.
 - rewrite -instance_46_word_4.
   apply (abstract_child0_4 _ a b).
   + cbn [instance_46_leaves]. exact E2.
   + cbn [instance_46_leaves]. exact E3.
 - rewrite -instance_46_word_5.
   apply (abstract_child0_5 _ a b).
   + cbn [instance_46_leaves]. exact E2.
   + cbn [instance_46_leaves]. exact E3.
 - rewrite -instance_46_word_15.
   apply (abstract_child0_15 _ a b).
   + cbn [instance_46_leaves]. exact E2.
   + cbn [instance_46_leaves]. exact E3.
Qed.

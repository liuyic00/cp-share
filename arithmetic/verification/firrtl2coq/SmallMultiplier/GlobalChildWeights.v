From Coq Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalChildBits GlobalAliases Compressors.
Local Open Scope Z_scope.
Lemma instance_1_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_279 v) + to_Zpos (global_word_282 v) = 1 * to_Zpos (global_word_289 v) + 2 * to_Zpos (global_word_293 v).
Proof.
 destruct (one_bit_form _ (global_size_279 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_282 v sizes)) as [b Eb].
 destruct (instance_1_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_1_assert v (sizes:global_leaf_sizes v) : global_word_1379 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_279 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_282 v sizes)) as [b Eb].
 destruct (instance_1_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_2_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_297 v) + to_Zpos (global_word_300 v) = 1 * to_Zpos (global_word_307 v) + 2 * to_Zpos (global_word_311 v).
Proof.
 destruct (one_bit_form _ (global_size_297 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_300 v sizes)) as [b Eb].
 destruct (instance_2_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_2_assert v (sizes:global_leaf_sizes v) : global_word_1394 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_297 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_300 v sizes)) as [b Eb].
 destruct (instance_2_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_3_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_318 v) + to_Zpos (global_word_321 v) + to_Zpos (global_word_315 v) = 1 * to_Zpos (global_word_331 v) + 2 * to_Zpos (global_word_335 v).
Proof.
 destruct (one_bit_form _ (global_size_318 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_321 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_315 v sizes)) as [c Ec].
 destruct (instance_3_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_3_assert v (sizes:global_leaf_sizes v) : global_word_1412 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_318 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_321 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_315 v sizes)) as [c Ec].
 destruct (instance_3_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_4_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_342 v) + to_Zpos (global_word_345 v) + to_Zpos (global_word_339 v) = 1 * to_Zpos (global_word_355 v) + 2 * to_Zpos (global_word_359 v).
Proof.
 destruct (one_bit_form _ (global_size_342 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_345 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_339 v sizes)) as [c Ec].
 destruct (instance_4_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_4_assert v (sizes:global_leaf_sizes v) : global_word_1430 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_342 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_345 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_339 v sizes)) as [c Ec].
 destruct (instance_4_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_5_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_374 v) + to_Zpos (global_word_379 v) + to_Zpos (global_word_369 v) + to_Zpos (global_word_398 v) + to_Zpos (global_word_363 v) = 1 * to_Zpos (global_word_414 v) + 2 * to_Zpos (global_word_421 v) + 2 * to_Zpos (global_word_428 v).
Proof.
 destruct (one_bit_form _ (global_size_374 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_379 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_369 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_398 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_363 v sizes)) as [e Ee].
 destruct (instance_5_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_5_assert v (sizes:global_leaf_sizes v) : global_word_1458 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_374 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_379 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_369 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_398 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_363 v sizes)) as [e Ee].
 destruct (instance_5_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_6_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_376 v) + to_Zpos (global_word_381 v) + to_Zpos (global_word_371 v) = 1 * to_Zpos (global_word_391 v) + 2 * to_Zpos (global_word_418 v).
Proof.
 destruct (one_bit_form _ (global_size_376 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_381 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_371 v sizes)) as [c Ec].
 destruct (instance_6_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_6_assert v (sizes:global_leaf_sizes v) : global_word_1480 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_376 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_381 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_371 v sizes)) as [c Ec].
 destruct (instance_6_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_7_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_395 v) + to_Zpos (global_word_401 v) + to_Zpos (global_word_366 v) = 1 * to_Zpos (global_word_411 v) + 2 * to_Zpos (global_word_425 v).
Proof.
 destruct (one_bit_form _ (global_size_395 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_401 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_366 v sizes)) as [c Ec].
 destruct (instance_7_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_7_assert v (sizes:global_leaf_sizes v) : global_word_1498 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_395 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_401 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_366 v sizes)) as [c Ec].
 destruct (instance_7_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_8_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_443 v) + to_Zpos (global_word_448 v) + to_Zpos (global_word_438 v) + to_Zpos (global_word_467 v) + to_Zpos (global_word_432 v) = 1 * to_Zpos (global_word_483 v) + 2 * to_Zpos (global_word_490 v) + 2 * to_Zpos (global_word_497 v).
Proof.
 destruct (one_bit_form _ (global_size_443 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_448 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_438 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_467 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_432 v sizes)) as [e Ee].
 destruct (instance_8_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_8_assert v (sizes:global_leaf_sizes v) : global_word_1526 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_443 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_448 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_438 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_467 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_432 v sizes)) as [e Ee].
 destruct (instance_8_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_9_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_445 v) + to_Zpos (global_word_450 v) + to_Zpos (global_word_440 v) = 1 * to_Zpos (global_word_460 v) + 2 * to_Zpos (global_word_487 v).
Proof.
 destruct (one_bit_form _ (global_size_445 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_450 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_440 v sizes)) as [c Ec].
 destruct (instance_9_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_9_assert v (sizes:global_leaf_sizes v) : global_word_1548 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_445 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_450 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_440 v sizes)) as [c Ec].
 destruct (instance_9_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_10_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_464 v) + to_Zpos (global_word_470 v) + to_Zpos (global_word_435 v) = 1 * to_Zpos (global_word_480 v) + 2 * to_Zpos (global_word_494 v).
Proof.
 destruct (one_bit_form _ (global_size_464 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_470 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_435 v sizes)) as [c Ec].
 destruct (instance_10_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_10_assert v (sizes:global_leaf_sizes v) : global_word_1566 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_464 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_470 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_435 v sizes)) as [c Ec].
 destruct (instance_10_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_11_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_512 v) + to_Zpos (global_word_517 v) + to_Zpos (global_word_507 v) + to_Zpos (global_word_536 v) + to_Zpos (global_word_501 v) = 1 * to_Zpos (global_word_552 v) + 2 * to_Zpos (global_word_559 v) + 2 * to_Zpos (global_word_566 v).
Proof.
 destruct (one_bit_form _ (global_size_512 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_517 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_507 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_536 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_501 v sizes)) as [e Ee].
 destruct (instance_11_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_11_assert v (sizes:global_leaf_sizes v) : global_word_1594 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_512 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_517 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_507 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_536 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_501 v sizes)) as [e Ee].
 destruct (instance_11_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_12_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_514 v) + to_Zpos (global_word_519 v) + to_Zpos (global_word_509 v) = 1 * to_Zpos (global_word_529 v) + 2 * to_Zpos (global_word_556 v).
Proof.
 destruct (one_bit_form _ (global_size_514 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_519 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_509 v sizes)) as [c Ec].
 destruct (instance_12_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_12_assert v (sizes:global_leaf_sizes v) : global_word_1616 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_514 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_519 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_509 v sizes)) as [c Ec].
 destruct (instance_12_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_13_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_533 v) + to_Zpos (global_word_539 v) + to_Zpos (global_word_504 v) = 1 * to_Zpos (global_word_549 v) + 2 * to_Zpos (global_word_563 v).
Proof.
 destruct (one_bit_form _ (global_size_533 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_539 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_504 v sizes)) as [c Ec].
 destruct (instance_13_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_13_assert v (sizes:global_leaf_sizes v) : global_word_1634 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_533 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_539 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_504 v sizes)) as [c Ec].
 destruct (instance_13_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_14_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_581 v) + to_Zpos (global_word_586 v) + to_Zpos (global_word_576 v) + to_Zpos (global_word_605 v) + to_Zpos (global_word_570 v) = 1 * to_Zpos (global_word_621 v) + 2 * to_Zpos (global_word_628 v) + 2 * to_Zpos (global_word_635 v).
Proof.
 destruct (one_bit_form _ (global_size_581 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_586 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_576 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_605 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_570 v sizes)) as [e Ee].
 destruct (instance_14_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_14_assert v (sizes:global_leaf_sizes v) : global_word_1662 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_581 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_586 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_576 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_605 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_570 v sizes)) as [e Ee].
 destruct (instance_14_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_15_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_583 v) + to_Zpos (global_word_588 v) + to_Zpos (global_word_578 v) = 1 * to_Zpos (global_word_598 v) + 2 * to_Zpos (global_word_625 v).
Proof.
 destruct (one_bit_form _ (global_size_583 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_588 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_578 v sizes)) as [c Ec].
 destruct (instance_15_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_15_assert v (sizes:global_leaf_sizes v) : global_word_1684 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_583 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_588 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_578 v sizes)) as [c Ec].
 destruct (instance_15_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_16_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_602 v) + to_Zpos (global_word_608 v) + to_Zpos (global_word_573 v) = 1 * to_Zpos (global_word_618 v) + 2 * to_Zpos (global_word_632 v).
Proof.
 destruct (one_bit_form _ (global_size_602 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_608 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_573 v sizes)) as [c Ec].
 destruct (instance_16_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_16_assert v (sizes:global_leaf_sizes v) : global_word_1702 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_602 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_608 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_573 v sizes)) as [c Ec].
 destruct (instance_16_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_17_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_650 v) + to_Zpos (global_word_655 v) + to_Zpos (global_word_645 v) + to_Zpos (global_word_674 v) + to_Zpos (global_word_639 v) = 1 * to_Zpos (global_word_690 v) + 2 * to_Zpos (global_word_697 v) + 2 * to_Zpos (global_word_704 v).
Proof.
 destruct (one_bit_form _ (global_size_650 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_655 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_645 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_674 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_639 v sizes)) as [e Ee].
 destruct (instance_17_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_17_assert v (sizes:global_leaf_sizes v) : global_word_1730 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_650 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_655 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_645 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_674 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_639 v sizes)) as [e Ee].
 destruct (instance_17_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_18_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_652 v) + to_Zpos (global_word_657 v) + to_Zpos (global_word_647 v) = 1 * to_Zpos (global_word_667 v) + 2 * to_Zpos (global_word_694 v).
Proof.
 destruct (one_bit_form _ (global_size_652 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_657 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_647 v sizes)) as [c Ec].
 destruct (instance_18_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_18_assert v (sizes:global_leaf_sizes v) : global_word_1752 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_652 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_657 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_647 v sizes)) as [c Ec].
 destruct (instance_18_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_19_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_671 v) + to_Zpos (global_word_677 v) + to_Zpos (global_word_642 v) = 1 * to_Zpos (global_word_687 v) + 2 * to_Zpos (global_word_701 v).
Proof.
 destruct (one_bit_form _ (global_size_671 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_677 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_642 v sizes)) as [c Ec].
 destruct (instance_19_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_19_assert v (sizes:global_leaf_sizes v) : global_word_1770 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_671 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_677 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_642 v sizes)) as [c Ec].
 destruct (instance_19_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_20_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_719 v) + to_Zpos (global_word_724 v) + to_Zpos (global_word_714 v) + to_Zpos (global_word_743 v) + to_Zpos (global_word_708 v) = 1 * to_Zpos (global_word_759 v) + 2 * to_Zpos (global_word_766 v) + 2 * to_Zpos (global_word_773 v).
Proof.
 destruct (one_bit_form _ (global_size_719 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_724 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_714 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_743 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_708 v sizes)) as [e Ee].
 destruct (instance_20_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_20_assert v (sizes:global_leaf_sizes v) : global_word_1798 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_719 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_724 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_714 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_743 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_708 v sizes)) as [e Ee].
 destruct (instance_20_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_21_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_721 v) + to_Zpos (global_word_726 v) + to_Zpos (global_word_716 v) = 1 * to_Zpos (global_word_736 v) + 2 * to_Zpos (global_word_763 v).
Proof.
 destruct (one_bit_form _ (global_size_721 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_726 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_716 v sizes)) as [c Ec].
 destruct (instance_21_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_21_assert v (sizes:global_leaf_sizes v) : global_word_1820 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_721 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_726 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_716 v sizes)) as [c Ec].
 destruct (instance_21_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_22_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_740 v) + to_Zpos (global_word_746 v) + to_Zpos (global_word_711 v) = 1 * to_Zpos (global_word_756 v) + 2 * to_Zpos (global_word_770 v).
Proof.
 destruct (one_bit_form _ (global_size_740 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_746 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_711 v sizes)) as [c Ec].
 destruct (instance_22_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_22_assert v (sizes:global_leaf_sizes v) : global_word_1838 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_740 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_746 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_711 v sizes)) as [c Ec].
 destruct (instance_22_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_23_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_788 v) + to_Zpos (global_word_793 v) + to_Zpos (global_word_783 v) + to_Zpos (global_word_812 v) + to_Zpos (global_word_777 v) = 1 * to_Zpos (global_word_828 v) + 2 * to_Zpos (global_word_835 v) + 2 * to_Zpos (global_word_842 v).
Proof.
 destruct (one_bit_form _ (global_size_788 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_793 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_783 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_812 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_777 v sizes)) as [e Ee].
 destruct (instance_23_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_23_assert v (sizes:global_leaf_sizes v) : global_word_1866 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_788 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_793 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_783 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_812 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_777 v sizes)) as [e Ee].
 destruct (instance_23_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_24_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_790 v) + to_Zpos (global_word_795 v) + to_Zpos (global_word_785 v) = 1 * to_Zpos (global_word_805 v) + 2 * to_Zpos (global_word_832 v).
Proof.
 destruct (one_bit_form _ (global_size_790 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_795 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_785 v sizes)) as [c Ec].
 destruct (instance_24_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_24_assert v (sizes:global_leaf_sizes v) : global_word_1888 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_790 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_795 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_785 v sizes)) as [c Ec].
 destruct (instance_24_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_25_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_809 v) + to_Zpos (global_word_815 v) + to_Zpos (global_word_780 v) = 1 * to_Zpos (global_word_825 v) + 2 * to_Zpos (global_word_839 v).
Proof.
 destruct (one_bit_form _ (global_size_809 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_815 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_780 v sizes)) as [c Ec].
 destruct (instance_25_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_25_assert v (sizes:global_leaf_sizes v) : global_word_1906 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_809 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_815 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_780 v sizes)) as [c Ec].
 destruct (instance_25_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_26_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_857 v) + to_Zpos (global_word_862 v) + to_Zpos (global_word_852 v) + to_Zpos (global_word_881 v) + to_Zpos (global_word_846 v) = 1 * to_Zpos (global_word_897 v) + 2 * to_Zpos (global_word_904 v) + 2 * to_Zpos (global_word_911 v).
Proof.
 destruct (one_bit_form _ (global_size_857 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_862 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_852 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_881 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_846 v sizes)) as [e Ee].
 destruct (instance_26_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]].
 rewrite Ea Eb Ec Ed Ee Out0 Out1 Out2.
 destruct a,b,c,d,e; reflexivity.
Qed.
Lemma instance_26_assert v (sizes:global_leaf_sizes v) : global_word_1934 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_857 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_862 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_852 v sizes)) as [c Ec].
 destruct (one_bit_form _ (global_size_881 v sizes)) as [d Ed].
 destruct (one_bit_form _ (global_size_846 v sizes)) as [e Ee].
 destruct (instance_26_bits v a b c d e Ea Eb Ec Ed Ee) as [Out0 [ Out1 [ Out2 Assert]]]. exact Assert.
Qed.
Lemma instance_27_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_859 v) + to_Zpos (global_word_864 v) + to_Zpos (global_word_854 v) = 1 * to_Zpos (global_word_874 v) + 2 * to_Zpos (global_word_901 v).
Proof.
 destruct (one_bit_form _ (global_size_859 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_864 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_854 v sizes)) as [c Ec].
 destruct (instance_27_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_27_assert v (sizes:global_leaf_sizes v) : global_word_1956 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_859 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_864 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_854 v sizes)) as [c Ec].
 destruct (instance_27_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_28_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_878 v) + to_Zpos (global_word_884 v) + to_Zpos (global_word_849 v) = 1 * to_Zpos (global_word_894 v) + 2 * to_Zpos (global_word_908 v).
Proof.
 destruct (one_bit_form _ (global_size_878 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_884 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_849 v sizes)) as [c Ec].
 destruct (instance_28_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_28_assert v (sizes:global_leaf_sizes v) : global_word_1974 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_878 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_884 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_849 v sizes)) as [c Ec].
 destruct (instance_28_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_29_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_918 v) + to_Zpos (global_word_921 v) + to_Zpos (global_word_915 v) = 1 * to_Zpos (global_word_931 v) + 2 * to_Zpos (global_word_935 v).
Proof.
 destruct (one_bit_form _ (global_size_918 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_921 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_915 v sizes)) as [c Ec].
 destruct (instance_29_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_29_assert v (sizes:global_leaf_sizes v) : global_word_1992 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_918 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_921 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_915 v sizes)) as [c Ec].
 destruct (instance_29_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_30_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_939 v) + to_Zpos (global_word_942 v) = 1 * to_Zpos (global_word_949 v) + 2 * to_Zpos (global_word_953 v).
Proof.
 destruct (one_bit_form _ (global_size_939 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_942 v sizes)) as [b Eb].
 destruct (instance_30_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_30_assert v (sizes:global_leaf_sizes v) : global_word_2007 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_939 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_942 v sizes)) as [b Eb].
 destruct (instance_30_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_31_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_957 v) + to_Zpos (global_word_960 v) = 1 * to_Zpos (global_word_967 v) + 2 * to_Zpos (global_word_971 v).
Proof.
 destruct (one_bit_form _ (global_size_957 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_960 v sizes)) as [b Eb].
 destruct (instance_31_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_31_assert v (sizes:global_leaf_sizes v) : global_word_2022 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_957 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_960 v sizes)) as [b Eb].
 destruct (instance_31_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_32_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_975 v) + to_Zpos (global_word_978 v) = 1 * to_Zpos (global_word_985 v) + 2 * to_Zpos (global_word_989 v).
Proof.
 destruct (one_bit_form _ (global_size_975 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_978 v sizes)) as [b Eb].
 destruct (instance_32_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_32_assert v (sizes:global_leaf_sizes v) : global_word_2037 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_975 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_978 v sizes)) as [b Eb].
 destruct (instance_32_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_33_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_993 v) + to_Zpos (global_word_996 v) = 1 * to_Zpos (global_word_1003 v) + 2 * to_Zpos (global_word_1007 v).
Proof.
 destruct (one_bit_form _ (global_size_993 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_996 v sizes)) as [b Eb].
 destruct (instance_33_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_33_assert v (sizes:global_leaf_sizes v) : global_word_2052 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_993 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_996 v sizes)) as [b Eb].
 destruct (instance_33_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_34_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1011 v) + to_Zpos (global_word_1014 v) = 1 * to_Zpos (global_word_1021 v) + 2 * to_Zpos (global_word_1025 v).
Proof.
 destruct (one_bit_form _ (global_size_1011 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1014 v sizes)) as [b Eb].
 destruct (instance_34_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_34_assert v (sizes:global_leaf_sizes v) : global_word_2067 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1011 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1014 v sizes)) as [b Eb].
 destruct (instance_34_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_35_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1029 v) + to_Zpos (global_word_1032 v) = 1 * to_Zpos (global_word_1039 v) + 2 * to_Zpos (global_word_1043 v).
Proof.
 destruct (one_bit_form _ (global_size_1029 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1032 v sizes)) as [b Eb].
 destruct (instance_35_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_35_assert v (sizes:global_leaf_sizes v) : global_word_2082 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1029 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1032 v sizes)) as [b Eb].
 destruct (instance_35_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_36_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1047 v) + to_Zpos (global_word_1050 v) = 1 * to_Zpos (global_word_1057 v) + 2 * to_Zpos (global_word_1061 v).
Proof.
 destruct (one_bit_form _ (global_size_1047 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1050 v sizes)) as [b Eb].
 destruct (instance_36_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_36_assert v (sizes:global_leaf_sizes v) : global_word_2097 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1047 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1050 v sizes)) as [b Eb].
 destruct (instance_36_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_37_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1068 v) + to_Zpos (global_word_1071 v) + to_Zpos (global_word_1065 v) = 1 * to_Zpos (global_word_1081 v) + 2 * to_Zpos (global_word_1085 v).
Proof.
 destruct (one_bit_form _ (global_size_1068 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1071 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_1065 v sizes)) as [c Ec].
 destruct (instance_37_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_37_assert v (sizes:global_leaf_sizes v) : global_word_2115 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1068 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1071 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_1065 v sizes)) as [c Ec].
 destruct (instance_37_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_38_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1092 v) + to_Zpos (global_word_1095 v) + to_Zpos (global_word_1089 v) = 1 * to_Zpos (global_word_1105 v) + 2 * to_Zpos (global_word_1109 v).
Proof.
 destruct (one_bit_form _ (global_size_1092 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1095 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_1089 v sizes)) as [c Ec].
 destruct (instance_38_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_38_assert v (sizes:global_leaf_sizes v) : global_word_2133 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1092 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1095 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_1089 v sizes)) as [c Ec].
 destruct (instance_38_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_39_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1113 v) + to_Zpos (global_word_1116 v) = 1 * to_Zpos (global_word_1123 v) + 2 * to_Zpos (global_word_1127 v).
Proof.
 destruct (one_bit_form _ (global_size_1113 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1116 v sizes)) as [b Eb].
 destruct (instance_39_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_39_assert v (sizes:global_leaf_sizes v) : global_word_2148 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1113 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1116 v sizes)) as [b Eb].
 destruct (instance_39_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_40_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1131 v) + to_Zpos (global_word_1134 v) = 1 * to_Zpos (global_word_1141 v) + 2 * to_Zpos (global_word_1145 v).
Proof.
 destruct (one_bit_form _ (global_size_1131 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1134 v sizes)) as [b Eb].
 destruct (instance_40_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_40_assert v (sizes:global_leaf_sizes v) : global_word_2163 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1131 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1134 v sizes)) as [b Eb].
 destruct (instance_40_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_41_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1149 v) + to_Zpos (global_word_1152 v) = 1 * to_Zpos (global_word_1159 v) + 2 * to_Zpos (global_word_1163 v).
Proof.
 destruct (one_bit_form _ (global_size_1149 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1152 v sizes)) as [b Eb].
 destruct (instance_41_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_41_assert v (sizes:global_leaf_sizes v) : global_word_2178 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1149 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1152 v sizes)) as [b Eb].
 destruct (instance_41_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_42_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1167 v) + to_Zpos (global_word_1170 v) = 1 * to_Zpos (global_word_1177 v) + 2 * to_Zpos (global_word_1181 v).
Proof.
 destruct (one_bit_form _ (global_size_1167 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1170 v sizes)) as [b Eb].
 destruct (instance_42_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_42_assert v (sizes:global_leaf_sizes v) : global_word_2193 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1167 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1170 v sizes)) as [b Eb].
 destruct (instance_42_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_43_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1188 v) + to_Zpos (global_word_1191 v) + to_Zpos (global_word_1185 v) = 1 * to_Zpos (global_word_1201 v) + 2 * to_Zpos (global_word_1205 v).
Proof.
 destruct (one_bit_form _ (global_size_1188 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1191 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_1185 v sizes)) as [c Ec].
 destruct (instance_43_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Ec Out0 Out1.
 destruct a,b,c; reflexivity.
Qed.
Lemma instance_43_assert v (sizes:global_leaf_sizes v) : global_word_2211 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1188 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1191 v sizes)) as [b Eb].
 destruct (one_bit_form _ (global_size_1185 v sizes)) as [c Ec].
 destruct (instance_43_bits v a b c Ea Eb Ec) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_44_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1209 v) + to_Zpos (global_word_1212 v) = 1 * to_Zpos (global_word_1219 v) + 2 * to_Zpos (global_word_1223 v).
Proof.
 destruct (one_bit_form _ (global_size_1209 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1212 v sizes)) as [b Eb].
 destruct (instance_44_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_44_assert v (sizes:global_leaf_sizes v) : global_word_2226 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1209 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1212 v sizes)) as [b Eb].
 destruct (instance_44_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_45_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1227 v) + to_Zpos (global_word_1230 v) = 1 * to_Zpos (global_word_1237 v) + 2 * to_Zpos (global_word_1241 v).
Proof.
 destruct (one_bit_form _ (global_size_1227 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1230 v sizes)) as [b Eb].
 destruct (instance_45_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_45_assert v (sizes:global_leaf_sizes v) : global_word_2241 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1227 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1230 v sizes)) as [b Eb].
 destruct (instance_45_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.
Lemma instance_46_weight v (sizes:global_leaf_sizes v) :
to_Zpos (global_word_1245 v) + to_Zpos (global_word_1248 v) = 1 * to_Zpos (global_word_1255 v) + 2 * to_Zpos (global_word_1259 v).
Proof.
 destruct (one_bit_form _ (global_size_1245 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1248 v sizes)) as [b Eb].
 destruct (instance_46_bits v a b Ea Eb) as [Out0 [ Out1 Assert]].
 rewrite Ea Eb Out0 Out1.
 destruct a,b; reflexivity.
Qed.
Lemma instance_46_assert v (sizes:global_leaf_sizes v) : global_word_2256 v=[::true].
Proof.
 destruct (one_bit_form _ (global_size_1245 v sizes)) as [a Ea].
 destruct (one_bit_form _ (global_size_1248 v sizes)) as [b Eb].
 destruct (instance_46_bits v a b Ea Eb) as [Out0 [ Out1 Assert]]. exact Assert.
Qed.

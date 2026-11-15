From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import GlobalStable GlobalWidths GlobalAliases GlobalBitWires GlobalChildWeights Compression8.
Local Open Scope Z_scope.
Definition global_register_numbers (v:global_leaves) (index:nat) : Z := nth 0 [::
to_Zpos (global_word_3 v);
to_Zpos (global_word_4 v);
to_Zpos (global_word_5 v);
to_Zpos (global_word_6 v);
to_Zpos (global_word_7 v);
to_Zpos (global_word_8 v);
to_Zpos (global_word_9 v);
to_Zpos (global_word_10 v);
to_Zpos (global_word_11 v);
to_Zpos (global_word_12 v);
to_Zpos (global_word_13 v);
to_Zpos (global_word_14 v);
to_Zpos (global_word_15 v);
to_Zpos (global_word_16 v);
to_Zpos (global_word_17 v);
to_Zpos (global_word_18 v);
to_Zpos (global_word_19 v);
to_Zpos (global_word_20 v);
to_Zpos (global_word_21 v);
to_Zpos (global_word_22 v);
to_Zpos (global_word_23 v);
to_Zpos (global_word_24 v);
to_Zpos (global_word_25 v);
to_Zpos (global_word_26 v);
to_Zpos (global_word_27 v);
to_Zpos (global_word_28 v);
to_Zpos (global_word_29 v);
to_Zpos (global_word_30 v);
to_Zpos (global_word_31 v);
to_Zpos (global_word_32 v);
to_Zpos (global_word_33 v);
to_Zpos (global_word_34 v);
to_Zpos (global_word_35 v);
to_Zpos (global_word_36 v);
to_Zpos (global_word_37 v);
to_Zpos (global_word_38 v);
to_Zpos (global_word_39 v);
to_Zpos (global_word_40 v);
to_Zpos (global_word_41 v);
to_Zpos (global_word_42 v);
to_Zpos (global_word_43 v);
to_Zpos (global_word_44 v);
to_Zpos (global_word_45 v);
to_Zpos (global_word_46 v);
to_Zpos (global_word_47 v);
to_Zpos (global_word_48 v);
to_Zpos (global_word_49 v);
to_Zpos (global_word_50 v);
to_Zpos (global_word_51 v);
to_Zpos (global_word_52 v);
to_Zpos (global_word_54 v);
to_Zpos (global_word_55 v)] index.
Definition global_compressor_outputs (v:global_leaves) (index bit:nat) : Z := nth 0 (nth [::] [::
[::to_Zpos (global_word_289 v);to_Zpos (global_word_293 v)];
[::to_Zpos (global_word_307 v);to_Zpos (global_word_311 v)];
[::to_Zpos (global_word_331 v);to_Zpos (global_word_335 v)];
[::to_Zpos (global_word_355 v);to_Zpos (global_word_359 v)];
[::to_Zpos (global_word_414 v);to_Zpos (global_word_421 v);to_Zpos (global_word_428 v)];
[::to_Zpos (global_word_483 v);to_Zpos (global_word_490 v);to_Zpos (global_word_497 v)];
[::to_Zpos (global_word_552 v);to_Zpos (global_word_559 v);to_Zpos (global_word_566 v)];
[::to_Zpos (global_word_621 v);to_Zpos (global_word_628 v);to_Zpos (global_word_635 v)];
[::to_Zpos (global_word_690 v);to_Zpos (global_word_697 v);to_Zpos (global_word_704 v)];
[::to_Zpos (global_word_759 v);to_Zpos (global_word_766 v);to_Zpos (global_word_773 v)];
[::to_Zpos (global_word_828 v);to_Zpos (global_word_835 v);to_Zpos (global_word_842 v)];
[::to_Zpos (global_word_897 v);to_Zpos (global_word_904 v);to_Zpos (global_word_911 v)];
[::to_Zpos (global_word_931 v);to_Zpos (global_word_935 v)];
[::to_Zpos (global_word_949 v);to_Zpos (global_word_953 v)];
[::to_Zpos (global_word_967 v);to_Zpos (global_word_971 v)];
[::to_Zpos (global_word_985 v);to_Zpos (global_word_989 v)];
[::to_Zpos (global_word_1003 v);to_Zpos (global_word_1007 v)];
[::to_Zpos (global_word_1021 v);to_Zpos (global_word_1025 v)];
[::to_Zpos (global_word_1039 v);to_Zpos (global_word_1043 v)];
[::to_Zpos (global_word_1057 v);to_Zpos (global_word_1061 v)];
[::to_Zpos (global_word_1081 v);to_Zpos (global_word_1085 v)];
[::to_Zpos (global_word_1105 v);to_Zpos (global_word_1109 v)];
[::to_Zpos (global_word_1123 v);to_Zpos (global_word_1127 v)];
[::to_Zpos (global_word_1141 v);to_Zpos (global_word_1145 v)];
[::to_Zpos (global_word_1159 v);to_Zpos (global_word_1163 v)];
[::to_Zpos (global_word_1177 v);to_Zpos (global_word_1181 v)];
[::to_Zpos (global_word_1201 v);to_Zpos (global_word_1205 v)];
[::to_Zpos (global_word_1219 v);to_Zpos (global_word_1223 v)];
[::to_Zpos (global_word_1237 v);to_Zpos (global_word_1241 v)];
[::to_Zpos (global_word_1255 v);to_Zpos (global_word_1259 v)]] index) bit.
Lemma global_compressor_contracts v (sizes:global_leaf_sizes v) : compressor_contracts (global_register_numbers v) (global_compressor_outputs v).
Proof.
 unfold compressor_contracts. repeat split.
 - have H := instance_1_weight v sizes.
   rewrite ?wire_alias_279 ?wire_alias_278 ?wire_alias_282 ?wire_alias_281 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_2_weight v sizes.
   rewrite ?wire_alias_297 ?wire_alias_296 ?wire_alias_300 ?wire_alias_299 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_3_weight v sizes.
   rewrite ?wire_alias_318 ?wire_alias_317 ?wire_alias_321 ?wire_alias_320 ?wire_alias_315 ?wire_alias_314 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_4_weight v sizes.
   rewrite ?wire_alias_342 ?wire_alias_341 ?wire_alias_345 ?wire_alias_344 ?wire_alias_339 ?wire_alias_338 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_5_weight v sizes.
   rewrite ?wire_alias_374 ?wire_alias_373 ?wire_alias_379 ?wire_alias_378 ?wire_alias_369 ?wire_alias_368 ?wire_alias_398 ?wire_alias_397 ?wire_alias_363 ?constant_wire_362 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_8_weight v sizes.
   rewrite ?wire_alias_443 ?wire_alias_442 ?wire_alias_448 ?wire_alias_447 ?wire_alias_438 ?wire_alias_437 ?wire_alias_467 ?wire_alias_466 ?wire_alias_432 ?wire_alias_431 ?(bit_wire_423 v sizes) ?wire_alias_422 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_11_weight v sizes.
   rewrite ?wire_alias_512 ?wire_alias_511 ?wire_alias_517 ?wire_alias_516 ?wire_alias_507 ?wire_alias_506 ?wire_alias_536 ?wire_alias_535 ?wire_alias_501 ?wire_alias_500 ?(bit_wire_492 v sizes) ?wire_alias_491 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_14_weight v sizes.
   rewrite ?wire_alias_581 ?wire_alias_580 ?wire_alias_586 ?wire_alias_585 ?wire_alias_576 ?wire_alias_575 ?wire_alias_605 ?wire_alias_604 ?wire_alias_570 ?wire_alias_569 ?(bit_wire_561 v sizes) ?wire_alias_560 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_17_weight v sizes.
   rewrite ?wire_alias_650 ?wire_alias_649 ?wire_alias_655 ?wire_alias_654 ?wire_alias_645 ?wire_alias_644 ?wire_alias_674 ?wire_alias_673 ?wire_alias_639 ?wire_alias_638 ?(bit_wire_630 v sizes) ?wire_alias_629 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_20_weight v sizes.
   rewrite ?wire_alias_719 ?wire_alias_718 ?wire_alias_724 ?wire_alias_723 ?wire_alias_714 ?wire_alias_713 ?wire_alias_743 ?wire_alias_742 ?wire_alias_708 ?wire_alias_707 ?(bit_wire_699 v sizes) ?wire_alias_698 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_23_weight v sizes.
   rewrite ?wire_alias_788 ?wire_alias_787 ?wire_alias_793 ?wire_alias_792 ?wire_alias_783 ?wire_alias_782 ?wire_alias_812 ?wire_alias_811 ?wire_alias_777 ?wire_alias_776 ?(bit_wire_768 v sizes) ?wire_alias_767 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_26_weight v sizes.
   rewrite ?wire_alias_857 ?wire_alias_856 ?wire_alias_862 ?wire_alias_861 ?wire_alias_852 ?wire_alias_851 ?wire_alias_881 ?wire_alias_880 ?wire_alias_846 ?wire_alias_845 ?(bit_wire_837 v sizes) ?wire_alias_836 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_29_weight v sizes.
   rewrite ?wire_alias_918 ?wire_alias_917 ?wire_alias_921 ?wire_alias_920 ?wire_alias_915 ?wire_alias_914 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_30_weight v sizes.
   rewrite ?wire_alias_939 ?wire_alias_938 ?wire_alias_942 ?wire_alias_941 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_31_weight v sizes.
   rewrite ?wire_alias_957 ?wire_alias_956 ?wire_alias_960 ?wire_alias_959 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_32_weight v sizes.
   rewrite ?wire_alias_975 ?wire_alias_974 ?(bit_wire_309 v sizes) ?wire_alias_308 ?wire_alias_978 ?wire_alias_977 ?(bit_wire_295 v sizes) ?wire_alias_294 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_33_weight v sizes.
   rewrite ?wire_alias_993 ?wire_alias_992 ?(bit_wire_333 v sizes) ?wire_alias_332 ?wire_alias_996 ?wire_alias_995 ?(bit_wire_313 v sizes) ?wire_alias_312 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_34_weight v sizes.
   rewrite ?wire_alias_1011 ?wire_alias_1010 ?(bit_wire_357 v sizes) ?wire_alias_356 ?wire_alias_1014 ?wire_alias_1013 ?(bit_wire_337 v sizes) ?wire_alias_336 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_35_weight v sizes.
   rewrite ?wire_alias_1029 ?wire_alias_1028 ?(bit_wire_416 v sizes) ?wire_alias_415 ?wire_alias_1032 ?wire_alias_1031 ?(bit_wire_361 v sizes) ?wire_alias_360 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_36_weight v sizes.
   rewrite ?wire_alias_1047 ?wire_alias_1046 ?(bit_wire_485 v sizes) ?wire_alias_484 ?wire_alias_1050 ?wire_alias_1049 ?(bit_wire_430 v sizes) ?wire_alias_429 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_37_weight v sizes.
   rewrite ?wire_alias_1068 ?wire_alias_1067 ?(bit_wire_554 v sizes) ?wire_alias_553 ?wire_alias_1071 ?wire_alias_1070 ?wire_alias_1065 ?wire_alias_1064 ?(bit_wire_499 v sizes) ?wire_alias_498 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_38_weight v sizes.
   rewrite ?wire_alias_1092 ?wire_alias_1091 ?(bit_wire_623 v sizes) ?wire_alias_622 ?wire_alias_1095 ?wire_alias_1094 ?wire_alias_1089 ?wire_alias_1088 ?(bit_wire_568 v sizes) ?wire_alias_567 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_39_weight v sizes.
   rewrite ?wire_alias_1113 ?wire_alias_1112 ?(bit_wire_692 v sizes) ?wire_alias_691 ?wire_alias_1116 ?wire_alias_1115 ?(bit_wire_637 v sizes) ?wire_alias_636 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_40_weight v sizes.
   rewrite ?wire_alias_1131 ?wire_alias_1130 ?(bit_wire_761 v sizes) ?wire_alias_760 ?wire_alias_1134 ?wire_alias_1133 ?(bit_wire_706 v sizes) ?wire_alias_705 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_41_weight v sizes.
   rewrite ?wire_alias_1149 ?wire_alias_1148 ?(bit_wire_830 v sizes) ?wire_alias_829 ?wire_alias_1152 ?wire_alias_1151 ?(bit_wire_775 v sizes) ?wire_alias_774 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_42_weight v sizes.
   rewrite ?wire_alias_1167 ?wire_alias_1166 ?(bit_wire_899 v sizes) ?wire_alias_898 ?wire_alias_1170 ?wire_alias_1169 ?(bit_wire_844 v sizes) ?wire_alias_843 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_43_weight v sizes.
   rewrite ?wire_alias_1188 ?wire_alias_1187 ?(bit_wire_933 v sizes) ?wire_alias_932 ?wire_alias_1191 ?wire_alias_1190 ?(bit_wire_906 v sizes) ?wire_alias_905 ?wire_alias_1185 ?wire_alias_1184 ?(bit_wire_913 v sizes) ?wire_alias_912 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_44_weight v sizes.
   rewrite ?wire_alias_1209 ?wire_alias_1208 ?(bit_wire_951 v sizes) ?wire_alias_950 ?wire_alias_1212 ?wire_alias_1211 ?(bit_wire_937 v sizes) ?wire_alias_936 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_45_weight v sizes.
   rewrite ?wire_alias_1227 ?wire_alias_1226 ?(bit_wire_969 v sizes) ?wire_alias_968 ?wire_alias_1230 ?wire_alias_1229 ?(bit_wire_955 v sizes) ?wire_alias_954 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
 - have H := instance_46_weight v sizes.
   rewrite ?wire_alias_1245 ?wire_alias_1244 ?wire_alias_1248 ?wire_alias_1247 ?(bit_wire_973 v sizes) ?wire_alias_972 in H.
   try change (to_Zpos [::false]) with 0 in H.
   cbn [global_register_numbers global_compressor_outputs nth]. lia.
Qed.
Lemma global_compression_mod v (sizes:global_leaf_sizes v) :
 output_rows (global_compressor_outputs v) mod 65536 = weighted_registers (global_register_numbers v) mod 65536.
Proof. apply compression_mod. apply global_compressor_contracts. exact sizes. Qed.

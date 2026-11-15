From Coq Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalChildBits GlobalAliases Compressors.
Local Open Scope Z_scope.
Transparent global_word_291.
Lemma bit_wire_291 v (sizes:global_leaf_sizes v) : global_word_291 v=global_word_290 v.
Proof.
 destruct (one_bit_form _ (global_size_290 v sizes)) as [bit E].
 unfold global_word_291, global_closed_291, global_expr_291, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_291.
Transparent global_word_295.
Lemma bit_wire_295 v (sizes:global_leaf_sizes v) : global_word_295 v=global_word_294 v.
Proof.
 destruct (one_bit_form _ (global_size_294 v sizes)) as [bit E].
 unfold global_word_295, global_closed_295, global_expr_295, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_295.
Transparent global_word_309.
Lemma bit_wire_309 v (sizes:global_leaf_sizes v) : global_word_309 v=global_word_308 v.
Proof.
 destruct (one_bit_form _ (global_size_308 v sizes)) as [bit E].
 unfold global_word_309, global_closed_309, global_expr_309, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_309.
Transparent global_word_313.
Lemma bit_wire_313 v (sizes:global_leaf_sizes v) : global_word_313 v=global_word_312 v.
Proof.
 destruct (one_bit_form _ (global_size_312 v sizes)) as [bit E].
 unfold global_word_313, global_closed_313, global_expr_313, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_313.
Transparent global_word_333.
Lemma bit_wire_333 v (sizes:global_leaf_sizes v) : global_word_333 v=global_word_332 v.
Proof.
 destruct (one_bit_form _ (global_size_332 v sizes)) as [bit E].
 unfold global_word_333, global_closed_333, global_expr_333, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_333.
Transparent global_word_337.
Lemma bit_wire_337 v (sizes:global_leaf_sizes v) : global_word_337 v=global_word_336 v.
Proof.
 destruct (one_bit_form _ (global_size_336 v sizes)) as [bit E].
 unfold global_word_337, global_closed_337, global_expr_337, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_337.
Transparent global_word_357.
Lemma bit_wire_357 v (sizes:global_leaf_sizes v) : global_word_357 v=global_word_356 v.
Proof.
 destruct (one_bit_form _ (global_size_356 v sizes)) as [bit E].
 unfold global_word_357, global_closed_357, global_expr_357, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_357.
Transparent global_word_361.
Lemma bit_wire_361 v (sizes:global_leaf_sizes v) : global_word_361 v=global_word_360 v.
Proof.
 destruct (one_bit_form _ (global_size_360 v sizes)) as [bit E].
 unfold global_word_361, global_closed_361, global_expr_361, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_361.
Transparent global_word_416.
Lemma bit_wire_416 v (sizes:global_leaf_sizes v) : global_word_416 v=global_word_415 v.
Proof.
 destruct (one_bit_form _ (global_size_415 v sizes)) as [bit E].
 unfold global_word_416, global_closed_416, global_expr_416, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_416.
Transparent global_word_423.
Lemma bit_wire_423 v (sizes:global_leaf_sizes v) : global_word_423 v=global_word_422 v.
Proof.
 destruct (one_bit_form _ (global_size_422 v sizes)) as [bit E].
 unfold global_word_423, global_closed_423, global_expr_423, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_423.
Transparent global_word_430.
Lemma bit_wire_430 v (sizes:global_leaf_sizes v) : global_word_430 v=global_word_429 v.
Proof.
 destruct (one_bit_form _ (global_size_429 v sizes)) as [bit E].
 unfold global_word_430, global_closed_430, global_expr_430, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_430.
Transparent global_word_485.
Lemma bit_wire_485 v (sizes:global_leaf_sizes v) : global_word_485 v=global_word_484 v.
Proof.
 destruct (one_bit_form _ (global_size_484 v sizes)) as [bit E].
 unfold global_word_485, global_closed_485, global_expr_485, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_485.
Transparent global_word_492.
Lemma bit_wire_492 v (sizes:global_leaf_sizes v) : global_word_492 v=global_word_491 v.
Proof.
 destruct (one_bit_form _ (global_size_491 v sizes)) as [bit E].
 unfold global_word_492, global_closed_492, global_expr_492, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_492.
Transparent global_word_499.
Lemma bit_wire_499 v (sizes:global_leaf_sizes v) : global_word_499 v=global_word_498 v.
Proof.
 destruct (one_bit_form _ (global_size_498 v sizes)) as [bit E].
 unfold global_word_499, global_closed_499, global_expr_499, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_499.
Transparent global_word_554.
Lemma bit_wire_554 v (sizes:global_leaf_sizes v) : global_word_554 v=global_word_553 v.
Proof.
 destruct (one_bit_form _ (global_size_553 v sizes)) as [bit E].
 unfold global_word_554, global_closed_554, global_expr_554, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_554.
Transparent global_word_561.
Lemma bit_wire_561 v (sizes:global_leaf_sizes v) : global_word_561 v=global_word_560 v.
Proof.
 destruct (one_bit_form _ (global_size_560 v sizes)) as [bit E].
 unfold global_word_561, global_closed_561, global_expr_561, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_561.
Transparent global_word_568.
Lemma bit_wire_568 v (sizes:global_leaf_sizes v) : global_word_568 v=global_word_567 v.
Proof.
 destruct (one_bit_form _ (global_size_567 v sizes)) as [bit E].
 unfold global_word_568, global_closed_568, global_expr_568, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_568.
Transparent global_word_623.
Lemma bit_wire_623 v (sizes:global_leaf_sizes v) : global_word_623 v=global_word_622 v.
Proof.
 destruct (one_bit_form _ (global_size_622 v sizes)) as [bit E].
 unfold global_word_623, global_closed_623, global_expr_623, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_623.
Transparent global_word_630.
Lemma bit_wire_630 v (sizes:global_leaf_sizes v) : global_word_630 v=global_word_629 v.
Proof.
 destruct (one_bit_form _ (global_size_629 v sizes)) as [bit E].
 unfold global_word_630, global_closed_630, global_expr_630, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_630.
Transparent global_word_637.
Lemma bit_wire_637 v (sizes:global_leaf_sizes v) : global_word_637 v=global_word_636 v.
Proof.
 destruct (one_bit_form _ (global_size_636 v sizes)) as [bit E].
 unfold global_word_637, global_closed_637, global_expr_637, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_637.
Transparent global_word_692.
Lemma bit_wire_692 v (sizes:global_leaf_sizes v) : global_word_692 v=global_word_691 v.
Proof.
 destruct (one_bit_form _ (global_size_691 v sizes)) as [bit E].
 unfold global_word_692, global_closed_692, global_expr_692, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_692.
Transparent global_word_699.
Lemma bit_wire_699 v (sizes:global_leaf_sizes v) : global_word_699 v=global_word_698 v.
Proof.
 destruct (one_bit_form _ (global_size_698 v sizes)) as [bit E].
 unfold global_word_699, global_closed_699, global_expr_699, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_699.
Transparent global_word_706.
Lemma bit_wire_706 v (sizes:global_leaf_sizes v) : global_word_706 v=global_word_705 v.
Proof.
 destruct (one_bit_form _ (global_size_705 v sizes)) as [bit E].
 unfold global_word_706, global_closed_706, global_expr_706, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_706.
Transparent global_word_761.
Lemma bit_wire_761 v (sizes:global_leaf_sizes v) : global_word_761 v=global_word_760 v.
Proof.
 destruct (one_bit_form _ (global_size_760 v sizes)) as [bit E].
 unfold global_word_761, global_closed_761, global_expr_761, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_761.
Transparent global_word_768.
Lemma bit_wire_768 v (sizes:global_leaf_sizes v) : global_word_768 v=global_word_767 v.
Proof.
 destruct (one_bit_form _ (global_size_767 v sizes)) as [bit E].
 unfold global_word_768, global_closed_768, global_expr_768, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_768.
Transparent global_word_775.
Lemma bit_wire_775 v (sizes:global_leaf_sizes v) : global_word_775 v=global_word_774 v.
Proof.
 destruct (one_bit_form _ (global_size_774 v sizes)) as [bit E].
 unfold global_word_775, global_closed_775, global_expr_775, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_775.
Transparent global_word_830.
Lemma bit_wire_830 v (sizes:global_leaf_sizes v) : global_word_830 v=global_word_829 v.
Proof.
 destruct (one_bit_form _ (global_size_829 v sizes)) as [bit E].
 unfold global_word_830, global_closed_830, global_expr_830, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_830.
Transparent global_word_837.
Lemma bit_wire_837 v (sizes:global_leaf_sizes v) : global_word_837 v=global_word_836 v.
Proof.
 destruct (one_bit_form _ (global_size_836 v sizes)) as [bit E].
 unfold global_word_837, global_closed_837, global_expr_837, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_837.
Transparent global_word_844.
Lemma bit_wire_844 v (sizes:global_leaf_sizes v) : global_word_844 v=global_word_843 v.
Proof.
 destruct (one_bit_form _ (global_size_843 v sizes)) as [bit E].
 unfold global_word_844, global_closed_844, global_expr_844, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_844.
Transparent global_word_899.
Lemma bit_wire_899 v (sizes:global_leaf_sizes v) : global_word_899 v=global_word_898 v.
Proof.
 destruct (one_bit_form _ (global_size_898 v sizes)) as [bit E].
 unfold global_word_899, global_closed_899, global_expr_899, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_899.
Transparent global_word_906.
Lemma bit_wire_906 v (sizes:global_leaf_sizes v) : global_word_906 v=global_word_905 v.
Proof.
 destruct (one_bit_form _ (global_size_905 v sizes)) as [bit E].
 unfold global_word_906, global_closed_906, global_expr_906, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_906.
Transparent global_word_913.
Lemma bit_wire_913 v (sizes:global_leaf_sizes v) : global_word_913 v=global_word_912 v.
Proof.
 destruct (one_bit_form _ (global_size_912 v sizes)) as [bit E].
 unfold global_word_913, global_closed_913, global_expr_913, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_913.
Transparent global_word_933.
Lemma bit_wire_933 v (sizes:global_leaf_sizes v) : global_word_933 v=global_word_932 v.
Proof.
 destruct (one_bit_form _ (global_size_932 v sizes)) as [bit E].
 unfold global_word_933, global_closed_933, global_expr_933, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_933.
Transparent global_word_937.
Lemma bit_wire_937 v (sizes:global_leaf_sizes v) : global_word_937 v=global_word_936 v.
Proof.
 destruct (one_bit_form _ (global_size_936 v sizes)) as [bit E].
 unfold global_word_937, global_closed_937, global_expr_937, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_937.
Transparent global_word_951.
Lemma bit_wire_951 v (sizes:global_leaf_sizes v) : global_word_951 v=global_word_950 v.
Proof.
 destruct (one_bit_form _ (global_size_950 v sizes)) as [bit E].
 unfold global_word_951, global_closed_951, global_expr_951, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_951.
Transparent global_word_955.
Lemma bit_wire_955 v (sizes:global_leaf_sizes v) : global_word_955 v=global_word_954 v.
Proof.
 destruct (one_bit_form _ (global_size_954 v sizes)) as [bit E].
 unfold global_word_955, global_closed_955, global_expr_955, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_955.
Transparent global_word_969.
Lemma bit_wire_969 v (sizes:global_leaf_sizes v) : global_word_969 v=global_word_968 v.
Proof.
 destruct (one_bit_form _ (global_size_968 v sizes)) as [bit E].
 unfold global_word_969, global_closed_969, global_expr_969, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_969.
Transparent global_word_973.
Lemma bit_wire_973 v (sizes:global_leaf_sizes v) : global_word_973 v=global_word_972 v.
Proof.
 destruct (one_bit_form _ (global_size_972 v sizes)) as [bit E].
 unfold global_word_973, global_closed_973, global_expr_973, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_973.
Transparent global_word_987.
Lemma bit_wire_987 v (sizes:global_leaf_sizes v) : global_word_987 v=global_word_986 v.
Proof.
 destruct (one_bit_form _ (global_size_986 v sizes)) as [bit E].
 unfold global_word_987, global_closed_987, global_expr_987, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_987.
Transparent global_word_991.
Lemma bit_wire_991 v (sizes:global_leaf_sizes v) : global_word_991 v=global_word_990 v.
Proof.
 destruct (one_bit_form _ (global_size_990 v sizes)) as [bit E].
 unfold global_word_991, global_closed_991, global_expr_991, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_991.
Transparent global_word_1005.
Lemma bit_wire_1005 v (sizes:global_leaf_sizes v) : global_word_1005 v=global_word_1004 v.
Proof.
 destruct (one_bit_form _ (global_size_1004 v sizes)) as [bit E].
 unfold global_word_1005, global_closed_1005, global_expr_1005, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1005.
Transparent global_word_1009.
Lemma bit_wire_1009 v (sizes:global_leaf_sizes v) : global_word_1009 v=global_word_1008 v.
Proof.
 destruct (one_bit_form _ (global_size_1008 v sizes)) as [bit E].
 unfold global_word_1009, global_closed_1009, global_expr_1009, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1009.
Transparent global_word_1023.
Lemma bit_wire_1023 v (sizes:global_leaf_sizes v) : global_word_1023 v=global_word_1022 v.
Proof.
 destruct (one_bit_form _ (global_size_1022 v sizes)) as [bit E].
 unfold global_word_1023, global_closed_1023, global_expr_1023, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1023.
Transparent global_word_1027.
Lemma bit_wire_1027 v (sizes:global_leaf_sizes v) : global_word_1027 v=global_word_1026 v.
Proof.
 destruct (one_bit_form _ (global_size_1026 v sizes)) as [bit E].
 unfold global_word_1027, global_closed_1027, global_expr_1027, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1027.
Transparent global_word_1041.
Lemma bit_wire_1041 v (sizes:global_leaf_sizes v) : global_word_1041 v=global_word_1040 v.
Proof.
 destruct (one_bit_form _ (global_size_1040 v sizes)) as [bit E].
 unfold global_word_1041, global_closed_1041, global_expr_1041, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1041.
Transparent global_word_1045.
Lemma bit_wire_1045 v (sizes:global_leaf_sizes v) : global_word_1045 v=global_word_1044 v.
Proof.
 destruct (one_bit_form _ (global_size_1044 v sizes)) as [bit E].
 unfold global_word_1045, global_closed_1045, global_expr_1045, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1045.
Transparent global_word_1059.
Lemma bit_wire_1059 v (sizes:global_leaf_sizes v) : global_word_1059 v=global_word_1058 v.
Proof.
 destruct (one_bit_form _ (global_size_1058 v sizes)) as [bit E].
 unfold global_word_1059, global_closed_1059, global_expr_1059, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1059.
Transparent global_word_1063.
Lemma bit_wire_1063 v (sizes:global_leaf_sizes v) : global_word_1063 v=global_word_1062 v.
Proof.
 destruct (one_bit_form _ (global_size_1062 v sizes)) as [bit E].
 unfold global_word_1063, global_closed_1063, global_expr_1063, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1063.
Transparent global_word_1083.
Lemma bit_wire_1083 v (sizes:global_leaf_sizes v) : global_word_1083 v=global_word_1082 v.
Proof.
 destruct (one_bit_form _ (global_size_1082 v sizes)) as [bit E].
 unfold global_word_1083, global_closed_1083, global_expr_1083, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1083.
Transparent global_word_1087.
Lemma bit_wire_1087 v (sizes:global_leaf_sizes v) : global_word_1087 v=global_word_1086 v.
Proof.
 destruct (one_bit_form _ (global_size_1086 v sizes)) as [bit E].
 unfold global_word_1087, global_closed_1087, global_expr_1087, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1087.
Transparent global_word_1107.
Lemma bit_wire_1107 v (sizes:global_leaf_sizes v) : global_word_1107 v=global_word_1106 v.
Proof.
 destruct (one_bit_form _ (global_size_1106 v sizes)) as [bit E].
 unfold global_word_1107, global_closed_1107, global_expr_1107, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1107.
Transparent global_word_1111.
Lemma bit_wire_1111 v (sizes:global_leaf_sizes v) : global_word_1111 v=global_word_1110 v.
Proof.
 destruct (one_bit_form _ (global_size_1110 v sizes)) as [bit E].
 unfold global_word_1111, global_closed_1111, global_expr_1111, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1111.
Transparent global_word_1125.
Lemma bit_wire_1125 v (sizes:global_leaf_sizes v) : global_word_1125 v=global_word_1124 v.
Proof.
 destruct (one_bit_form _ (global_size_1124 v sizes)) as [bit E].
 unfold global_word_1125, global_closed_1125, global_expr_1125, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1125.
Transparent global_word_1129.
Lemma bit_wire_1129 v (sizes:global_leaf_sizes v) : global_word_1129 v=global_word_1128 v.
Proof.
 destruct (one_bit_form _ (global_size_1128 v sizes)) as [bit E].
 unfold global_word_1129, global_closed_1129, global_expr_1129, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1129.
Transparent global_word_1143.
Lemma bit_wire_1143 v (sizes:global_leaf_sizes v) : global_word_1143 v=global_word_1142 v.
Proof.
 destruct (one_bit_form _ (global_size_1142 v sizes)) as [bit E].
 unfold global_word_1143, global_closed_1143, global_expr_1143, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1143.
Transparent global_word_1147.
Lemma bit_wire_1147 v (sizes:global_leaf_sizes v) : global_word_1147 v=global_word_1146 v.
Proof.
 destruct (one_bit_form _ (global_size_1146 v sizes)) as [bit E].
 unfold global_word_1147, global_closed_1147, global_expr_1147, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1147.
Transparent global_word_1161.
Lemma bit_wire_1161 v (sizes:global_leaf_sizes v) : global_word_1161 v=global_word_1160 v.
Proof.
 destruct (one_bit_form _ (global_size_1160 v sizes)) as [bit E].
 unfold global_word_1161, global_closed_1161, global_expr_1161, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1161.
Transparent global_word_1165.
Lemma bit_wire_1165 v (sizes:global_leaf_sizes v) : global_word_1165 v=global_word_1164 v.
Proof.
 destruct (one_bit_form _ (global_size_1164 v sizes)) as [bit E].
 unfold global_word_1165, global_closed_1165, global_expr_1165, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1165.
Transparent global_word_1179.
Lemma bit_wire_1179 v (sizes:global_leaf_sizes v) : global_word_1179 v=global_word_1178 v.
Proof.
 destruct (one_bit_form _ (global_size_1178 v sizes)) as [bit E].
 unfold global_word_1179, global_closed_1179, global_expr_1179, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1179.
Transparent global_word_1183.
Lemma bit_wire_1183 v (sizes:global_leaf_sizes v) : global_word_1183 v=global_word_1182 v.
Proof.
 destruct (one_bit_form _ (global_size_1182 v sizes)) as [bit E].
 unfold global_word_1183, global_closed_1183, global_expr_1183, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1183.
Transparent global_word_1203.
Lemma bit_wire_1203 v (sizes:global_leaf_sizes v) : global_word_1203 v=global_word_1202 v.
Proof.
 destruct (one_bit_form _ (global_size_1202 v sizes)) as [bit E].
 unfold global_word_1203, global_closed_1203, global_expr_1203, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1203.
Transparent global_word_1207.
Lemma bit_wire_1207 v (sizes:global_leaf_sizes v) : global_word_1207 v=global_word_1206 v.
Proof.
 destruct (one_bit_form _ (global_size_1206 v sizes)) as [bit E].
 unfold global_word_1207, global_closed_1207, global_expr_1207, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1207.
Transparent global_word_1221.
Lemma bit_wire_1221 v (sizes:global_leaf_sizes v) : global_word_1221 v=global_word_1220 v.
Proof.
 destruct (one_bit_form _ (global_size_1220 v sizes)) as [bit E].
 unfold global_word_1221, global_closed_1221, global_expr_1221, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1221.
Transparent global_word_1225.
Lemma bit_wire_1225 v (sizes:global_leaf_sizes v) : global_word_1225 v=global_word_1224 v.
Proof.
 destruct (one_bit_form _ (global_size_1224 v sizes)) as [bit E].
 unfold global_word_1225, global_closed_1225, global_expr_1225, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1225.
Transparent global_word_1239.
Lemma bit_wire_1239 v (sizes:global_leaf_sizes v) : global_word_1239 v=global_word_1238 v.
Proof.
 destruct (one_bit_form _ (global_size_1238 v sizes)) as [bit E].
 unfold global_word_1239, global_closed_1239, global_expr_1239, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1239.
Transparent global_word_1243.
Lemma bit_wire_1243 v (sizes:global_leaf_sizes v) : global_word_1243 v=global_word_1242 v.
Proof.
 destruct (one_bit_form _ (global_size_1242 v sizes)) as [bit E].
 unfold global_word_1243, global_closed_1243, global_expr_1243, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1243.
Transparent global_word_1257.
Lemma bit_wire_1257 v (sizes:global_leaf_sizes v) : global_word_1257 v=global_word_1256 v.
Proof.
 destruct (one_bit_form _ (global_size_1256 v sizes)) as [bit E].
 unfold global_word_1257, global_closed_1257, global_expr_1257, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1257.
Transparent global_word_1261.
Lemma bit_wire_1261 v (sizes:global_leaf_sizes v) : global_word_1261 v=global_word_1260 v.
Proof.
 destruct (one_bit_form _ (global_size_1260 v sizes)) as [bit E].
 unfold global_word_1261, global_closed_1261, global_expr_1261, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1261.
Transparent global_word_1301.
Lemma bit_wire_1301 v (sizes:global_leaf_sizes v) : global_word_1301 v=global_word_1 v.
Proof.
 destruct (one_bit_form _ (global_size_1 v sizes)) as [bit E].
 unfold global_word_1301, global_closed_1301, global_expr_1301, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1301.
Transparent global_word_1307.
Lemma bit_wire_1307 v (sizes:global_leaf_sizes v) : global_word_1307 v=global_word_1 v.
Proof.
 destruct (one_bit_form _ (global_size_1 v sizes)) as [bit E].
 unfold global_word_1307, global_closed_1307, global_expr_1307, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1307.
Transparent global_word_280.
Lemma bit_wire_280 v (sizes:global_leaf_sizes v) : global_word_280 v=global_word_279 v.
Proof.
 destruct (one_bit_form _ (global_size_279 v sizes)) as [bit E].
 unfold global_word_280, global_closed_280, global_expr_280, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_280.
Transparent global_word_283.
Lemma bit_wire_283 v (sizes:global_leaf_sizes v) : global_word_283 v=global_word_282 v.
Proof.
 destruct (one_bit_form _ (global_size_282 v sizes)) as [bit E].
 unfold global_word_283, global_closed_283, global_expr_283, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_283.
Transparent global_word_298.
Lemma bit_wire_298 v (sizes:global_leaf_sizes v) : global_word_298 v=global_word_297 v.
Proof.
 destruct (one_bit_form _ (global_size_297 v sizes)) as [bit E].
 unfold global_word_298, global_closed_298, global_expr_298, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_298.
Transparent global_word_301.
Lemma bit_wire_301 v (sizes:global_leaf_sizes v) : global_word_301 v=global_word_300 v.
Proof.
 destruct (one_bit_form _ (global_size_300 v sizes)) as [bit E].
 unfold global_word_301, global_closed_301, global_expr_301, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_301.
Transparent global_word_319.
Lemma bit_wire_319 v (sizes:global_leaf_sizes v) : global_word_319 v=global_word_318 v.
Proof.
 destruct (one_bit_form _ (global_size_318 v sizes)) as [bit E].
 unfold global_word_319, global_closed_319, global_expr_319, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_319.
Transparent global_word_322.
Lemma bit_wire_322 v (sizes:global_leaf_sizes v) : global_word_322 v=global_word_321 v.
Proof.
 destruct (one_bit_form _ (global_size_321 v sizes)) as [bit E].
 unfold global_word_322, global_closed_322, global_expr_322, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_322.
Transparent global_word_316.
Lemma bit_wire_316 v (sizes:global_leaf_sizes v) : global_word_316 v=global_word_315 v.
Proof.
 destruct (one_bit_form _ (global_size_315 v sizes)) as [bit E].
 unfold global_word_316, global_closed_316, global_expr_316, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_316.
Transparent global_word_343.
Lemma bit_wire_343 v (sizes:global_leaf_sizes v) : global_word_343 v=global_word_342 v.
Proof.
 destruct (one_bit_form _ (global_size_342 v sizes)) as [bit E].
 unfold global_word_343, global_closed_343, global_expr_343, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_343.
Transparent global_word_346.
Lemma bit_wire_346 v (sizes:global_leaf_sizes v) : global_word_346 v=global_word_345 v.
Proof.
 destruct (one_bit_form _ (global_size_345 v sizes)) as [bit E].
 unfold global_word_346, global_closed_346, global_expr_346, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_346.
Transparent global_word_340.
Lemma bit_wire_340 v (sizes:global_leaf_sizes v) : global_word_340 v=global_word_339 v.
Proof.
 destruct (one_bit_form _ (global_size_339 v sizes)) as [bit E].
 unfold global_word_340, global_closed_340, global_expr_340, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_340.
Transparent global_word_377.
Lemma bit_wire_377 v (sizes:global_leaf_sizes v) : global_word_377 v=global_word_376 v.
Proof.
 destruct (one_bit_form _ (global_size_376 v sizes)) as [bit E].
 unfold global_word_377, global_closed_377, global_expr_377, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_377.
Transparent global_word_382.
Lemma bit_wire_382 v (sizes:global_leaf_sizes v) : global_word_382 v=global_word_381 v.
Proof.
 destruct (one_bit_form _ (global_size_381 v sizes)) as [bit E].
 unfold global_word_382, global_closed_382, global_expr_382, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_382.
Transparent global_word_372.
Lemma bit_wire_372 v (sizes:global_leaf_sizes v) : global_word_372 v=global_word_371 v.
Proof.
 destruct (one_bit_form _ (global_size_371 v sizes)) as [bit E].
 unfold global_word_372, global_closed_372, global_expr_372, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_372.
Transparent global_word_396.
Lemma bit_wire_396 v (sizes:global_leaf_sizes v) : global_word_396 v=global_word_395 v.
Proof.
 destruct (one_bit_form _ (global_size_395 v sizes)) as [bit E].
 unfold global_word_396, global_closed_396, global_expr_396, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_396.
Transparent global_word_402.
Lemma bit_wire_402 v (sizes:global_leaf_sizes v) : global_word_402 v=global_word_401 v.
Proof.
 destruct (one_bit_form _ (global_size_401 v sizes)) as [bit E].
 unfold global_word_402, global_closed_402, global_expr_402, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_402.
Transparent global_word_367.
Lemma bit_wire_367 v (sizes:global_leaf_sizes v) : global_word_367 v=global_word_366 v.
Proof.
 destruct (one_bit_form _ (global_size_366 v sizes)) as [bit E].
 unfold global_word_367, global_closed_367, global_expr_367, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_367.
Transparent global_word_446.
Lemma bit_wire_446 v (sizes:global_leaf_sizes v) : global_word_446 v=global_word_445 v.
Proof.
 destruct (one_bit_form _ (global_size_445 v sizes)) as [bit E].
 unfold global_word_446, global_closed_446, global_expr_446, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_446.
Transparent global_word_451.
Lemma bit_wire_451 v (sizes:global_leaf_sizes v) : global_word_451 v=global_word_450 v.
Proof.
 destruct (one_bit_form _ (global_size_450 v sizes)) as [bit E].
 unfold global_word_451, global_closed_451, global_expr_451, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_451.
Transparent global_word_441.
Lemma bit_wire_441 v (sizes:global_leaf_sizes v) : global_word_441 v=global_word_440 v.
Proof.
 destruct (one_bit_form _ (global_size_440 v sizes)) as [bit E].
 unfold global_word_441, global_closed_441, global_expr_441, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_441.
Transparent global_word_465.
Lemma bit_wire_465 v (sizes:global_leaf_sizes v) : global_word_465 v=global_word_464 v.
Proof.
 destruct (one_bit_form _ (global_size_464 v sizes)) as [bit E].
 unfold global_word_465, global_closed_465, global_expr_465, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_465.
Transparent global_word_471.
Lemma bit_wire_471 v (sizes:global_leaf_sizes v) : global_word_471 v=global_word_470 v.
Proof.
 destruct (one_bit_form _ (global_size_470 v sizes)) as [bit E].
 unfold global_word_471, global_closed_471, global_expr_471, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_471.
Transparent global_word_436.
Lemma bit_wire_436 v (sizes:global_leaf_sizes v) : global_word_436 v=global_word_435 v.
Proof.
 destruct (one_bit_form _ (global_size_435 v sizes)) as [bit E].
 unfold global_word_436, global_closed_436, global_expr_436, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_436.
Transparent global_word_515.
Lemma bit_wire_515 v (sizes:global_leaf_sizes v) : global_word_515 v=global_word_514 v.
Proof.
 destruct (one_bit_form _ (global_size_514 v sizes)) as [bit E].
 unfold global_word_515, global_closed_515, global_expr_515, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_515.
Transparent global_word_520.
Lemma bit_wire_520 v (sizes:global_leaf_sizes v) : global_word_520 v=global_word_519 v.
Proof.
 destruct (one_bit_form _ (global_size_519 v sizes)) as [bit E].
 unfold global_word_520, global_closed_520, global_expr_520, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_520.
Transparent global_word_510.
Lemma bit_wire_510 v (sizes:global_leaf_sizes v) : global_word_510 v=global_word_509 v.
Proof.
 destruct (one_bit_form _ (global_size_509 v sizes)) as [bit E].
 unfold global_word_510, global_closed_510, global_expr_510, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_510.
Transparent global_word_534.
Lemma bit_wire_534 v (sizes:global_leaf_sizes v) : global_word_534 v=global_word_533 v.
Proof.
 destruct (one_bit_form _ (global_size_533 v sizes)) as [bit E].
 unfold global_word_534, global_closed_534, global_expr_534, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_534.
Transparent global_word_540.
Lemma bit_wire_540 v (sizes:global_leaf_sizes v) : global_word_540 v=global_word_539 v.
Proof.
 destruct (one_bit_form _ (global_size_539 v sizes)) as [bit E].
 unfold global_word_540, global_closed_540, global_expr_540, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_540.
Transparent global_word_505.
Lemma bit_wire_505 v (sizes:global_leaf_sizes v) : global_word_505 v=global_word_504 v.
Proof.
 destruct (one_bit_form _ (global_size_504 v sizes)) as [bit E].
 unfold global_word_505, global_closed_505, global_expr_505, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_505.
Transparent global_word_584.
Lemma bit_wire_584 v (sizes:global_leaf_sizes v) : global_word_584 v=global_word_583 v.
Proof.
 destruct (one_bit_form _ (global_size_583 v sizes)) as [bit E].
 unfold global_word_584, global_closed_584, global_expr_584, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_584.
Transparent global_word_589.
Lemma bit_wire_589 v (sizes:global_leaf_sizes v) : global_word_589 v=global_word_588 v.
Proof.
 destruct (one_bit_form _ (global_size_588 v sizes)) as [bit E].
 unfold global_word_589, global_closed_589, global_expr_589, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_589.
Transparent global_word_579.
Lemma bit_wire_579 v (sizes:global_leaf_sizes v) : global_word_579 v=global_word_578 v.
Proof.
 destruct (one_bit_form _ (global_size_578 v sizes)) as [bit E].
 unfold global_word_579, global_closed_579, global_expr_579, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_579.
Transparent global_word_603.
Lemma bit_wire_603 v (sizes:global_leaf_sizes v) : global_word_603 v=global_word_602 v.
Proof.
 destruct (one_bit_form _ (global_size_602 v sizes)) as [bit E].
 unfold global_word_603, global_closed_603, global_expr_603, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_603.
Transparent global_word_609.
Lemma bit_wire_609 v (sizes:global_leaf_sizes v) : global_word_609 v=global_word_608 v.
Proof.
 destruct (one_bit_form _ (global_size_608 v sizes)) as [bit E].
 unfold global_word_609, global_closed_609, global_expr_609, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_609.
Transparent global_word_574.
Lemma bit_wire_574 v (sizes:global_leaf_sizes v) : global_word_574 v=global_word_573 v.
Proof.
 destruct (one_bit_form _ (global_size_573 v sizes)) as [bit E].
 unfold global_word_574, global_closed_574, global_expr_574, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_574.
Transparent global_word_653.
Lemma bit_wire_653 v (sizes:global_leaf_sizes v) : global_word_653 v=global_word_652 v.
Proof.
 destruct (one_bit_form _ (global_size_652 v sizes)) as [bit E].
 unfold global_word_653, global_closed_653, global_expr_653, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_653.
Transparent global_word_658.
Lemma bit_wire_658 v (sizes:global_leaf_sizes v) : global_word_658 v=global_word_657 v.
Proof.
 destruct (one_bit_form _ (global_size_657 v sizes)) as [bit E].
 unfold global_word_658, global_closed_658, global_expr_658, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_658.
Transparent global_word_648.
Lemma bit_wire_648 v (sizes:global_leaf_sizes v) : global_word_648 v=global_word_647 v.
Proof.
 destruct (one_bit_form _ (global_size_647 v sizes)) as [bit E].
 unfold global_word_648, global_closed_648, global_expr_648, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_648.
Transparent global_word_672.
Lemma bit_wire_672 v (sizes:global_leaf_sizes v) : global_word_672 v=global_word_671 v.
Proof.
 destruct (one_bit_form _ (global_size_671 v sizes)) as [bit E].
 unfold global_word_672, global_closed_672, global_expr_672, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_672.
Transparent global_word_678.
Lemma bit_wire_678 v (sizes:global_leaf_sizes v) : global_word_678 v=global_word_677 v.
Proof.
 destruct (one_bit_form _ (global_size_677 v sizes)) as [bit E].
 unfold global_word_678, global_closed_678, global_expr_678, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_678.
Transparent global_word_643.
Lemma bit_wire_643 v (sizes:global_leaf_sizes v) : global_word_643 v=global_word_642 v.
Proof.
 destruct (one_bit_form _ (global_size_642 v sizes)) as [bit E].
 unfold global_word_643, global_closed_643, global_expr_643, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_643.
Transparent global_word_722.
Lemma bit_wire_722 v (sizes:global_leaf_sizes v) : global_word_722 v=global_word_721 v.
Proof.
 destruct (one_bit_form _ (global_size_721 v sizes)) as [bit E].
 unfold global_word_722, global_closed_722, global_expr_722, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_722.
Transparent global_word_727.
Lemma bit_wire_727 v (sizes:global_leaf_sizes v) : global_word_727 v=global_word_726 v.
Proof.
 destruct (one_bit_form _ (global_size_726 v sizes)) as [bit E].
 unfold global_word_727, global_closed_727, global_expr_727, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_727.
Transparent global_word_717.
Lemma bit_wire_717 v (sizes:global_leaf_sizes v) : global_word_717 v=global_word_716 v.
Proof.
 destruct (one_bit_form _ (global_size_716 v sizes)) as [bit E].
 unfold global_word_717, global_closed_717, global_expr_717, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_717.
Transparent global_word_741.
Lemma bit_wire_741 v (sizes:global_leaf_sizes v) : global_word_741 v=global_word_740 v.
Proof.
 destruct (one_bit_form _ (global_size_740 v sizes)) as [bit E].
 unfold global_word_741, global_closed_741, global_expr_741, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_741.
Transparent global_word_747.
Lemma bit_wire_747 v (sizes:global_leaf_sizes v) : global_word_747 v=global_word_746 v.
Proof.
 destruct (one_bit_form _ (global_size_746 v sizes)) as [bit E].
 unfold global_word_747, global_closed_747, global_expr_747, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_747.
Transparent global_word_712.
Lemma bit_wire_712 v (sizes:global_leaf_sizes v) : global_word_712 v=global_word_711 v.
Proof.
 destruct (one_bit_form _ (global_size_711 v sizes)) as [bit E].
 unfold global_word_712, global_closed_712, global_expr_712, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_712.
Transparent global_word_791.
Lemma bit_wire_791 v (sizes:global_leaf_sizes v) : global_word_791 v=global_word_790 v.
Proof.
 destruct (one_bit_form _ (global_size_790 v sizes)) as [bit E].
 unfold global_word_791, global_closed_791, global_expr_791, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_791.
Transparent global_word_796.
Lemma bit_wire_796 v (sizes:global_leaf_sizes v) : global_word_796 v=global_word_795 v.
Proof.
 destruct (one_bit_form _ (global_size_795 v sizes)) as [bit E].
 unfold global_word_796, global_closed_796, global_expr_796, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_796.
Transparent global_word_786.
Lemma bit_wire_786 v (sizes:global_leaf_sizes v) : global_word_786 v=global_word_785 v.
Proof.
 destruct (one_bit_form _ (global_size_785 v sizes)) as [bit E].
 unfold global_word_786, global_closed_786, global_expr_786, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_786.
Transparent global_word_810.
Lemma bit_wire_810 v (sizes:global_leaf_sizes v) : global_word_810 v=global_word_809 v.
Proof.
 destruct (one_bit_form _ (global_size_809 v sizes)) as [bit E].
 unfold global_word_810, global_closed_810, global_expr_810, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_810.
Transparent global_word_816.
Lemma bit_wire_816 v (sizes:global_leaf_sizes v) : global_word_816 v=global_word_815 v.
Proof.
 destruct (one_bit_form _ (global_size_815 v sizes)) as [bit E].
 unfold global_word_816, global_closed_816, global_expr_816, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_816.
Transparent global_word_781.
Lemma bit_wire_781 v (sizes:global_leaf_sizes v) : global_word_781 v=global_word_780 v.
Proof.
 destruct (one_bit_form _ (global_size_780 v sizes)) as [bit E].
 unfold global_word_781, global_closed_781, global_expr_781, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_781.
Transparent global_word_860.
Lemma bit_wire_860 v (sizes:global_leaf_sizes v) : global_word_860 v=global_word_859 v.
Proof.
 destruct (one_bit_form _ (global_size_859 v sizes)) as [bit E].
 unfold global_word_860, global_closed_860, global_expr_860, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_860.
Transparent global_word_865.
Lemma bit_wire_865 v (sizes:global_leaf_sizes v) : global_word_865 v=global_word_864 v.
Proof.
 destruct (one_bit_form _ (global_size_864 v sizes)) as [bit E].
 unfold global_word_865, global_closed_865, global_expr_865, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_865.
Transparent global_word_855.
Lemma bit_wire_855 v (sizes:global_leaf_sizes v) : global_word_855 v=global_word_854 v.
Proof.
 destruct (one_bit_form _ (global_size_854 v sizes)) as [bit E].
 unfold global_word_855, global_closed_855, global_expr_855, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_855.
Transparent global_word_879.
Lemma bit_wire_879 v (sizes:global_leaf_sizes v) : global_word_879 v=global_word_878 v.
Proof.
 destruct (one_bit_form _ (global_size_878 v sizes)) as [bit E].
 unfold global_word_879, global_closed_879, global_expr_879, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_879.
Transparent global_word_885.
Lemma bit_wire_885 v (sizes:global_leaf_sizes v) : global_word_885 v=global_word_884 v.
Proof.
 destruct (one_bit_form _ (global_size_884 v sizes)) as [bit E].
 unfold global_word_885, global_closed_885, global_expr_885, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_885.
Transparent global_word_850.
Lemma bit_wire_850 v (sizes:global_leaf_sizes v) : global_word_850 v=global_word_849 v.
Proof.
 destruct (one_bit_form _ (global_size_849 v sizes)) as [bit E].
 unfold global_word_850, global_closed_850, global_expr_850, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_850.
Transparent global_word_919.
Lemma bit_wire_919 v (sizes:global_leaf_sizes v) : global_word_919 v=global_word_918 v.
Proof.
 destruct (one_bit_form _ (global_size_918 v sizes)) as [bit E].
 unfold global_word_919, global_closed_919, global_expr_919, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_919.
Transparent global_word_922.
Lemma bit_wire_922 v (sizes:global_leaf_sizes v) : global_word_922 v=global_word_921 v.
Proof.
 destruct (one_bit_form _ (global_size_921 v sizes)) as [bit E].
 unfold global_word_922, global_closed_922, global_expr_922, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_922.
Transparent global_word_916.
Lemma bit_wire_916 v (sizes:global_leaf_sizes v) : global_word_916 v=global_word_915 v.
Proof.
 destruct (one_bit_form _ (global_size_915 v sizes)) as [bit E].
 unfold global_word_916, global_closed_916, global_expr_916, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_916.
Transparent global_word_940.
Lemma bit_wire_940 v (sizes:global_leaf_sizes v) : global_word_940 v=global_word_939 v.
Proof.
 destruct (one_bit_form _ (global_size_939 v sizes)) as [bit E].
 unfold global_word_940, global_closed_940, global_expr_940, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_940.
Transparent global_word_943.
Lemma bit_wire_943 v (sizes:global_leaf_sizes v) : global_word_943 v=global_word_942 v.
Proof.
 destruct (one_bit_form _ (global_size_942 v sizes)) as [bit E].
 unfold global_word_943, global_closed_943, global_expr_943, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_943.
Transparent global_word_958.
Lemma bit_wire_958 v (sizes:global_leaf_sizes v) : global_word_958 v=global_word_957 v.
Proof.
 destruct (one_bit_form _ (global_size_957 v sizes)) as [bit E].
 unfold global_word_958, global_closed_958, global_expr_958, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_958.
Transparent global_word_961.
Lemma bit_wire_961 v (sizes:global_leaf_sizes v) : global_word_961 v=global_word_960 v.
Proof.
 destruct (one_bit_form _ (global_size_960 v sizes)) as [bit E].
 unfold global_word_961, global_closed_961, global_expr_961, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_961.
Transparent global_word_976.
Lemma bit_wire_976 v (sizes:global_leaf_sizes v) : global_word_976 v=global_word_975 v.
Proof.
 destruct (one_bit_form _ (global_size_975 v sizes)) as [bit E].
 unfold global_word_976, global_closed_976, global_expr_976, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_976.
Transparent global_word_979.
Lemma bit_wire_979 v (sizes:global_leaf_sizes v) : global_word_979 v=global_word_978 v.
Proof.
 destruct (one_bit_form _ (global_size_978 v sizes)) as [bit E].
 unfold global_word_979, global_closed_979, global_expr_979, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_979.
Transparent global_word_994.
Lemma bit_wire_994 v (sizes:global_leaf_sizes v) : global_word_994 v=global_word_993 v.
Proof.
 destruct (one_bit_form _ (global_size_993 v sizes)) as [bit E].
 unfold global_word_994, global_closed_994, global_expr_994, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_994.
Transparent global_word_997.
Lemma bit_wire_997 v (sizes:global_leaf_sizes v) : global_word_997 v=global_word_996 v.
Proof.
 destruct (one_bit_form _ (global_size_996 v sizes)) as [bit E].
 unfold global_word_997, global_closed_997, global_expr_997, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_997.
Transparent global_word_1012.
Lemma bit_wire_1012 v (sizes:global_leaf_sizes v) : global_word_1012 v=global_word_1011 v.
Proof.
 destruct (one_bit_form _ (global_size_1011 v sizes)) as [bit E].
 unfold global_word_1012, global_closed_1012, global_expr_1012, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1012.
Transparent global_word_1015.
Lemma bit_wire_1015 v (sizes:global_leaf_sizes v) : global_word_1015 v=global_word_1014 v.
Proof.
 destruct (one_bit_form _ (global_size_1014 v sizes)) as [bit E].
 unfold global_word_1015, global_closed_1015, global_expr_1015, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1015.
Transparent global_word_1030.
Lemma bit_wire_1030 v (sizes:global_leaf_sizes v) : global_word_1030 v=global_word_1029 v.
Proof.
 destruct (one_bit_form _ (global_size_1029 v sizes)) as [bit E].
 unfold global_word_1030, global_closed_1030, global_expr_1030, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1030.
Transparent global_word_1033.
Lemma bit_wire_1033 v (sizes:global_leaf_sizes v) : global_word_1033 v=global_word_1032 v.
Proof.
 destruct (one_bit_form _ (global_size_1032 v sizes)) as [bit E].
 unfold global_word_1033, global_closed_1033, global_expr_1033, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1033.
Transparent global_word_1048.
Lemma bit_wire_1048 v (sizes:global_leaf_sizes v) : global_word_1048 v=global_word_1047 v.
Proof.
 destruct (one_bit_form _ (global_size_1047 v sizes)) as [bit E].
 unfold global_word_1048, global_closed_1048, global_expr_1048, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1048.
Transparent global_word_1051.
Lemma bit_wire_1051 v (sizes:global_leaf_sizes v) : global_word_1051 v=global_word_1050 v.
Proof.
 destruct (one_bit_form _ (global_size_1050 v sizes)) as [bit E].
 unfold global_word_1051, global_closed_1051, global_expr_1051, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1051.
Transparent global_word_1069.
Lemma bit_wire_1069 v (sizes:global_leaf_sizes v) : global_word_1069 v=global_word_1068 v.
Proof.
 destruct (one_bit_form _ (global_size_1068 v sizes)) as [bit E].
 unfold global_word_1069, global_closed_1069, global_expr_1069, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1069.
Transparent global_word_1072.
Lemma bit_wire_1072 v (sizes:global_leaf_sizes v) : global_word_1072 v=global_word_1071 v.
Proof.
 destruct (one_bit_form _ (global_size_1071 v sizes)) as [bit E].
 unfold global_word_1072, global_closed_1072, global_expr_1072, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1072.
Transparent global_word_1066.
Lemma bit_wire_1066 v (sizes:global_leaf_sizes v) : global_word_1066 v=global_word_1065 v.
Proof.
 destruct (one_bit_form _ (global_size_1065 v sizes)) as [bit E].
 unfold global_word_1066, global_closed_1066, global_expr_1066, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1066.
Transparent global_word_1093.
Lemma bit_wire_1093 v (sizes:global_leaf_sizes v) : global_word_1093 v=global_word_1092 v.
Proof.
 destruct (one_bit_form _ (global_size_1092 v sizes)) as [bit E].
 unfold global_word_1093, global_closed_1093, global_expr_1093, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1093.
Transparent global_word_1096.
Lemma bit_wire_1096 v (sizes:global_leaf_sizes v) : global_word_1096 v=global_word_1095 v.
Proof.
 destruct (one_bit_form _ (global_size_1095 v sizes)) as [bit E].
 unfold global_word_1096, global_closed_1096, global_expr_1096, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1096.
Transparent global_word_1090.
Lemma bit_wire_1090 v (sizes:global_leaf_sizes v) : global_word_1090 v=global_word_1089 v.
Proof.
 destruct (one_bit_form _ (global_size_1089 v sizes)) as [bit E].
 unfold global_word_1090, global_closed_1090, global_expr_1090, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1090.
Transparent global_word_1114.
Lemma bit_wire_1114 v (sizes:global_leaf_sizes v) : global_word_1114 v=global_word_1113 v.
Proof.
 destruct (one_bit_form _ (global_size_1113 v sizes)) as [bit E].
 unfold global_word_1114, global_closed_1114, global_expr_1114, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1114.
Transparent global_word_1117.
Lemma bit_wire_1117 v (sizes:global_leaf_sizes v) : global_word_1117 v=global_word_1116 v.
Proof.
 destruct (one_bit_form _ (global_size_1116 v sizes)) as [bit E].
 unfold global_word_1117, global_closed_1117, global_expr_1117, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1117.
Transparent global_word_1132.
Lemma bit_wire_1132 v (sizes:global_leaf_sizes v) : global_word_1132 v=global_word_1131 v.
Proof.
 destruct (one_bit_form _ (global_size_1131 v sizes)) as [bit E].
 unfold global_word_1132, global_closed_1132, global_expr_1132, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1132.
Transparent global_word_1135.
Lemma bit_wire_1135 v (sizes:global_leaf_sizes v) : global_word_1135 v=global_word_1134 v.
Proof.
 destruct (one_bit_form _ (global_size_1134 v sizes)) as [bit E].
 unfold global_word_1135, global_closed_1135, global_expr_1135, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1135.
Transparent global_word_1150.
Lemma bit_wire_1150 v (sizes:global_leaf_sizes v) : global_word_1150 v=global_word_1149 v.
Proof.
 destruct (one_bit_form _ (global_size_1149 v sizes)) as [bit E].
 unfold global_word_1150, global_closed_1150, global_expr_1150, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1150.
Transparent global_word_1153.
Lemma bit_wire_1153 v (sizes:global_leaf_sizes v) : global_word_1153 v=global_word_1152 v.
Proof.
 destruct (one_bit_form _ (global_size_1152 v sizes)) as [bit E].
 unfold global_word_1153, global_closed_1153, global_expr_1153, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1153.
Transparent global_word_1168.
Lemma bit_wire_1168 v (sizes:global_leaf_sizes v) : global_word_1168 v=global_word_1167 v.
Proof.
 destruct (one_bit_form _ (global_size_1167 v sizes)) as [bit E].
 unfold global_word_1168, global_closed_1168, global_expr_1168, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1168.
Transparent global_word_1171.
Lemma bit_wire_1171 v (sizes:global_leaf_sizes v) : global_word_1171 v=global_word_1170 v.
Proof.
 destruct (one_bit_form _ (global_size_1170 v sizes)) as [bit E].
 unfold global_word_1171, global_closed_1171, global_expr_1171, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1171.
Transparent global_word_1189.
Lemma bit_wire_1189 v (sizes:global_leaf_sizes v) : global_word_1189 v=global_word_1188 v.
Proof.
 destruct (one_bit_form _ (global_size_1188 v sizes)) as [bit E].
 unfold global_word_1189, global_closed_1189, global_expr_1189, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1189.
Transparent global_word_1192.
Lemma bit_wire_1192 v (sizes:global_leaf_sizes v) : global_word_1192 v=global_word_1191 v.
Proof.
 destruct (one_bit_form _ (global_size_1191 v sizes)) as [bit E].
 unfold global_word_1192, global_closed_1192, global_expr_1192, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1192.
Transparent global_word_1186.
Lemma bit_wire_1186 v (sizes:global_leaf_sizes v) : global_word_1186 v=global_word_1185 v.
Proof.
 destruct (one_bit_form _ (global_size_1185 v sizes)) as [bit E].
 unfold global_word_1186, global_closed_1186, global_expr_1186, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1186.
Transparent global_word_1210.
Lemma bit_wire_1210 v (sizes:global_leaf_sizes v) : global_word_1210 v=global_word_1209 v.
Proof.
 destruct (one_bit_form _ (global_size_1209 v sizes)) as [bit E].
 unfold global_word_1210, global_closed_1210, global_expr_1210, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1210.
Transparent global_word_1213.
Lemma bit_wire_1213 v (sizes:global_leaf_sizes v) : global_word_1213 v=global_word_1212 v.
Proof.
 destruct (one_bit_form _ (global_size_1212 v sizes)) as [bit E].
 unfold global_word_1213, global_closed_1213, global_expr_1213, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1213.
Transparent global_word_1228.
Lemma bit_wire_1228 v (sizes:global_leaf_sizes v) : global_word_1228 v=global_word_1227 v.
Proof.
 destruct (one_bit_form _ (global_size_1227 v sizes)) as [bit E].
 unfold global_word_1228, global_closed_1228, global_expr_1228, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1228.
Transparent global_word_1231.
Lemma bit_wire_1231 v (sizes:global_leaf_sizes v) : global_word_1231 v=global_word_1230 v.
Proof.
 destruct (one_bit_form _ (global_size_1230 v sizes)) as [bit E].
 unfold global_word_1231, global_closed_1231, global_expr_1231, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1231.
Transparent global_word_1246.
Lemma bit_wire_1246 v (sizes:global_leaf_sizes v) : global_word_1246 v=global_word_1245 v.
Proof.
 destruct (one_bit_form _ (global_size_1245 v sizes)) as [bit E].
 unfold global_word_1246, global_closed_1246, global_expr_1246, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1246.
Transparent global_word_1249.
Lemma bit_wire_1249 v (sizes:global_leaf_sizes v) : global_word_1249 v=global_word_1248 v.
Proof.
 destruct (one_bit_form _ (global_size_1248 v sizes)) as [bit E].
 unfold global_word_1249, global_closed_1249, global_expr_1249, Stable.word_of_eval. rewrite E.
 destruct bit; reflexivity.
Qed.
Opaque global_word_1249.
Transparent global_word_362.
Lemma constant_wire_362 v : global_word_362 v=[::false].
Proof. reflexivity. Qed.
Opaque global_word_362.

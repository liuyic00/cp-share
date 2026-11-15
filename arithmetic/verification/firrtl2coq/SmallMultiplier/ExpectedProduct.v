From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import BitvectorFacts.
From SmallMultiplier Require Import Stable GlobalStable Booth8.
Local Open Scope Z_scope.
Lemma signed_word8 a (bounded:N.lt a 256) : to_Z(from_N 8 a)=signed8(Z.of_N a).
Proof.
 have Checked:List.forallb (fun n=>Z.eqb (to_Z(from_N 8 (N.of_nat n))) (signed8(Z.of_N(N.of_nat n)))) (List.seq 0 256)=true by vm_compute;reflexivity.
 have Member:List.In (N.to_nat a) (List.seq 0 256) by apply List.in_seq;lia.
 have Value:=(proj1(List.forallb_forall _ _) Checked) (N.to_nat a) Member.
 apply Z.eqb_eq in Value. rewrite Nnat.N2Nat.id in Value. exact Value.
Qed.
Local Transparent global_word_1293 global_word_1294 global_word_1295 global_word_1296.
Lemma expected_product_bits v : global_word_1296 v=from_Z 16 (to_Z(global_word_2 v)*to_Z(global_word_53 v)).
Proof.
 unfold global_word_1296,global_closed_1296,global_expr_1296,word_of_eval.
 cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; [|reflexivity].
 change (global_word_1295 v=from_Z 16 (to_Z(global_word_2 v)*to_Z(global_word_53 v))).
 unfold global_word_1295,global_closed_1295,global_expr_1295,word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 change (from_Z 16 (to_Z(global_word_1293 v)*to_Z(global_word_1294 v))=from_Z 16 (to_Z(global_word_2 v)*to_Z(global_word_53 v))).
 have A:global_word_1293 v=global_word_2 v by reflexivity.
 have B:global_word_1294 v=global_word_53 v by reflexivity.
 rewrite A B. reflexivity.
Qed.
Lemma expected_product_integer v a b
 (Ha:global_word_2 v=from_N 8 a) (Hb:global_word_53 v=from_N 8 b)
 (Hamin:N.lt a 256) (Hbmin:N.lt b 256) :
 to_Zpos(global_word_1296 v)=(signed8(Z.of_N a)*signed8(Z.of_N b)) mod 65536.
Proof. rewrite expected_product_bits Ha Hb unsigned_from_Z (signed_word8 a Hamin) (signed_word8 b Hbmin). reflexivity. Qed.
Print Assumptions expected_product_integer.

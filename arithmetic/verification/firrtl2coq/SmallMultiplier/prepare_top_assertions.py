from pathlib import Path
import json
H=Path(__file__).resolve().parent
idx=json.loads((H/'global-key-index.json').read_text())
s=r'''From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From ArithmeticFIRRTL Require ArrayMulDataModule8.
From SmallMultiplier Require Import GlobalStable GlobalWidths GlobalContracts GlobalOutput GlobalProgressTypes PipelineInvariant ControlEquations.
Module Tool:=ArithmeticFIRRTL.ArrayMulDataModule8.
Local Open Scope N_scope.
'''
s+='Local Opaque '+' '.join('global_word_'+str(i) for i in range(2262))+'.\n'
for a,reg,gate,pred,expected in [(3,410,414,412,408),(4,419,422,420,416)]:
 ri,gi,pi,ei=[idx[':'+str(x)] for x in (reg,gate,pred,expected)]
 s+=f'''Local Transparent global_word_{pi}.
Lemma top_predicate_{a} v (sizes:global_leaf_sizes v) (invariant:pipeline_invariant v)
 (active:is_zero(global_word_{ri} v)=false) : global_word_{pi} v=[::true].
Proof.
 have Number:to_Zpos(global_word_1299 v)=to_Zpos(global_word_{ei} v).
 {{ rewrite(global_output_weight v sizes). apply (proj{1 if a==3 else 2} invariant). exact active. }}
 have Equal:to_N(global_word_1299 v)=to_N(global_word_{ei} v).
 {{ rewrite !to_Zpos_N in Number. lia. }}
 unfold global_word_{pi},global_expr_{pi},global_closed_{pi},Stable.word_of_eval.
 cbn [eval_hfexpr eval_href].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 change ([::to_N(global_word_1299 v)==to_N(global_word_{ei} v)]=[::true]).
 rewrite Equal eqxx. reflexivity.
Qed.
Local Opaque global_word_{pi}.
Lemma top_assertion_{a} v states env
 (sizes:global_leaf_sizes v) (invariant:pipeline_invariant v)
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v))
 (found:SVM.find [::] states=Some env) : Tool.generated_assert_m3_{a}_local env.
Proof.
'''
 for r,n in [(reg,ri),(gate,gi),(pred,pi)]:
  s+=f''' have Value{r}:VM.find {r} env=Some(Gval(Fuint 1)(global_word_{n} v)).
 {{ have Known:=values {n}%nat (ltac:(lia)).
   change (circuit_lookup [::] {r} states=Some(Gval(Fuint 1)(global_word_{n} v))) in Known.
   unfold circuit_lookup in Known. rewrite found in Known. exact Known. }}
'''
 s+=f''' unfold Tool.generated_assert_m3_{a}_local. intros Guard.
 unfold Tool.generated_expr_true in Guard. cbn [eval_hfexpr eval_href] in Guard.
 rewrite Value{reg} Value{gate} in Guard.
 destruct(one_bit_word _ (global_size_{ri} v sizes)) as [valid R].
 destruct(one_bit_word _ (global_size_{gi} v sizes)) as [gate G].
 rewrite R G in Guard.
 have Active:is_zero(global_word_{ri} v)=false.
 {{ rewrite R. destruct valid,gate; vm_compute in Guard |- *; congruence. }}
 unfold Tool.generated_expr_true. cbn [eval_hfexpr eval_href]. rewrite Value{pred} (top_predicate_{a} v sizes invariant Active). reflexivity.
Qed.
'''
(H/'TopAssertions.v').write_text(s)

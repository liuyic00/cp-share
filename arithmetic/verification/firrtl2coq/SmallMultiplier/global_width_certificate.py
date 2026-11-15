#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent;x=runpy.run_path(str(H/'global_stable_certificate.py'));g=x['g'];idx=x['idx'];typ=x['typ'];word=x['word'];typeof=x['typeof'];parts=x['parts']
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import EnvironmentFacts ScalarEvaluation ScalarTyping.','From SmallMultiplier Require Import GlobalStable GlobalWidthFacts.','Local Open Scope N_scope.']
for k in g['order']:
 n=idx[k];node=g['nodes'][k];ds=node['deps'];kind,w=typeof(k)
 hs=' '.join(f'(H{j}:size ({word(d)} v)={typeof(d)[1]}%nat)' for j,d in enumerate(ds))
 out +=[f'Lemma global_local_width_{n} v {hs} : size ({word(k)} v)={w}%nat.']
 if node['kind'].startswith('sync'):
  out +=[f'Proof. rewrite global_sync_{n}. exact H0. Qed.'];continue
 if node['expr'].startswith('(@Eref '):
  out +=[f'Proof. unfold {word(k)}, global_closed_{n}, global_expr_{n}, Stable.word_of_eval. change (size ({word(ds[0])} v)={w}%nat). exact H0. Qed.'];continue
 if any(len(parts(d)[1])==2 for d in ds):
  assert len(ds)==1 and w==1 and typeof(ds[0])[1]==1
  out +=[f'Proof. destruct (one_bit_form _ H0) as [b E]. unfold {word(k)}, global_closed_{n}, global_expr_{n}, Stable.word_of_eval. rewrite E. destruct b;vm_compute;reflexivity. Qed.'];continue
 rew=' '.join(f'?H{j}' for j in range(len(ds)))+' ?eqxx'
 out +=[f'Proof. have T : env_typed (global_closed_{n} v).',f' {{ unfold global_closed_{n}. repeat (apply env_typed_add; [|cbn [hvalue_is_type_correct type_of_val]; rewrite {rew}; reflexivity]). apply env_typed_empty. }}',f' have E := scalar_eval_type_correct (global_closed_{n} v) (global_closed_{n} v) global_expr_{n} T (Logic.eq_refl _).',f' rewrite global_closed_{n}_value in E.',f' have K : eval_type_of_expr global_expr_{n} (global_closed_{n} v) = Some (Gtyp {typ(k)}) by reflexivity.', ' rewrite K in E.']
 out +=[' exact (uint_value_typed_size _ _ _ E).' if kind==0 else ' exact (sint_value_typed_size _ _ E).' if kind==1 else ' exact (clock_value_typed_size _ E).','Qed.']
widthlist='[::'+';'.join(str(typeof(k)[1])+'%nat' for k in g['leaves'])+']'
out +=[f'Definition global_leaf_sizes (v:global_leaves) := forall i, (i < {len(g["leaves"])})%nat -> size (v i) = nth 0%nat {widthlist} i.']
for k in g['leaves']:
 n=idx[k];w=typeof(k)[1];out +=[f'Lemma global_size_{n} v (H:global_leaf_sizes v) : size ({word(k)} v)={w}%nat.',f'Proof. unfold {word(k)}. exact (H {n}%nat (Logic.eq_refl _)). Qed.']
for k in g['order']:
 n=idx[k];w=typeof(k)[1];out +=[f'Lemma global_size_{n} v (H:global_leaf_sizes v) : size ({word(k)} v)={w}%nat.',f'Proof. apply global_local_width_{n}.']
 for d in g['nodes'][k]['deps']:out +=[f' exact (global_size_{idx[d]} v H).']
 out+=['Qed.']
(H/'GlobalWidths.v').write_text('\n'.join(out)+'\n')

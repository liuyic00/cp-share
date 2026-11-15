from pathlib import Path
import json
H=Path(__file__).resolve().parent
m=json.loads((H/'stable-nodes.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
regs=m['registers']; byindex={idx[':'+str(r)]:r for r in regs}
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From SmallMultiplier Require Import GlobalStable GlobalWidths GlobalProgressTypes GlobalInitialLocal PipelineCommit.
Local Open Scope N_scope.
Lemma register_adapt_size width word : size (zext_to width (take width word))=width.
Proof.
 unfold zext_to. rewrite size_zext size_take.
 have Bound: (minn width (size word) <= width)%nat by apply geq_minl.
 rewrite subnKC; [reflexivity|exact Bound].
Qed.
'''
for r in regs:
 w=m['root_types'][str(r)][1]
 s+=f'Lemma next_word_{r}_size v : size(next_word_{r} v)={w}%nat.\nProof. apply register_adapt_size. Qed.\n'
s+='Definition next_register_leaves (v:global_leaves) : global_leaves := fun index => match N.of_nat index with\n'
for i,r in sorted(byindex.items()):s+=f'| {i} => next_word_{r} v\n'
s+='| _ => v index end.\n'
s+='Lemma next_register_leaves_sizes v (sized:global_leaf_sizes v) : global_leaf_sizes (next_register_leaves v).\nProof. intros index inside.\n have Member:List.In index (List.seq 0 62) by apply List.in_seq; move/ltP:inside;lia.\n change (List.In index [::'+ ';'.join(f'{i}%nat' for i in range(62))+']) in Member.\n'
for i in range(62):
 s+=' destruct Member as [same|Member].\n - subst index. '
 if i in byindex:s+=f'exact(next_word_{byindex[i]}_size v).\n'
 else:s+=f'exact(sized {i}%nat (ltac:(reflexivity))).\n'
s+=' contradiction.\nQed.\n'
s+='Lemma committed_register_leaves v env (committed:multiplier_committed v env) : multiplier_register_values (next_register_leaves v) env.\nProof. intros index inside.\n'
for i,r in sorted(byindex.items()):
 s+=f''' destruct inside as [same|inside].
 - subst index. have Known:=committed {r} (ltac:(unfold List.In;tauto)).
   change (VM.find {r} env=Some(next_register_value v {r})). exact Known.
'''
s+=' contradiction.\nQed.\nPrint Assumptions committed_register_leaves.\n'
(H/'RuntimeWords.v').write_text(s)

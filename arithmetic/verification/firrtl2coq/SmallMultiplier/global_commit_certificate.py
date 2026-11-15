from pathlib import Path
import json
H=Path(__file__).resolve().parent
m=json.loads((H/'stable-nodes.json').read_text());idx=json.loads((H/'global-key-index.json').read_text())
s='''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts GlobalLocalFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalLookups GlobalInstances GlobalLeaves InstanceChecks GlobalProgressTypes PipelineCommit.
Local Open Scope N_scope.
Lemma global_root_agrees v states env
 (values:forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v))
 (found:SVM.find [::] states=Some env) :
 forall id,root_domain id -> VM.find id env=VM.find id(global_env_root v).
Proof.
 intros id inside.
 have Member:List.In id (List.map N.of_nat (List.seq 0 421)).
 { rewrite -(Nnat.N2Nat.id id). apply List.in_map. apply List.in_seq. destruct inside as [Bound Rest]. lia. }
 change (List.In id [::'''+ ';'.join(map(str,range(421)))+''']) in Member.
'''
for id in range(421):
 s+=' destruct Member as [Same|Member].\n - subst id. '
 if 7<=id<37:s+='unfold root_domain in inside; lia.\n'
 else:
  n=idx[':'+str(id)]
  s+=f'''have Known:=values {n}%nat (ltac:(lia)).
   change (circuit_lookup [::] {id} states=Some(global_target_at {n}%nat v)) in Known.
   unfold circuit_lookup in Known. rewrite found in Known.
   rewrite global_lookup_{n}. exact Known.
'''
s+=' contradiction.\nQed.\n'
for id in m['registers']:
 n=idx[':'+str(id)];w=m['root_types'][str(id)][1]
 s+=f'''Lemma global_commit_{id} invalid v snapshot final
 (values:forall index,Nat.lt index 2262 -> global_value_at index snapshot=Some(global_target_at index v))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot true=Some final) :
 circuit_lookup [::] {id} final=Some(Gval(Fuint {w})(next_word_{id} v)).
Proof.
 eapply circuit_pass_local_value with (invalid:=invalid) (snapshot:=snapshot) (set_regs:=true) (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after Found Step. apply (commit_register_{id} (invalid [::]) v before before after); [exact(global_root_agrees v snapshot before values Found)|exact Step].
 - exact(node_sync_check_child _ _ _ _ global_leaf_{n}_sync).
 - exact(node_sync_check_parent _ _ _ _ global_leaf_{n}_sync).
 - exact ran.
Qed.
'''
(H/'GlobalCommit.v').write_text(s)

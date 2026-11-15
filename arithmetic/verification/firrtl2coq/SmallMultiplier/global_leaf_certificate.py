#!/usr/bin/env python3
from pathlib import Path
import runpy,json
H=Path(__file__).resolve().parent;x=runpy.run_path(str(H/'global_lookup_certificate.py'));g=x['g'];idx=x['idx'];typ=x['typ'];regs=json.loads((H/'stable-nodes.json').read_text())['registers']
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import StatementFacts GroundFrames HierarchyFacts GlobalLocalFacts.','From SmallMultiplier Require Import Model GlobalStable GlobalInstances FlatRegisterCheck InstanceChecks.','Local Open Scope N_scope.']
for k in g['leaves']:
 _,id=k.split(':');id=int(id);n=idx[k];gt=typ(k)
 out +=[f'Lemma global_leaf_{n}_sync : node_sync_check generated_modules multiplier_instances [::] {id}=true.','Proof. vm_compute. reflexivity. Qed.']
 if id in regs:out +=[f'Lemma global_leaf_{n}_register : flat_register_certificate {id} generated_module_3_stmts_0.','Proof. apply flat_register_check_sound. vm_compute. reflexivity. Qed.']
 out +=[f'''Lemma global_leaf_{n}_preserved invalid snapshot final value
 (known:circuit_lookup [::] {id} snapshot=Some value)
 (typed:type_of_val value=Gtyp {gt})
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] {id} final=Some value.
Proof. eapply circuit_pass_local_value with (instances:=multiplier_instances) (module_id:=3) (ports:=multiplier_ports 3) (stmts:=generated_module_3_stmts_0).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - intros before after found step. unfold circuit_lookup in known. rewrite found in known.''']
 if id in regs:out +=[f'   eapply pass_register_preserved; [exact known|exact global_leaf_{n}_register|exact step].']
 else:out +=['   eapply pass_preserves_ground with (stmts:=generated_module_3_stmts_0); [vm_compute;reflexivity|vm_compute;reflexivity|exact typed|exact known|exact step].']
 out +=[f' - exact(node_sync_check_child _ _ _ _ global_leaf_{n}_sync).',f' - exact(node_sync_check_parent _ _ _ _ global_leaf_{n}_sync).',' - exact ran.','Qed.']
(H/'GlobalLeaves.v').write_text('\n'.join(out)+'\n')

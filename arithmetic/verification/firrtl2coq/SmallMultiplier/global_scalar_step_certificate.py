#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent;x=runpy.run_path(str(H/'global_lookup_certificate.py'));g=x['g'];idx=x['idx'];typ=x['typ'];path=x['path']
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import StatementFacts GroundFrames HierarchyFacts.','From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalScalarFacts InstanceChecks ScalarCertificateCheck.','Local Open Scope N_scope.']
for k in g['order']:
 node=g['nodes'][k]
 if node['kind']!='connect':continue
 assert len(node['deps'])==1
 d=node['deps'][0];p,target=k.split(':');dp,source=d.split(':');assert dp==p
 mid=g['instances'][p];scope=path(p);n=idx[k];nd=idx[d];gt=typ(k);sgt=typ(d)
 out +=[f'''Lemma global_scalar_{n}_syntax : framed_write_certificate {target}
 (@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source}))) generated_module_{mid}_stmts_0.
Proof. apply checked_scalar_write_sound. vm_compute. reflexivity. Qed.
Lemma global_scalar_{n}_sync : node_sync_check generated_modules multiplier_instances {scope} {target} = true.
Proof. vm_compute. reflexivity. Qed.
Lemma global_scalar_{n}_type invalid snapshot final initial
 (initial_found:circuit_lookup {scope} {target} snapshot=Some initial)
 (typed:type_of_val initial=Gtyp {gt})
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 exists result,circuit_lookup {scope} {target} final=Some result /\ type_of_val result=Gtyp {gt}.
Proof. eapply circuit_pass_scalar_type with (instances:=multiplier_instances) (module_id:={mid}) (ports:=multiplier_ports {mid}) (stmts:=generated_module_{mid}_stmts_0) (source:={source}).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_{n}_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact global_scalar_{n}_sync.
 - exact ran.
Qed.
Lemma global_scalar_{n}_step invalid snapshot final v initial
 (source_found:circuit_lookup {scope} {source} snapshot=Some(Gval {sgt} (global_word_{nd} v)))
 (initial_found:circuit_lookup {scope} {target} snapshot=Some initial)
 (typed:type_of_val initial=Gtyp {gt})
 (adapted:adapt_hvalue_as_type (Gval {sgt} (global_word_{nd} v)) (Gtyp {gt})=Some(Gval {gt} (global_word_{n} v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup {scope} {target} final=Some(Gval {gt} (global_word_{n} v)).
Proof. eapply circuit_pass_scalar_value with (instances:=multiplier_instances) (module_id:={mid}) (ports:=multiplier_ports {mid}) (stmts:=generated_module_{mid}_stmts_0) (source:={source}).
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - exact global_scalar_{n}_syntax.
 - vm_compute. reflexivity.
 - reflexivity.
 - exact initial_found.
 - exact typed.
 - exact source_found.
 - exact adapted.
 - exact global_scalar_{n}_sync.
 - exact ran.
Qed.''']
(H/'GlobalScalarSteps.v').write_text('\n'.join(out)+'\n')

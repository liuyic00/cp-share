#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent
x=runpy.run_path(str(H/'global_lookup_certificate.py'));g=x['g'];idx=x['idx'];typ=x['typ'];path=x['path']
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import StatementFacts HierarchyFacts PortFieldFacts GlobalNodeFacts.','From SmallMultiplier Require Import Model GlobalStable GlobalLocal GlobalMemory GlobalInstances NodeCertificateCheck InstanceChecks.','Local Open Scope N_scope.']
count=0
for k in g['order']:
 node=g['nodes'][k]
 if node['kind']!='node':continue
 n=idx[k];p,id=k.split(':');mid=g['instances'][p];scope=path(p);gt=typ(k);count+=1
 out +=[f'Lemma global_node_{n}_syntax : node_certificate {id} global_expr_{n} generated_module_{mid}_stmts_0.','Proof. apply checked_node_sound. vm_compute. reflexivity. Qed.',f'Lemma global_node_{n}_sync : node_sync_check generated_modules multiplier_instances {scope} {id} = true.','Proof. vm_compute. reflexivity. Qed.',f'Lemma global_node_{n}_step invalid snapshot final v']
 for j,d in enumerate(node['deps']):
  dp,*r=d.split(':');read=f'circuit_lookup {path(dp)} {r[0]} snapshot' if len(r)==1 else f'circuit_interface {path(dp)} {r[0]} {r[1]} snapshot'
  out +=[f' (H{j} : {read} = Some (Gval {typ(d)} (global_word_{idx[d]} v)))']
 out +=[f' (ran : circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false = Some final) :',f' circuit_lookup {scope} {id} final = Some (Gval {gt} (global_word_{n} v)).',f'Proof. eapply circuit_pass_node_value with (instances:=multiplier_instances) (module_id:={mid}) (ports:=multiplier_ports {mid}) (stmts:=generated_module_{mid}_stmts_0) (expr:=global_expr_{n}).', ' - exact multiplier_instances_correct.', ' - vm_compute. reflexivity.',' - reflexivity.',' - reflexivity.',f' - exact global_node_{n}_syntax.',' - vm_compute. reflexivity.',f' - intros old found. rewrite global_memory_{n}. apply global_local_{n}.']
 for j,d in enumerate(node['deps']):
  _,*r=d.split(':')
  if len(r)==1:out +=[f'   + unfold circuit_lookup in H{j}. rewrite found in H{j}. exact H{j}.']
  else:out +=[f'   + unfold circuit_interface, circuit_lookup in H{j}. rewrite found in H{j}. rewrite interface_field_eval. exact H{j}.']
 out +=[f' - exact (node_sync_check_child _ _ _ _ global_node_{n}_sync).',f' - exact (node_sync_check_parent _ _ _ _ global_node_{n}_sync).',' - exact ran.','Qed.']
(H/'GlobalNodeSteps.v').write_text('\n'.join(out)+'\n');print(count,'global original node steps')

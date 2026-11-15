#!/usr/bin/env python3
from pathlib import Path
import runpy
H=Path(__file__).resolve().parent;x=runpy.run_path(str(H/'global_lookup_certificate.py'));g=x['g'];idx=x['idx'];typ=x['typ'];path=x['path'];ports=x['ports']
def plist(ps):
 return '[::'+';'.join(f'(@F{d} VarOrder.T {pid} (Gtyp '+('Fclock' if kind==2 else f'({"Fuint" if kind==0 else "Fsint"} {w})')+'))' for pid,d,kind,w in ps)+']'
out=['From Coq Require Import NArith.','From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.','From simplssrlib Require Import Types SsrOrder Var.','From nbits Require Import NBits.','From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.','From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts CircuitPortTypes.','From SmallMultiplier Require Import Model GlobalStable GlobalInstances GlobalSyncFacts InstanceChecks.','Local Open Scope N_scope.']
for k in g['order']:
 node=g['nodes'][k]
 if not node['kind'].startswith('sync'):continue
 n=idx[k];d=node['deps'][0];nd=idx[d];gt=typ(k)
 if node['kind']=='syncinput':childp,field=k.split(':');pp,*rest=childp.rsplit('/',1);parent=pp if rest else '';inst=rest[0] if rest else pp
 else:parent,inst,field=k.split(':');childp=parent+'/'+inst if parent else inst
 mid=g['instances'][childp];ps=ports[str(mid)];pos=next(i for i,p in enumerate(ps) if p[0]==int(field));prefix=plist(ps[:pos]);suffix=plist(ps[pos+1:]);parentpath=path(parent);childpath=path(childp)
 inp=node['kind']=='syncinput';direction='input' if inp else 'output'
 source=f'circuit_interface {parentpath} {inst} {field} final' if inp else f'circuit_lookup {childpath} {field} final'
 target=f'circuit_lookup {childpath} {field} final' if inp else f'circuit_interface {parentpath} {inst} {field} final'
 predicate=f'circuit_value_ground {childpath} {field} {gt} final' if inp else f'circuit_interface_ground {parentpath} {inst} {field} {gt} final'
 arguments=f'(instances:=multiplier_instances) (instance:={inst}) (parent:={parentpath}) (module_id:={mid}) (prefix:={prefix}) (suffix:={suffix}) (body:=generated_module_{mid}_stmts_0)'
 out +=[f'''Lemma global_sync_{n}_link invalid snapshot final v
 (source_after:{source}=Some(Gval {gt} (global_word_{nd} v)))
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 {target}=Some(Gval {gt} (global_word_{n} v)).
Proof. rewrite global_sync_{n}. eapply circuit_pass_{direction}_link with {arguments}.
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - vm_compute. reflexivity.
 - exact source_after.
 - exact ran.
Qed.
Lemma global_sync_{n}_type invalid snapshot final
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 {predicate}.
Proof. eapply circuit_pass_{direction}_type with {arguments}.
 - exact multiplier_instances_correct.
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - vm_compute. reflexivity.
 - exact ran.
Qed.''']
(H/'GlobalSyncSteps.v').write_text('\n'.join(out)+'\n')

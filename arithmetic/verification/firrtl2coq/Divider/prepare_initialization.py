#!/usr/bin/env python3
"""Checked initialization/leaf bridge for the unmodified divider AST."""
from pathlib import Path
import json
P=Path(__file__).resolve().parent;j=json.loads((P/'nodes.json').read_text());w={int(k):v for k,v in j['widths'].items()};regs=j['registers'];inputs=j['inputs'];outputs=[2,8,9]
def ground(id):return 'Fclock' if id==0 else f'(Fuint {w[id]})'
head='''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import InitialMapFacts RankConvergence.
From Divider Require Import Model Stable Frames Certificates SingleModule NodeProgress.
Local Open Scope N_scope.
'''
s=[head]
for id in regs:s.append(f'''Lemma initial_register_{id} : initial_register_certificate {id} generated_module_0_stmts_0.
Proof. apply checked_initial_register_sound. vm_compute. reflexivity. Qed.
''')
for id in outputs:s.append(f'''Lemma initial_output_{id}_frame : initial_sequence_frames {id} generated_module_0_stmts_0 = true.
Proof. vm_compute. reflexivity. Qed.
''')
s.append('Definition divider_register_values v (env : VM.t hvalue) := forall id, List.In id [:: '+ '; '.join(map(str,regs))+'] -> VM.find id env = VM.find id (stable_env v).\n')
s.append('Definition divider_input_values v (env : VM.t hvalue) := forall id, List.In id [:: '+ '; '.join(map(str,inputs))+'] -> VM.find id env = VM.find id (stable_env v).\n')
expr='declared'
for id in inputs:expr=f'(VM.add {id} (Gval {ground(id)} (word_{id} v)) {expr})'
s.append(f'Definition divider_externalized v (declared : VM.t hvalue) := {expr}.\n')
s.append('''Lemma divider_external_update v declared external
 (values : divider_input_values v external) :
 update_external_ports declared external divider_ports = Some (divider_externalized v declared).
Proof.
''')
for id in inputs:s.append(f' have E{id} : VM.find {id} external = Some (Gval {ground(id)} (word_{id} v)).\n {{ rewrite -(target_{id}_value v). apply values. simpl; tauto. }}\n')
s.append(' cbn [divider_ports generated_module_0 update_external_ports is_passive].\n rewrite '+ ' '.join(f'E{id}' for id in inputs)+'. reflexivity.\nQed.\n')
for id in inputs:
 s.append(f'''Lemma externalized_{id} v declared : VM.find {id} (divider_externalized v declared) = VM.find {id} (stable_env v).
Proof. rewrite (target_{id}_value v). unfold divider_externalized.
 repeat first [rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]].
Qed.
''')
for id in regs+outputs:
 s.append(f'''Lemma externalized_{id} v declared : VM.find {id} (divider_externalized v declared) = VM.find {id} declared.
Proof. unfold divider_externalized.
 repeat (rewrite VM.Lemmas.find_add_neq; [|vm_compute; discriminate]). reflexivity.
Qed.
''')
s.append('''Lemma divider_initial_ranked v previous old external states
 (old_found : SVM.find [::] previous = Some old)
 (registers : divider_register_values v old)
 (inputs : divider_input_values v external)
 (ran : circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some states) :
 exists env, SVM.find [::] states = Some env /\\ divider_ranked v O env.
Proof.
 destruct (divider_initial_local _ _ _ ran) as [declared [env [Declared [External Found]]]].
 change (statements_initial_map_with_memory generated_modules generated_module_0_stmts_0 (SVM.find [::] previous) (ports_initial_map divider_ports) = Some declared) in Declared. rewrite old_found in Declared.
 rewrite (divider_external_update v declared external inputs) in External. inversion External; subst env.
 exists (divider_externalized v declared). split; [exact Found|].
''')
for id in inputs:s.append(f' have L{id} := externalized_{id} v declared.\n')
for id in regs:
 s.append(f''' have L{id} : VM.find {id} (divider_externalized v declared) = VM.find {id} (stable_env v).
 {{ rewrite externalized_{id} (target_{id}_value v).
    eapply initial_register_value; [|exact initial_register_{id}|exact Declared].
    rewrite -(target_{id}_value v). apply registers. simpl; tauto. }}
''')
for id in outputs:
 s.append(f''' have T{id} : VM.find {id} (divider_externalized v declared) = Some (Needtobedefined (Gtyp {ground(id)})).
 {{ rewrite externalized_{id} (initial_sequence_preserves _ _ _ _ _ _ initial_output_{id}_frame Declared). reflexivity. }}
''')
s.append(' split.\n - intros id inside bound. apply divider_domain_cases in inside. unfold divider_ids in inside.\n')
s.append('   repeat destruct inside as [same|inside]; try contradiction; subst id; cbn [dependency_rank] in bound; try lia; assumption.\n')
s.append(' - split; [exists (Needtobedefined (Gtyp (Fuint 1))); split; [exact T2|reflexivity]|].\n   split; [exists (Needtobedefined (Gtyp (Fuint 1))); split; [exact T8|reflexivity]|].\n   exists (Needtobedefined (Gtyp (Fuint 64))); split; [exact T9|reflexivity].\nQed.\nPrint Assumptions divider_initial_ranked.\n')
(P/'Initialization.v').write_text(''.join(s))

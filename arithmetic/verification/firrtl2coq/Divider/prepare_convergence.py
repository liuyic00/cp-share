#!/usr/bin/env python3
"""Generate checked rank progress for the original divider interpreter."""
from pathlib import Path
import json,re
P=Path(__file__).resolve().parent
j=json.loads((P/'nodes.json').read_text())
width={int(k):v for k,v in j['widths'].items()}; regs=j['registers']; inputs=j['inputs']; order=j['order']; ex=j['expressions']
leaves=sorted(regs+inputs); outputs=[2,8,9]
s=['''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts ConnectionFacts GroundFrames ScalarEvaluation
 ScalarExtensionality RankConvergence InstanceFoldFacts.
From Divider Require Import Model Stable Typing Certificates Frames SingleModule.
Local Open Scope N_scope.
Definition divider_ids : list N := ('''+ '[:: '+ '; '.join(map(str,sorted(width))) + ''']).
Definition divider_domain (id : N) : Prop := N.lt id 484.
Lemma divider_domain_cases id : divider_domain id -> List.In id divider_ids.
Proof.
 intro inside. unfold divider_domain in inside.
 change (List.In id (List.map N.of_nat (List.seq 0 484))).
 rewrite -(Nnat.N2Nat.id id). apply List.in_map. apply List.in_seq. lia.
Qed.
Definition divider_output_types (env : VM.t hvalue) : Prop :=
 (exists value, VM.find 2 env = Some value /\\ type_of_val value = Gtyp (Fuint 1)) /\\
 (exists value, VM.find 8 env = Some value /\\ type_of_val value = Gtyp (Fuint 1)) /\\
 (exists value, VM.find 9 env = Some value /\\ type_of_val value = Gtyp (Fuint 64)).
Section Progress.
Variable v : leaf_values.
''']
for id in leaves:s.append(f'Hypothesis leaf_{id}_size : size (v {id}) = {width[id]}%nat.\n')
s.append('Definition divider_ranked n env := rank_agrees_on divider_domain dependency_rank (stable_env v) n env /\\ divider_output_types env.\n')
for id in order:
 if id in outputs:continue
 s.append(f'''Lemma pass_node_{id} invalid n old before after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (bound : Nat.le (dependency_rank {id}) (S n))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find {id} after = VM.find {id} (stable_env v).
Proof.
 eapply ranked_pass_node_on with (expr:=expr_{id}); [exact agree|reflexivity| |exact bound|exact node_{id}_certificate|exact node_{id}_not_register|exact (node_{id}_value v)|exact (target_{id}_value v)|exact ran].
 intros dep occurs. split.
 - cbn [expr_{id} scalar_refs List.In] in occurs.
   repeat destruct occurs as [occurs|occurs]; try contradiction; subst dep; unfold divider_domain; vm_compute; reflexivity.
 - apply/ltP. exact (node_{id}_dependencies dep occurs).
Qed.
''')
for id in outputs:
 source=int(re.search(r'Eid VarOrder.T (\d+)',ex[str(id)])[1]);w=width[id]
 s.append(f'''Lemma pass_output_{id}_type invalid old before after value
 (found : VM.find {id} before = Some value) (typed : type_of_val value = Gtyp (Fuint {w}))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 exists result, VM.find {id} after = Some result /\\ type_of_val result = Gtyp (Fuint {w}).
Proof.
 eapply pass_framed_write_ground_type; [exact output_{id}_certificate|exact output_{id}_not_register|exact typed|exact found| |exact ran].
 intros position initial final initial_value lookup initial_type step.
 eapply bidirectional_eid_preserves_target_type with (source:={source}) (target:={id}) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite initial_type. reflexivity.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
Lemma pass_output_{id} invalid n old before after value
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (bound : Nat.le (dependency_rank {id}) (S n))
 (found : VM.find {id} before = Some value) (typed : type_of_val value = Gtyp (Fuint {w}))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find {id} after = VM.find {id} (stable_env v).
Proof.
 have source_eq : VM.find {source} old = VM.find {source} (stable_env v).
 {{ apply agree; [unfold divider_domain; vm_compute; reflexivity|].
    have smaller : Nat.lt (dependency_rank {source}) (dependency_rank {id}) by vm_compute; repeat constructor.
    lia. }}
 rewrite (target_{id}_value v).
 eapply pass_framed_write_value; [exact output_{id}_certificate|exact output_{id}_not_register|exact typed|exact found| |exact ran].
 intros position initial final lookup step.
 eapply bidirectional_eid_target with (value:=Gval (Fuint {w}) (word_{source} v)) (source:={source}) (target:={id}) (mm:=empty_memory_map) (before:=initial) (after:=final) (old:=old); [reflexivity| | | |].
 - cbn [eval_type_of_ref]. rewrite lookup. cbn [option_map]. rewrite typed. reflexivity.
 - change (VM.find {source} old = Some (Gval (Fuint {w}) (word_{source} v))).
   rewrite source_eq. exact (target_{source}_value v).
 - have size_source : size (word_{source} v) = {w}%nat by (apply word_{source}_size; assumption).
   change (Some (Gval (Fuint {w}) (zext_to {w} (take {w} (word_{source} v)))) = Some (Gval (Fuint {w}) (word_{id} v))).
   have trim : zext_to {w} (take {w} (word_{source} v)) = word_{source} v.\n   {{ rewrite -size_source take_size /zext_to subnn zext0. reflexivity. }}\n   rewrite trim.
   change (Some (Gval (Fuint {w}) (word_{source} v)) = Some (Gval (Fuint {w}) (word_{id} v))).
   have same := node_{id}_value v.\n   change (VM.find {source} (stable_env v) = Some (Gval (Fuint {w}) (word_{id} v))) in same.\n   rewrite (target_{source}_value v) in same. exact same.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
''')

for id in leaves:
 ground='Fclock' if id==0 else f'(Fuint {width[id]})'
 s.append(f"""Lemma pass_leaf_{id} invalid n old after
 (agree : rank_agrees_on divider_domain dependency_rank (stable_env v) n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 VM.find {id} after = VM.find {id} (stable_env v).
Proof.
 have known : VM.find {id} old = Some (Gval {ground} (word_{id} v)).
 {{ rewrite -(target_{id}_value v). apply agree; [unfold divider_domain; vm_compute; reflexivity|change (Nat.le O n); lia]. }}
 rewrite (target_{id}_value v).
""")
 if id in regs:s.append(f' eapply pass_register_preserved; [exact known|exact register_{id}_certificate|exact ran].\nQed.\n')
 else:s.append(f' eapply pass_preserves_ground; [exact input_{id}_frame|exact input_{id}_not_register|reflexivity|exact known|exact ran].\nQed.\n')
s.append("""Lemma divider_pass_rank_progress invalid n old after
 (ranked : divider_ranked n old)
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false old generated_module_0_stmts_0 = Some after) :
 divider_ranked (S n) after.
Proof.
 destruct ranked as [agree [T2 [T8 T9]]].
 destruct T2 as [value2 [found2 typed2]].
 destruct T8 as [value8 [found8 typed8]].
 destruct T9 as [value9 [found9 typed9]]. split.
 - intros id inside bound. apply divider_domain_cases in inside. unfold divider_ids in inside.
""")
for id in sorted(width):
 s.append(f'   destruct inside as [same|inside].\n   + subst id. ')
 if id in leaves:s.append(f'eapply pass_leaf_{id}; eassumption.\n')
 elif id in outputs:s.append(f'eapply pass_output_{id}; eauto.\n')
 else:s.append(f'eapply pass_node_{id}; eassumption.\n')
s.append('   contradiction.\n - split; [eapply pass_output_2_type; eassumption|]. split; [eapply pass_output_8_type; eassumption|eapply pass_output_9_type; eassumption].\nQed.\n')

s.append(r"""Lemma divider_domain_rank_bound id (inside : divider_domain id) : Nat.le (dependency_rank id) 25.
Proof.
 apply divider_domain_cases in inside. unfold divider_ids in inside.
 repeat destruct inside as [same|inside]; try contradiction; subst id; vm_compute; repeat constructor.
Qed.
Definition divider_circuit_ranked n states := exists env,
 SVM.find [::] states = Some env /\ divider_ranked n env.
Lemma divider_circuit_rank_progress inputs n states final
 (ranked : divider_circuit_ranked n states)
 (ran : circuit_value_iter_with_memory_policy (formal_invalid_policy inputs)
  generated_modules generated_top states false = Some final) :
 divider_circuit_ranked (S n) final.
Proof.
 destruct ranked as [env [Found Ranked]].
 destruct (divider_iteration_local _ _ _ _ ran) as [before [after [Before [Step After]]]].
 rewrite Found in Before. inversion Before; subst before.
 exists after. split; [exact After|]. eapply divider_pass_rank_progress; eassumption.
Qed.
Lemma divider_iterations_ranked inputs count states final
 (ranked : divider_circuit_ranked O states)
 (ran : circuit_formal_iterations generated_modules generated_top inputs count states = Some final) :
 divider_circuit_ranked count final.
Proof.
 have progress := formal_iterations_rank_progress generated_modules generated_top inputs
  divider_circuit_ranked (divider_circuit_rank_progress inputs) count O states final ranked ran.
 rewrite Nat.add_0_r in progress. exact progress.
Qed.
Lemma divider_iterations_converge inputs count states final
 (ranked : divider_circuit_ranked O states)
 (enough : Nat.le 25 count)
 (ran : circuit_formal_iterations generated_modules generated_top inputs count states = Some final) :
 exists env, SVM.find [::] final = Some env /\
 (forall id, divider_domain id -> VM.find id env = VM.find id (stable_env v)) /\ divider_output_types env.
Proof.
 destruct (divider_iterations_ranked inputs count states final ranked ran) as [env [Found [Agree Types]]].
 exists env. split; [exact Found|]. split; [|exact Types].
 intros id inside. apply Agree; [exact inside|].
 have bound := divider_domain_rank_bound id inside. lia.
Qed.
""")
s.append('End Progress.\nPrint Assumptions divider_iterations_converge.\n')
text=''.join(s)
cut=text.index('Lemma pass_output_2_type')
(P/'NodeProgress.v').write_text(text[:cut]+'End Progress.\nPrint Assumptions pass_node_483.\n')
imports=text[:text.index('Definition divider_ids')]
section=text[text.index('Section Progress.'):text.index('Definition divider_ranked')]
(P/'Convergence.v').write_text(imports+'From Divider Require Import NodeProgress.\n'+section+text[cut:].replace('divider_ranked', '(divider_ranked v)'))

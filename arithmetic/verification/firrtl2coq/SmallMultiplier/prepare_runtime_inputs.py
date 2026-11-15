from pathlib import Path
import json
H=Path(__file__).resolve().parent
idx=json.loads((H/'global-key-index.json').read_text());m=json.loads((H/'stable-nodes.json').read_text());regindices=sorted(idx[':'+str(r)] for r in m['registers']);ports={idx[':'+str(r)]:r for r in range(6)}
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalInitialLocal GlobalProgressTypes PipelineInvariant.
Local Open Scope N_scope.
Lemma ground_external_port_defined external id ground
 (defined:external_port_defined external (@Finput VarOrder.T id (Gtyp ground))=true) :
 exists bits,VM.find id external=Some(Gval ground bits) /\ size bits=sizeof_fgtyp ground.
Proof.
 cbn [external_port_defined type_has_input] in defined.
 destruct (VM.find id external) as [value|] eqn:Found; [|discriminate].
 destruct value; cbn [known_input_value type_has_input] in defined; try discriminate.
 move/andP:defined => [/eqP Same /eqP Sized]. subst f.
 exists b;split;[reflexivity|exact Sized].
Qed.
Definition external_bits (inputs:formal_inputs) (id:VarOrder.T) :=
 match VM.find id (formal_external_inputs inputs) with Some(Gval _ b)=>b|_=>[::]end.
Lemma all_list_member (A:Type) (test:A->bool) items :
 forall item,all test items=true -> List.In item items -> test item=true.
Proof.
 induction items as [|head tail IH];intros item checked member;[contradiction|].
 move/andP:checked => [H T]. destruct member as [same|member];[subst;exact H|eapply IH;eassumption].
Qed.
Lemma runtime_external_port inputs id ground
 (member:List.In (Finput id (Gtyp ground)) (multiplier_ports 3))
 (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find id (formal_external_inputs inputs)=Some(Gval ground(external_bits inputs id)) /\\ size(external_bits inputs id)=sizeof_fgtyp ground.
Proof.
 have Ports:all (external_port_defined(formal_external_inputs inputs)) (multiplier_ports 3)=true by exact defined.
 have Port:=all_list_member _ _ _ _ Ports member.
 destruct (ground_external_port_defined _ _ _ Port) as [bits [Found Sized]].
 unfold external_bits. rewrite Found. split;[reflexivity|exact Sized].
Qed.
'''
for r in range(6):
 ground='Fclock' if r==0 else f'(Fuint {8 if r in [2,3] else 1})'
 s+=f'''Lemma runtime_port_{r} inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 VM.find {r} (formal_external_inputs inputs)=Some(Gval {ground}(external_bits inputs {r})) /\\ size(external_bits inputs {r})={8 if r in [2,3] else 1}%nat.
Proof. apply runtime_external_port;[vm_compute;tauto|exact defined]. Qed.
'''
s+='Definition runtime_leaves (v:global_leaves) inputs : global_leaves := fun index=>match N.of_nat index with\n'
for i,r in ports.items():s+=f'| {i}=>external_bits inputs {r}\n'
s+='| _=>v index end.\n'
s+='''Lemma runtime_input_values v inputs (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 multiplier_input_values (runtime_leaves v inputs) (formal_external_inputs inputs).
Proof. repeat split.
'''
for r in range(6):s+=f' exact(proj1(runtime_port_{r} inputs defined)).\n'
s+='Qed.\n'
s+='''Lemma runtime_leaf_sizes v inputs (sized:global_leaf_sizes v) (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 global_leaf_sizes(runtime_leaves v inputs).
Proof. intros index inside.
 have Member:List.In index (List.seq 0 62) by apply List.in_seq; move/ltP:inside;lia.
 change (List.In index [::'''+ ';'.join(f'{i}%nat' for i in range(62))+''']) in Member.
'''
for i in range(62):
 s+=' destruct Member as [same|Member].\n - subst index. '
 s+=f'exact(proj2(runtime_port_{ports[i]} inputs defined)).\n' if i in ports else f'exact(sized {i}%nat (ltac:(reflexivity))).\n'
s+=' contradiction.\nQed.\n'
s+='''Lemma runtime_register_values v inputs env (registers:multiplier_register_values v env) :
 multiplier_register_values(runtime_leaves v inputs) env.
Proof. intros index inside.
'''
for i in regindices:
 s+=f''' destruct inside as [same|inside].
 - subst index. exact(registers {i}%nat (ltac:(unfold List.In;tauto))).
'''
s+=' contradiction.\nQed.\n'
s+='''Lemma runtime_invariant v inputs (invariant:pipeline_invariant v) : pipeline_invariant(runtime_leaves v inputs).
Proof. exact invariant. Qed.
'''
(H/'RuntimeInputs.v').write_text(s)

from pathlib import Path
import json
H=Path(__file__).resolve().parent
regs=json.loads((H/'stable-nodes.json').read_text())['registers']
s=r'''From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalInitialLocal PipelineCommit GlobalCommit ObservationBridge.
Local Open Scope N_scope.
Local Opaque circuit_initial_map_with_memory circuit_iter_count_with_memory circuit_formal_iterations circuit_value_iter_with_memory_policy.
Lemma multiplier_cycle_decompose previous inputs final
 (ran:circuit_formal_cycle generated_modules generated_top (Some previous) inputs=Some final) :
 exists stable, multiplier_observe previous inputs=Some stable /\
 circuit_value_iter_with_memory_policy (formal_invalid_policy inputs) generated_modules generated_top stable true=Some final.
Proof.
 unfold circuit_formal_cycle in ran. unfold multiplier_observe.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Initial; [|discriminate].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count) as [count|] eqn:Count; [|discriminate].
 destruct (circuit_formal_iterations generated_modules generated_top inputs count initial) as [stable|] eqn:Settled; [|discriminate].
 exists stable. split; [reflexivity|exact ran].
Qed.
Theorem multiplier_cycle_registers v previous old inputs final
 (sized:global_leaf_sizes v)
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v (formal_external_inputs inputs))
 (ran:circuit_formal_cycle generated_modules generated_top (Some previous) inputs=Some final) :
 exists after,SVM.find [::] final=Some after /\ multiplier_committed v after.
Proof.
 destruct (multiplier_cycle_decompose previous inputs final ran) as [stable [Observed Committed]].
 have Values:=multiplier_observation_values v previous old inputs stable sized old_found registers ports Observed.
 have First:=global_commit_201 (formal_invalid_policy inputs) v stable final Values Committed.
 unfold circuit_lookup in First.
 destruct (SVM.find [::] final) as [after|] eqn:Found; [|discriminate].
 exists after. split; [reflexivity|].
 unfold multiplier_committed. intros id inside.
'''
for r in regs:
 s+=f''' destruct inside as [same|inside].
 - subst id. have Value:=global_commit_{r} (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
'''
s+=' contradiction.\nQed.\nPrint Assumptions multiplier_cycle_registers.\n'
(H/'CycleBridge.v').write_text(s)

From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From SmallMultiplier Require Model.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInitialLocal GlobalProgressTypes PipelineInvariant RuntimeInputs RuntimeState RuntimeReset ObservationBridge RuntimeObservation.
Module Tool := SmallMultiplier.Model.
Local Opaque circuit_initial_map_with_memory circuit_iter_count_with_memory circuit_formal_iterations.
Lemma observe_cycle_matches previous inputs : Tool.generated_observe_cycle previous inputs=multiplier_observe previous inputs.
Proof. unfold Tool.generated_observe_cycle,multiplier_observe. reflexivity. Qed.
Local Opaque formal_run_after_reset multiplier_observe circuit_formal_cycle circuit_formal_run circuit_symbolic_initial_state formal_state_after_reset.
Lemma generated_run_matches contents inputs k : Tool.generated_run contents inputs k=
 formal_run_after_reset Model.generated_modules Model.generated_top 1%num (Fuint 1) contents inputs k.
Proof. unfold Tool.generated_run. reflexivity. Qed.
Local Opaque Tool.generated_run Tool.generated_observe_cycle.
Lemma generated_run_invariant contents inputs k states
 (defined:forall j,Nat.le j k -> formal_external_inputs_defined Model.generated_modules Model.generated_top (inputs j)=true)
 (ran:Tool.generated_run contents inputs k=Some states) : invariant_state states.
Proof. rewrite generated_run_matches in ran. exact(invariant_run_after_reset contents inputs k states defined ran). Qed.
Lemma legal_inputs_defined contents inputs k
 (legal:Tool.generated_legal_trace contents inputs k) :
 (forall j,Nat.le j k -> formal_external_inputs_defined Model.generated_modules Model.generated_top (inputs j)=true) /\
 formal_external_inputs_defined Model.generated_modules Model.generated_top (inputs(S k))=true.
Proof.
 destruct legal as [Defined Legal]. split.
 - intros j Bound.
   destruct j as [|j];[exact Defined|]. exact(proj1(Legal j (ltac:(lia)))).
 -  exact(proj1(Legal k (Nat.le_refl k))).
Qed.
Lemma observation_success (State:Type) (run:option State) (observe:State->option State) states
 (observed:(match run with Some previous=>observe previous|None=>None end)=Some states) :
 exists previous,run=Some previous /\ observe previous=Some states.
Proof. destruct run as [previous|];[exists previous;split;[reflexivity|exact observed]|discriminate]. Qed.
Theorem generated_observation_values contents inputs k states
 (observed:Tool.generated_observe contents inputs k=Some states)
 (legal:Tool.generated_legal_trace contents inputs k) :
 exists v,global_leaf_sizes v /\ pipeline_invariant v /\
 (forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)).
Proof.
 destruct(legal_inputs_defined contents inputs k legal) as [AllDefined Current].
 unfold Tool.generated_observe in observed.
 destruct(observation_success _ (Tool.generated_run contents inputs k) (fun previous=>Tool.generated_observe_cycle previous (Tool.generated_observation_input inputs k)) states observed) as [previous [Ran Observed]].
 have Invariant:=generated_run_invariant contents inputs k previous AllDefined Ran.
 rewrite observe_cycle_matches in Observed.
 exact(invariant_observation_values previous (inputs(S k)) states Invariant Current Observed).
Qed.

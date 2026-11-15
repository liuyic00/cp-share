From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInitialLocal GlobalProgressTypes PipelineInvariant RuntimeInputs RuntimeState ObservationBridge.
Local Opaque multiplier_observe.
Theorem invariant_observation_values previous inputs states
 (invariant:invariant_state previous)
 (defined:formal_external_inputs_defined generated_modules generated_top inputs=true)
 (observed:multiplier_observe previous inputs=Some states) :
 exists v,global_leaf_sizes v /\ pipeline_invariant v /\
 (forall index,Nat.lt index 2262 -> global_value_at index states=Some(global_target_at index v)).
Proof.
 destruct invariant as [v [old [Found [Sizes [Registers Inv]]]]].
 exists(runtime_leaves v inputs).
 split;[apply runtime_leaf_sizes;assumption|]. split;[apply runtime_invariant;exact Inv|].
 exact(multiplier_observation_values (runtime_leaves v inputs) previous old inputs states
 (runtime_leaf_sizes v inputs Sizes defined) Found (runtime_register_values v inputs old Registers)
 (runtime_input_values v inputs defined) observed).
Qed.

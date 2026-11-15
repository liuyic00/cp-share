From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInitialLocal PipelineCommit RuntimeWords PipelineInvariant RuntimeInputs CycleBridge.
Local Open Scope N_scope.
Definition represented_state (states:SVM.t(VM.t hvalue)) : Prop := exists v env,
 SVM.find [::] states=Some env /\ global_leaf_sizes v /\ multiplier_register_values v env.
Definition invariant_state (states:SVM.t(VM.t hvalue)) : Prop := exists v env,
 SVM.find [::] states=Some env /\ global_leaf_sizes v /\ multiplier_register_values v env /\ pipeline_invariant v.
Local Opaque circuit_formal_cycle.
Theorem invariant_cycle previous inputs final
 (invariant:invariant_state previous)
 (defined:formal_external_inputs_defined generated_modules generated_top inputs=true)
 (ran:circuit_formal_cycle generated_modules generated_top (Some previous) inputs=Some final) : invariant_state final.
Proof.
 destruct invariant as [v [old [Found [Sized [Registers Invariant]]]]].
 have Sizes:=runtime_leaf_sizes v inputs Sized defined.
 have Regs:=runtime_register_values v inputs old Registers.
 have Ports:=runtime_input_values v inputs defined.
 destruct (multiplier_cycle_registers (runtime_leaves v inputs) previous old inputs final Sizes Found Regs Ports ran) as [after [After Updated]].
 exists (next_register_leaves(runtime_leaves v inputs)),after.
 split;[exact After|]. split;[apply next_register_leaves_sizes;exact Sizes|].
 split;[apply committed_register_leaves;exact Updated|].
 apply pipeline_invariant_step;[exact Sizes|apply runtime_invariant;exact Invariant].
Qed.
Theorem invariant_reset_cycle previous inputs final
 (represented:represented_state previous)
 (defined:formal_external_inputs_defined generated_modules generated_top inputs=true)
 (reset:external_bits inputs 1=[::true])
 (ran:circuit_formal_cycle generated_modules generated_top (Some previous) inputs=Some final) : invariant_state final.
Proof.
 destruct represented as [v [old [Found [Sized Registers]]]].
 have Sizes:=runtime_leaf_sizes v inputs Sized defined.
 have Regs:=runtime_register_values v inputs old Registers.
 have Ports:=runtime_input_values v inputs defined.
 destruct (multiplier_cycle_registers (runtime_leaves v inputs) previous old inputs final Sizes Found Regs Ports ran) as [after [After Updated]].
 exists (next_register_leaves(runtime_leaves v inputs)),after.
 split;[exact After|]. split;[apply next_register_leaves_sizes;exact Sizes|].
 split;[apply committed_register_leaves;exact Updated|].
 apply pipeline_invariant_reset;[exact Sizes|exact reset].
Qed.
Theorem invariant_run initial inputs k final
 (invariant:invariant_state initial)
 (defined:forall j,Nat.lt j k -> formal_external_inputs_defined generated_modules generated_top (inputs j)=true)
 (ran:circuit_formal_run generated_modules generated_top initial inputs k=Some final) : invariant_state final.
Proof.
 revert final defined ran. induction k as [|k IH];intros final defined ran.
 - cbn [circuit_formal_run] in ran. inversion ran;subst final. exact invariant.
 - cbn [circuit_formal_run] in ran.
   destruct (circuit_formal_run generated_modules generated_top initial inputs k) as [previous|] eqn:Previous;[|discriminate].
   eapply invariant_cycle with (previous:=previous) (inputs:=inputs k);[eapply IH;[intros;apply defined;lia|reflexivity]|apply defined;lia|exact ran].
Qed.

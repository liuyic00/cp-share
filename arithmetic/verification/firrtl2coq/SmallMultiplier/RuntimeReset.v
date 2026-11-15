From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From SmallMultiplier Require Import Model GlobalInstances RuntimeInputs RuntimeState RuntimeSeed.
Local Open Scope N_scope.
Definition reset_input:=force_formal_reset 1 (Fuint 1).
Lemma reset_input_defined inputs
 (defined:formal_external_inputs_defined generated_modules generated_top inputs=true) :
 formal_external_inputs_defined generated_modules generated_top (reset_input inputs)=true.
Proof.
 destruct(runtime_port_0 inputs defined) as [Found0 Sized0].
 destruct(runtime_port_2 inputs defined) as [Found2 Sized2].
 destruct(runtime_port_3 inputs defined) as [Found3 Sized3].
 destruct(runtime_port_4 inputs defined) as [Found4 Sized4].
 destruct(runtime_port_5 inputs defined) as [Found5 Sized5].
 change (all (external_port_defined(formal_external_inputs(reset_input inputs))) (multiplier_ports 3)=true).
 let ports := eval vm_compute in (multiplier_ports 3) in change (all (external_port_defined(formal_external_inputs(reset_input inputs))) ports=true).
 cbn [all external_port_defined type_has_input reset_input force_formal_reset formal_external_inputs].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 rewrite Found0 Found2 Found3 Found4 Found5.
 cbn [known_input_value type_has_input]. rewrite Sized0 Sized2 Sized3 Sized4 Sized5. reflexivity.
Qed.
Lemma reset_input_high inputs : external_bits (reset_input inputs) 1=[::true].
Proof. unfold external_bits,reset_input,force_formal_reset. cbn [formal_external_inputs]. rewrite VM.Lemmas.find_add_eq;reflexivity. Qed.
Local Opaque circuit_symbolic_initial_state circuit_formal_cycle.
Theorem invariant_after_reset contents inputs states
 (defined:formal_external_inputs_defined generated_modules generated_top inputs=true)
 (ran:formal_state_after_reset generated_modules generated_top 1 (Fuint 1) contents inputs=Some states) : invariant_state states.
Proof.
 unfold formal_state_after_reset in ran.
 destruct(circuit_symbolic_initial_state generated_modules generated_top contents inputs) as [initial|] eqn:Initial;[|discriminate].
 eapply invariant_reset_cycle with (previous:=initial) (inputs:=reset_input inputs).
 - exact(represented_symbolic_initial contents inputs initial Initial).
 - exact(reset_input_defined inputs defined).
 - exact(reset_input_high inputs).
 - exact ran.
Qed.
Theorem invariant_run_after_reset contents inputs k final
 (defined:forall j,Nat.le j k -> formal_external_inputs_defined generated_modules generated_top (inputs j)=true)
 (ran:formal_run_after_reset generated_modules generated_top 1 (Fuint 1) contents inputs k=Some final) : invariant_state final.
Proof.
 unfold formal_run_after_reset in ran.
 destruct(formal_state_after_reset generated_modules generated_top 1 (Fuint 1) contents (inputs 0%nat)) as [initial|] eqn:Initial;[|discriminate].
 eapply invariant_run with (initial:=initial) (inputs:=fun n=>inputs(S n)) (k:=k).
 - eapply invariant_after_reset with (contents:=contents) (inputs:=inputs 0%nat);[apply defined;lia|exact Initial].
 - intros j Bound. apply defined. lia.
 - exact ran.
Qed.
Print Assumptions invariant_run_after_reset.

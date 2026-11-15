From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From Divider Require Import Model Representation RuntimeInputs RuntimeState RuntimeSeed.
Local Open Scope N_scope.
Definition reset_input := force_formal_reset 1 (Fuint 1).
Lemma reset_input_defined inputs
 (defined:formal_external_inputs_defined generated_modules generated_top inputs = true) :
 formal_external_inputs_defined generated_modules generated_top (reset_input inputs) = true.
Proof.
 destruct (runtime_port_0 inputs defined) as [Found0 Sized0].
 destruct (runtime_port_3 inputs defined) as [Found3 Sized3].
 destruct (runtime_port_4 inputs defined) as [Found4 Sized4].
 destruct (runtime_port_5 inputs defined) as [Found5 Sized5].
 destruct (runtime_port_6 inputs defined) as [Found6 Sized6].
 destruct (runtime_port_7 inputs defined) as [Found7 Sized7].
 destruct (runtime_port_10 inputs defined) as [Found10 Sized10].
 destruct (runtime_port_11 inputs defined) as [Found11 Sized11].
 destruct (runtime_port_12 inputs defined) as [Found12 Sized12].
 change (all (external_port_defined (formal_external_inputs (reset_input inputs))) RuntimeInputs.divider_ports = true).
 cbn [RuntimeInputs.divider_ports generated_module_0 all external_port_defined type_has_input reset_input force_formal_reset formal_external_inputs].
 repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
 rewrite Found0 Found3 Found4 Found5 Found6 Found7 Found10 Found11 Found12.
 cbn [known_input_value type_has_input].
 rewrite Sized0 Sized3 Sized4 Sized5 Sized6 Sized7 Sized10 Sized11 Sized12. reflexivity.
Qed.
Lemma reset_input_high inputs : Radix2Divider.CIRCTBits.word 1 (Reference.nreset (runtime_inputs (reset_input inputs))) = 1%Z.
Proof.
 unfold runtime_inputs, external_bits, reset_input, force_formal_reset. cbn [formal_external_inputs Reference.nreset].
 rewrite VM.Lemmas.find_add_eq; [reflexivity|reflexivity].
Qed.
Local Opaque circuit_symbolic_initial_state circuit_formal_cycle Reference.step.
Lemma runtime_reset memory inputs states
 (defined:formal_external_inputs_defined generated_modules generated_top inputs = true)
 (ran:formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states) :
 state_matches (Reference.step (seed_state inputs) (runtime_inputs (reset_input inputs))) states.
Proof.
 unfold formal_state_after_reset in ran.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Initial; [|discriminate].
 eapply runtime_cycle; [eapply runtime_symbolic_initial; exact Initial|apply reset_input_defined; exact defined|exact ran].
Qed.
Lemma runtime_run initial state inputs k final
 (matches:state_matches state initial)
 (defined:forall j, (j < k)%coq_nat -> formal_external_inputs_defined generated_modules generated_top (inputs j) = true)
 (ran:circuit_formal_run generated_modules generated_top initial inputs k = Some final) :
 state_matches (Reference.run state (fun j => runtime_inputs (inputs j)) k) final.
Proof.
 revert final defined ran. induction k as [|k IH]; intros final defined ran.
 - cbn [circuit_formal_run] in ran. inversion ran; subst final. exact matches.
 - cbn [circuit_formal_run] in ran.
   destruct (circuit_formal_run generated_modules generated_top initial inputs k) as [previous|] eqn:Previous; [|discriminate].
   change (state_matches (Reference.step (Reference.run state (fun j => runtime_inputs (inputs j)) k) (runtime_inputs (inputs k))) final).
   eapply runtime_cycle; [eapply IH; [intros; apply defined; lia|reflexivity]|apply defined; lia|exact ran].
Qed.

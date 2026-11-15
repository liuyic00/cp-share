From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Model Stable Representation SingleModule RuntimeInputs RuntimeState.
Local Open Scope N_scope.
Definition seed_bits (inputs:formal_inputs) (id:N) width := proj1_sig (formal_symbolic_inputs inputs [::] [::0%nat;N.to_nat id] [::] width).
Lemma seed_bits_size inputs id width : size (seed_bits inputs id width) = width.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs [::] [::0%nat;N.to_nat id] [::] width)). Qed.
Definition seed_leaves inputs : leaf_values := fun id => match id with
| 13 => seed_bits inputs 13 3
| 18 => seed_bits inputs 18 1
| 20 => seed_bits inputs 20 129
| 33 => seed_bits inputs 33 1
| 38 => seed_bits inputs 38 1
| 40 => seed_bits inputs 40 64
| 43 => seed_bits inputs 43 65
| 45 => seed_bits inputs 45 1
| 46 => seed_bits inputs 46 1
| 47 => seed_bits inputs 47 1
| 51 => seed_bits inputs 51 6
| 445 => seed_bits inputs 445 1
| 446 => seed_bits inputs 446 3
| 447 => seed_bits inputs 447 6
| 475 => seed_bits inputs 475 1
| 476 => seed_bits inputs 476 64
| _ => [::] end.
Definition seed_state inputs := project_state (seed_leaves inputs).
Lemma seed_registers_expanded inputs env : initialize_symbolic_registers inputs [::] generated_module_0_stmts_0 env =
(VM.add 476 (Gval (Fuint 64) (seed_bits inputs 476 64)) (VM.add 475 (Gval (Fuint 1) (seed_bits inputs 475 1)) (VM.add 447 (Gval (Fuint 6) (seed_bits inputs 447 6)) (VM.add 446 (Gval (Fuint 3) (seed_bits inputs 446 3)) (VM.add 445 (Gval (Fuint 1) (seed_bits inputs 445 1)) (VM.add 51 (Gval (Fuint 6) (seed_bits inputs 51 6)) (VM.add 47 (Gval (Fuint 1) (seed_bits inputs 47 1)) (VM.add 46 (Gval (Fuint 1) (seed_bits inputs 46 1)) (VM.add 45 (Gval (Fuint 1) (seed_bits inputs 45 1)) (VM.add 43 (Gval (Fuint 65) (seed_bits inputs 43 65)) (VM.add 40 (Gval (Fuint 64) (seed_bits inputs 40 64)) (VM.add 38 (Gval (Fuint 1) (seed_bits inputs 38 1)) (VM.add 33 (Gval (Fuint 1) (seed_bits inputs 33 1)) (VM.add 20 (Gval (Fuint 129) (seed_bits inputs 20 129)) (VM.add 18 (Gval (Fuint 1) (seed_bits inputs 18 1)) (VM.add 13 (Gval (Fuint 3) (seed_bits inputs 13 3)) env)))))))))))))))).
Proof. reflexivity. Qed.
Lemma seed_registers_match inputs env : registers_match (seed_state inputs) (to_Zpos (seed_bits inputs 45 1))
 (initialize_symbolic_registers inputs [::] generated_module_0_stmts_0 env).
Proof.
 rewrite seed_registers_expanded. intros id inside.
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 3) (seed_bits inputs 13 3)) = Some (Gval (Fuint 3) (encode 3 (to_Zpos (seed_bits inputs 13 3))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 18 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 18 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 129) (seed_bits inputs 20 129)) = Some (Gval (Fuint 129) (encode 129 (to_Zpos (seed_bits inputs 20 129))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 33 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 33 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 38 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 38 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 64) (seed_bits inputs 40 64)) = Some (Gval (Fuint 64) (encode 64 (to_Zpos (seed_bits inputs 40 64))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 65) (seed_bits inputs 43 65)) = Some (Gval (Fuint 65) (encode 65 (to_Zpos (seed_bits inputs 43 65))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 45 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 45 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 46 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 46 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 47 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 47 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 6) (seed_bits inputs 51 6)) = Some (Gval (Fuint 6) (encode 6 (to_Zpos (seed_bits inputs 51 6))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 445 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 445 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 3) (seed_bits inputs 446 3)) = Some (Gval (Fuint 3) (encode 3 (to_Zpos (seed_bits inputs 446 3))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 6) (seed_bits inputs 447 6)) = Some (Gval (Fuint 6) (encode 6 (to_Zpos (seed_bits inputs 447 6))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 1) (seed_bits inputs 475 1)) = Some (Gval (Fuint 1) (encode 1 (to_Zpos (seed_bits inputs 475 1))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 destruct inside as [same|inside].
 - subst id. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]].
   change (Some (Gval (Fuint 64) (seed_bits inputs 476 64)) = Some (Gval (Fuint 64) (encode 64 (to_Zpos (seed_bits inputs 476 64))))).
   rewrite encode_decode_bits; [reflexivity|apply seed_bits_size].
 contradiction.
Qed.
Local Opaque circuit_initial_map_with_memory initialize_module_memories initialize_symbolic_registers.
Lemma runtime_symbolic_initial memory inputs states
 (ran:circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states) :
 state_matches (seed_state inputs) states.
Proof.
 unfold circuit_symbolic_initial_state in ran. rewrite divider_instances_computed in ran.
 destruct (circuit_initial_map_with_memory generated_modules generated_top None (formal_external_inputs inputs)) as [initial|] eqn:Initial; [|discriminate].
 rewrite SVM.fold_1 in ran.
 change (match SVM.find [::] initial with
 | Some env => Some (SVM.add [::] (initialize_symbolic_registers inputs [::] generated_module_0_stmts_0 (initialize_module_memories memory [::] generated_module_0_stmts_0 env)) initial)
 | None => None end = Some states) in ran.
 destruct (SVM.find [::] initial) as [env|] eqn:Found; [|discriminate].
 inversion ran; subst states.
 eexists. exists (to_Zpos (seed_bits inputs 45 1)). split.
 - apply SVM.Lemmas.find_add_eq. reflexivity.
 - apply seed_registers_match.
Qed.

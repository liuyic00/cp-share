From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Model Stable Representation Frames Initialization Commit Bridge RuntimeRepresentation RuntimeInputs NextState StateSimulation.
Local Open Scope N_scope.
Definition register_ids : seq N := [:: 13; 18; 20; 33; 38; 40; 43; 45; 46; 47; 51; 445; 446; 447; 475; 476].
Definition register_value (state:Reference.State) (ghost:Z) (id:N) : hvalue := match id with
| 13 => Gval (Fuint 3) (encode 3 (Reference.r0_nstate state))
| 18 => Gval (Fuint 1) (encode 1 (Reference.r1_ndivBy0Reg state))
| 20 => Gval (Fuint 129) (encode 129 (Reference.r2_nshiftReg state))
| 33 => Gval (Fuint 1) (encode 1 (Reference.r3_naSignReg state))
| 38 => Gval (Fuint 1) (encode 1 (Reference.r4_nqSignReg state))
| 40 => Gval (Fuint 64) (encode 64 (Reference.r5_nbReg state))
| 43 => Gval (Fuint 65) (encode 65 (Reference.r6_naValx2Reg state))
| 45 => Gval (Fuint 1) (encode 1 ghost)
| 46 => Gval (Fuint 1) (encode 1 (Reference.r7_nctrlReg_5FisW state))
| 47 => Gval (Fuint 1) (encode 1 (Reference.r8_nctrlReg_5FisHi state))
| 51 => Gval (Fuint 6) (encode 6 (Reference.r9_ncnt_5Fvalue state))
| 445 => Gval (Fuint 1) (encode 1 (Reference.r10_nhistoryValid state))
| 446 => Gval (Fuint 3) (encode 3 (Reference.r11_npreviousState state))
| 447 => Gval (Fuint 6) (encode 6 (Reference.r12_npreviousCount state))
| 475 => Gval (Fuint 1) (encode 1 (Reference.r13_nwasStalled state))
| 476 => Gval (Fuint 64) (encode 64 (Reference.r14_npreviousOutput state))
| _ => Needtobedefined (Gtyp (Fuint 0)) end.
Definition registers_match state ghost env := forall id, List.In id register_ids -> VM.find id env = Some (register_value state ghost id).
Definition state_matches state states := exists env ghost, SVM.find [::] states = Some env /\ registers_match state ghost env.
Lemma registers_runtime state ghost env inputs (matches:registers_match state ghost env) :
 divider_register_values (runtime_leaves state inputs ghost) env.
Proof.
 intros id inside. rewrite (matches id inside).
 destruct inside as [same|inside]; [subst id; rewrite target_13_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_18_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_20_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_33_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_38_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_40_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_43_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_45_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_46_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_47_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_51_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_445_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_446_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_447_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_475_value; reflexivity|].
 destruct inside as [same|inside]; [subst id; rewrite target_476_value; reflexivity|].
 contradiction.
Qed.
Lemma committed_registers state inputs ghost env (committed:divider_committed (runtime_leaves state inputs ghost) env) :
 registers_match (Reference.step state (runtime_inputs inputs))
 (to_Zpos (next_word_45 (encoded_leaves state (runtime_inputs inputs) ghost))) env.
Proof.
 rewrite - (next_state_simulation state (runtime_inputs inputs) ghost).
 intros id inside. rewrite (committed id inside).
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r0_nstate].
   unfold runtime_leaves. rewrite next_13_clock encode_decode_bits; [reflexivity|apply next_13_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r1_ndivBy0Reg].
   unfold runtime_leaves. rewrite next_18_clock encode_decode_bits; [reflexivity|apply next_18_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r2_nshiftReg].
   unfold runtime_leaves. rewrite next_20_clock encode_decode_bits; [reflexivity|apply next_20_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r3_naSignReg].
   unfold runtime_leaves. rewrite next_33_clock encode_decode_bits; [reflexivity|apply next_33_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r4_nqSignReg].
   unfold runtime_leaves. rewrite next_38_clock encode_decode_bits; [reflexivity|apply next_38_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r5_nbReg].
   unfold runtime_leaves. rewrite next_40_clock encode_decode_bits; [reflexivity|apply next_40_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r6_naValx2Reg].
   unfold runtime_leaves. rewrite next_43_clock encode_decode_bits; [reflexivity|apply next_43_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state].
   unfold runtime_leaves. rewrite next_45_clock encode_decode_bits; [reflexivity|apply next_45_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r7_nctrlReg_5FisW].
   unfold runtime_leaves. rewrite next_46_clock encode_decode_bits; [reflexivity|apply next_46_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r8_nctrlReg_5FisHi].
   unfold runtime_leaves. rewrite next_47_clock encode_decode_bits; [reflexivity|apply next_47_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r9_ncnt_5Fvalue].
   unfold runtime_leaves. rewrite next_51_clock encode_decode_bits; [reflexivity|apply next_51_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r10_nhistoryValid].
   unfold runtime_leaves. rewrite next_445_clock encode_decode_bits; [reflexivity|apply next_445_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r11_npreviousState].
   unfold runtime_leaves. rewrite next_446_clock encode_decode_bits; [reflexivity|apply next_446_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r12_npreviousCount].
   unfold runtime_leaves. rewrite next_447_clock encode_decode_bits; [reflexivity|apply next_447_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r13_nwasStalled].
   unfold runtime_leaves. rewrite next_475_clock encode_decode_bits; [reflexivity|apply next_475_size].
 destruct inside as [same|inside].
 - subst id. cbn [next_register_value register_value next_projected_state Reference.r14_npreviousOutput].
   unfold runtime_leaves. rewrite next_476_clock encode_decode_bits; [reflexivity|apply next_476_size].
 contradiction.
Qed.
Local Opaque circuit_formal_cycle Reference.step.
Lemma runtime_cycle state previous inputs final
 (matches:state_matches state previous)
 (defined:formal_external_inputs_defined generated_modules generated_top inputs = true)
 (ran:circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some final) :
 state_matches (Reference.step state (runtime_inputs inputs)) final.
Proof.
 destruct matches as [old [ghost [Found Registers]]].
 destruct (divider_cycle_values (runtime_leaves state inputs ghost) previous old inputs final
 (runtime_leaf_sizes state inputs ghost defined) Found
 (registers_runtime state ghost old inputs Registers)
 (runtime_port_values state inputs ghost defined) ran) as [env [Final Committed]].
 exists env, (to_Zpos (next_word_45 (encoded_leaves state (runtime_inputs inputs) ghost))).
 split; [exact Final|]. apply committed_registers. exact Committed.
Qed.

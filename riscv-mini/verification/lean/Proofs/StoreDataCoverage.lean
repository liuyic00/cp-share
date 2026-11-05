import Proofs.StoreDataFacts
import Proofs.StoreEncoding
import Proofs.StoreDataTask
import Proofs.MemoryAddressCoverage
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedVariables false
theorem lui_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_lui_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms lui_store_data_task
theorem auipc_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_auipc_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms auipc_store_data_task
theorem jal_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_jal_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms jal_store_data_task
theorem jalr_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_jalr_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms jalr_store_data_task
theorem beq_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_beq_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms beq_store_data_task
theorem bne_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_bne_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms bne_store_data_task
theorem blt_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_blt_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms blt_store_data_task
theorem bge_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_bge_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms bge_store_data_task
theorem bltu_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_bltu_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms bltu_store_data_task
theorem bgeu_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_bgeu_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms bgeu_store_data_task
theorem lb_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_lb_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms lb_store_data_task
theorem lh_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have guard := reference_lh_memory_guard _ _ commit event known
  have reference := reference_lh_memory_protocol _ _ commit guard known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms lh_store_data_task
theorem lw_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have guard := reference_lw_memory_guard _ _ commit event known
  have reference := reference_lw_memory_protocol _ _ commit guard known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms lw_store_data_task
theorem lbu_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_lbu_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms lbu_store_data_task
theorem lhu_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have guard := reference_lhu_memory_guard _ _ commit event known
  have reference := reference_lhu_memory_protocol _ _ commit guard known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms lhu_store_data_task
theorem sb_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have encoding := store_encoding_reachable initial inputs cycles reset env t ht
    ((commit_iff_valid_writeback _ _ (reset.2.2 t ht)).mp commit)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  apply store_data_task_of_equality
  rw [reference_sb_store_data _ _ commit known,
    checked_store_data_cone, encoding.mask, encoding.data,
    sb_store _ known, register_reads_agree _ agree, reference_sb_operand2 _ _ zero commit known]
  exact store_byte_roundtrip _ _
#print axioms sb_store_data_task
theorem sh_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have guard := reference_sh_memory_guard _ _ commit event known
  have encoding := store_encoding_reachable initial inputs cycles reset env t ht
    ((commit_iff_valid_writeback _ _ (reset.2.2 t ht)).mp commit)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_sh _ 0 0 0 known)
  have aligned : BitVec.extractLsb' 0 1 (run initial inputs t).g4.r154_ndut_5Fdpath_5Freq_5Faddr = 0 := by
    rw [request]
    exact no_trap_half_store _ _
      (environment_no_trap _ _ (reset.2.2 t ht) (env t))
      (control.store.trans (sh_store _ known))
  apply store_data_task_of_equality
  rw [reference_sh_store_data _ _ commit guard known,
    checked_store_data_cone, encoding.mask, encoding.data,
    sh_store _ known, register_reads_agree _ agree, reference_sh_operand2 _ _ zero commit known]
  exact store_half_roundtrip _ _ aligned
#print axioms sh_store_data_task
theorem sw_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have guard := reference_sw_memory_guard _ _ commit event known
  have encoding := store_encoding_reachable initial inputs cycles reset env t ht
    ((commit_iff_valid_writeback _ _ (reset.2.2 t ht)).mp commit)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_sw _ 0 0 0 known)
  have aligned : BitVec.extractLsb' 0 2 (run initial inputs t).g4.r154_ndut_5Fdpath_5Freq_5Faddr = 0 := by
    rw [request]
    exact no_trap_word_store _ _
      (environment_no_trap _ _ (reset.2.2 t ht) (env t))
      (control.store.trans (sw_store _ known))
  apply store_data_task_of_equality
  rw [reference_sw_store_data _ _ commit guard known,
    checked_store_data_cone, encoding.mask, encoding.data,
    sw_store _ known, register_reads_agree _ agree, reference_sw_operand2 _ _ zero commit known]
  exact store_word_roundtrip _ _ aligned
#print axioms sw_store_data_task
theorem addi_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_addi_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms addi_store_data_task
theorem slti_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_slti_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms slti_store_data_task
theorem sltiu_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_sltiu_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms sltiu_store_data_task
theorem xori_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_xori_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms xori_store_data_task
theorem ori_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_ori_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms ori_store_data_task
theorem andi_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_andi_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms andi_store_data_task
theorem slli_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_slli_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms slli_store_data_task
theorem srli_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_srli_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms srli_store_data_task
theorem srai_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_srai_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms srai_store_data_task
theorem add_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_add_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms add_store_data_task
theorem sub_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_sub_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms sub_store_data_task
theorem sll_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_sll_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms sll_store_data_task
theorem slt_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_slt_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms slt_store_data_task
theorem sltu_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_sltu_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms sltu_store_data_task
theorem xor_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_xor_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms xor_store_data_task
theorem srl_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_srl_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms srl_store_data_task
theorem sra_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_sra_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms sra_store_data_task
theorem or_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_or_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms or_store_data_task
theorem and_store_data_task (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  have reference := reference_and_memory_protocol _ _ commit known
  exact store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht) reference.2.2.1
#print axioms and_store_data_task
theorem store_data_task_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : TaskHolds ⟨5, by decide⟩ (run initial inputs t) (inputs t) := by
  rcases BitVec.eq_zero_or_eq_one (v964 (run initial inputs t) (inputs t)) with idle | commit
  · apply store_data_task_inactive _ _ (memory_protocol_reachable initial inputs cycles reset env t ht)
    simp [v9203, v9202, v9201, idle, v4]
  · have supported := environment_supported_at_commit _ _ (reset.2.2 t ht) (env t) commit
    cases supported with
    | op_add known => exact add_store_data_task initial inputs cycles reset env t ht commit known
    | op_addi known => exact addi_store_data_task initial inputs cycles reset env t ht commit known
    | op_and known => exact and_store_data_task initial inputs cycles reset env t ht commit known
    | op_andi known => exact andi_store_data_task initial inputs cycles reset env t ht commit known
    | op_auipc known => exact auipc_store_data_task initial inputs cycles reset env t ht commit known
    | op_beq known => exact beq_store_data_task initial inputs cycles reset env t ht commit known
    | op_bge known => exact bge_store_data_task initial inputs cycles reset env t ht commit known
    | op_bgeu known => exact bgeu_store_data_task initial inputs cycles reset env t ht commit known
    | op_blt known => exact blt_store_data_task initial inputs cycles reset env t ht commit known
    | op_bltu known => exact bltu_store_data_task initial inputs cycles reset env t ht commit known
    | op_bne known => exact bne_store_data_task initial inputs cycles reset env t ht commit known
    | op_jal known => exact jal_store_data_task initial inputs cycles reset env t ht commit known
    | op_jalr known => exact jalr_store_data_task initial inputs cycles reset env t ht commit known
    | op_lb known => exact lb_store_data_task initial inputs cycles reset env t ht commit known
    | op_lbu known => exact lbu_store_data_task initial inputs cycles reset env t ht commit known
    | op_lh known => exact lh_store_data_task initial inputs cycles reset env t ht commit known
    | op_lhu known => exact lhu_store_data_task initial inputs cycles reset env t ht commit known
    | op_lui known => exact lui_store_data_task initial inputs cycles reset env t ht commit known
    | op_lw known => exact lw_store_data_task initial inputs cycles reset env t ht commit known
    | op_or known => exact or_store_data_task initial inputs cycles reset env t ht commit known
    | op_ori known => exact ori_store_data_task initial inputs cycles reset env t ht commit known
    | op_sb known => exact sb_store_data_task initial inputs cycles reset env t ht commit known
    | op_sh known => exact sh_store_data_task initial inputs cycles reset env t ht commit known
    | op_sll known => exact sll_store_data_task initial inputs cycles reset env t ht commit known
    | op_slli known => exact slli_store_data_task initial inputs cycles reset env t ht commit known
    | op_slt known => exact slt_store_data_task initial inputs cycles reset env t ht commit known
    | op_slti known => exact slti_store_data_task initial inputs cycles reset env t ht commit known
    | op_sltiu known => exact sltiu_store_data_task initial inputs cycles reset env t ht commit known
    | op_sltu known => exact sltu_store_data_task initial inputs cycles reset env t ht commit known
    | op_sra known => exact sra_store_data_task initial inputs cycles reset env t ht commit known
    | op_srai known => exact srai_store_data_task initial inputs cycles reset env t ht commit known
    | op_srl known => exact srl_store_data_task initial inputs cycles reset env t ht commit known
    | op_srli known => exact srli_store_data_task initial inputs cycles reset env t ht commit known
    | op_sub known => exact sub_store_data_task initial inputs cycles reset env t ht commit known
    | op_sw known => exact sw_store_data_task initial inputs cycles reset env t ht commit known
    | op_xor known => exact xor_store_data_task initial inputs cycles reset env t ht commit known
    | op_xori known => exact xori_store_data_task initial inputs cycles reset env t ht commit known
#print axioms store_data_task_reachable
end RiscvMiniProofs

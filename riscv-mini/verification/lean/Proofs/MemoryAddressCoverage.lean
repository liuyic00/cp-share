import Proofs.MemoryAddresses
import Proofs.MemoryProtocolCoverage
import Proofs.RequestAddress
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedVariables false
theorem lui_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lui_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms lui_memory_addresses
theorem auipc_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_auipc_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms auipc_memory_addresses
theorem jal_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_jal_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms jal_memory_addresses
theorem jalr_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_jalr_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms jalr_memory_addresses
theorem beq_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_beq_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms beq_memory_addresses
theorem bne_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bne_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms bne_memory_addresses
theorem blt_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_blt_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms blt_memory_addresses
theorem bge_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bge_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms bge_memory_addresses
theorem bltu_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bltu_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms bltu_memory_addresses
theorem bgeu_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_bgeu_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms bgeu_memory_addresses
theorem lb_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lb_memory_protocol _ _ commit known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_lb _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := load_address_lb _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have reference := reference_lb_memory_address _ _ commit known
  constructor
  · intro active
    exact request.trans (address.trans reference.symm)
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms lb_memory_addresses
theorem lh_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have aligned := reference_lh_memory_guard _ _ commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lh_memory_protocol _ _ commit aligned known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_lh _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := load_address_lh _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have reference := reference_lh_memory_address _ _ commit aligned known
  constructor
  · intro active
    exact request.trans (address.trans reference.symm)
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms lh_memory_addresses
theorem lw_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have aligned := reference_lw_memory_guard _ _ commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lw_memory_protocol _ _ commit aligned known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_lw _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := load_address_lw _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have reference := reference_lw_memory_address _ _ commit aligned known
  constructor
  · intro active
    exact request.trans (address.trans reference.symm)
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms lw_memory_addresses
theorem lbu_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lbu_memory_protocol _ _ commit known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_lbu _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := load_address_lbu _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have reference := reference_lbu_memory_address _ _ commit known
  constructor
  · intro active
    exact request.trans (address.trans reference.symm)
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms lbu_memory_addresses
theorem lhu_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have aligned := reference_lhu_memory_guard _ _ commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_lhu_memory_protocol _ _ commit aligned known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_lhu _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := load_address_lhu _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have reference := reference_lhu_memory_address _ _ commit aligned known
  constructor
  · intro active
    exact request.trans (address.trans reference.symm)
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms lhu_memory_addresses
theorem sb_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sb_memory_protocol _ _ commit known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_sb _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := store_address_sb _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have normalized := address.trans (reference_load_address _ _).symm
  have reference := reference_sb_memory_address _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    exact request.trans (normalized.trans reference.symm)
#print axioms sb_memory_addresses
theorem sh_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have aligned := reference_sh_memory_guard _ _ commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sh_memory_protocol _ _ commit aligned known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_sh _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := store_address_sh _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have normalized := address.trans (reference_load_address _ _).symm
  have reference := reference_sh_memory_address _ _ commit aligned known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    exact request.trans (normalized.trans reference.symm)
#print axioms sh_memory_addresses
theorem sw_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  have aligned := reference_sw_memory_guard _ _ commit event known
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sw_memory_protocol _ _ commit aligned known
  have request := request_address_reachable_of_op initial inputs cycles reset env t ht
    (decoded_alu_op_sw _ 0 0 0 known)
  have agree := (registers_and_pipeline_reachable initial inputs cycles reset env t ht).1
  have address := store_address_sw _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have normalized := address.trans (reference_load_address _ _).symm
  have reference := reference_sw_memory_address _ _ commit aligned known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    exact request.trans (normalized.trans reference.symm)
#print axioms sw_memory_addresses
theorem addi_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_addi_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms addi_memory_addresses
theorem slti_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_slti_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms slti_memory_addresses
theorem sltiu_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sltiu_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms sltiu_memory_addresses
theorem xori_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_xori_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms xori_memory_addresses
theorem ori_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_ori_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms ori_memory_addresses
theorem andi_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_andi_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms andi_memory_addresses
theorem slli_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_slli_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms slli_memory_addresses
theorem srli_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_srli_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms srli_memory_addresses
theorem srai_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_srai_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms srai_memory_addresses
theorem add_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_add_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms add_memory_addresses
theorem sub_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sub_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms sub_memory_addresses
theorem sll_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sll_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms sll_memory_addresses
theorem slt_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_slt_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms slt_memory_addresses
theorem sltu_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sltu_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms sltu_memory_addresses
theorem xor_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_xor_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms xor_memory_addresses
theorem srl_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_srl_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms srl_memory_addresses
theorem sra_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_sra_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms sra_memory_addresses
theorem or_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_or_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms or_memory_addresses
theorem and_memory_addresses (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : MemoryAddresses (run initial inputs t) (inputs t) := by
  have event := (event_validity_iff_no_reference_event _ _ (reset.2.2 t ht) (env t)).mp
    (event_valid_reachable initial inputs cycles reset env t ht)
  obtain ⟨readValid, readWidth, writeValid, writeWidth⟩ := reference_and_memory_protocol _ _ commit known
  constructor
  · intro active
    rw [readValid] at active
    contradiction
  · intro active
    rw [writeValid] at active
    contradiction
#print axioms and_memory_addresses
theorem memory_addresses_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : MemoryAddresses (run initial inputs t) (inputs t) := by
  rcases BitVec.eq_zero_or_eq_one (v964 (run initial inputs t) (inputs t)) with idle | commit
  · exact memory_addresses_idle _ _ idle
  · have supported := environment_supported_at_commit _ _ (reset.2.2 t ht) (env t) commit
    cases supported with
    | op_add known => exact add_memory_addresses initial inputs cycles reset env t ht commit known
    | op_addi known => exact addi_memory_addresses initial inputs cycles reset env t ht commit known
    | op_and known => exact and_memory_addresses initial inputs cycles reset env t ht commit known
    | op_andi known => exact andi_memory_addresses initial inputs cycles reset env t ht commit known
    | op_auipc known => exact auipc_memory_addresses initial inputs cycles reset env t ht commit known
    | op_beq known => exact beq_memory_addresses initial inputs cycles reset env t ht commit known
    | op_bge known => exact bge_memory_addresses initial inputs cycles reset env t ht commit known
    | op_bgeu known => exact bgeu_memory_addresses initial inputs cycles reset env t ht commit known
    | op_blt known => exact blt_memory_addresses initial inputs cycles reset env t ht commit known
    | op_bltu known => exact bltu_memory_addresses initial inputs cycles reset env t ht commit known
    | op_bne known => exact bne_memory_addresses initial inputs cycles reset env t ht commit known
    | op_jal known => exact jal_memory_addresses initial inputs cycles reset env t ht commit known
    | op_jalr known => exact jalr_memory_addresses initial inputs cycles reset env t ht commit known
    | op_lb known => exact lb_memory_addresses initial inputs cycles reset env t ht commit known
    | op_lbu known => exact lbu_memory_addresses initial inputs cycles reset env t ht commit known
    | op_lh known => exact lh_memory_addresses initial inputs cycles reset env t ht commit known
    | op_lhu known => exact lhu_memory_addresses initial inputs cycles reset env t ht commit known
    | op_lui known => exact lui_memory_addresses initial inputs cycles reset env t ht commit known
    | op_lw known => exact lw_memory_addresses initial inputs cycles reset env t ht commit known
    | op_or known => exact or_memory_addresses initial inputs cycles reset env t ht commit known
    | op_ori known => exact ori_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sb known => exact sb_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sh known => exact sh_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sll known => exact sll_memory_addresses initial inputs cycles reset env t ht commit known
    | op_slli known => exact slli_memory_addresses initial inputs cycles reset env t ht commit known
    | op_slt known => exact slt_memory_addresses initial inputs cycles reset env t ht commit known
    | op_slti known => exact slti_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sltiu known => exact sltiu_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sltu known => exact sltu_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sra known => exact sra_memory_addresses initial inputs cycles reset env t ht commit known
    | op_srai known => exact srai_memory_addresses initial inputs cycles reset env t ht commit known
    | op_srl known => exact srl_memory_addresses initial inputs cycles reset env t ht commit known
    | op_srli known => exact srli_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sub known => exact sub_memory_addresses initial inputs cycles reset env t ht commit known
    | op_sw known => exact sw_memory_addresses initial inputs cycles reset env t ht commit known
    | op_xor known => exact xor_memory_addresses initial inputs cycles reset env t ht commit known
    | op_xori known => exact xori_memory_addresses initial inputs cycles reset env t ht commit known
theorem memory_address_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : MemoryAddressTasks (run initial inputs t) (inputs t) :=
  memory_address_tasks _ _ (memory_protocol_reachable initial inputs cycles reset env t ht)
    (memory_addresses_reachable initial inputs cycles reset env t ht)
#print axioms memory_addresses_reachable
#print axioms memory_address_tasks_reachable
end RiscvMiniProofs

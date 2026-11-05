import Proofs.SubwordData
namespace RiscvMiniProofs
open nCoreSoc
theorem lbu_value_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) :
    v765 (run initial inputs t) (inputs t) = v2132 (run initial inputs t) (inputs t) := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have sel := control.write_select.trans (lbu_write_select _ known)
  have kind := control.load.trans (lbu_load _ known)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lbu known)
  rw [dut_load_data_cone _ _ sel, kind, address, reference_load_lbu_cone]
  exact unsigned_byte_data_agrees _ _
#print axioms lbu_value_reachable

theorem lhu_value_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) :
    v765 (run initial inputs t) (inputs t) = v2117 (run initial inputs t) (inputs t) := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have sel := control.write_select.trans (lhu_write_select _ known)
  have kind := control.load.trans (lhu_load _ known)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lhu known)
  rw [dut_load_data_cone _ _ sel, kind, address, reference_load_lhu_cone]
  exact unsigned_half_data_agrees _ _
#print axioms lhu_value_reachable

end RiscvMiniProofs

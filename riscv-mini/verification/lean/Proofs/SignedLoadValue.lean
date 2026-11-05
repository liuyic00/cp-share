import Proofs.SignedLoadData
namespace RiscvMiniProofs
open nCoreSoc
theorem lb_value_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) :
    v765 (run initial inputs t) (inputs t) = v2193 (run initial inputs t) (inputs t) := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have sel := control.write_select.trans (lb_write_select _ known)
  have kind := control.load.trans (lb_load _ known)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lb known)
  rw [dut_load_data_cone _ _ sel, kind, address, reference_load_lb_cone]
  exact lb_data_agrees _ _
#print axioms lb_value_reachable

theorem lh_value_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) :
    v765 (run initial inputs t) (inputs t) = v2176 (run initial inputs t) (inputs t) := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have sel := control.write_select.trans (lh_write_select _ known)
  have kind := control.load.trans (lh_load _ known)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lh known)
  rw [dut_load_data_cone _ _ sel, kind, address, reference_load_lh_cone]
  exact lh_data_agrees _ _
#print axioms lh_value_reachable

end RiscvMiniProofs

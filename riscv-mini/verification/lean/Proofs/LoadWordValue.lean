import Proofs.LoadDataSemantics
import Proofs.TrapFacts
namespace RiscvMiniProofs
open nCoreSoc

theorem load_word_value_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) :
    v765 (run initial inputs t) (inputs t) = v2153 (run initial inputs t) (inputs t) := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have sel := control.write_select.trans (lw_write_select _ known)
  have kind := control.load.trans (lw_load _ known)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lw known)
  have aligned := no_trap_word_load _ _
    (environment_no_trap _ _ (reset.2.2 t ht) (env t)) kind
  rw [address] at aligned
  rw [dut_load_data_cone _ _ sel, kind, dut_load_word,
    reference_load_lw_cone, reference_load_word _ _ aligned]

#print axioms load_word_value_reachable
end RiscvMiniProofs

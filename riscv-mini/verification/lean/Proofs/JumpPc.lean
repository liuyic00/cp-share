import Proofs.ReferenceJumpPc
import Proofs.JalAlignment
import Proofs.JalrAlignment
namespace RiscvMiniProofs
open nCoreSoc
theorem jal_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        v2235 (run initial inputs t) (inputs t) := by
  have config := reference_config_reachable initial inputs cycles reset t ht
  have aligned := jal_target_aligned_reachable initial inputs cycles reset env t ht pc commit known
  have guard := (reference_jal_alignment _ _ config).mpr aligned
  exact ⟨reference_jal_event_task _ _ (reset.2.2 t ht) (env t) commit guard known,
    reference_jal_next_pc _ _ (reset.2.2 t ht) commit guard known⟩
#print axioms jal_event_and_pc_reachable

theorem jalr_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        v2205 (run initial inputs t) (inputs t) := by
  have config := reference_config_reachable initial inputs cycles reset t ht
  have aligned := jalr_target_aligned_reachable initial inputs cycles reset env t ht agree commit known
  have guard := (reference_jalr_alignment _ _ config).mpr aligned
  exact ⟨reference_jalr_event_task _ _ (reset.2.2 t ht) (env t) commit guard known,
    reference_jalr_next_pc _ _ (reset.2.2 t ht) commit guard known⟩
#print axioms jalr_event_and_pc_reachable

end RiscvMiniProofs

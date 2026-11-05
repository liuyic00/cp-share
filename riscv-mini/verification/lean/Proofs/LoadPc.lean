import Proofs.ReferenceAlignedLoadPc
import Proofs.ReferenceOrdinaryPc
import Proofs.SignedLoadCommit
namespace RiscvMiniProofs
open nCoreSoc
theorem lh_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        v2222 (run initial inputs t) (inputs t) + 4 := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have kind := control.load.trans (lh_load _ known)
  have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lh known)
  have aligned := no_trap_signed_half_load _ _ trap kind
  rw [address] at aligned
  have refAligned : v2159 (run initial inputs t) (inputs t) = 1#1 := by
    change (if BitVec.extractLsb' 0 1 (v2095 (run initial inputs t) (inputs t)) = 0#1 then 1 else 0) = 1#1
    exact if_pos aligned
  exact ⟨reference_lh_event_task _ _ (reset.2.2 t ht) (env t) commit refAligned known,
    reference_lh_next_pc _ _ (reset.2.2 t ht) commit refAligned known⟩
#print axioms lh_event_and_pc_reachable

theorem lhu_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        v2222 (run initial inputs t) (inputs t) + 4 := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have kind := control.load.trans (lhu_load _ known)
  have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lhu known)
  have aligned := no_trap_unsigned_half_load _ _ trap kind
  rw [address] at aligned
  have refAligned : v2097 (run initial inputs t) (inputs t) = 1#1 := by
    change (if BitVec.extractLsb' 0 1 (v2095 (run initial inputs t) (inputs t)) = 0#1 then 1 else 0) = 1#1
    exact if_pos aligned
  exact ⟨reference_lhu_event_task _ _ (reset.2.2 t ht) (env t) commit refAligned known,
    reference_lhu_next_pc _ _ (reset.2.2 t ht) commit refAligned known⟩
#print axioms lhu_event_and_pc_reachable

theorem lw_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        v2222 (run initial inputs t) (inputs t) + 4 := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have kind := control.load.trans (lw_load _ known)
  have trap := environment_no_trap _ _ (reset.2.2 t ht) (env t)
  have address := load_address_reachable initial inputs cycles reset env t ht agree commit
    (LoadInstruction.op_lw known)
  have aligned := no_trap_word_load _ _ trap kind
  rw [address] at aligned
  have refAligned : v2139 (run initial inputs t) (inputs t) = 1#1 := by
    change (if BitVec.extractLsb' 0 2 (v2095 (run initial inputs t) (inputs t)) = 0#2 then 1 else 0) = 1#1
    exact if_pos aligned
  exact ⟨reference_lw_event_task _ _ (reset.2.2 t ht) (env t) commit refAligned known,
    reference_lw_next_pc _ _ (reset.2.2 t ht) commit refAligned known⟩
#print axioms lw_event_and_pc_reachable

end RiscvMiniProofs

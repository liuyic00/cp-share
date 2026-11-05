import Proofs.DecodeCases
import Proofs.StoreExecution
import Proofs.ReferenceStoreDecode
import Proofs.StoreAlignment
import Proofs.ControlAlignment
namespace RiscvMiniProofs
open nCoreSoc
theorem store_address_sb (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v1721 s i + v2092 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_sb _ _ _ _ known)
  rw [← reference_sb_operand1 s i zero commit known,
    ← reference_sb_immediate s i commit known] at value
  exact value

theorem store_address_sh (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v1721 s i + v2092 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_sh _ _ _ _ known)
  rw [← reference_sh_operand1 s i zero commit known,
    ← reference_sh_immediate s i commit known] at value
  exact value

theorem sh_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        v2222 (run initial inputs t) (inputs t) + 4 := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have kind := control.store.trans (sh_store _ known)
  have address := store_address_sh _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  exact sh_event_and_pc_of_address _ _ (reset.2.2 t ht) (env t) commit known kind address
#print axioms sh_event_and_pc_reachable

theorem store_address_sw (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v1721 s i + v2092 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_sw _ _ _ _ known)
  rw [← reference_sw_operand1 s i zero commit known,
    ← reference_sw_immediate s i commit known] at value
  exact value

theorem sw_event_and_pc_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) ∧
      (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
        v2222 (run initial inputs t) (inputs t) + 4 := by
  have control := control_values_at_commit _ _
    (control_alignment_reachable initial inputs cycles reset env t ht) (reset.2.2 t ht) commit
  have kind := control.store.trans (sw_store _ known)
  have address := store_address_sw _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  exact sw_event_and_pc_of_address _ _ (reset.2.2 t ht) (env t) commit known kind address
#print axioms sw_event_and_pc_reachable

end RiscvMiniProofs

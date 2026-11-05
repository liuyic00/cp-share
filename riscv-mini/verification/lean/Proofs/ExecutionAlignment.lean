import Proofs.ExecutionDecode
import Proofs.HazardAlignment
namespace RiscvMiniProofs
open nCoreSoc

-- A state relation with no dependence on the preceding state or inputs.
def DecodedAluAligned (s : State) : Prop :=
  s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu =
    decodedExecution s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
      s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc
      (dutRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))
      (dutRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))

theorem decoded_alu_alignment_reset (s : State) (i : Inputs)
    (reset : i.nreset = 1) : DecodedAluAligned (step s i) := by
  have instruction : (step s i).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst = 19 := by
    change v7780 s i = 19
    simp [v7780, v1, v0, reset, v427]
  have value : (step s i).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 := by
    change v8167 s i = 0
    simp [v8167, v1, v0, reset, v3]
  simp [DecodedAluAligned, instruction, value, dutRead]
  exact (decoded_execution_nop _).symm

theorem decoded_alu_alignment_step (s : State) (i : Inputs)
    (hazard : HazardAligned s) (reset : i.nreset = 0) (env : assumes s i) :
    DecodedAluAligned (step s i) := by
  have transfer := execute_transfer_step s i reset env
  have trap := environment_no_trap s i reset env
  have rs1 := forwarding_aligned_port1 s i hazard reset trap
  have rs2 := forwarding_aligned_port2 s i hazard reset trap
  unfold DecodedAluAligned
  rw [transfer.alu, circuit_alu_correct, decoded_execution_eq,
    transfer.instruction, transfer.pc, rs1, rs2]
  rfl

theorem decoded_alu_alignment_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t) :
    DecodedAluAligned (run initial inputs t) := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    change DecodedAluAligned (step (run initial inputs n) (inputs n))
    by_cases hn : cycles ≤ n
    · exact decoded_alu_alignment_step _ _
        (hazard_alignment_reachable initial inputs cycles reset env n hn)
        (reset.2.2 n hn) (env n)
    · exact decoded_alu_alignment_reset _ _ (reset.2.1 n (by omega))

-- This bridge is conditional on register agreement, whose committing-step
-- preservation is still an outstanding obligation. It is not an assumption.
theorem decoded_alu_reference_operands (s : State)
    (aligned : DecodedAluAligned s) (registers : RegisterAgreement s) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu =
      decodedExecution s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
        s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc
        (referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))
        (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) := by
  simpa only [DecodedAluAligned, register_reads_agree s registers] using aligned

#print axioms decoded_alu_alignment_reachable
#print axioms decoded_alu_reference_operands
end RiscvMiniProofs

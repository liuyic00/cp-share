import Proofs.PcCheckDecode
import Proofs.HazardAlignment
namespace RiscvMiniProofs
open nCoreSoc

def PcCheckAligned (s : State) : Prop :=
  s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck =
    decodedPcCheck s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
      (dutRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))
      (dutRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))

theorem pc_check_alignment_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    PcCheckAligned (step s i) := by
  have instruction : (step s i).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst = 19 := by
    change v7780 s i = 19
    simp [v7780, v1, v0, reset, v427]
  have value : (step s i).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 0 := by
    change v8477 s i = 0
    have ones (x : BitVec 1) : 1#1 ||| x = 1#1 := BitVec.allOnes_or
    simp [ones, v8477, v7774, v7773, v1, v0, reset, v4]
  simp only [PcCheckAligned, instruction, value]
  simp [dutRead]
  exact decoded_pc_check_nop.symm

theorem pc_check_alignment_step (s : State) (i : Inputs)
    (hazard : HazardAligned s) (reset : i.nreset = 0) (env : assumes s i) :
    PcCheckAligned (step s i) := by
  have transfer := execute_transfer_step s i reset env
  have trap := environment_no_trap s i reset env
  have stall := no_stall_after_reset s i reset
  have rs1 := forwarding_aligned_port1 s i hazard reset trap
  have rs2 := forwarding_aligned_port2 s i hazard reset trap
  have value : (step s i).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v8475 s i := by
    change v8477 s i = v8475 s i
    simp [v8477, v8476, v7774, v7773, v7772, v7777, v7776, v7775,
      v1, v0, v4, reset, trap, stall]
  unfold PcCheckAligned
  rw [value, decoded_pc_check_eq, transfer.instruction, rs1, rs2]
  rfl

theorem pc_check_alignment_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : PcCheckAligned (run initial inputs t) := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    by_cases hn : cycles ≤ n
    · exact pc_check_alignment_step _ _
        (hazard_alignment_reachable initial inputs cycles reset env n hn)
        (reset.2.2 n hn) (env n)
    · exact pc_check_alignment_reset _ _ (reset.2.1 n (by omega))

theorem pc_check_reference_operands (s : State) (aligned : PcCheckAligned s)
    (agree : RegisterAgreement s) :
    s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck =
      decodedPcCheck s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
        (referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst))
        (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) := by
  simpa only [PcCheckAligned, register_reads_agree s agree] using aligned

#print axioms pc_check_reference_operands
#print axioms pc_check_alignment_reachable
end RiscvMiniProofs

import Proofs.PcSuccessor
import Proofs.BranchReachable
import Proofs.JumpPc
namespace RiscvMiniProofs
open nCoreSoc

private theorem clear_aligned_target (x : BitVec 32) (aligned : BitVec.extractLsb' 0 2 x = 0) :
    (BitVec.extractLsb' 1 31 x) ++ (0#1) = x := by
  apply clear_even_target
  rw [← extract_prefix x 2 0 1 (by decide), aligned]
  decide

theorem jal_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkOne : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 1 :=
    checked.trans (decoded_check_jal _ _ _ known)
  simp only [writebackNextPc, checkOne, ↓reduceIte]
  rw [(jal_event_and_pc_reachable initial inputs cycles reset env t ht pc commit known).2,
    reference_jal_target, jal_target_agreement _ _ alu pc commit known]
  exact (clear_aligned_target _
    (jal_target_aligned_reachable initial inputs cycles reset env t ht pc commit known)).symm
#print axioms jal_reference_successor
theorem jalr_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkOne : (run initial inputs t).g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 1 :=
    checked.trans (decoded_check_jalr _ _ _ known)
  simp only [writebackNextPc, checkOne, ↓reduceIte]
  rw [(jalr_event_and_pc_reachable initial inputs cycles reset env t ht agree commit known).2,
    reference_jalr_target, jalr_sum_agreement _ _ alu agree zero commit known]
#print axioms jalr_reference_successor
theorem beq_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkEq := beq_check_agreement _ _ checked agree zero commit known
  have target := beq_target_agreement _ _ alu pc commit known
  have next := (beq_event_and_pc_reachable initial inputs cycles reset env t ht agree pc commit known).2
  rw [next]
  simp only [writebackNextPc, checkEq, target, pcEq]
  by_cases taken : v6665 (run initial inputs t) (inputs t) = 1
  · rw [if_pos taken, if_pos taken]
    exact (clear_aligned_target _
      (beq_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known taken)).symm
  · rw [if_neg taken, if_neg taken]
#print axioms beq_reference_successor
theorem bne_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkEq := bne_check_agreement _ _ checked agree zero commit known
  have target := bne_target_agreement _ _ alu pc commit known
  have next := (bne_event_and_pc_reachable initial inputs cycles reset env t ht agree pc commit known).2
  rw [next]
  simp only [writebackNextPc, checkEq, target, pcEq]
  by_cases taken : v6641 (run initial inputs t) (inputs t) = 1
  · rw [if_pos taken, if_pos taken]
    exact (clear_aligned_target _
      (bne_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known taken)).symm
  · rw [if_neg taken, if_neg taken]
#print axioms bne_reference_successor
theorem blt_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkEq := blt_check_agreement _ _ checked agree zero commit known
  have target := blt_target_agreement _ _ alu pc commit known
  have next := (blt_event_and_pc_reachable initial inputs cycles reset env t ht agree pc commit known).2
  rw [next]
  simp only [writebackNextPc, checkEq, target, pcEq]
  by_cases taken : v6617 (run initial inputs t) (inputs t) = 1
  · rw [if_pos taken, if_pos taken]
    exact (clear_aligned_target _
      (blt_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known taken)).symm
  · rw [if_neg taken, if_neg taken]
#print axioms blt_reference_successor
theorem bge_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkEq := bge_check_agreement _ _ checked agree zero commit known
  have target := bge_target_agreement _ _ alu pc commit known
  have next := (bge_event_and_pc_reachable initial inputs cycles reset env t ht agree pc commit known).2
  rw [next]
  simp only [writebackNextPc, checkEq, target, pcEq]
  by_cases taken : v6569 (run initial inputs t) (inputs t) = 1
  · rw [if_pos taken, if_pos taken]
    exact (clear_aligned_target _
      (bge_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known taken)).symm
  · rw [if_neg taken, if_neg taken]
#print axioms bge_reference_successor
theorem bltu_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkEq := bltu_check_agreement _ _ checked agree zero commit known
  have target := bltu_target_agreement _ _ alu pc commit known
  have next := (bltu_event_and_pc_reachable initial inputs cycles reset env t ht agree pc commit known).2
  rw [next]
  simp only [writebackNextPc, checkEq, target, pcEq]
  by_cases taken : v6593 (run initial inputs t) (inputs t) = 1
  · rw [if_pos taken, if_pos taken]
    exact (clear_aligned_target _
      (bltu_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known taken)).symm
  · rw [if_neg taken, if_neg taken]
#print axioms bltu_reference_successor
theorem bgeu_reference_successor (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    (run initial inputs (t+1)).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      writebackNextPc (run initial inputs t) := by
  have checked := pc_check_alignment_reachable initial inputs cycles reset env t ht
  have alu := decoded_alu_alignment_reachable initial inputs cycles reset env t ht
  have zero := reference_zero_reachable initial inputs cycles reset t ht
  have pcEq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
      v2222 (run initial inputs t) (inputs t) := pc
  have checkEq := bgeu_check_agreement _ _ checked agree zero commit known
  have target := bgeu_target_agreement _ _ alu pc commit known
  have next := (bgeu_event_and_pc_reachable initial inputs cycles reset env t ht agree pc commit known).2
  rw [next]
  simp only [writebackNextPc, checkEq, target, pcEq]
  by_cases taken : v6545 (run initial inputs t) (inputs t) = 1
  · rw [if_pos taken, if_pos taken]
    exact (clear_aligned_target _
      (bgeu_target_aligned_reachable initial inputs cycles reset env t ht agree pc commit known taken)).symm
  · rw [if_neg taken, if_neg taken]
#print axioms bgeu_reference_successor
end RiscvMiniProofs

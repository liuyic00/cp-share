import Proofs.AluRedirectPriority
import Proofs.BranchAlignmentAssumption
namespace NutShellProofs
open nNutCore

/-- The original alignment assumption covers taken branches and jumps;
only the sequential branch fall-through needs execute-PC alignment. -/
theorem alu_control_target_aligned (s : State) (i : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0)
    (control : v12142 s i = 1)
    (sequential : BitVec.extractLsb' 0 2 (v12202 s i) = 0) :
    BitVec.extractLsb' 0 2 (v12212 s i) = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v12181 s i) with branchBit | jumpBit
  · have branch : v12182 s i = 1 := by simp [v12182, branchBit, v24]
    rcases BitVec.eq_zero_or_eq_one (v12179 s i) with notTaken | taken
    · simpa [v12212, v12190, v12189, notTaken, branch, v24] using sequential
    · have target := original_branch_alignment_assumption s i environment reset branch taken
      simpa [v12212, v12190, v12189, taken, v24] using target
  · have all : (assumptionChecks0 s i).all id = true := environment
    simp only [assumptionChecks0, List.all_cons, List.all_nil, Bool.and_eq_true,
      Bool.and_true] at all
    have check : v31810 s i ≠ 1 ∨ v31809 s i = 1 := of_decide_eq_true all.2.2.1
    have gate : v31810 s i = 1 := by simp [v31810, v24, reset]
    have enabled := check.resolve_left (not_not_intro gate)
    have jumpCheck : v31805 s i = 1 := by
      change v31795 s i &&& v31805 s i = 1 at enabled
      rcases BitVec.eq_zero_or_eq_one (v31805 s i) with zero | one
      · simp [zero] at enabled
      · exact one
    have target : BitVec.extractLsb' 0 2 (v12211 s i) = 0 := by
      have bit4 : BitVec.extractLsb' 4 1 (v12141 s i) = 1 := control
      have bit3 : BitVec.extractLsb' 3 1 (v12141 s i) = 1 := jumpBit
      simpa [v31805, v31801, v31800, v31796, v31799, v31798, v31797,
        bit3, bit4, v24, v31804, v31802, v31803] using jumpCheck
    have notBranch : v12182 s i = 0 := by simp [v12182, jumpBit, v24]
    simpa [v12212, v12190, notBranch] using target

/-- A committed, non-trapping ALU redirect is a control-flow operation. -/
theorem committed_alu_redirect_control (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (noTrap : v13725 s i = 0) (redirect : v8 (step s i) next = 1) :
    v12142 s i = 1 := by
  obtain ⟨mou, csr⟩ := alu_redirect_priority s i unit
  have csrZero := csr.trans noTrap
  change v25388 s i = 1 at redirect
  rw [v25388, if_pos (commit_requires_capture s i next commit)] at redirect
  rcases BitVec.eq_zero_or_eq_one (v12142 s i) with zero | one
  · simp [v25387, v25386, mou, v25385, csrZero, v25384, v25383,
      v25382, zero] at redirect
  · exact one

theorem committed_alu_redirect_aligned (s : State) (i next : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (noTrap : v13725 s i = 0) (redirect : v8 (step s i) next = 1)
    (sequential : BitVec.extractLsb' 0 2 (v12202 s i) = 0) :
    BitVec.extractLsb' 0 2 (v2709 (step s i) next) = 0 := by
  change BitVec.extractLsb' 0 2
    (step s i).g49.r1571_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fredirect_5Ftarget = 0
  rw [committed_alu_redirect_target s i next commit unit noTrap]
  exact alu_control_target_aligned s i environment reset
    (committed_alu_redirect_control s i next commit unit noTrap redirect) sequential

theorem execute_sequential_target_aligned (s : State) (i : Inputs)
    (pc : BitVec.extractLsb' 0 2 s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc = 0)
    (width : BitVec.extractLsb' 0 2 (v11547 s i) = 3) :
    BitVec.extractLsb' 0 2 (v12202 s i) = 0 := by
  have full : v12193 s i = 0 := by
    simp [v12193, v12192, v12191, width, v2750]
  simp [v12202, full, v12201, v12200, v12198, v12199,
    low_low _ (by decide : 2 ≤ 39), low_add _ _ (by decide : 2 ≤ 40),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 39),
    v12145, v12144, pc]

#print axioms execute_sequential_target_aligned
#print axioms alu_control_target_aligned
#print axioms committed_alu_redirect_control
#print axioms committed_alu_redirect_aligned
end NutShellProofs

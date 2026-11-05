import Proofs.JalrExecution
import Proofs.ReferenceJumpDecode
import Proofs.JumpCheck
import Proofs.JumpCommit
namespace RiscvMiniProofs
open nCoreSoc

theorem jalr_sum_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (agree : RegisterAgreement s) (zero : ReferenceZero s)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v1721 s i + v2092 s i := by
  have value := (decoded_alu_reference_operands s alu agree).trans
    (decoded_execution_jalr _ _ _ _ known)
  rw [← reference_jalr_operand1 s i zero commit known,
    ← reference_jalr_immediate s i commit known] at value
  exact value

private theorem cleared_target_aligned (x : BitVec 32)
    (bit : BitVec.extractLsb' 1 1 x = 0) :
    BitVec.extractLsb' 0 2 ((BitVec.extractLsb' 1 31 x) ++ (0#1)) = 0 := by
  have b := congrArg (fun y : BitVec 1 => y.getLsbD 0) bit
  have b1 : x.getLsbD 1 = false := by simpa [BitVec.getLsbD_extractLsb'] using b
  have b2 : x[1] = false := by simpa using b1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : j = 0
  · subst j
    simp [BitVec.getElem_append (n := 31) (m := 1), BitVec.getElem_extractLsb']
  · have h1 : j = 1 := by omega
    subst j
    simp [BitVec.getElem_append (n := 31) (m := 1), BitVec.getElem_extractLsb', b2]

theorem jalr_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    BitVec.extractLsb' 0 2 (v2205 (run initial inputs t) (inputs t)) = 0 := by
  have sum := jalr_sum_agreement _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) agree
    (reference_zero_reachable initial inputs cycles reset t ht) commit known
  have bit := jump_target_bit_reachable initial inputs cycles reset env t ht (Or.inr known)
  rw [sum] at bit
  rw [reference_jalr_target]
  exact cleared_target_aligned _ bit

theorem jalr_tasks_reachable_of_pc (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    RegisterTasks (run initial inputs t) (inputs t) :=
  jalr_tasks_reachable initial inputs cycles reset env t ht agree commit pc
    (jalr_target_aligned_reachable initial inputs cycles reset env t ht agree commit known) known

#print axioms jalr_sum_agreement
#print axioms jalr_target_aligned_reachable
#print axioms jalr_tasks_reachable_of_pc
end RiscvMiniProofs

import Proofs.JalTarget
import Proofs.PcLowBit
namespace RiscvMiniProofs
open nCoreSoc

private theorem low_two_zero (x : BitVec 32)
    (bit0 : BitVec.extractLsb' 0 1 x = 0) (bit1 : BitVec.extractLsb' 1 1 x = 0) :
    BitVec.extractLsb' 0 2 x = 0 := by
  have b0 := congrArg (fun y : BitVec 1 => y.getLsbD 0) bit0
  have b1 := congrArg (fun y : BitVec 1 => y.getLsbD 0) bit1
  have h0 : x[0] = false := by simpa using b0
  have h1 : x[1] = false := by simpa using b1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with h | h <;> subst j <;> simp [h0, h1]

theorem jal_target_aligned_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    BitVec.extractLsb' 0 2 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  apply low_two_zero
  · rw [jal_target_low_bit _ _ commit known]
    have low := (pc_low_bit_reachable initial inputs cycles reset env t ht).writeback
    have eq : (run initial inputs t).g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc =
        v2222 (run initial inputs t) (inputs t) := pc
    rw [eq] at low
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h : j = 0 := by omega
    subst j
    simpa using low
  · exact jal_target_bit_reachable initial inputs cycles reset env t ht pc commit known

theorem jal_tasks_reachable_of_pc (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (pc : WritebackPcAgreement (run initial inputs t))
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    RegisterTasks (run initial inputs t) (inputs t) :=
  jal_tasks_reachable initial inputs cycles reset env t ht agree commit pc
    (jal_target_aligned_reachable initial inputs cycles reset env t ht pc commit known) known

#print axioms jal_target_aligned_reachable
#print axioms jal_tasks_reachable_of_pc
end RiscvMiniProofs

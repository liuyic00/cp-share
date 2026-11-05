import Proofs.JalExecution
import Proofs.ReferenceJumpDecode
import Proofs.JumpCheck
import Proofs.JumpCommit
namespace RiscvMiniProofs
open nCoreSoc

theorem jal_target_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (pc : WritebackPcAgreement s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2222 s i + v2092 s i := by
  have value := alu.trans (decoded_execution_jal _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [pcEq, ← reference_jal_immediate s i commit known] at value
  exact value

theorem jal_target_bit_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (pc : WritebackPcAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    BitVec.extractLsb' 1 1 (v2222 (run initial inputs t) (inputs t) +
      v2092 (run initial inputs t) (inputs t)) = 0 := by
  have target := jal_target_agreement _ _
    (decoded_alu_alignment_reachable initial inputs cycles reset env t ht) pc commit known
  rw [← target]
  exact jump_target_bit_reachable initial inputs cycles reset env t ht (Or.inl known)

theorem jal_target_low_bit (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    BitVec.extractLsb' 0 1 (v2222 s i + v2092 s i) =
      BitVec.extractLsb' 0 1 (v2222 s i) := by
  rw [BitVec.extractLsb'_add (by decide), reference_jal_immediate s i commit known,
    immediateJ_even]
  simp

#print axioms jal_target_low_bit
#print axioms jal_target_agreement
#print axioms jal_target_bit_reachable
end RiscvMiniProofs

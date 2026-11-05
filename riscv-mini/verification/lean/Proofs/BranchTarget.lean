import Proofs.BranchExecution
import Proofs.ReferenceBranchDecode
import Proofs.PcRelation
namespace RiscvMiniProofs
open nCoreSoc
theorem beq_target_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (pc : WritebackPcAgreement s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2222 s i + v2092 s i := by
  have value := alu.trans (decoded_execution_beq _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [pcEq, ← reference_beq_immediate s i commit known] at value
  exact value

theorem beq_target_low_bit (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    BitVec.extractLsb' 0 1 (v2222 s i + v2092 s i) =
      BitVec.extractLsb' 0 1 (v2222 s i) := by
  rw [BitVec.extractLsb'_add (by decide), reference_beq_immediate s i commit known,
    immediateB_even]
  simp
#print axioms beq_target_agreement
#print axioms beq_target_low_bit

theorem bne_target_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (pc : WritebackPcAgreement s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2222 s i + v2092 s i := by
  have value := alu.trans (decoded_execution_bne _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [pcEq, ← reference_bne_immediate s i commit known] at value
  exact value

theorem bne_target_low_bit (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    BitVec.extractLsb' 0 1 (v2222 s i + v2092 s i) =
      BitVec.extractLsb' 0 1 (v2222 s i) := by
  rw [BitVec.extractLsb'_add (by decide), reference_bne_immediate s i commit known,
    immediateB_even]
  simp
#print axioms bne_target_agreement
#print axioms bne_target_low_bit

theorem blt_target_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (pc : WritebackPcAgreement s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2222 s i + v2092 s i := by
  have value := alu.trans (decoded_execution_blt _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [pcEq, ← reference_blt_immediate s i commit known] at value
  exact value

theorem blt_target_low_bit (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    BitVec.extractLsb' 0 1 (v2222 s i + v2092 s i) =
      BitVec.extractLsb' 0 1 (v2222 s i) := by
  rw [BitVec.extractLsb'_add (by decide), reference_blt_immediate s i commit known,
    immediateB_even]
  simp
#print axioms blt_target_agreement
#print axioms blt_target_low_bit

theorem bge_target_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (pc : WritebackPcAgreement s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2222 s i + v2092 s i := by
  have value := alu.trans (decoded_execution_bge _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [pcEq, ← reference_bge_immediate s i commit known] at value
  exact value

theorem bge_target_low_bit (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    BitVec.extractLsb' 0 1 (v2222 s i + v2092 s i) =
      BitVec.extractLsb' 0 1 (v2222 s i) := by
  rw [BitVec.extractLsb'_add (by decide), reference_bge_immediate s i commit known,
    immediateB_even]
  simp
#print axioms bge_target_agreement
#print axioms bge_target_low_bit

theorem bltu_target_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (pc : WritebackPcAgreement s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2222 s i + v2092 s i := by
  have value := alu.trans (decoded_execution_bltu _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [pcEq, ← reference_bltu_immediate s i commit known] at value
  exact value

theorem bltu_target_low_bit (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    BitVec.extractLsb' 0 1 (v2222 s i + v2092 s i) =
      BitVec.extractLsb' 0 1 (v2222 s i) := by
  rw [BitVec.extractLsb'_add (by decide), reference_bltu_immediate s i commit known,
    immediateB_even]
  simp
#print axioms bltu_target_agreement
#print axioms bltu_target_low_bit

theorem bgeu_target_agreement (s : State) (i : Inputs)
    (alu : DecodedAluAligned s) (pc : WritebackPcAgreement s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2222 s i + v2092 s i := by
  have value := alu.trans (decoded_execution_bgeu _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [pcEq, ← reference_bgeu_immediate s i commit known] at value
  exact value

theorem bgeu_target_low_bit (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    BitVec.extractLsb' 0 1 (v2222 s i + v2092 s i) =
      BitVec.extractLsb' 0 1 (v2222 s i) := by
  rw [BitVec.extractLsb'_add (by decide), reference_bgeu_immediate s i commit known,
    immediateB_even]
  simp
#print axioms bgeu_target_agreement
#print axioms bgeu_target_low_bit

end RiscvMiniProofs

import Proofs.WordWriteback
namespace NutShellProofs
open nNutCore

theorem reference_addiw_result (s : State) (i : Inputs) :
    v16336 s i = WordImmediateOp.add.eval (v15632 s i) (v16164 s i) := by
  have sum : v16332 s i = v15632 s i + v16164 s i := by
    simp only [v16332, v16331, v16329, v16330, low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  simp only [v16336, v16335, v16334, v11488, v11103,
    v16333, sum, WordImmediateOp.eval]
  exact sign_extend_word _

theorem reference_slliw_result (s : State) (i : Inputs) :
    v16309 s i = WordImmediateOp.sll.eval (v15632 s i) (v16164 s i) := by
  have core : v16306 s i = (BitVec.extractLsb' 0 32 (v15632 s i)) <<<
      (BitVec.extractLsb' 0 5 (v16164 s i)).toNat := by
    simp only [v16306, v16305, v16302, v16301, v16304, v16303, v11483,
      BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
    have result := low_shiftLeft (v16242 s i ++ BitVec.extractLsb' 0 32 (v15632 s i))
      (BitVec.extractLsb' 0 5 (v16164 s i)).toNat (by decide : 32 ≤ 63)
    simpa only [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 32 ≤ 32),
      BitVec.extractLsb'_eq_self] using result
  simp only [v16309, v16308, v16307, v11488, v11103,
    core, WordImmediateOp.eval]
  exact sign_extend_word _

theorem reference_srliw_result (s : State) (i : Inputs) :
    v16298 s i = WordImmediateOp.srl.eval (v15632 s i) (v16164 s i) := by
  have core : v16295 s i = (BitVec.extractLsb' 0 32 (v15632 s i)) >>>
      (BitVec.extractLsb' 0 5 (v16164 s i)).toNat := by
    simp only [v16295, v16292, v16294, v16293, v11710]
    rw [BitVec.toNat_append]
    simp
  simp only [v16298, v16297, v16296, v11488, v11103,
    core, WordImmediateOp.eval]
  exact sign_extend_word _

theorem reference_sraiw_result (s : State) (i : Inputs) :
    v16289 s i = WordImmediateOp.sra.eval (v15632 s i) (v16164 s i) := by
  have core : v16286 s i = (BitVec.extractLsb' 0 32 (v15632 s i)).sshiftRight
      (BitVec.extractLsb' 0 5 (v16164 s i)).toNat := by
    simp only [v16286, v16283, v16285, v16284, v11710]
    rw [BitVec.toNat_append]
    simp
  simp only [v16289, v16288, v16287, v11488, v11103,
    core, WordImmediateOp.eval]
  exact sign_extend_word _

#print axioms reference_addiw_result
#print axioms reference_slliw_result
#print axioms reference_srliw_result
#print axioms reference_sraiw_result
end NutShellProofs

import Proofs.AluResults
import Proofs.WordBits
namespace NutShellProofs
open nNutCore

theorem alu_word_output (s : State) (i : Inputs)
    (word : BitVec.extractLsb' 5 1 (v28 s i) = 1)
    (branch : BitVec.extractLsb' 4 1 (v28 s i) = 0) :
    v25095 s i = (BitVec.extractLsb' 0 32 (v25086 s i)).signExtend 64 := by
  simp only [v25095, v25094, v25093, v12142, v12141, branch,
    v25092, v25025, word, v25091, v24, v25090, v25089, v25088, v25087,
    v11488, v11103, show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  simp only [BitVec.extractLsb'_eq_self]
  exact sign_extend_word _

#print axioms alu_word_output
end NutShellProofs

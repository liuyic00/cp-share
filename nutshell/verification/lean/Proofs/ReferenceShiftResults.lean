import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

/-- The reference has overlapping shift decoders; these pairs match identically. -/
theorem reference_shift_duplicate_matches (s : State) (i : Inputs) :
    v14825 s i = v15023 s i ∧ v14818 s i = v15016 s i ∧ v14811 s i = v15009 s i := by
  exact ⟨rfl, rfl, rfl⟩

theorem reference_slli64_result (s : State) (i : Inputs) :
    v16326 s i = v15632 s i <<< (BitVec.extractLsb' 0 6 (v16164 s i)).toNat := by
  simp only [v16326, v16325, v16322, v16324, v16323, v16276,
    BitVec.toNat_append, BitVec.toNat_ofNat]
  simp only [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  have result := low_shiftLeft (v12724 s i ++ v15632 s i)
    (BitVec.extractLsb' 0 6 (v16164 s i)).toNat (by decide : 64 ≤ 127)
  simpa only [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
    BitVec.extractLsb'_eq_self] using result

theorem reference_srli64_result (s : State) (i : Inputs) :
    v16319 s i = v15632 s i >>> (BitVec.extractLsb' 0 6 (v16164 s i)).toNat := by
  simp only [v16319, v16318, v16317, v11483]
  rw [BitVec.toNat_append]
  simp

theorem reference_srai64_result (s : State) (i : Inputs) :
    v16314 s i = BitVec.sshiftRight (v15632 s i) (BitVec.extractLsb' 0 6 (v16164 s i)).toNat := by
  simp only [v16314, v16313, v16312, v11483]
  rw [BitVec.toNat_append]
  simp

/-- The actual higher-priority x1 update stage selects the six-bit result. -/
theorem reference_slli64_x1_stage (s : State) (i : Inputs)
    (matched : v14825 s i = 1) (dest : v15142 s i = 1) :
    v16650 s i = v15632 s i <<< (BitVec.extractLsb' 0 6 (v16164 s i)).toNat := by
  simp only [v16650, matched, ↓reduceIte, v16649, v16321, v16320, dest]
  exact reference_slli64_result s i

theorem reference_srli64_x1_stage (s : State) (i : Inputs)
    (matched : v14818 s i = 1) (dest : v15142 s i = 1) :
    v16652 s i = v15632 s i >>> (BitVec.extractLsb' 0 6 (v16164 s i)).toNat := by
  simp only [v16652, matched, ↓reduceIte, v16651, v16316, v16315, dest]
  exact reference_srli64_result s i

theorem reference_srai64_x1_stage (s : State) (i : Inputs)
    (matched : v14811 s i = 1) (dest : v15142 s i = 1) :
    v16654 s i = BitVec.sshiftRight (v15632 s i) (BitVec.extractLsb' 0 6 (v16164 s i)).toNat := by
  simp only [v16654, matched, ↓reduceIte, v16653, v16311, v16310, dest]
  exact reference_srai64_result s i

#print axioms reference_shift_duplicate_matches
#print axioms reference_slli64_x1_stage
#print axioms reference_srli64_x1_stage
#print axioms reference_srai64_x1_stage
end NutShellProofs

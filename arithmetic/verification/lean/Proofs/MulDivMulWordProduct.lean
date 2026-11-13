import Proofs.MulDivMulWord

namespace MulDivMultiply
open nMulDiv

/-- A virtual unsigned final digit has the same low 64 bits as the real
final edge. Its exact integer balance exposes the MULW product at bits 63:32. -/
theorem word_balance (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (b : BitVec 65)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 32)
    (divisor : s.r7_ndivisor = b) (initialSign : sign s = 0)
    (initial : packed s = 0#65 ++ a)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (reset : ∀ t, t < 32 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 32 → (inputs t).nio_5Fkill = 0) :
    ∃ (virtual : BitVec 129) (consumed : Nat), consumed < 4294967296 ∧
      (packed (run s inputs 32)).extractLsb' 0 64 = virtual.extractLsb' 0 64 ∧
      4294967296 * virtual.toInt + consumed =
        (a.toNat : Int) + 18446744073709551616 * b.toInt * consumed := by
  have countNat : s.r3_ncount.toNat = 32 := congrArg BitVec.toNat count
  rcases signed_prefix_from_count 31 s inputs a b (by omega) state divisor initialSign initial bBound
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega)) with
    ⟨captured, accBound, q, size, balance⟩
  let p := packed (run s inputs 31)
  let bit := digit p
  have bits : bit = 0 ∨ bit = 1 := by unfold bit digit; split <;> simp
  have coefficient : (((0 : BitVec 1) ++ p.extractLsb' 0 1) : BitVec 2).toInt = (bit : Int) :=
    unsigned_coefficient p
  have cases : (((0 : BitVec 1) ++ p.extractLsb' 0 1) : BitVec 2).toInt = -1 ∨
      (((0 : BitVec 1) ++ p.extractLsb' 0 1) : BitVec 2).toInt = 0 ∨
      (((0 : BitVec 1) ++ p.extractLsb' 0 1) : BitVec 2).toInt = 1 := by
    rw [coefficient]
    rcases bits with h | h <;> simp [h]
  have edge := signed_step_balance p b 0 cases bBound accBound
  have bitCast : (if (lowWord p).getLsbD 0 then (1 : Int) else 0) = (bit : Int) := by
    unfold bit digit
    split <;> rfl
  rw [bitCast, coefficient] at edge
  have localEdge : 2 * (multiplyStep p b 0).toInt + (bit : Int) =
      p.toInt + 18446744073709551616 * b.toInt * (bit : Int) := by
    simpa only [Int.mul_comm (bit : Int) b.toInt, Int.mul_assoc] using edge
  have nextBalance := advance_integer_balance 2147483648 p.toInt (multiplyStep p b 0).toInt
    bit b.toInt q a.toNat localEdge balance
  have control := compute_prefix 31 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  refine ⟨multiplyStep p b 0, q + bit * 2147483648, ?_, ?_, ?_⟩
  · rcases bits with h | h <;> rw [h] <;> simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] <;> omega
  · change (packed (step (run s inputs 31) (inputs 31))).extractLsb' 0 64 = _
    rw [compute_datapath _ _ control.1, captured]
    exact low_step_sign p b _ 0
  · simpa only [Int.natCast_add, Int.natCast_mul] using nextBalance

theorem word_balance_decode (a : BitVec 64) (b value : Int) (consumed : Nat)
    (size : consumed < 4294967296)
    (balance : 4294967296 * value + consumed =
      (a.toNat : Int) + 18446744073709551616 * b * consumed) :
    consumed = a.toNat % 4294967296 ∧
    value = 4294967296 * (b * consumed) + (a.toNat / 4294967296 : Nat) := by
  rw [Int.mul_assoc] at balance
  have range := a.isLt
  have quotient := Nat.mod_add_div a.toNat 4294967296
  omega

theorem word_slice_decode (a : BitVec 64) (b : Int) (value : BitVec 129) (consumed : Nat)
    (size : consumed < 4294967296)
    (balance : 4294967296 * value.toInt + consumed =
      (a.toNat : Int) + 18446744073709551616 * b * consumed) :
    value.extractLsb' 32 32 =
      (BitVec.ofInt 129 (b * (a.toNat % 4294967296 : Nat))).extractLsb' 0 32 := by
  have decoded := word_balance_decode a b value.toInt consumed size balance
  have range := a.isLt
  have shifted : (value.sshiftRight 32).toInt = b * consumed := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    change value.toInt / 4294967296 = _
    omega
  have encoded := congrArg (BitVec.ofInt 129) shifted
  rw [BitVec.ofInt_toInt, decoded.1] at encoded
  have slice : value.extractLsb' 32 32 = (value.sshiftRight 32).extractLsb' 0 32 := by bv_decide
  rw [slice, encoded]

def wordSpecification (i : Inputs) : BitVec 64 :=
  ((BitVec.ofInt 129 ((i.nio_5Freq_5Fbits_5Fin2.extractLsb' 0 32).toInt *
    (i.nio_5Freq_5Fbits_5Fin1.extractLsb' 0 32).toNat)).extractLsb' 0 32).signExtend 64

theorem wordSpecification_eq (i : Inputs) :
    wordSpecification i = ((i.nio_5Freq_5Fbits_5Fin1.extractLsb' 0 32) *
      (i.nio_5Freq_5Fbits_5Fin2.extractLsb' 0 32)).signExtend 64 := by
  unfold wordSpecification
  congr 1
  rw [BitVec.ofInt_mul, ← BitVec.setWidth_eq_extractLsb' (by decide),
    BitVec.setWidth_mul _ _ (by decide)]
  have signedNarrow (x : BitVec 32) : (BitVec.ofInt 129 x.toInt).setWidth 32 = x := by
    change (x.signExtend 129).setWidth 32 = x
    bv_decide
  have unsignedNarrow (x : BitVec 32) : (BitVec.ofInt 129 x.toNat).setWidth 32 = x := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [signedNarrow, unsignedNarrow, BitVec.mul_comm]

theorem word_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0)
    (word : (inputs 0).nio_5Freq_5Fbits_5Fdw = 0)
    (reset : ∀ t, t < 33 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 33 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Fdata = wordSpecification (inputs 0) ∧
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Ftag =
      (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have captured := capture_word s (inputs 0) idle valid operation word (reset 0 (by decide))
  let a := ((inputs 0).nio_5Freq_5Fbits_5Fin1.extractLsb' 0 32).signExtend 64
  let b := ((inputs 0).nio_5Freq_5Fbits_5Fin2.extractLsb' 0 32).signExtend 65
  have bValue : b.toInt = ((inputs 0).nio_5Freq_5Fbits_5Fin2.extractLsb' 0 32).toInt :=
    BitVec.toInt_signExtend_of_le (by decide)
  have bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616 := by
    rw [bValue]
    have lo := BitVec.le_toInt ((inputs 0).nio_5Freq_5Fbits_5Fin2.extractLsb' 0 32)
    have hi := BitVec.toInt_lt (x := (inputs 0).nio_5Freq_5Fbits_5Fin2.extractLsb' 0 32)
    omega
  rcases word_balance (step s (inputs 0)) (fun t => inputs (t + 1)) a b
    captured.1 captured.2.1 captured.2.2.2.1 captured.2.2.2.2.1 captured.2.2.1 bBound
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega)) with
    ⟨virtual, consumed, size, sameLow, balance⟩
  rw [← MulDivControl.run_from_next s inputs 32] at sameLow
  have sameSlice : (packed (run s inputs 33)).extractLsb' 32 32 = virtual.extractLsb' 32 32 := by
    bv_decide
  have decoded := word_slice_decode a b.toInt virtual consumed size balance
  have aValue : a.toNat % 4294967296 = ((inputs 0).nio_5Freq_5Fbits_5Fin1.extractLsb' 0 32).toNat := by
    have slice : a.extractLsb' 0 32 = (inputs 0).nio_5Freq_5Fbits_5Fin1.extractLsb' 0 32 := by
      simp only [a]
      bv_decide
    have h := congrArg BitVec.toNat slice
    simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.reducePow] using h
  have response := word_response s inputs idle valid operation word reset kill
  refine ⟨response.1, ?_, response.2.2⟩
  rw [response.2.1, sameSlice, decoded, bValue, aValue]
  rfl

theorem word_after_reset (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0)
    (word : (inputs 0).nio_5Freq_5Fbits_5Fdw = 0)
    (reset : ∀ t, t < 33 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 33 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step initial resetInput) inputs 33) (inputs 33)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step initial resetInput) inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Fdata = wordSpecification (inputs 0) ∧
    (observe (run (step initial resetInput) inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Ftag =
      (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  exact word_result _ inputs (MulDivControl.reset_ready initial resetInput resetEdge)
    valid operation word reset kill

end MulDivMultiply

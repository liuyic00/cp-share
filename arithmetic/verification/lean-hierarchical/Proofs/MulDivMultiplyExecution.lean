import Proofs.MulDivMultiplication

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

def multiplyMany (d : BitVec 65) (negative : BitVec 1) (start : Nat) :
    Nat → BitVec 130 → BitVec 130
  | 0, bits => bits
  | n + 1, bits => multiplyAdvance (multiplyMany d negative start n bits) d
      (BitVec.ofNat 7 (start + n)) negative

/-- Full-width and word multiplication share this trace theorem; their initial
    counter determines how many digits remain. -/
theorem multiplication_prefix (s : State) (inputs : Nat → Inputs)
    (multiplying : s.r0_nstate = 2) (start : Nat) (counter : s.r3_ncount.toNat = start)
    (reset : ∀ t, t < 64 - start → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 - start → (inputs t).nio_5Fkill = 0)
    (n : Nat) (beforeLast : start + n < 64) :
    (run s inputs n).r0_nstate = 2 ∧
    (run s inputs n).r3_ncount.toNat = start + n ∧
    (run s inputs n).r7_ndivisor = s.r7_ndivisor ∧
    (run s inputs n).r4_nneg_5Fout = s.r4_nneg_5Fout ∧
    (run s inputs n).r8_nremainder =
      multiplyMany s.r7_ndivisor s.r4_nneg_5Fout start n s.r8_nremainder := by
  induction n with
  | zero => simp [run, multiplyMany, multiplying, counter]
  | succ n ih =>
    obtain ⟨state, count, divisor, sign, bits⟩ := ih (by omega)
    have control := multiplication_control (run s inputs n) (inputs n) state
      (reset n (by omega)) (alive n (by omega))
    have notLast : (run s inputs n).r3_ncount ≠ 63#7 := by
      intro h
      have value := congrArg BitVec.toNat h
      change (run s inputs n).r3_ncount.toNat = 63 at value
      omega
    have countBits : (run s inputs n).r3_ncount = BitVec.ofNat 7 (start + n) := by
      apply BitVec.eq_of_toNat_eq
      rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ?_, control.2.2.1.trans divisor, control.2.2.2.1.trans sign, ?_⟩
    · change (step (run s inputs n) (inputs n)).r0_nstate = _
      simpa [notLast] using control.1
    · change (step (run s inputs n) (inputs n)).r3_ncount.toNat = _
      rw [control.2.1, BitVec.toNat_add, count]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · change (step (run s inputs n) (inputs n)).r8_nremainder = _
      rw [multiplication_edge _ _ state, divisor, sign, bits, countBits]
      rfl

/-- After the remaining digits, the hardware enters its multiply response
    state with exactly the iterated data value and unchanged request metadata. -/
theorem multiplication_finishes (s : State) (inputs : Nat → Inputs)
    (multiplying : s.r0_nstate = 2) (start : Nat) (counter : s.r3_ncount.toNat = start)
    (range : start < 64)
    (reset : ∀ t, t < 64 - start → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 - start → (inputs t).nio_5Fkill = 0) :
    (run s inputs (64 - start)).r0_nstate = 6 ∧
    (run s inputs (64 - start)).r8_nremainder =
      multiplyMany s.r7_ndivisor s.r4_nneg_5Fout start (64 - start) s.r8_nremainder ∧
    metadata (run s inputs (64 - start)) = metadata s := by
  let n := 63 - start
  have last := multiplication_prefix s inputs multiplying start counter reset alive n (by dsimp [n]; omega)
  have countBits : (run s inputs n).r3_ncount = 63#7 := by
    apply BitVec.eq_of_toNat_eq
    have value := last.2.1
    change (run s inputs n).r3_ncount.toNat = 63
    dsimp [n] at value
    omega
  have control := multiplication_control (run s inputs n) (inputs n) last.1
    (reset n (by dsimp [n]; omega)) (alive n (by dsimp [n]; omega))
  have length : 64 - start = n + 1 := by dsimp [n]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [length, run, control.1, countBits, if_pos rfl]
    rfl
  · rw [length, run, multiplication_edge _ _ last.1, last.2.2.1,
      last.2.2.2.1, last.2.2.2.2, countBits, multiplyMany]
    congr 1
    have index : start + n = 63 := by dsimp [n]; omega
    rw [index]
  · apply metadata_run
    intro t h
    have active := multiplication_prefix s inputs multiplying start counter reset alive t (by omega)
    rw [active.1]
    decide

#print axioms multiplication_finishes
#print axioms multiplication_prefix
end HierarchicalMulDiv

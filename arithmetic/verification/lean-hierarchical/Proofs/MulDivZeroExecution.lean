import Proofs.MulDivZeroArithmetic

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

theorem zero_prefix (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#65) (initial : s.r8_nremainder = 0#66 ++ a)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0)
    (n : Nat) (within : n ≤ 64) :
    (run s inputs n).r0_nstate = 3 ∧ (run s inputs n).r3_ncount.toNat = n ∧
    (run s inputs n).r7_ndivisor = 0#65 ∧ (run s inputs n).r8_nremainder = zeroBits a n := by
  induction n with
  | zero => simp [run, zeroBits, dividing, count, divisor, initial]
  | succ n ih =>
    obtain ⟨state, counter, storedDivisor, remainder⟩ := ih (by omega)
    have control := division_control (run s inputs n) (inputs n) state
      (reset n (by omega)) (alive n (by omega))
    have notLast : (run s inputs n).r3_ncount ≠ 64#7 := by
      intro h
      have value := congrArg BitVec.toNat h
      change (run s inputs n).r3_ncount.toNat = 64 at value
      omega
    simp only [run]
    refine ⟨?_, ?_, control.2.2.trans storedDivisor, ?_⟩
    · simpa [notLast] using control.1
    · rw [control.2.1, BitVec.toNat_add, counter]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · rw [division_edge _ _ state, remainder, storedDivisor, zeroBits_step _ _ (by omega)]

/-- The zero-divisor computation produces a formatted response after all 65
    digits, including the leading digit, with the captured tag unchanged. -/
theorem zero_core_result (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#65) (initial : s.r8_nremainder = 0#66 ++ a)
    (nonnegative : s.r4_nneg_5Fout = 0#1)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata =
      formatUnsigned (BitVec.allOnes 64) a s.r1_nreq_5Fdw s.r5_nisHi := by
  have traceFacts := zero_prefix s inputs a dividing count divisor initial reset alive
  have active (t : Nat) (h : t < 65) : (run s inputs t).r0_nstate = 3 := (traceFacts t (by omega)).1
  have last := traceFacts 64 (by omega)
  have counter : (run s inputs 64).r3_ncount = 64#7 := BitVec.eq_of_toNat_eq last.2.1
  have sign := nonnegative_run s inputs 64 nonnegative (by intro t h; exact active t (by omega))
  have control := division_control (run s inputs 64) (inputs 64) last.1
    (reset 64 (by omega)) (alive 64 (by omega))
  have finished : (run s inputs 65).r0_nstate = 7 := by
    change (step (run s inputs 64) (inputs 64)).r0_nstate = _
    rw [control.1, counter, if_pos rfl, sign]
    rfl
  have bits : (run s inputs 65).r8_nremainder = zeroBits a 65 := by
    change (step (run s inputs 64) (inputs 64)).r8_nremainder = _
    rw [division_edge _ _ last.1, last.2.2.1, last.2.2.2, zeroBits_step _ _ (by omega)]
  have earlier := metadata_run s inputs 64 (by intro t h; rw [active t (by omega)]; decide)
  have later := metadata_run s inputs 65 (by intro t h; rw [active t h]; decide)
  have mode : (run s inputs 65).r6_nresHi = s.r5_nisHi :=
    (select_response _ _ last.1 counter).trans (congrArg (fun f => f.2.2) earlier)
  have output := observe_division (run s inputs 65) (inputs 65) finished
  refine ⟨output.1, output.2.1.trans (congrArg (fun f => f.2.1) later), ?_⟩
  rw [output.2.2, bits, (zeroBits_result a).1, (zeroBits_result a).2, mode,
    show (run s inputs 65).r1_nreq_5Fdw = s.r1_nreq_5Fdw from congrArg (fun f => f.1) later]

#print axioms zero_core_result
end HierarchicalMulDiv

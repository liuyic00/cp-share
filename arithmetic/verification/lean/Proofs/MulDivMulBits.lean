import Proofs.MulDivMultiplyRun

namespace MulDivMultiply
open nMulDiv

/-- Bits below the accumulator feed point move right independently of the
partial product. This theorem refers to the actual generated edge. -/
theorem low_bit_step (s : State) (i : Inputs) (k : Nat)
    (state : s.r0_nstate = 2) (bound : k < 63) :
    (packed (step s i)).getLsbD k = (packed s).getLsbD (k + 1) := by
  rw [compute_datapath _ _ state]
  simp only [multiplyStep, BitVec.getLsbD_append, bound, if_true,
    BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]
  rw [Nat.add_comm 1 k]

/-- Every unconsumed multiplier bit still comes from the initial operand,
regardless of accumulator values, multiplicand signs, or injected sign bits. -/
theorem bit_run (n : Nat) (s : State) (inputs : Nat → Inputs) (k : Nat)
    (state : s.r0_nstate = 2) (remaining : s.r3_ncount.toNat + n ≤ 64)
    (position : k + n < 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    (packed (run s inputs n)).getLsbD k = (packed s).getLsbD (k + n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have control := compute_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    change (packed (step (run s inputs n) (inputs n))).getLsbD k = _
    rw [low_bit_step _ _ k control.1 (by omega)]
    have prior := ih (k + 1) (by omega) (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    rw [prior]
    congr 1
    omega

theorem negative_run (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (remaining : s.r3_ncount.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    (run s inputs n).r4_nneg_5Fout = s.r4_nneg_5Fout := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have control := compute_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    change (step (run s inputs n) (inputs n)).r4_nneg_5Fout = _
    rw [(preserve_operands _ _ control.1).2.1]
    exact ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))

theorem prefix_sign_from_count (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (initialSign : sign s = 0)
    (limit : s.r3_ncount.toNat + n ≤ 62)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    sign (run s inputs n) = 0 := by
  cases n with
  | zero => exact initialSign
  | succ n =>
    have control := compute_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have notLast : (run s inputs n).r3_ncount ≠ 62 := by
      intro eq
      have : (run s inputs n).r3_ncount.toNat = 62 := congrArg BitVec.toNat eq
      omega
    change sign (step (run s inputs n) (inputs n)) = _
    rw [inject_sign _ _ control.1, if_neg notLast]

theorem unsigned_prefix_sign (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 0) (initialSign : sign s = 0)
    (limit : n ≤ 62)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    sign (run s inputs n) = 0 := by
  cases n with
  | zero => exact initialSign
  | succ n =>
    have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
    have control := compute_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have notLast : (run s inputs n).r3_ncount ≠ 62 := by
      intro eq
      have : (run s inputs n).r3_ncount.toNat = 62 := congrArg BitVec.toNat eq
      omega
    change sign (step (run s inputs n) (inputs n)) = _
    rw [inject_sign _ _ control.1, if_neg notLast]

theorem last_sign (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (reset : ∀ t, t < 63 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 63 → (inputs t).nio_5Fkill = 0) :
    sign (run s inputs 63) = s.r4_nneg_5Fout := by
  have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
  have control := compute_prefix 62 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have lastCount : (run s inputs 62).r3_ncount = 62 := by
    apply BitVec.eq_of_toNat_eq
    change (run s inputs 62).r3_ncount.toNat = 62
    omega
  change sign (step (run s inputs 62) (inputs 62)) = _
  rw [inject_sign _ _ control.1, lastCount, if_pos rfl]
  exact negative_run 62 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))

/-- For signed high products, the final two-bit coefficient is 0 or -1;
it is never -2. Its negative weight is exactly the original sign bit. -/
theorem last_signed_digit (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (initial : packed s = 0#65 ++ a) (negative : s.r4_nneg_5Fout = BitVec.ofBool a.msb)
    (reset : ∀ t, t < 63 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 63 → (inputs t).nio_5Fkill = 0) :
    ((sign (run s inputs 63) ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt =
      if a.msb then -1 else 0 := by
  have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
  have bit := bit_run 63 s inputs 0 state (by omega) (by decide) reset kill
  rw [initial] at bit
  have original : (packed (run s inputs 63)).getLsbD 0 = a.msb := by
    simpa only [Nat.zero_add, BitVec.getLsbD_append, show 63 < 64 by decide, if_true,
      BitVec.msb_eq_getLsbD_last] using bit
  have extract (p : BitVec 129) : p.extractLsb' 0 1 = BitVec.ofBool (p.getLsbD 0) := by bv_decide
  rw [last_sign s inputs state count reset kill, negative, extract, original]
  cases h : a.msb <;> decide

theorem capture_signed_high (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 1 ∨ i.nio_5Freq_5Fbits_5Ffn = 2)
    (full : i.nio_5Freq_5Fbits_5Fdw = 1) (reset : i.nreset = 0) :
    (step s i).r0_nstate = 2 ∧ (step s i).r3_ncount = 0 ∧
    packed (step s i) = 0#65 ++ i.nio_5Freq_5Fbits_5Fin1 ∧
    (step s i).r7_ndivisor = (if i.nio_5Freq_5Fbits_5Ffn = 1
      then i.nio_5Freq_5Fbits_5Fin2.signExtend 65 else 0#1 ++ i.nio_5Freq_5Fbits_5Fin2) ∧
    sign (step s i) = 0 ∧ (step s i).r4_nneg_5Fout = BitVec.ofBool i.nio_5Freq_5Fbits_5Fin1.msb ∧
    MulDivOutput.metadata (step s i) = (1, i.nio_5Freq_5Fbits_5Ftag, 1) := by
  rcases operation with operation | operation <;>
    simp only [step, eval, packed, sign, MulDivOutput.metadata, idle, valid,
      operation, full, reset, Prod.mk.injEq] <;> bv_decide

end MulDivMultiply

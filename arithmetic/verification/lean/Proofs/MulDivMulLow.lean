import Proofs.MulDivMulSignedHigh

namespace MulDivMultiply
open nMulDiv

theorem low_step_sign (p : BitVec 129) (b : BitVec 65) (x y : BitVec 1) :
    (multiplyStep p b x).extractLsb' 0 64 = (multiplyStep p b y).extractLsb' 0 64 := by
  simp only [multiplyStep, stepProduct]
  bv_decide

theorem low_product (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (b : BitVec 65)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = b) (initialSign : sign s = 0)
    (initial : packed s = 0#65 ++ a)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (packed (run s inputs 64)).extractLsb' 0 64 =
      (BitVec.ofInt 129 (a.toInt * b.toInt)).extractLsb' 0 64 := by
  have resets : ∀ t, t < 63 → (inputs t).nreset = 0 := fun t h => reset t (by omega)
  have kills : ∀ t, t < 63 → (inputs t).nio_5Fkill = 0 := fun t h => kill t (by omega)
  rcases signed_prefix 63 s inputs a b (by decide) state count divisor initialSign initial
    bBound resets kills with ⟨captured, accBound, q, size, balance⟩
  have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
  have control := compute_prefix 63 s inputs state (by omega) resets kills
  have bit := bit_run 63 s inputs 0 state (by omega) (by decide) resets kills
  rw [initial] at bit
  have original : (lowWord (packed (run s inputs 63))).getLsbD 0 = a.msb := by
    simpa only [lowWord, BitVec.getLsbD_extractLsb', show 0 < 64 by decide, Bool.true_and,
      Nat.zero_add, BitVec.getLsbD_append, show 63 < 64 by decide, if_true,
      BitVec.msb_eq_getLsbD_last] using bit
  have coefficient : ((BitVec.ofBool a.msb ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt =
      if a.msb then -1 else 0 := by
    have extract (p : BitVec 129) : p.extractLsb' 0 1 = BitVec.ofBool ((lowWord p).getLsbD 0) := by
      simp only [lowWord]
      bv_decide
    rw [extract, original]
    cases a.msb <;> decide
  have coefficientCases :
      ((BitVec.ofBool a.msb ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt = -1 ∨
      ((BitVec.ofBool a.msb ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt = 0 ∨
      ((BitVec.ofBool a.msb ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt = 1 := by
    rw [coefficient]
    cases a.msb <;> simp
  have edge := signed_step_balance (packed (run s inputs 63)) b (BitVec.ofBool a.msb)
    coefficientCases bBound accBound
  rw [original, coefficient] at edge
  have next : packed (run s inputs 64) =
      multiplyStep (packed (run s inputs 63)) b (sign (run s inputs 63)) := by
    change packed (step (run s inputs 63) (inputs 63)) = _
    rw [compute_datapath _ _ control.1, captured]
  have virtual := decode_signed_product a b.toInt (packed (run s inputs 63)).toInt
    (multiplyStep (packed (run s inputs 63)) b (BitVec.ofBool a.msb)).toInt q size balance edge
  have encoded := congrArg (BitVec.ofInt 129) virtual
  rw [BitVec.ofInt_toInt] at encoded
  rw [next, low_step_sign _ _ _ (BitVec.ofBool a.msb), encoded]

theorem capture_low (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 0) (full : i.nio_5Freq_5Fbits_5Fdw = 1)
    (reset : i.nreset = 0) :
    (step s i).r0_nstate = 2 ∧ (step s i).r3_ncount = 0 ∧
    packed (step s i) = 0#65 ++ i.nio_5Freq_5Fbits_5Fin1 ∧
    (step s i).r7_ndivisor = i.nio_5Freq_5Fbits_5Fin2.signExtend 65 ∧
    sign (step s i) = 0 ∧ (step s i).r4_nneg_5Fout = BitVec.ofBool (i.nio_5Freq_5Fbits_5Fin1.msb != i.nio_5Freq_5Fbits_5Fin2.msb) ∧
    MulDivOutput.metadata (step s i) = (1, i.nio_5Freq_5Fbits_5Ftag, 0) := by
  simp only [step, eval, packed, sign, MulDivOutput.metadata, idle, valid,
    operation, full, reset, Prod.mk.injEq]
  bv_decide

def lowSpecification (i : Inputs) : BitVec 64 :=
  (BitVec.ofInt 129 (i.nio_5Freq_5Fbits_5Fin1.toInt * i.nio_5Freq_5Fbits_5Fin2.toInt)).extractLsb' 0 64

theorem lowSpecification_eq (i : Inputs) :
    lowSpecification i = i.nio_5Freq_5Fbits_5Fin1 * i.nio_5Freq_5Fbits_5Fin2 := by
  unfold lowSpecification
  rw [BitVec.ofInt_mul, ← BitVec.setWidth_eq_extractLsb' (by decide),
    BitVec.setWidth_mul _ _ (by decide)]
  have narrow (a : BitVec 64) : (BitVec.ofInt 129 a.toInt).setWidth 64 = a := by
    change (a.signExtend 129).setWidth 64 = a
    bv_decide
  rw [narrow, narrow]

/-- All full-width MUL operands: exactly 64 further edges after acceptance yield the
correct low half of the product, a valid response, and the original tag. -/
theorem low_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0) (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata = lowSpecification (inputs 0) ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have captured := capture_low s (inputs 0) idle valid operation full (reset 0 (by decide))
  let b := (inputs 0).nio_5Freq_5Fbits_5Fin2.signExtend 65
  have bValue : b.toInt = (inputs 0).nio_5Freq_5Fbits_5Fin2.toInt :=
    BitVec.toInt_signExtend_of_le (by decide)
  have bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616 := by
    rw [bValue]
    have lo := BitVec.le_toInt (inputs 0).nio_5Freq_5Fbits_5Fin2
    have hi := BitVec.toInt_lt (x := (inputs 0).nio_5Freq_5Fbits_5Fin2)
    omega
  have product := low_product (step s (inputs 0)) (fun t => inputs (t + 1))
    (inputs 0).nio_5Freq_5Fbits_5Fin1 b
    captured.1 captured.2.1 captured.2.2.2.1 captured.2.2.2.2.1 captured.2.2.1
    bBound (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  have finish := finish64 (step s (inputs 0)) (fun t => inputs (t + 1)) captured.1 captured.2.1
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  rw [← MulDivControl.run_from_next s inputs 64] at product finish
  have captureMeta := captured.2.2.2.2.2.2
  have finalMeta := finish.2.2.trans captureMeta
  have width := congrArg (fun m => m.1) finalMeta
  have tag := congrArg (fun m => m.2.1) finalMeta
  have select := finish.2.1.trans (congrArg (fun m => m.2.2) captureMeta)
  have output := observe_product (run s inputs 65) (inputs 65) finish.1 width
  refine ⟨MulDivControl.done_valid _ _ (Or.inl finish.1), ?_, output.2.trans tag⟩
  rw [output.1, select, if_neg (by change (0 : BitVec 1) ≠ 1; decide), product, bValue]
  rfl

theorem low_after_reset (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs)
    (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0) (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata = lowSpecification (inputs 0) ∧
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  exact low_result _ inputs (MulDivControl.reset_ready initial resetInput resetEdge)
    valid operation full reset kill

end MulDivMultiply

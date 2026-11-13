import Proofs.MulDivMulSignedProduct
import Proofs.MulDivMulHigh

namespace MulDivMultiply
open nMulDiv

def signedHighSpecification (i : Inputs) : BitVec 64 :=
  (BitVec.ofInt 129 (i.nio_5Freq_5Fbits_5Fin1.toInt *
    (if i.nio_5Freq_5Fbits_5Ffn = 1 then i.nio_5Freq_5Fbits_5Fin2.toInt
      else i.nio_5Freq_5Fbits_5Fin2.toNat))).extractLsb' 64 64

/-- All MULH/MULHSU operands: exactly 64 further edges after acceptance yield the
correct high half of the product, a valid response, and the original tag. -/
theorem signed_high_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 1 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 2) (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata = signedHighSpecification (inputs 0) ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have captured := capture_signed_high s (inputs 0) idle valid operation full (reset 0 (by decide))
  let b := if (inputs 0).nio_5Freq_5Fbits_5Ffn = 1
    then (inputs 0).nio_5Freq_5Fbits_5Fin2.signExtend 65
    else 0#1 ++ (inputs 0).nio_5Freq_5Fbits_5Fin2
  have bValue : b.toInt = if (inputs 0).nio_5Freq_5Fbits_5Ffn = 1
      then (inputs 0).nio_5Freq_5Fbits_5Fin2.toInt else (inputs 0).nio_5Freq_5Fbits_5Fin2.toNat := by
    unfold b
    split
    · exact BitVec.toInt_signExtend_of_le (by decide)
    · rw [BitVec.toInt_append]
      simp
  have bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616 := by
    rw [bValue]
    have lo := BitVec.le_toInt (inputs 0).nio_5Freq_5Fbits_5Fin2
    have hi := BitVec.toInt_lt (x := (inputs 0).nio_5Freq_5Fbits_5Fin2)
    have natBound := (inputs 0).nio_5Freq_5Fbits_5Fin2.isLt
    split <;> omega
  have product := signed_product (step s (inputs 0)) (fun t => inputs (t + 1))
    (inputs 0).nio_5Freq_5Fbits_5Fin1 b
    captured.1 captured.2.1 captured.2.2.2.1 captured.2.2.2.2.1 captured.2.2.1
    captured.2.2.2.2.2.1 bBound
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
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
  rw [output.1, select, if_pos rfl]
  have encoded := congrArg (BitVec.ofInt 129) product
  rw [BitVec.ofInt_toInt, bValue] at encoded
  rw [encoded]
  rfl

theorem signed_high_after_reset (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs)
    (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 1 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 2) (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata = signedHighSpecification (inputs 0) ∧
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  exact signed_high_result _ inputs (MulDivControl.reset_ready initial resetInput resetEdge)
    valid operation full reset kill

end MulDivMultiply

import Proofs.MulDivMulLow

namespace MulDivMultiply
open nMulDiv
open MulDivOutput (metadata)

theorem finish32 (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 32)
    (reset : ∀ t, t < 32 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 32 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 32).r0_nstate = 6 ∧ (run s inputs 32).r6_nresHi = s.r5_nisHi ∧
    metadata (run s inputs 32) = metadata s := by
  have countNat : s.r3_ncount.toNat = 32 := congrArg BitVec.toNat count
  have control := compute_prefix 31 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have prior := metadata_run 31 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have lastCount : (run s inputs 31).r3_ncount = 63 := by
    apply BitVec.eq_of_toNat_eq
    change (run s inputs 31).r3_ncount.toNat = 63
    omega
  have edge := last_edge (run s inputs 31) (inputs 31) control.1 lastCount
    (reset 31 (by decide)) (kill 31 (by decide))
  exact ⟨edge.1, edge.2.trans (congrArg (fun m => m.2.2) prior),
    metadata_run 32 s inputs state (by omega) reset kill⟩


theorem capture_word (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 0) (word : i.nio_5Freq_5Fbits_5Fdw = 0)
    (reset : i.nreset = 0) :
    (step s i).r0_nstate = 2 ∧ (step s i).r3_ncount = 32 ∧
    packed (step s i) = 0#65 ++ (i.nio_5Freq_5Fbits_5Fin1.extractLsb' 0 32).signExtend 64 ∧
    (step s i).r7_ndivisor = (i.nio_5Freq_5Fbits_5Fin2.extractLsb' 0 32).signExtend 65 ∧
    sign (step s i) = 0 ∧
    metadata (step s i) = (0, i.nio_5Freq_5Fbits_5Ftag, 0) := by
  simp only [step, eval, packed, sign, metadata, idle, valid, operation, word, reset, Prod.mk.injEq]
  bv_decide

theorem observe_word (s : State) (i : Inputs)
    (state : s.r0_nstate = 6) (word : s.r1_nreq_5Fdw = 0) (low : s.r6_nresHi = 0) :
    (observe s i).nio_5Fresp_5Fbits_5Fdata = ((packed s).extractLsb' 32 32).signExtend 64 ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag := by
  simp only [observe, eval, packed, state, word, low]
  bv_decide

/-- MULW completes after 32 further edges; the response selects packed bits
63:32 and preserves the accepted tag. The operand-product equality is supplied by MulDivMulWordProduct. -/
theorem word_response (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0)
    (word : (inputs 0).nio_5Freq_5Fbits_5Fdw = 0)
    (reset : ∀ t, t < 33 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 33 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Fdata =
      ((packed (run s inputs 33)).extractLsb' 32 32).signExtend 64 ∧
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Ftag =
      (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have captured := capture_word s (inputs 0) idle valid operation word (reset 0 (by decide))
  have finish := finish32 (step s (inputs 0)) (fun t => inputs (t + 1)) captured.1 captured.2.1
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  rw [← MulDivControl.run_from_next s inputs 32] at finish
  have captureMeta := captured.2.2.2.2.2
  have finalMeta := finish.2.2.trans captureMeta
  have width := congrArg (fun m => m.1) finalMeta
  have tag := congrArg (fun m => m.2.1) finalMeta
  have select := finish.2.1.trans (congrArg (fun m => m.2.2) captureMeta)
  have output := observe_word (run s inputs 33) (inputs 33) finish.1 width select
  exact ⟨MulDivControl.done_valid _ _ (Or.inl finish.1), output.1, output.2.trans tag⟩

end MulDivMultiply

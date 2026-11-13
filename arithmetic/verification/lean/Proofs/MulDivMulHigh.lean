import Proofs.MulDivMultiplyRun

namespace MulDivMultiply
open nMulDiv
open MulDivOutput (metadata)

theorem metadata_run (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (remaining : s.r3_ncount.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    metadata (run s inputs n) = metadata s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have control := compute_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    change metadata (step (run s inputs n) (inputs n)) = _
    rw [(preserve_operands _ _ control.1).2.2]
    exact ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))

theorem last_edge (s : State) (i : Inputs) (state : s.r0_nstate = 2)
    (count : s.r3_ncount = 63) (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 6 ∧ (step s i).r6_nresHi = s.r5_nisHi := by
  simp only [step, eval, state, count, reset, kill]
  bv_decide

theorem finish64 (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 64).r0_nstate = 6 ∧ (run s inputs 64).r6_nresHi = s.r5_nisHi ∧
    metadata (run s inputs 64) = metadata s := by
  have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
  have control := compute_prefix 63 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have prior := metadata_run 63 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have lastCount : (run s inputs 63).r3_ncount = 63 := by
    apply BitVec.eq_of_toNat_eq
    change (run s inputs 63).r3_ncount.toNat = 63
    omega
  have edge := last_edge (run s inputs 63) (inputs 63) control.1 lastCount
    (reset 63 (by decide)) (kill 63 (by decide))
  exact ⟨edge.1, edge.2.trans (congrArg (fun m => m.2.2) prior),
    metadata_run 64 s inputs state (by omega) reset kill⟩

theorem observe_product (s : State) (i : Inputs)
    (state : s.r0_nstate = 6) (full : s.r1_nreq_5Fdw = 1) :
    (observe s i).nio_5Fresp_5Fbits_5Fdata =
      (if s.r6_nresHi = 1 then (packed s).extractLsb' 64 64 else (packed s).extractLsb' 0 64) ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag := by
  simp only [observe, eval, state, full, packed]
  bv_decide

def unsignedHighSpecification (i : Inputs) : BitVec 64 :=
  BitVec.ofNat 64 ((i.nio_5Freq_5Fbits_5Fin1.toNat * i.nio_5Freq_5Fbits_5Fin2.toNat) / 18446744073709551616)

/-- All MULHU operands: exactly 64 further edges after acceptance yield the
correct high half of the product, a valid response, and the original tag. -/
theorem unsigned_high_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 3) (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata = unsignedHighSpecification (inputs 0) ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have captured := capture_unsigned_high s (inputs 0) idle valid operation full (reset 0 (by decide))
  have initial : (packed (step s (inputs 0))).toNat = (inputs 0).nio_5Freq_5Fbits_5Fin1.toNat := by
    rw [captured.2.2.1, BitVec.toNat_append]
    simp
  have product := unsigned_product (step s (inputs 0)) (fun t => inputs (t + 1))
    (inputs 0).nio_5Freq_5Fbits_5Fin1 (inputs 0).nio_5Freq_5Fbits_5Fin2
    captured.1 captured.2.1 captured.2.2.2.1 captured.2.2.2.2.1 captured.2.2.2.2.2.1 initial
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
  apply BitVec.eq_of_toNat_eq
  simp only [unsignedHighSpecification, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow, product]

theorem unsigned_high_after_reset (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs)
    (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 3) (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata = unsignedHighSpecification (inputs 0) ∧
    (observe (run (step initial resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  exact unsigned_high_result _ inputs (MulDivControl.reset_ready initial resetInput resetEdge)
    valid operation full reset kill

end MulDivMultiply

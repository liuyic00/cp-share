import Proofs.MulDivZero

namespace MulDivOutput
open nMulDiv
open MulDivDivision (packed)

def metadata (s : State) : BitVec 1 × BitVec 5 × BitVec 1 :=
  (s.r1_nreq_5Fdw, s.r2_nreq_5Ftag, s.r5_nisHi)

theorem metadata_edge (s : State) (i : Inputs) (state : s.r0_nstate = 3) :
    metadata (step s i) = metadata s := by
  simp [metadata, step, eval, state]

theorem nonnegative_edge (s : State) (i : Inputs) (state : s.r0_nstate = 3)
    (nonnegative : s.r4_nneg_5Fout = 0) :
    (step s i).r4_nneg_5Fout = 0 := by
  simp [step, eval, state, nonnegative]

theorem metadata_run (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r3_ncount.toNat + n ≤ 65)
    (nonnegative : s.r4_nneg_5Fout = 0)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    metadata (run s inputs n) = metadata s ∧ (run s inputs n).r4_nneg_5Fout = 0 := by
  induction n with
  | zero => exact ⟨rfl, nonnegative⟩
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have control := MulDivDivision.div_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    change metadata (step (run s inputs n) (inputs n)) = _ ∧ _
    exact ⟨(metadata_edge _ _ control.1).trans prior.1, nonnegative_edge _ _ control.1 prior.2⟩

theorem last_edge (s : State) (i : Inputs) (state : s.r0_nstate = 3)
    (count : s.r3_ncount = 64) (nonnegative : s.r4_nneg_5Fout = 0)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 7 ∧ (step s i).r6_nresHi = s.r5_nisHi := by
  simp only [step, eval, state, count, nonnegative, reset, kill]
  bv_decide

theorem unsigned_finish (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (nonnegative : s.r4_nneg_5Fout = 0)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 65).r0_nstate = 7 ∧
    (run s inputs 65).r6_nresHi = s.r5_nisHi ∧
    metadata (run s inputs 65) = metadata s := by
  have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
  have control := MulDivDivision.div_prefix 64 s inputs state (by omega)
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have prior := metadata_run 64 s inputs state (by omega) nonnegative
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have lastCount : (run s inputs 64).r3_ncount = 64 := by
    apply BitVec.eq_of_toNat_eq
    change (run s inputs 64).r3_ncount.toNat = 64
    omega
  have edge := last_edge (run s inputs 64) (inputs 64) control.1 lastCount prior.2
    (reset 64 (by decide)) (kill 64 (by decide))
  have selection := congrArg (fun m => m.2.2) prior.1
  exact ⟨edge.1, edge.2.trans selection,
    (metadata_run 65 s inputs state (by omega) nonnegative reset kill).1⟩

theorem unsigned_capture_metadata (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (full : i.nio_5Freq_5Fbits_5Fdw = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 5 ∨ i.nio_5Freq_5Fbits_5Ffn = 7) :
    (step s i).r4_nneg_5Fout = 0 ∧
    metadata (step s i) = (1, i.nio_5Freq_5Fbits_5Ftag,
      if i.nio_5Freq_5Fbits_5Ffn = 7 then 1 else 0) := by
  rcases operation with operation | operation <;>
    simp only [step, eval, metadata, idle, valid, full, operation, Prod.mk.injEq] <;> bv_decide

theorem observe_division (s : State) (i : Inputs)
    (state : s.r0_nstate = 7) (full : s.r1_nreq_5Fdw = 1) :
    (observe s i).nio_5Fresp_5Fbits_5Fdata =
      (if s.r6_nresHi = 1 then (packed s).extractLsb' 65 64 else (packed s).extractLsb' 0 64) ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag := by
  simp only [observe, eval, state, full, packed]
  bv_decide

theorem unsigned_request_control (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 66).r0_nstate = 7 ∧
    (run s inputs 66).r6_nresHi = (if (inputs 0).nio_5Freq_5Fbits_5Ffn = 7 then 1 else 0) ∧
    metadata (run s inputs 66) = (1, (inputs 0).nio_5Freq_5Fbits_5Ftag,
      if (inputs 0).nio_5Freq_5Fbits_5Ffn = 7 then 1 else 0) := by
  have captured := MulDivDivision.unsigned_capture s (inputs 0) idle valid (reset 0 (by decide)) full operation
  have captureMeta := unsigned_capture_metadata s (inputs 0) idle valid full operation
  have finish : (run s inputs 66).r0_nstate = 7 ∧
      (run s inputs 66).r6_nresHi = (step s (inputs 0)).r5_nisHi ∧
      metadata (run s inputs 66) = metadata (step s (inputs 0)) := by
    rw [show 66 = 65 + 1 from rfl, MulDivControl.run_from_next]
    exact unsigned_finish _ _ captured.1 captured.2.1 captureMeta.1
      (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  exact ⟨finish.1, finish.2.1.trans (congrArg (fun m => m.2.2) captureMeta.2),
    finish.2.2.trans captureMeta.2⟩

def unsignedSpecification (i : Inputs) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Ffn = 7 then
    BitVec.ofNat 64 (i.nio_5Freq_5Fbits_5Fin1.toNat % i.nio_5Freq_5Fbits_5Fin2.toNat)
  else if i.nio_5Freq_5Fbits_5Fin2 = 0 then BitVec.allOnes 64
  else BitVec.ofNat 64 (i.nio_5Freq_5Fbits_5Fin1.toNat / i.nio_5Freq_5Fbits_5Fin2.toNat)

/-- Actual response data for a nonzero unsigned request, including its original tag. -/
theorem unsigned_nonzero_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (nonzero : (inputs 0).nio_5Freq_5Fbits_5Fin2 ≠ 0)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have control := unsigned_request_control s inputs idle valid full operation reset kill
  have finalFull := congrArg (fun m => m.1) control.2.2
  have tag := congrArg (fun m => m.2.1) control.2.2
  have arithmetic := MulDivDivision.unsigned_accepted_magnitudes s inputs idle valid full operation nonzero reset kill
  have quotient := congrArg (BitVec.ofNat 64) arithmetic.1
  have remainder := congrArg (BitVec.ofNat 64) arithmetic.2
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at quotient remainder
  have output := observe_division (run s inputs 66) (inputs 66) control.1 finalFull
  refine ⟨MulDivControl.done_valid _ _ (Or.inr control.1), ?_, output.2.trans tag⟩
  rw [output.1, control.2.1]
  by_cases choose : (inputs 0).nio_5Freq_5Fbits_5Ffn = 7 <;>
    simp only [unsignedSpecification, choose, nonzero, if_true, if_false, quotient, remainder] <;> simp

theorem unsigned_zero_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (zero : (inputs 0).nio_5Freq_5Fbits_5Fin2 = 0)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have control := unsigned_request_control s inputs idle valid full operation reset kill
  have finalFull := congrArg (fun m => m.1) control.2.2
  have tag := congrArg (fun m => m.2.1) control.2.2
  have arithmetic := MulDivZero.unsigned_accepted_zero s inputs idle valid full operation zero reset kill
  have output := observe_division (run s inputs 66) (inputs 66) control.1 finalFull
  refine ⟨MulDivControl.done_valid _ _ (Or.inr control.1), ?_, output.2.trans tag⟩
  rw [output.1, control.2.1]
  by_cases choose : (inputs 0).nio_5Freq_5Fbits_5Ffn = 7 <;>
    simp only [unsignedSpecification, choose, zero, if_true, if_false, arithmetic.1, arithmetic.2] <;> simp

/-- All 64-bit unsigned division/remainder operands, including zero divisors:
65 further edges after acceptance yield the correct valid response and tag.
Only reset and kill are constrained after the initial request. -/
theorem unsigned_accepted_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  by_cases zero : (inputs 0).nio_5Freq_5Fbits_5Fin2 = 0
  · exact unsigned_zero_result s inputs idle valid full operation zero reset kill
  · exact unsigned_nonzero_result s inputs idle valid full operation zero reset kill

theorem unsigned_after_reset_result (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs)
    (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step initial resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step initial resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) ∧
    (observe (run (step initial resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  exact unsigned_accepted_result _ inputs (MulDivControl.reset_ready initial resetInput resetEdge)
    valid full operation reset kill

end MulDivOutput

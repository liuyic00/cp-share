import Generated.MultiCycleMac

namespace HierarchicalMac
open DesignnMultiCycleMac.nMultiCycleMac

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60

/-- Acceptance stores operands without imposing conditions on later inputs. -/
theorem capture (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (reset : i.nreset = 0)
    (valid : i.nio_5Fin_5Fvalid = 1) :
    (step s i).r0_nstate = 1 ∧
    (step s i).r1_noperands_5Fa = i.nio_5Fin_5Fbits_5Fa ∧
    (step s i).r2_noperands_5Fb = i.nio_5Fin_5Fbits_5Fb ∧
    (step s i).r3_noperands_5Fc = i.nio_5Fin_5Fbits_5Fc := by
  simp [step, eval_eq_spec, evalSpec, idle, reset, valid]

/-- Exact widened arithmetic at the externally visible response. -/
theorem accepted_result (s : State) (request adding multiplying observing : Inputs)
    (idle : s.r0_nstate = 0) (valid : request.nio_5Fin_5Fvalid = 1)
    (r0 : request.nreset = 0) (r1 : adding.nreset = 0)
    (r2 : multiplying.nreset = 0) (r3 : observing.nreset = 0) :
    let response := observe (step (step (step s request) adding) multiplying) observing
    response.nio_5Fout_5Fvalid = 1 ∧
    response.nio_5Fout_5Fbits =
      (0#8 ++ ((0#1 ++ request.nio_5Fin_5Fbits_5Fa) + (0#1 ++ request.nio_5Fin_5Fbits_5Fb))) *
      (0#9 ++ request.nio_5Fin_5Fbits_5Fc) := by
  simp [observe, step, eval_eq_spec, evalSpec, idle, valid, r0, r1, r2, r3]

/-- Backpressure retains the completed result while arbitrary requests arrive. -/
theorem backpressure (s : State) (i nextInput : Inputs)
    (done : s.r0_nstate = 3) (reset : i.nreset = 0)
    (blocked : i.nio_5Fout_5Fready = 0) (nextReset : nextInput.nreset = 0) :
    (observe (step s i) nextInput).nio_5Fout_5Fvalid = 1 ∧
    (observe (step s i) nextInput).nio_5Fout_5Fbits = (observe s i).nio_5Fout_5Fbits := by
  simp [observe, step, eval_eq_spec, evalSpec, done, reset, blocked, nextReset]

theorem no_early_response (s : State) (request adding multiplying : Inputs)
    (idle : s.r0_nstate = 0) (valid : request.nio_5Fin_5Fvalid = 1)
    (r0 : request.nreset = 0) (r1 : adding.nreset = 0) (r2 : multiplying.nreset = 0) :
    (observe (step s request) adding).nio_5Fout_5Fvalid = 0 ∧
    (observe (step (step s request) adding) multiplying).nio_5Fout_5Fvalid = 0 := by
  simp [observe, step, eval_eq_spec, evalSpec, idle, valid, r0, r1, r2]

theorem reset_idle (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).r0_nstate = 0 := by simp [step, eval_eq_spec, evalSpec, reset]

/-- Widths are sufficient for the mathematical result, not only modular arithmetic. -/
theorem full_width (a b c : BitVec 8) :
    (((0#8 ++ ((0#1 ++ a) + (0#1 ++ b))) * (0#9 ++ c) : BitVec 17)).toNat =
      (a.toNat + b.toNat) * c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have sumBound : a.toNat + b.toNat < 512 := by omega
  have productBound : (a.toNat + b.toNat) * c.toNat < 131072 := by
    have bound := Nat.mul_le_mul (show a.toNat + b.toNat ≤ 510 by omega)
      (show c.toNat ≤ 255 by omega)
    omega
  simp only [BitVec.toNat_mul, BitVec.toNat_append, BitVec.toNat_add]
  simp [Nat.mod_eq_of_lt sumBound, Nat.mod_eq_of_lt productBound]

/-- Data-stage facts together with the one-cycle assertion history. -/
def PipelineInvariant (s : State) : Prop :=
  ((s.r0_nstate = 2 ∨ s.r0_nstate = 3) →
    s.r4_nsum = (0#1 ++ s.r1_noperands_5Fa) + (0#1 ++ s.r2_noperands_5Fb)) ∧
  (s.r0_nstate = 3 → s.r5_nresult =
    (0#8 ++ ((0#1 ++ s.r1_noperands_5Fa) + (0#1 ++ s.r2_noperands_5Fb))) *
      (0#9 ++ s.r3_noperands_5Fc)) ∧
  (s.r6_naccepted = 1 → s.r0_nstate = 1) ∧
  (s.r7_nwasAdding = 1 → s.r0_nstate = 2) ∧
  (s.r8_nwasMultiplying = 1 → s.r0_nstate = 3) ∧
  (s.r9_nstalled = 1 → s.r0_nstate = 3 ∧ s.r10_npreviousOutput = s.r5_nresult)

private theorem bit_cases (b : BitVec 1) : b = 0 ∨ b = 1 := by
  have bound := b.isLt
  have values : b.toNat = 0 ∨ b.toNat = 1 := by omega
  rcases values with h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

private theorem state_cases (b : BitVec 2) : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
  have all : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  exact all b

theorem invariant_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    PipelineInvariant (step s i) := by
  simp [PipelineInvariant, step, eval_eq_spec, evalSpec, reset]

set_option maxHeartbeats 2000000 in
theorem invariant_preserved (s : State) (i : Inputs) (h : PipelineInvariant s) :
    PipelineInvariant (step s i) := by
  rcases state_cases s.r0_nstate with hs | hs | hs | hs <;>
    rcases bit_cases i.nreset with hr | hr <;>
    rcases bit_cases i.nio_5Fin_5Fvalid with hv | hv <;>
    rcases bit_cases i.nio_5Fout_5Fready with hd | hd <;>
    simp_all [PipelineInvariant, step, eval_eq_spec, evalSpec]

@[local simp] private theorem bit_and_one (b : BitVec 1) : b &&& (1#1) = b := by
  have all : ∀ b : BitVec 1, b &&& (1#1) = b := by decide
  exact all b

set_option maxHeartbeats 2000000 in
theorem invariant_checks (s : State) (i : Inputs) (h : PipelineInvariant s) : asserts s i := by
  apply asserts_of_parts
  rcases state_cases s.r0_nstate with hs | hs | hs | hs <;>
    rcases bit_cases i.nreset with hr | hr <;>
    simp_all [PipelineInvariant, localAsserts]
  by_cases stalled : s.r9_nstalled = 1#1
  · exact Or.inr (h.2.1.symm.trans (h.2.2.2.2 stalled).symm)
  · exact Or.inl stalled

theorem all_assertions_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (cycle : Nat) :
    asserts (run (step initial resetInput) inputs cycle) (inputs cycle) := by
  apply invariant_checks
  induction cycle with
  | zero => exact invariant_reset initial resetInput reset
  | succ cycle ih => exact invariant_preserved _ _ ih

#print axioms all_assertions_after_reset
#print axioms accepted_result
end HierarchicalMac

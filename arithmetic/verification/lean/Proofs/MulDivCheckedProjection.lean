import Generated.MulDiv
import Generated.MulDivChecked

namespace MulDivCheckedProjection

def inputs (x : nMulDivChecked.Inputs) : nMulDiv.Inputs :=
  {nreset := x.nreset, nio_5Freq_5Fvalid := x.nio_5Freq_5Fvalid, nio_5Freq_5Fbits_5Ffn := x.nio_5Freq_5Fbits_5Ffn, nio_5Freq_5Fbits_5Fdw := x.nio_5Freq_5Fbits_5Fdw, nio_5Freq_5Fbits_5Fin1 := x.nio_5Freq_5Fbits_5Fin1, nio_5Freq_5Fbits_5Fin2 := x.nio_5Freq_5Fbits_5Fin2, nio_5Freq_5Fbits_5Ftag := x.nio_5Freq_5Fbits_5Ftag, nio_5Fkill := x.nio_5Fkill, nio_5Fresp_5Fready := x.nio_5Fresp_5Fready}

def state (x : nMulDivChecked.State) : nMulDiv.State :=
  {r0_nstate := x.r0_nstate, r1_nreq_5Fdw := x.r1_nreq_5Fdw, r2_nreq_5Ftag := x.r2_nreq_5Ftag, r3_ncount := x.r3_ncount, r4_nneg_5Fout := x.r4_nneg_5Fout, r5_nisHi := x.r5_nisHi, r6_nresHi := x.r6_nresHi, r7_ndivisor := x.r7_ndivisor, r8_nremainder := x.r8_nremainder}

def outputs (x : nMulDivChecked.Outputs) : nMulDiv.Outputs :=
  {nio_5Freq_5Fready := x.nio_5Freq_5Fready, nio_5Fresp_5Fvalid := x.nio_5Fresp_5Fvalid, nio_5Fresp_5Fbits_5Fdata := x.nio_5Fresp_5Fbits_5Fdata, nio_5Fresp_5Fbits_5Ftag := x.nio_5Fresp_5Fbits_5Ftag}

theorem step_projects (s : nMulDivChecked.State) (i : nMulDivChecked.Inputs) :
    state (nMulDivChecked.step s i) = nMulDiv.step (state s) (inputs i) := by
  rfl

theorem observe_projects (s : nMulDivChecked.State) (i : nMulDivChecked.Inputs) :
    outputs (nMulDivChecked.observe s i) = nMulDiv.observe (state s) (inputs i) := by
  rfl

/-- Instrumentation preserves every core state on arbitrary input and reset traces. -/
theorem run_projects (s : nMulDivChecked.State) (pins : Nat → nMulDivChecked.Inputs) (n : Nat) :
    state (nMulDivChecked.run s pins n) = nMulDiv.run (state s) (fun t => inputs (pins t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change state (nMulDivChecked.step (nMulDivChecked.run s pins n) (pins n)) = _
    rw [step_projects, ih]
    rfl

end MulDivCheckedProjection

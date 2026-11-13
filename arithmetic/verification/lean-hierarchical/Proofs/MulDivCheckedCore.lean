import Generated.MulDivChecked
import Generated.MulDiv

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked
namespace Core
export DesignnMulDiv.nMulDiv (State Inputs Outputs step observe run)
end Core

def coreInputs (x : Inputs) : Core.Inputs :=
  { nreset := x.nreset, nio_5Freq_5Fvalid := x.nio_5Freq_5Fvalid, nio_5Freq_5Fbits_5Ffn := x.nio_5Freq_5Fbits_5Ffn, nio_5Freq_5Fbits_5Fdw := x.nio_5Freq_5Fbits_5Fdw, nio_5Freq_5Fbits_5Fin1 := x.nio_5Freq_5Fbits_5Fin1, nio_5Freq_5Fbits_5Fin2 := x.nio_5Freq_5Fbits_5Fin2, nio_5Freq_5Fbits_5Ftag := x.nio_5Freq_5Fbits_5Ftag, nio_5Fkill := x.nio_5Fkill, nio_5Fresp_5Fready := x.nio_5Fresp_5Fready }

def coreState (x : State) : Core.State :=
  { r0_nstate := x.r0_nstate, r1_nreq_5Fdw := x.r1_nreq_5Fdw, r2_nreq_5Ftag := x.r2_nreq_5Ftag, r3_ncount := x.r3_ncount, r4_nneg_5Fout := x.r4_nneg_5Fout, r5_nisHi := x.r5_nisHi, r6_nresHi := x.r6_nresHi, r7_ndivisor := x.r7_ndivisor, r8_nremainder := x.r8_nremainder }

def coreOutputs (x : Outputs) : Core.Outputs :=
  { nio_5Freq_5Fready := x.nio_5Freq_5Fready, nio_5Fresp_5Fvalid := x.nio_5Fresp_5Fvalid, nio_5Fresp_5Fbits_5Fdata := x.nio_5Fresp_5Fbits_5Fdata, nio_5Fresp_5Fbits_5Ftag := x.nio_5Fresp_5Fbits_5Ftag }

theorem core_step (s : State) (i : Inputs) :
    coreState (step s i) = Core.step (coreState s) (coreInputs i) := by
  simp only [step, eval_eq_spec, Core.step, DesignnMulDiv.nMulDiv.eval_eq_spec]
  rfl

theorem core_observe (s : State) (i : Inputs) :
    coreOutputs (observe s i) = Core.observe (coreState s) (coreInputs i) := by
  simp only [observe, eval_eq_spec, Core.observe, DesignnMulDiv.nMulDiv.eval_eq_spec]
  rfl

theorem core_run (s : State) (inputs : Nat → Inputs) (n : Nat) :
    coreState (run s inputs n) = Core.run (coreState s) (fun t => coreInputs (inputs t)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run, Core.run, core_step, ih]

end HierarchicalMulDivChecked

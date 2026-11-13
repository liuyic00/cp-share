import Generated.Radix2Divider
import Std.Tactic

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

/-- The history registers describe the immediately preceding control edge. -/
def HistoryInvariant (s : State) : Prop :=
  s.r10_nhistoryValid = 1 →
    (s.r11_npreviousState = 1 → s.r0_nstate = 2) ∧
    (s.r11_npreviousState = 2 → s.r0_nstate = 3) ∧
    (s.r11_npreviousState = 3 →
      s.r0_nstate = (if s.r12_npreviousCount = 63 then 4 else 3) ∧
      s.r9_ncnt_5Fvalue = (if s.r12_npreviousCount = 63 then 0 else s.r12_npreviousCount + 1))

theorem history_after_step (s : State) (i : Inputs) : HistoryInvariant (step s i) := by
  simp only [HistoryInvariant, step, eval_eq_spec, evalSpec,
    v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13,
    v14, v15, v16, v17, v18, v19, v22, v26, v62,
    v392, v393, v394, v395, v396, v397, v398]
  bv_decide

theorem history_checks (s : State) (i : Inputs) (history : HistoryInvariant s) :
    ((v433 s i) ≠ 1 ∨ (v6 s i) = 1) ∧
    ((v435 s i) ≠ 1 ∨ (v8 s i) = 1) ∧
    ((v440 s i) ≠ 1 ∨ (v439 s i) = 1) ∧
    ((v440 s i) ≠ 1 ∨ (v443 s i) = 1) := by
  unfold HistoryInvariant at history
  simp only [v433, v435, v440, v439, v443, v432, v434, v436,
    v437, v438, v441, v442, v416, v3, v5, v7, v9, v11, v22,
    v62, v394, v6, v8]
  bv_decide

end HierarchicalRadix

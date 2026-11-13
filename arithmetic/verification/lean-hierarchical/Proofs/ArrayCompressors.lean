import Generated.ArrayMulDataModule.Part000
import Std.Tactic

namespace HierarchicalArray
open DesignnArrayMulDataModule

/-- Natural-number contracts are independent of the compressor's column weight. -/
theorem c22_sum (s : nC22.State) (i : nC22.Inputs) :
    (nC22.observe s i).nio_5Fout_5F0.toNat +
      2 * (nC22.observe s i).nio_5Fout_5F1.toNat =
    i.nio_5Fin_5F0.toNat + i.nio_5Fin_5F1.toNat := by
  have truth : ∀ a b : BitVec 1,
      (a ^^^ b).toNat + 2 * (a &&& b).toNat = a.toNat + b.toNat := by decide
  exact truth i.nio_5Fin_5F0 i.nio_5Fin_5F1

private theorem fullAdder_sum : ∀ a b c : BitVec 1,
    (a ^^^ b ^^^ c).toNat + 2 * ((a &&& b) ||| ((a ^^^ b) &&& c)).toNat =
      a.toNat + b.toNat + c.toNat := by decide

theorem c32_sum (s : nC32.State) (i : nC32.Inputs) :
    (nC32.observe s i).nio_5Fout_5F0.toNat +
      2 * (nC32.observe s i).nio_5Fout_5F1.toNat =
    i.nio_5Fin_5F0.toNat + i.nio_5Fin_5F1.toNat + i.nio_5Fin_5F2.toNat := by
  exact fullAdder_sum i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2

theorem csa32_sum (s : nCSA3_5F2.State) (i : nCSA3_5F2.Inputs) :
    (nCSA3_5F2.observe s i).nio_5Fout_5F0.toNat +
      2 * (nCSA3_5F2.observe s i).nio_5Fout_5F1.toNat =
    i.nio_5Fin_5F0.toNat + i.nio_5Fin_5F1.toNat + i.nio_5Fin_5F2.toNat := by
  exact fullAdder_sum i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2

/-- Both child instances reuse the same full-adder contract. -/
theorem c53_sum (s : nC53.State) (i : nC53.Inputs) :
    (nC53.observe s i).nio_5Fout_5F0.toNat +
      2 * (nC53.observe s i).nio_5Fout_5F1.toNat +
      2 * (nC53.observe s i).nio_5Fout_5F2.toNat =
    i.nio_5Fin_5F0.toNat + i.nio_5Fin_5F1.toNat + i.nio_5Fin_5F2.toNat +
      i.nio_5Fin_5F3.toNat + i.nio_5Fin_5F4.toNat := by
  have first := csa32_sum s.inst_nCSA3_5F2 (nC53.inst_nCSA3_5F2Inputs s i)
  have second := csa32_sum s.inst_nCSA3_5F2_5F1 (nC53.inst_nCSA3_5F2_5F1Inputs s i)
  change (nC53.inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F0.toNat +
    2 * (nC53.inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F1.toNat = _ at first
  change (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F0.toNat +
    2 * (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F1.toNat = _ at second
  simp only [nC53.inst_nCSA3_5F2Inputs, nC53.inst_nCSA3_5F2_5F1Inputs] at first second
  change (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F0.toNat +
    2 * (nC53.inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F1.toNat +
    2 * (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F1.toNat = _
  omega

theorem c22_asserts (s : nC22.State) (i : nC22.Inputs) :
    nC22.asserts s i := by
  apply nC22.asserts_of_parts
  have all : ∀ reset x0 x1 : BitVec 1,
      nC22.localAsserts {} ⟨reset, x0, x1⟩ := by
        unfold nC22.localAsserts
        decide
  cases s
  exact all i.nreset i.nio_5Fin_5F0 i.nio_5Fin_5F1

theorem c32_asserts (s : nC32.State) (i : nC32.Inputs) :
    nC32.asserts s i := by
  apply nC32.asserts_of_parts
  have all : ∀ reset x0 x1 x2 : BitVec 1,
      nC32.localAsserts {} ⟨reset, x0, x1, x2⟩ := by
        unfold nC32.localAsserts
        decide
  cases s
  exact all i.nreset i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2

theorem csa32_asserts (s : nCSA3_5F2.State) (i : nCSA3_5F2.Inputs) :
    nCSA3_5F2.asserts s i := by
  apply nCSA3_5F2.asserts_of_parts
  have all : ∀ reset x0 x1 x2 : BitVec 1,
      nCSA3_5F2.localAsserts {} ⟨reset, x0, x1, x2⟩ := by
        unfold nCSA3_5F2.localAsserts
        decide
  cases s
  exact all i.nreset i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2

theorem c53_asserts (s : nC53.State) (i : nC53.Inputs) : nC53.asserts s i := by
  apply nC53.asserts_of_parts
  · have all : ∀ reset a b c d e : BitVec 1,
        nC53.localAsserts ⟨{}, {}⟩ ⟨reset, a, b, c, d, e⟩ := by
        unfold nC53.localAsserts
        decide
    rcases s with ⟨⟨⟩, ⟨⟩⟩
    exact all i.nreset i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2
      i.nio_5Fin_5F3 i.nio_5Fin_5F4
  · exact csa32_asserts s.inst_nCSA3_5F2 (nC53.inst_nCSA3_5F2Inputs s i)
  · exact csa32_asserts s.inst_nCSA3_5F2_5F1 (nC53.inst_nCSA3_5F2_5F1Inputs s i)

end HierarchicalArray

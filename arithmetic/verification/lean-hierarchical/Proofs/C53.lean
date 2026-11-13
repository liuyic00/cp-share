import Generated.C53

open DesignnC53

namespace HierarchicalCompressors

/-- The primitive full adder conserves the natural-number sum. -/
theorem fullAdder (s : nCSA3_5F2.State) (i : nCSA3_5F2.Inputs) :
    (nCSA3_5F2.observe s i).nio_5Fout_5F0.toNat +
      2 * (nCSA3_5F2.observe s i).nio_5Fout_5F1.toNat =
    i.nio_5Fin_5F0.toNat + i.nio_5Fin_5F1.toNat + i.nio_5Fin_5F2.toNat := by
  have truth : ∀ a b c : BitVec 1,
      ((a ^^^ b) ^^^ c).toNat + 2 * ((a &&& b) ||| ((a ^^^ b) &&& c)).toNat =
        a.toNat + b.toNat + c.toNat := by decide
  exact truth i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2

/-- C53 reuses the same primitive theorem at both instances. Its proof only
    reasons about their port connections and integer addition. -/
theorem c53_sum (s : nC53.State) (i : nC53.Inputs) :
    (nC53.observe s i).nio_5Fout_5F0.toNat +
      2 * (nC53.observe s i).nio_5Fout_5F1.toNat +
      2 * (nC53.observe s i).nio_5Fout_5F2.toNat =
    i.nio_5Fin_5F0.toNat + i.nio_5Fin_5F1.toNat + i.nio_5Fin_5F2.toNat +
      i.nio_5Fin_5F3.toNat + i.nio_5Fin_5F4.toNat := by
  have first := fullAdder s.inst_nCSA3_5F2 (nC53.inst_nCSA3_5F2Inputs s i)
  have second := fullAdder s.inst_nCSA3_5F2_5F1 (nC53.inst_nCSA3_5F2_5F1Inputs s i)
  change (nC53.inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F0.toNat +
    2 * (nC53.inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F1.toNat = _ at first
  change (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F0.toNat +
    2 * (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F1.toNat = _ at second
  simp only [nC53.inst_nCSA3_5F2Inputs, nC53.inst_nCSA3_5F2_5F1Inputs] at first second
  change (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F0.toNat +
    2 * (nC53.inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F1.toNat +
    2 * (nC53.inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F1.toNat = _
  omega

theorem primitive_checks (s : nCSA3_5F2.State) (i : nCSA3_5F2.Inputs) :
    nCSA3_5F2.asserts s i := by
  have all : ∀ reset a b c : BitVec 1,
      nCSA3_5F2.localAsserts {} ⟨reset, a, b, c⟩ := by
    unfold nCSA3_5F2.localAsserts
    decide
  apply nCSA3_5F2.asserts_of_parts
  cases s
  exact all i.nreset i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2

theorem primitive_balance (s : nCSA3_5F2.State) (i : nCSA3_5F2.Inputs) :
    ((0#4 ++ i.nio_5Fin_5F0) : BitVec 5) + (0#4 ++ i.nio_5Fin_5F1) + (0#4 ++ i.nio_5Fin_5F2) =
    (0#4 ++ (nCSA3_5F2.eval s i).output.nio_5Fout_5F0) +
      ((0#4 ++ (nCSA3_5F2.eval s i).output.nio_5Fout_5F1) <<< 1) := by
  have all : ∀ a b c : BitVec 1,
      ((0#4 ++ a) : BitVec 5) + (0#4 ++ b) + (0#4 ++ c) =
      (0#4 ++ (a ^^^ b ^^^ c)) + ((0#4 ++ ((a &&& b) ||| ((a ^^^ b) &&& c))) <<< 1) := by decide
  exact all i.nio_5Fin_5F0 i.nio_5Fin_5F1 i.nio_5Fin_5F2

open nC53 in
theorem local_checks (s : State) (i : Inputs) : localAsserts s i := by
  have first := primitive_balance s.inst_nCSA3_5F2 (inst_nCSA3_5F2Inputs s i)
  have second := primitive_balance s.inst_nCSA3_5F2_5F1 (inst_nCSA3_5F2_5F1Inputs s i)
  change ((0#4 ++ i.nio_5Fin_5F0) : BitVec 5) + (0#4 ++ i.nio_5Fin_5F1) + (0#4 ++ i.nio_5Fin_5F2) =
    (0#4 ++ (inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F0) +
    ((0#4 ++ (inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F1) <<< 1) at first
  change ((0#4 ++ (inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F0) : BitVec 5) +
    (0#4 ++ i.nio_5Fin_5F3) + (0#4 ++ i.nio_5Fin_5F4) =
    (0#4 ++ (inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F0) +
    ((0#4 ++ (inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F1) <<< 1) at second
  simp only [localAsserts, List.all_cons, List.all_nil, Bool.and_true, id_eq, decide_eq_true_eq]
  dsimp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19]
  bv_decide

open nC53 in
theorem all_checks (s : State) (i : Inputs) : asserts s i :=
  asserts_of_parts s i (local_checks s i)
    (primitive_checks s.inst_nCSA3_5F2 (inst_nCSA3_5F2Inputs s i))
    (primitive_checks s.inst_nCSA3_5F2_5F1 (inst_nCSA3_5F2_5F1Inputs s i))

#print axioms fullAdder
#print axioms c53_sum
end HierarchicalCompressors

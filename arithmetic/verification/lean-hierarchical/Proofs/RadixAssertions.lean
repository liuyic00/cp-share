import Proofs.RadixResultChecks
import Proofs.RadixHolding

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

/-- The arithmetic obligations apply to completed transactions only. -/
def ResultInvariant (s : State) : Prop :=
  s.r0_nstate = 4 →
    (s.r1_ndivBy0Reg = 1 →
      BitVec.extractLsb' 0 64 s.r2_nshiftReg = BitVec.allOnes 64 ∧
      BitVec.extractLsb' 65 64 s.r2_nshiftReg = BitVec.extractLsb' 1 64 s.r6_naValx2Reg) ∧
    (s.r1_ndivBy0Reg = 0 →
      (BitVec.extractLsb' 0 64 s.r2_nshiftReg).toNat * s.r5_nbReg.toNat +
        (BitVec.extractLsb' 65 64 s.r2_nshiftReg).toNat =
        (BitVec.extractLsb' 1 64 s.r6_naValx2Reg).toNat ∧
      (BitVec.extractLsb' 65 64 s.r2_nshiftReg).toNat < s.r5_nbReg.toNat)

theorem result_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    ResultInvariant (step s i) := by
  simp [ResultInvariant, step, eval_eq_spec, evalSpec, reset, v0]

theorem completed_result_preserved (s : State) (i : Inputs)
    (done : s.r0_nstate = 4) (inv : ResultInvariant s) :
    ResultInvariant (step s i) := by
  intro _
  have result := inv done
  simpa [step, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5, v6,
    v7, v8, v24, v25, v42, v43, v44, v55, v59, done] using result

theorem arithmetic_checks (s : State) (i : Inputs) (inv : ResultInvariant s) :
    ((v417 s i) ≠ 1 ∨ (v415 s i) = 1) ∧
    ((v417 s i) ≠ 1 ∨ (v419 s i) = 1) ∧
    ((v422 s i) ≠ 1 ∨ (v430 s i) = 1) ∧
    ((v422 s i) ≠ 1 ∨ (v431 s i) = 1) := by
  by_cases done : s.r0_nstate = 4
  · obtain ⟨zero, nonzero⟩ := inv done
    by_cases flag : s.r1_ndivBy0Reg = 1
    · obtain ⟨q, r⟩ := zero flag
      simp [v417, v399, v11, v416, v22, v415, v40, v414, v419, v402, v418,
        v422, v420, done, flag, q, r]
    · have clear : s.r1_ndivBy0Reg = 0 := by bv_decide
      obtain ⟨balance, bound⟩ := nonzero clear
      obtain ⟨reconstruct, remainder⟩ := nonzero_result_checks s i balance bound
      simp [v417, v399, v11, done, clear, reconstruct, remainder]
  · have inactive : s.r0_nstate ≠ 4#3 := done
    simp [v417, v422, v399, v11, inactive]

theorem asserts_of_invariants (s : State) (i : Inputs)
    (result : ResultInvariant s) (divisor : DivisorInvariant s)
    (history : HistoryInvariant s) (stall : StallInvariant s) : asserts s i := by
  apply asserts_of_parts
  have arithmetic := arithmetic_checks s i result
  have nonzero := divisor_check s i divisor
  have controls := history_checks s i history
  have holding := stall_checks s i stall
  unfold localAsserts
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨arithmetic.1, arithmetic.2.1, nonzero, arithmetic.2.2.1, arithmetic.2.2.2,
    controls.1, controls.2.1, controls.2.2.1, controls.2.2.2, holding.1, holding.2⟩

end HierarchicalRadix

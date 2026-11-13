import Generated.Adder

open DesignnAdder

namespace HierarchicalAdder
open nAdder

/-- The exported output implements eight-bit addition with a valid gate. -/
theorem result_correct (s : State) (i : Inputs) :
    (observe s i).nio_5Fout =
      if i.nio_5Fvalid = 1 then i.nio_5Fin1 + i.nio_5Fin2 else 0 := by
  rfl

/-- Every immediate Chisel assertion holds, including outside reset. -/
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  have cases : i.nio_5Fvalid = 0 ∨ i.nio_5Fvalid = 1 := by
    have bound := i.nio_5Fvalid.isLt
    have h : i.nio_5Fvalid.toNat = 0 ∨ i.nio_5Fvalid.toNat = 1 := by omega
    rcases h with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (BitVec.eq_of_toNat_eq h)
  rcases cases with h | h <;>
    simp [asserts, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, h]

#print axioms result_correct
#print axioms assertions_hold
end HierarchicalAdder

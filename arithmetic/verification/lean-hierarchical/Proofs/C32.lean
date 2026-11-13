import Generated.C32

namespace HierarchicalC32
open DesignnC32.nC32

/-- Prove the module's local arithmetic checks, then use its composition API. -/
theorem local_checks (s : State) (i : Inputs) : localAsserts s i := by
  simp only [localAsserts, List.all_cons, List.all_nil, Bool.and_true,
    id_eq, Bool.and_eq_true, decide_eq_true_eq]
  dsimp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21]
  bv_decide

theorem assertions (s : State) (i : Inputs) : asserts s i :=
  asserts_of_parts s i (local_checks s i)

#print axioms assertions
end HierarchicalC32

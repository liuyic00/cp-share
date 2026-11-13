import Generated.Adder

namespace nAdder
/-- The combinational result is correct for every input, including overflow. -/
theorem result_correct (s : State) (i : Inputs) :
    (observe s i).nio_5Fout =
      if i.nio_5Fvalid = 1 then i.nio_5Fin1 + i.nio_5Fin2 else 0 := by
  rfl

/-- The assertion exported from Chisel holds for all states and inputs. -/
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  unfold asserts eval
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, decide_eq_true_eq]
  bv_decide
end nAdder

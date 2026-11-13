import Generated.CSA2_2
import Generated.CSA3_2
import Generated.CSA5_3
import Generated.C22
import Generated.C32
import Generated.C53

set_option maxRecDepth 4096

namespace nCSA2_5F2
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  unfold asserts eval
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, decide_eq_true_eq]
  bv_decide
end nCSA2_5F2
namespace nCSA3_5F2
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  unfold asserts eval
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, decide_eq_true_eq]
  bv_decide
end nCSA3_5F2
namespace nCSA5_5F3
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  unfold asserts eval
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq]
  bv_decide
end nCSA5_5F3
namespace nC22
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  unfold asserts eval
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, decide_eq_true_eq]
  bv_decide
end nC22
namespace nC32
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  unfold asserts eval
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, decide_eq_true_eq]
  bv_decide
end nC32
namespace nC53
theorem assertions_hold (s : State) (i : Inputs) : asserts s i := by
  unfold asserts eval
  simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq]
  bv_decide
end nC53

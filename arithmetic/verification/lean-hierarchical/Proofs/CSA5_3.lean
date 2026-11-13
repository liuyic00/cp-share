import Generated.CSA5_3

namespace HierarchicalCSA53
open DesignnCSA5_5F3

namespace nCSA3_5F2Proof
open DesignnCSA5_5F3.nCSA3_5F2
theorem local_checks (s : State) (i : Inputs) : localAsserts s i := by
  simp only [localAsserts, List.all_cons, List.all_nil, Bool.and_true,
    id_eq, Bool.and_eq_true, decide_eq_true_eq]
  dsimp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82]
  bv_decide

theorem balance (s : State) (i : Inputs) :
    ((0#8 ++ i.nio_5Fin_5F0) : BitVec 16) + (0#8 ++ i.nio_5Fin_5F1) + (0#8 ++ i.nio_5Fin_5F2) =
    (0#8 ++ (eval s i).output.nio_5Fout_5F0) + ((0#8 ++ (eval s i).output.nio_5Fout_5F1) <<< 1) := by
  simp only [eval_eq_spec]
  dsimp [evalSpec, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82]
  bv_decide

theorem assertions (s : State) (i : Inputs) : asserts s i := by
  exact asserts_of_parts s i (local_checks s i)
end nCSA3_5F2Proof

namespace nCSA5_5F3Proof
open DesignnCSA5_5F3.nCSA5_5F3
theorem local_checks (s : State) (i : Inputs) : localAsserts s i := by
  have first := nCSA3_5F2Proof.balance s.inst_nCSA3_5F2 (inst_nCSA3_5F2Inputs s i)
  have second := nCSA3_5F2Proof.balance s.inst_nCSA3_5F2_5F1 (inst_nCSA3_5F2_5F1Inputs s i)
  change ((0#8 ++ i.nio_5Fin_5F0) : BitVec 16) + (0#8 ++ i.nio_5Fin_5F1) + (0#8 ++ i.nio_5Fin_5F2) =
    (0#8 ++ (inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F0) +
    ((0#8 ++ (inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F1) <<< 1) at first
  change ((0#8 ++ (inst_nCSA3_5F2Eval s i).output.nio_5Fout_5F0) : BitVec 16) +
    (0#8 ++ i.nio_5Fin_5F3) + (0#8 ++ i.nio_5Fin_5F4) =
    (0#8 ++ (inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F0) +
    ((0#8 ++ (inst_nCSA3_5F2_5F1Eval s i).output.nio_5Fout_5F1) <<< 1) at second
  simp only [localAsserts, List.all_cons, List.all_nil, Bool.and_true,
    id_eq, Bool.and_eq_true, decide_eq_true_eq]
  dsimp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19]
  bv_decide

theorem assertions (s : State) (i : Inputs) : asserts s i := by
  apply asserts_of_parts s i (local_checks s i)
  · exact nCSA3_5F2Proof.assertions s.inst_nCSA3_5F2 (inst_nCSA3_5F2Inputs s i)
  · exact nCSA3_5F2Proof.assertions s.inst_nCSA3_5F2_5F1 (inst_nCSA3_5F2_5F1Inputs s i)
end nCSA5_5F3Proof

end HierarchicalCSA53

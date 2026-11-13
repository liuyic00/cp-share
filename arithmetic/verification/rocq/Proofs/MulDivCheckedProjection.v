From Coq Require Import ZArith.
From Generated Require Import MulDiv MulDivChecked.
Module MulDivCheckedProjection.
Module Core := MulDiv.nMulDiv.
Module Checked := MulDivChecked.nMulDivChecked.
Definition inputs (x : Checked.Inputs) : Core.Inputs :=
  Core.mkInputs (Checked.nreset x) (Checked.nio_5Freq_5Fvalid x) (Checked.nio_5Freq_5Fbits_5Ffn x) (Checked.nio_5Freq_5Fbits_5Fdw x) (Checked.nio_5Freq_5Fbits_5Fin1 x) (Checked.nio_5Freq_5Fbits_5Fin2 x) (Checked.nio_5Freq_5Fbits_5Ftag x) (Checked.nio_5Fkill x) (Checked.nio_5Fresp_5Fready x).
Definition state (x : Checked.State) : Core.State :=
  Core.mkState (Checked.r0_nstate x) (Checked.r1_nreq_5Fdw x) (Checked.r2_nreq_5Ftag x) (Checked.r3_ncount x) (Checked.r4_nneg_5Fout x) (Checked.r5_nisHi x) (Checked.r6_nresHi x) (Checked.r7_ndivisor x) (Checked.r8_nremainder x).
Definition outputs (x : Checked.Outputs) : Core.Outputs :=
  Core.mkOutputs (Checked.nio_5Freq_5Fready x) (Checked.nio_5Fresp_5Fvalid x) (Checked.nio_5Fresp_5Fbits_5Fdata x) (Checked.nio_5Fresp_5Fbits_5Ftag x).
Lemma repeat_bridge n w x : MulDivChecked.CIRCTBits.repeatWord n w x=MulDiv.CIRCTBits.repeatWord n w x.
Proof. induction n; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.
Lemma word_function_bridge : MulDivChecked.CIRCTBits.word=MulDiv.CIRCTBits.word.
Proof. reflexivity. Qed.
Lemma repeat_function_bridge : MulDivChecked.CIRCTBits.repeatWord=MulDiv.CIRCTBits.repeatWord.
Proof. reflexivity. Qed.
Local Opaque MulDivChecked.CIRCTBits.word MulDiv.CIRCTBits.word MulDivChecked.CIRCTBits.repeatWord MulDiv.CIRCTBits.repeatWord.
Lemma node_v0 s i : Checked.v0 s i=Core.v0 (state s) (inputs i).
Proof. unfold Checked.v0, Core.v0.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v0.
Local Opaque Checked.v0.
Lemma node_v1 s i : Checked.v1 s i=Core.v1 (state s) (inputs i).
Proof. unfold Checked.v1, Core.v1.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v0.
  reflexivity. Qed.
Local Opaque Core.v1.
Local Opaque Checked.v1.
Lemma node_v2 s i : Checked.v2 s i=Core.v2 (state s) (inputs i).
Proof. unfold Checked.v2, Core.v2.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v1.
  reflexivity. Qed.
Local Opaque Core.v2.
Local Opaque Checked.v2.
Lemma node_v3 s i : Checked.v3 s i=Core.v3 (state s) (inputs i).
Proof. unfold Checked.v3, Core.v3.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v3.
Local Opaque Checked.v3.
Lemma node_v4 s i : Checked.v4 s i=Core.v4 (state s) (inputs i).
Proof. unfold Checked.v4, Core.v4.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v4.
Local Opaque Checked.v4.
Lemma node_v5 s i : Checked.v5 s i=Core.v5 (state s) (inputs i).
Proof. unfold Checked.v5, Core.v5.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v3.
  try rewrite node_v4.
  reflexivity. Qed.
Local Opaque Core.v5.
Local Opaque Checked.v5.
Lemma node_v6 s i : Checked.v6 s i=Core.v6 (state s) (inputs i).
Proof. unfold Checked.v6, Core.v6.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v5.
  reflexivity. Qed.
Local Opaque Core.v6.
Local Opaque Checked.v6.
Lemma node_v7 s i : Checked.v7 s i=Core.v7 (state s) (inputs i).
Proof. unfold Checked.v7, Core.v7.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v7.
Local Opaque Checked.v7.
Lemma node_v8 s i : Checked.v8 s i=Core.v8 (state s) (inputs i).
Proof. unfold Checked.v8, Core.v8.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v8.
Local Opaque Checked.v8.
Lemma node_v9 s i : Checked.v9 s i=Core.v9 (state s) (inputs i).
Proof. unfold Checked.v9, Core.v9.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v5.
  reflexivity. Qed.
Local Opaque Core.v9.
Local Opaque Checked.v9.
Lemma node_v10 s i : Checked.v10 s i=Core.v10 (state s) (inputs i).
Proof. unfold Checked.v10, Core.v10.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v5.
  reflexivity. Qed.
Local Opaque Core.v10.
Local Opaque Checked.v10.
Lemma node_v11 s i : Checked.v11 s i=Core.v11 (state s) (inputs i).
Proof. unfold Checked.v11, Core.v11.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v10.
  try rewrite node_v6.
  reflexivity. Qed.
Local Opaque Core.v11.
Local Opaque Checked.v11.
Lemma node_v12 s i : Checked.v12 s i=Core.v12 (state s) (inputs i).
Proof. unfold Checked.v12, Core.v12.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v12.
Local Opaque Checked.v12.
Lemma node_v13 s i : Checked.v13 s i=Core.v13 (state s) (inputs i).
Proof. unfold Checked.v13, Core.v13.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v11.
  try rewrite node_v12.
  reflexivity. Qed.
Local Opaque Core.v13.
Local Opaque Checked.v13.
Lemma node_v14 s i : Checked.v14 s i=Core.v14 (state s) (inputs i).
Proof. unfold Checked.v14, Core.v14.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v9.
  try rewrite node_v13.
  reflexivity. Qed.
Local Opaque Core.v14.
Local Opaque Checked.v14.
Lemma node_v15 s i : Checked.v15 s i=Core.v15 (state s) (inputs i).
Proof. unfold Checked.v15, Core.v15.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v15.
Local Opaque Checked.v15.
Lemma node_v16 s i : Checked.v16 s i=Core.v16 (state s) (inputs i).
Proof. unfold Checked.v16, Core.v16.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v14.
  try rewrite node_v15.
  reflexivity. Qed.
Local Opaque Core.v16.
Local Opaque Checked.v16.
Lemma node_v17 s i : Checked.v17 s i=Core.v17 (state s) (inputs i).
Proof. unfold Checked.v17, Core.v17.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v17.
Local Opaque Checked.v17.
Lemma node_v18 s i : Checked.v18 s i=Core.v18 (state s) (inputs i).
Proof. unfold Checked.v18, Core.v18.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v18.
Local Opaque Checked.v18.
Lemma node_v19 s i : Checked.v19 s i=Core.v19 (state s) (inputs i).
Proof. unfold Checked.v19, Core.v19.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v17.
  try rewrite node_v18.
  reflexivity. Qed.
Local Opaque Core.v19.
Local Opaque Checked.v19.
Lemma node_v20 s i : Checked.v20 s i=Core.v20 (state s) (inputs i).
Proof. unfold Checked.v20, Core.v20.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v16.
  try rewrite node_v19.
  reflexivity. Qed.
Local Opaque Core.v20.
Local Opaque Checked.v20.
Lemma node_v21 s i : Checked.v21 s i=Core.v21 (state s) (inputs i).
Proof. unfold Checked.v21, Core.v21.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v21.
Local Opaque Checked.v21.
Lemma node_v22 s i : Checked.v22 s i=Core.v22 (state s) (inputs i).
Proof. unfold Checked.v22, Core.v22.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v9.
  try rewrite node_v21.
  reflexivity. Qed.
Local Opaque Core.v22.
Local Opaque Checked.v22.
Lemma node_v23 s i : Checked.v23 s i=Core.v23 (state s) (inputs i).
Proof. unfold Checked.v23, Core.v23.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v22.
  try rewrite node_v12.
  reflexivity. Qed.
Local Opaque Core.v23.
Local Opaque Checked.v23.
Lemma node_v24 s i : Checked.v24 s i=Core.v24 (state s) (inputs i).
Proof. unfold Checked.v24, Core.v24.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v13.
  try rewrite node_v23.
  reflexivity. Qed.
Local Opaque Core.v24.
Local Opaque Checked.v24.
Lemma node_v25 s i : Checked.v25 s i=Core.v25 (state s) (inputs i).
Proof. unfold Checked.v25, Core.v25.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v24.
  try rewrite node_v15.
  reflexivity. Qed.
Local Opaque Core.v25.
Local Opaque Checked.v25.
Lemma node_v26 s i : Checked.v26 s i=Core.v26 (state s) (inputs i).
Proof. unfold Checked.v26, Core.v26.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v26.
Local Opaque Checked.v26.
Lemma node_v27 s i : Checked.v27 s i=Core.v27 (state s) (inputs i).
Proof. unfold Checked.v27, Core.v27.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v27.
Local Opaque Checked.v27.
Lemma node_v28 s i : Checked.v28 s i=Core.v28 (state s) (inputs i).
Proof. unfold Checked.v28, Core.v28.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v26.
  try rewrite node_v27.
  reflexivity. Qed.
Local Opaque Core.v28.
Local Opaque Checked.v28.
Lemma node_v29 s i : Checked.v29 s i=Core.v29 (state s) (inputs i).
Proof. unfold Checked.v29, Core.v29.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v25.
  try rewrite node_v28.
  reflexivity. Qed.
Local Opaque Core.v29.
Local Opaque Checked.v29.
Lemma node_v30 s i : Checked.v30 s i=Core.v30 (state s) (inputs i).
Proof. unfold Checked.v30, Core.v30.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v20.
  try rewrite node_v29.
  reflexivity. Qed.
Local Opaque Core.v30.
Local Opaque Checked.v30.
Lemma node_v31 s i : Checked.v31 s i=Core.v31 (state s) (inputs i).
Proof. unfold Checked.v31, Core.v31.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v31.
Local Opaque Checked.v31.
Lemma node_v32 s i : Checked.v32 s i=Core.v32 (state s) (inputs i).
Proof. unfold Checked.v32, Core.v32.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v30.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v32.
Local Opaque Checked.v32.
Lemma node_v33 s i : Checked.v33 s i=Core.v33 (state s) (inputs i).
Proof. unfold Checked.v33, Core.v33.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v8.
  try rewrite node_v32.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v33.
Local Opaque Checked.v33.
Lemma node_v34 s i : Checked.v34 s i=Core.v34 (state s) (inputs i).
Proof. unfold Checked.v34, Core.v34.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v6.
  try rewrite node_v7.
  try rewrite node_v33.
  reflexivity. Qed.
Local Opaque Core.v34.
Local Opaque Checked.v34.
Lemma node_v35 s i : Checked.v35 s i=Core.v35 (state s) (inputs i).
Proof. unfold Checked.v35, Core.v35.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v35.
Local Opaque Checked.v35.
Lemma node_v36 s i : Checked.v36 s i=Core.v36 (state s) (inputs i).
Proof. unfold Checked.v36, Core.v36.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v35.
  reflexivity. Qed.
Local Opaque Core.v36.
Local Opaque Checked.v36.
Lemma node_v37 s i : Checked.v37 s i=Core.v37 (state s) (inputs i).
Proof. unfold Checked.v37, Core.v37.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v4.
  reflexivity. Qed.
Local Opaque Core.v37.
Local Opaque Checked.v37.
Lemma node_v38 s i : Checked.v38 s i=Core.v38 (state s) (inputs i).
Proof. unfold Checked.v38, Core.v38.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v36.
  try rewrite node_v37.
  reflexivity. Qed.
Local Opaque Core.v38.
Local Opaque Checked.v38.
Lemma node_v39 s i : Checked.v39 s i=Core.v39 (state s) (inputs i).
Proof. unfold Checked.v39, Core.v39.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v38.
  reflexivity. Qed.
Local Opaque Core.v39.
Local Opaque Checked.v39.
Lemma node_v40 s i : Checked.v40 s i=Core.v40 (state s) (inputs i).
Proof. unfold Checked.v40, Core.v40.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v39.
  reflexivity. Qed.
Local Opaque Core.v40.
Local Opaque Checked.v40.
Lemma node_v41 s i : Checked.v41 s i=Core.v41 (state s) (inputs i).
Proof. unfold Checked.v41, Core.v41.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v41.
Local Opaque Checked.v41.
Lemma node_v42 s i : Checked.v42 s i=Core.v42 (state s) (inputs i).
Proof. unfold Checked.v42, Core.v42.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v41.
  reflexivity. Qed.
Local Opaque Core.v42.
Local Opaque Checked.v42.
Lemma node_v43 s i : Checked.v43 s i=Core.v43 (state s) (inputs i).
Proof. unfold Checked.v43, Core.v43.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v43.
Local Opaque Checked.v43.
Lemma node_v44 s i : Checked.v44 s i=Core.v44 (state s) (inputs i).
Proof. unfold Checked.v44, Core.v44.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v43.
  reflexivity. Qed.
Local Opaque Core.v44.
Local Opaque Checked.v44.
Lemma node_v45 s i : Checked.v45 s i=Core.v45 (state s) (inputs i).
Proof. unfold Checked.v45, Core.v45.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v42.
  try rewrite node_v44.
  reflexivity. Qed.
Local Opaque Core.v45.
Local Opaque Checked.v45.
Lemma node_v46 s i : Checked.v46 s i=Core.v46 (state s) (inputs i).
Proof. unfold Checked.v46, Core.v46.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v46.
Local Opaque Checked.v46.
Lemma node_v47 s i : Checked.v47 s i=Core.v47 (state s) (inputs i).
Proof. unfold Checked.v47, Core.v47.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v31.
  try rewrite node_v46.
  reflexivity. Qed.
Local Opaque Core.v47.
Local Opaque Checked.v47.
Lemma node_v48 s i : Checked.v48 s i=Core.v48 (state s) (inputs i).
Proof. unfold Checked.v48, Core.v48.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v7.
  reflexivity. Qed.
Local Opaque Core.v48.
Local Opaque Checked.v48.
Lemma node_v49 s i : Checked.v49 s i=Core.v49 (state s) (inputs i).
Proof. unfold Checked.v49, Core.v49.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v49.
Local Opaque Checked.v49.
Lemma node_v50 s i : Checked.v50 s i=Core.v50 (state s) (inputs i).
Proof. unfold Checked.v50, Core.v50.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v49.
  reflexivity. Qed.
Local Opaque Core.v50.
Local Opaque Checked.v50.
Lemma node_v51 s i : Checked.v51 s i=Core.v51 (state s) (inputs i).
Proof. unfold Checked.v51, Core.v51.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v48.
  try rewrite node_v50.
  reflexivity. Qed.
Local Opaque Core.v51.
Local Opaque Checked.v51.
Lemma node_v52 s i : Checked.v52 s i=Core.v52 (state s) (inputs i).
Proof. unfold Checked.v52, Core.v52.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v52.
Local Opaque Checked.v52.
Lemma node_v53 s i : Checked.v53 s i=Core.v53 (state s) (inputs i).
Proof. unfold Checked.v53, Core.v53.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v52.
  reflexivity. Qed.
Local Opaque Core.v53.
Local Opaque Checked.v53.
Lemma node_v54 s i : Checked.v54 s i=Core.v54 (state s) (inputs i).
Proof. unfold Checked.v54, Core.v54.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v54.
Local Opaque Checked.v54.
Lemma node_v55 s i : Checked.v55 s i=Core.v55 (state s) (inputs i).
Proof. unfold Checked.v55, Core.v55.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v54.
  reflexivity. Qed.
Local Opaque Core.v55.
Local Opaque Checked.v55.
Lemma node_v56 s i : Checked.v56 s i=Core.v56 (state s) (inputs i).
Proof. unfold Checked.v56, Core.v56.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v55.
  try rewrite node_v41.
  reflexivity. Qed.
Local Opaque Core.v56.
Local Opaque Checked.v56.
Lemma node_v57 s i : Checked.v57 s i=Core.v57 (state s) (inputs i).
Proof. unfold Checked.v57, Core.v57.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v53.
  try rewrite node_v4.
  try rewrite node_v56.
  reflexivity. Qed.
Local Opaque Core.v57.
Local Opaque Checked.v57.
Lemma node_v58 s i : Checked.v58 s i=Core.v58 (state s) (inputs i).
Proof. unfold Checked.v58, Core.v58.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v51.
  try rewrite node_v35.
  try rewrite node_v57.
  reflexivity. Qed.
Local Opaque Core.v58.
Local Opaque Checked.v58.
Lemma node_v59 s i : Checked.v59 s i=Core.v59 (state s) (inputs i).
Proof. unfold Checked.v59, Core.v59.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v45.
  try rewrite node_v47.
  try rewrite node_v58.
  reflexivity. Qed.
Local Opaque Core.v59.
Local Opaque Checked.v59.
Lemma node_v60 s i : Checked.v60 s i=Core.v60 (state s) (inputs i).
Proof. unfold Checked.v60, Core.v60.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v40.
  try rewrite node_v0.
  try rewrite node_v59.
  reflexivity. Qed.
Local Opaque Core.v60.
Local Opaque Checked.v60.
Lemma node_v61 s i : Checked.v61 s i=Core.v61 (state s) (inputs i).
Proof. unfold Checked.v61, Core.v61.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  try rewrite node_v34.
  try rewrite node_v60.
  reflexivity. Qed.
Local Opaque Core.v61.
Local Opaque Checked.v61.
Lemma node_v62 s i : Checked.v62 s i=Core.v62 (state s) (inputs i).
Proof. unfold Checked.v62, Core.v62.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  reflexivity. Qed.
Local Opaque Core.v62.
Local Opaque Checked.v62.
Lemma node_v63 s i : Checked.v63 s i=Core.v63 (state s) (inputs i).
Proof. unfold Checked.v63, Core.v63.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  reflexivity. Qed.
Local Opaque Core.v63.
Local Opaque Checked.v63.
Lemma node_v64 s i : Checked.v64 s i=Core.v64 (state s) (inputs i).
Proof. unfold Checked.v64, Core.v64.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v64.
Local Opaque Checked.v64.
Lemma node_v65 s i : Checked.v65 s i=Core.v65 (state s) (inputs i).
Proof. unfold Checked.v65, Core.v65.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v6.
  try rewrite node_v64.
  reflexivity. Qed.
Local Opaque Core.v65.
Local Opaque Checked.v65.
Lemma node_v66 s i : Checked.v66 s i=Core.v66 (state s) (inputs i).
Proof. unfold Checked.v66, Core.v66.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v66.
Local Opaque Checked.v66.
Lemma node_v67 s i : Checked.v67 s i=Core.v67 (state s) (inputs i).
Proof. unfold Checked.v67, Core.v67.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v8.
  try rewrite node_v65.
  try rewrite node_v66.
  reflexivity. Qed.
Local Opaque Core.v67.
Local Opaque Checked.v67.
Lemma node_v68 s i : Checked.v68 s i=Core.v68 (state s) (inputs i).
Proof. unfold Checked.v68, Core.v68.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v68.
Local Opaque Checked.v68.
Lemma node_v69 s i : Checked.v69 s i=Core.v69 (state s) (inputs i).
Proof. unfold Checked.v69, Core.v69.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v68.
  reflexivity. Qed.
Local Opaque Core.v69.
Local Opaque Checked.v69.
Lemma node_v70 s i : Checked.v70 s i=Core.v70 (state s) (inputs i).
Proof. unfold Checked.v70, Core.v70.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v68.
  reflexivity. Qed.
Local Opaque Core.v70.
Local Opaque Checked.v70.
Lemma node_v71 s i : Checked.v71 s i=Core.v71 (state s) (inputs i).
Proof. unfold Checked.v71, Core.v71.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v48.
  try rewrite node_v70.
  reflexivity. Qed.
Local Opaque Core.v71.
Local Opaque Checked.v71.
Lemma node_v72 s i : Checked.v72 s i=Core.v72 (state s) (inputs i).
Proof. unfold Checked.v72, Core.v72.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v42.
  try rewrite node_v69.
  try rewrite node_v71.
  reflexivity. Qed.
Local Opaque Core.v72.
Local Opaque Checked.v72.
Lemma node_v73 s i : Checked.v73 s i=Core.v73 (state s) (inputs i).
Proof. unfold Checked.v73, Core.v73.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  try rewrite node_v67.
  try rewrite node_v72.
  reflexivity. Qed.
Local Opaque Core.v73.
Local Opaque Checked.v73.
Lemma node_v74 s i : Checked.v74 s i=Core.v74 (state s) (inputs i).
Proof. unfold Checked.v74, Core.v74.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v74.
Local Opaque Checked.v74.
Lemma node_v75 s i : Checked.v75 s i=Core.v75 (state s) (inputs i).
Proof. unfold Checked.v75, Core.v75.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v74.
  try rewrite node_v6.
  reflexivity. Qed.
Local Opaque Core.v75.
Local Opaque Checked.v75.
Lemma node_v76 s i : Checked.v76 s i=Core.v76 (state s) (inputs i).
Proof. unfold Checked.v76, Core.v76.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v75.
  try rewrite node_v12.
  reflexivity. Qed.
Local Opaque Core.v76.
Local Opaque Checked.v76.
Lemma node_v77 s i : Checked.v77 s i=Core.v77 (state s) (inputs i).
Proof. unfold Checked.v77, Core.v77.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v77.
Local Opaque Checked.v77.
Lemma node_v78 s i : Checked.v78 s i=Core.v78 (state s) (inputs i).
Proof. unfold Checked.v78, Core.v78.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v76.
  try rewrite node_v77.
  reflexivity. Qed.
Local Opaque Core.v78.
Local Opaque Checked.v78.
Lemma node_v79 s i : Checked.v79 s i=Core.v79 (state s) (inputs i).
Proof. unfold Checked.v79, Core.v79.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v78.
  try rewrite node_v15.
  reflexivity. Qed.
Local Opaque Core.v79.
Local Opaque Checked.v79.
Lemma node_v80 s i : Checked.v80 s i=Core.v80 (state s) (inputs i).
Proof. unfold Checked.v80, Core.v80.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v20.
  try rewrite node_v29.
  reflexivity. Qed.
Local Opaque Core.v80.
Local Opaque Checked.v80.
Lemma node_v81 s i : Checked.v81 s i=Core.v81 (state s) (inputs i).
Proof. unfold Checked.v81, Core.v81.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v79.
  try rewrite node_v20.
  try rewrite node_v80.
  reflexivity. Qed.
Local Opaque Core.v81.
Local Opaque Checked.v81.
Lemma node_v82 s i : Checked.v82 s i=Core.v82 (state s) (inputs i).
Proof. unfold Checked.v82, Core.v82.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v82.
Local Opaque Checked.v82.
Lemma node_v83 s i : Checked.v83 s i=Core.v83 (state s) (inputs i).
Proof. unfold Checked.v83, Core.v83.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v82.
  reflexivity. Qed.
Local Opaque Core.v83.
Local Opaque Checked.v83.
Lemma node_v84 s i : Checked.v84 s i=Core.v84 (state s) (inputs i).
Proof. unfold Checked.v84, Core.v84.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v84.
Local Opaque Checked.v84.
Lemma node_v85 s i : Checked.v85 s i=Core.v85 (state s) (inputs i).
Proof. unfold Checked.v85, Core.v85.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v84.
  reflexivity. Qed.
Local Opaque Core.v85.
Local Opaque Checked.v85.
Lemma node_v86 s i : Checked.v86 s i=Core.v86 (state s) (inputs i).
Proof. unfold Checked.v86, Core.v86.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v85.
  reflexivity. Qed.
Local Opaque Core.v86.
Local Opaque Checked.v86.
Lemma node_v87 s i : Checked.v87 s i=Core.v87 (state s) (inputs i).
Proof. unfold Checked.v87, Core.v87.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v86.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v87.
Local Opaque Checked.v87.
Lemma node_v88 s i : Checked.v88 s i=Core.v88 (state s) (inputs i).
Proof. unfold Checked.v88, Core.v88.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v88.
Local Opaque Checked.v88.
Lemma node_v89 s i : Checked.v89 s i=Core.v89 (state s) (inputs i).
Proof. unfold Checked.v89, Core.v89.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v42.
  try rewrite node_v83.
  try rewrite node_v87.
  try rewrite node_v88.
  reflexivity. Qed.
Local Opaque Core.v89.
Local Opaque Checked.v89.
Lemma node_v90 s i : Checked.v90 s i=Core.v90 (state s) (inputs i).
Proof. unfold Checked.v90, Core.v90.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v89.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v90.
Local Opaque Checked.v90.
Lemma node_v91 s i : Checked.v91 s i=Core.v91 (state s) (inputs i).
Proof. unfold Checked.v91, Core.v91.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v90.
  reflexivity. Qed.
Local Opaque Core.v91.
Local Opaque Checked.v91.
Lemma node_v92 s i : Checked.v92 s i=Core.v92 (state s) (inputs i).
Proof. unfold Checked.v92, Core.v92.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  try rewrite node_v81.
  try rewrite node_v91.
  reflexivity. Qed.
Local Opaque Core.v92.
Local Opaque Checked.v92.
Lemma node_v93 s i : Checked.v93 s i=Core.v93 (state s) (inputs i).
Proof. unfold Checked.v93, Core.v93.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  try rewrite node_v79.
  reflexivity. Qed.
Local Opaque Core.v93.
Local Opaque Checked.v93.
Lemma node_v94 s i : Checked.v94 s i=Core.v94 (state s) (inputs i).
Proof. unfold Checked.v94, Core.v94.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v94.
Local Opaque Checked.v94.
Lemma node_v95 s i : Checked.v95 s i=Core.v95 (state s) (inputs i).
Proof. unfold Checked.v95, Core.v95.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v42.
  try rewrite node_v44.
  reflexivity. Qed.
Local Opaque Core.v95.
Local Opaque Checked.v95.
Lemma node_v96 s i : Checked.v96 s i=Core.v96 (state s) (inputs i).
Proof. unfold Checked.v96, Core.v96.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v95.
  try rewrite node_v51.
  reflexivity. Qed.
Local Opaque Core.v96.
Local Opaque Checked.v96.
Lemma node_v97 s i : Checked.v97 s i=Core.v97 (state s) (inputs i).
Proof. unfold Checked.v97, Core.v97.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v53.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v97.
Local Opaque Checked.v97.
Lemma node_v98 s i : Checked.v98 s i=Core.v98 (state s) (inputs i).
Proof. unfold Checked.v98, Core.v98.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v97.
  reflexivity. Qed.
Local Opaque Core.v98.
Local Opaque Checked.v98.
Lemma node_v99 s i : Checked.v99 s i=Core.v99 (state s) (inputs i).
Proof. unfold Checked.v99, Core.v99.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v96.
  try rewrite node_v98.
  reflexivity. Qed.
Local Opaque Core.v99.
Local Opaque Checked.v99.
Lemma node_v100 s i : Checked.v100 s i=Core.v100 (state s) (inputs i).
Proof. unfold Checked.v100, Core.v100.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v94.
  try rewrite node_v99.
  reflexivity. Qed.
Local Opaque Core.v100.
Local Opaque Checked.v100.
Lemma node_v101 s i : Checked.v101 s i=Core.v101 (state s) (inputs i).
Proof. unfold Checked.v101, Core.v101.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v101.
Local Opaque Checked.v101.
Lemma node_v102 s i : Checked.v102 s i=Core.v102 (state s) (inputs i).
Proof. unfold Checked.v102, Core.v102.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v29.
  reflexivity. Qed.
Local Opaque Core.v102.
Local Opaque Checked.v102.
Lemma node_v103 s i : Checked.v103 s i=Core.v103 (state s) (inputs i).
Proof. unfold Checked.v103, Core.v103.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v101.
  try rewrite node_v102.
  reflexivity. Qed.
Local Opaque Core.v103.
Local Opaque Checked.v103.
Lemma node_v104 s i : Checked.v104 s i=Core.v104 (state s) (inputs i).
Proof. unfold Checked.v104, Core.v104.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v104.
Local Opaque Checked.v104.
Lemma node_v105 s i : Checked.v105 s i=Core.v105 (state s) (inputs i).
Proof. unfold Checked.v105, Core.v105.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v29.
  try rewrite node_v103.
  try rewrite node_v104.
  reflexivity. Qed.
Local Opaque Core.v105.
Local Opaque Checked.v105.
Lemma node_v106 s i : Checked.v106 s i=Core.v106 (state s) (inputs i).
Proof. unfold Checked.v106, Core.v106.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v106.
Local Opaque Checked.v106.
Lemma node_v107 s i : Checked.v107 s i=Core.v107 (state s) (inputs i).
Proof. unfold Checked.v107, Core.v107.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v55.
  try rewrite node_v106.
  reflexivity. Qed.
Local Opaque Core.v107.
Local Opaque Checked.v107.
Lemma node_v108 s i : Checked.v108 s i=Core.v108 (state s) (inputs i).
Proof. unfold Checked.v108, Core.v108.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v107.
  try rewrite node_v85.
  reflexivity. Qed.
Local Opaque Core.v108.
Local Opaque Checked.v108.
Lemma node_v109 s i : Checked.v109 s i=Core.v109 (state s) (inputs i).
Proof. unfold Checked.v109, Core.v109.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  try rewrite node_v105.
  try rewrite node_v108.
  reflexivity. Qed.
Local Opaque Core.v109.
Local Opaque Checked.v109.
Lemma node_v110 s i : Checked.v110 s i=Core.v110 (state s) (inputs i).
Proof. unfold Checked.v110, Core.v110.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v110.
Local Opaque Checked.v110.
Lemma node_v111 s i : Checked.v111 s i=Core.v111 (state s) (inputs i).
Proof. unfold Checked.v111, Core.v111.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v111.
Local Opaque Checked.v111.
Lemma node_v112 s i : Checked.v112 s i=Core.v112 (state s) (inputs i).
Proof. unfold Checked.v112, Core.v112.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v20.
  reflexivity. Qed.
Local Opaque Core.v112.
Local Opaque Checked.v112.
Lemma node_v113 s i : Checked.v113 s i=Core.v113 (state s) (inputs i).
Proof. unfold Checked.v113, Core.v113.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v111.
  try rewrite node_v112.
  reflexivity. Qed.
Local Opaque Core.v113.
Local Opaque Checked.v113.
Lemma node_v114 s i : Checked.v114 s i=Core.v114 (state s) (inputs i).
Proof. unfold Checked.v114, Core.v114.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v114.
Local Opaque Checked.v114.
Lemma node_v115 s i : Checked.v115 s i=Core.v115 (state s) (inputs i).
Proof. unfold Checked.v115, Core.v115.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v110.
  try rewrite node_v113.
  try rewrite node_v114.
  reflexivity. Qed.
Local Opaque Core.v115.
Local Opaque Checked.v115.
Lemma node_v116 s i : Checked.v116 s i=Core.v116 (state s) (inputs i).
Proof. unfold Checked.v116, Core.v116.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v116.
Local Opaque Checked.v116.
Lemma node_v117 s i : Checked.v117 s i=Core.v117 (state s) (inputs i).
Proof. unfold Checked.v117, Core.v117.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v85.
  reflexivity. Qed.
Local Opaque Core.v117.
Local Opaque Checked.v117.
Lemma node_v118 s i : Checked.v118 s i=Core.v118 (state s) (inputs i).
Proof. unfold Checked.v118, Core.v118.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v86.
  try rewrite node_v116.
  try rewrite node_v117.
  reflexivity. Qed.
Local Opaque Core.v118.
Local Opaque Checked.v118.
Lemma node_v119 s i : Checked.v119 s i=Core.v119 (state s) (inputs i).
Proof. unfold Checked.v119, Core.v119.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v119.
Local Opaque Checked.v119.
Lemma node_v120 s i : Checked.v120 s i=Core.v120 (state s) (inputs i).
Proof. unfold Checked.v120, Core.v120.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v86.
  try rewrite node_v31.
  reflexivity. Qed.
Local Opaque Core.v120.
Local Opaque Checked.v120.
Lemma node_v121 s i : Checked.v121 s i=Core.v121 (state s) (inputs i).
Proof. unfold Checked.v121, Core.v121.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v8.
  try rewrite node_v118.
  try rewrite node_v119.
  try rewrite node_v120.
  reflexivity. Qed.
Local Opaque Core.v121.
Local Opaque Checked.v121.
Lemma node_v122 s i : Checked.v122 s i=Core.v122 (state s) (inputs i).
Proof. unfold Checked.v122, Core.v122.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v122.
Local Opaque Checked.v122.
Lemma node_v123 s i : Checked.v123 s i=Core.v123 (state s) (inputs i).
Proof. unfold Checked.v123, Core.v123.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v122.
  reflexivity. Qed.
Local Opaque Core.v123.
Local Opaque Checked.v123.
Lemma node_v124 s i : Checked.v124 s i=Core.v124 (state s) (inputs i).
Proof. unfold Checked.v124, Core.v124.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v124.
Local Opaque Checked.v124.
Lemma node_v125 s i : Checked.v125 s i=Core.v125 (state s) (inputs i).
Proof. unfold Checked.v125, Core.v125.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v123.
  try rewrite node_v124.
  reflexivity. Qed.
Local Opaque Core.v125.
Local Opaque Checked.v125.
Lemma node_v126 s i : Checked.v126 s i=Core.v126 (state s) (inputs i).
Proof. unfold Checked.v126, Core.v126.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v126.
Local Opaque Checked.v126.
Lemma node_v127 s i : Checked.v127 s i=Core.v127 (state s) (inputs i).
Proof. unfold Checked.v127, Core.v127.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v126.
  reflexivity. Qed.
Local Opaque Core.v127.
Local Opaque Checked.v127.
Lemma node_v128 s i : Checked.v128 s i=Core.v128 (state s) (inputs i).
Proof. unfold Checked.v128, Core.v128.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v125.
  try rewrite node_v127.
  reflexivity. Qed.
Local Opaque Core.v128.
Local Opaque Checked.v128.
Lemma node_v129 s i : Checked.v129 s i=Core.v129 (state s) (inputs i).
Proof. unfold Checked.v129, Core.v129.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v129.
Local Opaque Checked.v129.
Lemma node_v130 s i : Checked.v130 s i=Core.v130 (state s) (inputs i).
Proof. unfold Checked.v130, Core.v130.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v130.
Local Opaque Checked.v130.
Lemma node_v131 s i : Checked.v131 s i=Core.v131 (state s) (inputs i).
Proof. unfold Checked.v131, Core.v131.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v129.
  try rewrite node_v130.
  reflexivity. Qed.
Local Opaque Core.v131.
Local Opaque Checked.v131.
Lemma node_v132 s i : Checked.v132 s i=Core.v132 (state s) (inputs i).
Proof. unfold Checked.v132, Core.v132.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v128.
  try rewrite node_v131.
  reflexivity. Qed.
Local Opaque Core.v132.
Local Opaque Checked.v132.
Lemma node_v133 s i : Checked.v133 s i=Core.v133 (state s) (inputs i).
Proof. unfold Checked.v133, Core.v133.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v132.
  reflexivity. Qed.
Local Opaque Core.v133.
Local Opaque Checked.v133.
Lemma node_v134 s i : Checked.v134 s i=Core.v134 (state s) (inputs i).
Proof. unfold Checked.v134, Core.v134.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v134.
Local Opaque Checked.v134.
Lemma node_v135 s i : Checked.v135 s i=Core.v135 (state s) (inputs i).
Proof. unfold Checked.v135, Core.v135.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v134.
  reflexivity. Qed.
Local Opaque Core.v135.
Local Opaque Checked.v135.
Lemma node_v136 s i : Checked.v136 s i=Core.v136 (state s) (inputs i).
Proof. unfold Checked.v136, Core.v136.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v135.
  reflexivity. Qed.
Local Opaque Core.v136.
Local Opaque Checked.v136.
Lemma node_v137 s i : Checked.v137 s i=Core.v137 (state s) (inputs i).
Proof. unfold Checked.v137, Core.v137.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v132.
  reflexivity. Qed.
Local Opaque Core.v137.
Local Opaque Checked.v137.
Lemma node_v138 s i : Checked.v138 s i=Core.v138 (state s) (inputs i).
Proof. unfold Checked.v138, Core.v138.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v138.
Local Opaque Checked.v138.
Lemma node_v139 s i : Checked.v139 s i=Core.v139 (state s) (inputs i).
Proof. unfold Checked.v139, Core.v139.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v133.
  try rewrite node_v136.
  try rewrite node_v137.
  try rewrite node_v138.
  reflexivity. Qed.
Local Opaque Core.v139.
Local Opaque Checked.v139.
Lemma node_v140 s i : Checked.v140 s i=Core.v140 (state s) (inputs i).
Proof. unfold Checked.v140, Core.v140.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v140.
Local Opaque Checked.v140.
Lemma node_v141 s i : Checked.v141 s i=Core.v141 (state s) (inputs i).
Proof. unfold Checked.v141, Core.v141.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v55.
  try rewrite node_v140.
  reflexivity. Qed.
Local Opaque Core.v141.
Local Opaque Checked.v141.
Lemma node_v142 s i : Checked.v142 s i=Core.v142 (state s) (inputs i).
Proof. unfold Checked.v142, Core.v142.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v53.
  try rewrite node_v141.
  reflexivity. Qed.
Local Opaque Core.v142.
Local Opaque Checked.v142.
Lemma node_v143 s i : Checked.v143 s i=Core.v143 (state s) (inputs i).
Proof. unfold Checked.v143, Core.v143.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v143.
Local Opaque Checked.v143.
Lemma node_v144 s i : Checked.v144 s i=Core.v144 (state s) (inputs i).
Proof. unfold Checked.v144, Core.v144.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v144.
Local Opaque Checked.v144.
Lemma node_v145 s i : Checked.v145 s i=Core.v145 (state s) (inputs i).
Proof. unfold Checked.v145, Core.v145.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v144.
  try rewrite node_v119.
  reflexivity. Qed.
Local Opaque Core.v145.
Local Opaque Checked.v145.
Lemma node_v146 s i : Checked.v146 s i=Core.v146 (state s) (inputs i).
Proof. unfold Checked.v146, Core.v146.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v143.
  try rewrite node_v145.
  reflexivity. Qed.
Local Opaque Core.v146.
Local Opaque Checked.v146.
Lemma node_v147 s i : Checked.v147 s i=Core.v147 (state s) (inputs i).
Proof. unfold Checked.v147, Core.v147.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v110.
  try rewrite node_v146.
  reflexivity. Qed.
Local Opaque Core.v147.
Local Opaque Checked.v147.
Lemma node_v148 s i : Checked.v148 s i=Core.v148 (state s) (inputs i).
Proof. unfold Checked.v148, Core.v148.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v142.
  try rewrite node_v147.
  reflexivity. Qed.
Local Opaque Core.v148.
Local Opaque Checked.v148.
Lemma node_v149 s i : Checked.v149 s i=Core.v149 (state s) (inputs i).
Proof. unfold Checked.v149, Core.v149.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v48.
  try rewrite node_v139.
  try rewrite node_v148.
  reflexivity. Qed.
Local Opaque Core.v149.
Local Opaque Checked.v149.
Lemma node_v150 s i : Checked.v150 s i=Core.v150 (state s) (inputs i).
Proof. unfold Checked.v150, Core.v150.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v42.
  try rewrite node_v121.
  try rewrite node_v149.
  reflexivity. Qed.
Local Opaque Core.v150.
Local Opaque Checked.v150.
Lemma node_v151 s i : Checked.v151 s i=Core.v151 (state s) (inputs i).
Proof. unfold Checked.v151, Core.v151.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v2.
  try rewrite node_v115.
  try rewrite node_v150.
  reflexivity. Qed.
Local Opaque Core.v151.
Local Opaque Checked.v151.
Lemma node_v152 s i : Checked.v179 s i=Core.v152 (state s) (inputs i).
Proof. unfold Checked.v179, Core.v152.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v145.
  reflexivity. Qed.
Local Opaque Core.v152.
Local Opaque Checked.v179.
Lemma node_v153 s i : Checked.v180 s i=Core.v153 (state s) (inputs i).
Proof. unfold Checked.v180, Core.v153.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  reflexivity. Qed.
Local Opaque Core.v153.
Local Opaque Checked.v180.
Lemma node_v154 s i : Checked.v181 s i=Core.v154 (state s) (inputs i).
Proof. unfold Checked.v181, Core.v154.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v153.
  reflexivity. Qed.
Local Opaque Core.v154.
Local Opaque Checked.v181.
Lemma node_v155 s i : Checked.v182 s i=Core.v155 (state s) (inputs i).
Proof. unfold Checked.v182, Core.v155.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v145.
  reflexivity. Qed.
Local Opaque Core.v155.
Local Opaque Checked.v182.
Lemma node_v156 s i : Checked.v183 s i=Core.v156 (state s) (inputs i).
Proof. unfold Checked.v183, Core.v156.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v154.
  try rewrite node_v155.
  try rewrite node_v152.
  reflexivity. Qed.
Local Opaque Core.v156.
Local Opaque Checked.v183.
Lemma node_v157 s i : Checked.v184 s i=Core.v157 (state s) (inputs i).
Proof. unfold Checked.v184, Core.v157.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v156.
  reflexivity. Qed.
Local Opaque Core.v157.
Local Opaque Checked.v184.
Lemma node_v158 s i : Checked.v185 s i=Core.v158 (state s) (inputs i).
Proof. unfold Checked.v185, Core.v158.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v157.
  reflexivity. Qed.
Local Opaque Core.v158.
Local Opaque Checked.v185.
Lemma node_v159 s i : Checked.v186 s i=Core.v159 (state s) (inputs i).
Proof. unfold Checked.v186, Core.v159.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v152.
  try rewrite node_v158.
  reflexivity. Qed.
Local Opaque Core.v159.
Local Opaque Checked.v186.
Lemma node_v160 s i : Checked.v187 s i=Core.v160 (state s) (inputs i).
Proof. unfold Checked.v187, Core.v160.
  rewrite word_function_bridge; try rewrite repeat_function_bridge.
  try rewrite node_v159.
  try rewrite node_v156.
  reflexivity. Qed.
Local Opaque Core.v160.
Local Opaque Checked.v187.
Theorem step_projects s i : state (Checked.step s i)=Core.step (state s) (inputs i).
Proof. unfold state, Checked.step, Core.step; cbn [Checked.r0_nstate Checked.r1_nreq_5Fdw Checked.r2_nreq_5Ftag Checked.r3_ncount Checked.r4_nneg_5Fout Checked.r5_nisHi Checked.r6_nresHi Checked.r7_ndivisor Checked.r8_nremainder].
  rewrite node_v0. rewrite node_v61. rewrite node_v62. rewrite node_v63. rewrite node_v73. rewrite node_v92. rewrite node_v93. rewrite node_v100. rewrite node_v109. rewrite node_v151. rewrite word_function_bridge; reflexivity. Qed.
Theorem observe_projects s i : outputs (Checked.observe s i)=Core.observe (state s) (inputs i).
Proof. unfold outputs, Checked.observe, Core.observe; cbn [Checked.nio_5Freq_5Fready Checked.nio_5Fresp_5Fvalid Checked.nio_5Fresp_5Fbits_5Fdata Checked.nio_5Fresp_5Fbits_5Ftag].
  rewrite node_v1, node_v38, node_v160,word_function_bridge; reflexivity. Qed.
Local Opaque Core.step Checked.step Core.observe Checked.observe.
Theorem run_projects s pins n : state (Checked.run s pins n)=Core.run (state s) (fun t => inputs (pins t)) n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (state (Checked.step (Checked.run s pins n) (pins n))=Core.step (Core.run (state s) (fun t => inputs (pins t)) n) (inputs (pins n))).
  rewrite step_projects,IH; reflexivity.
Qed.
Theorem trace_projects s pins n : outputs (Checked.observe (Checked.run s pins n) (pins n))=
  Core.observe (Core.run (state s) (fun t => inputs (pins t)) n) (inputs (pins n)).
Proof. rewrite observe_projects,run_projects; reflexivity. Qed.
End MulDivCheckedProjection.
Print Assumptions MulDivCheckedProjection.step_projects.
Print Assumptions MulDivCheckedProjection.observe_projects.
Print Assumptions MulDivCheckedProjection.run_projects.
Print Assumptions MulDivCheckedProjection.trace_projects.

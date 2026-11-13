From Stdlib Require Import ZArith Zmod.Bits.
From BitsGenerated Require Import MulDiv MulDivChecked.
Module NativeCheckedProjection.
Module C := BitsGenerated.MulDivChecked.nMulDivChecked.
Module M := BitsGenerated.MulDiv.nMulDiv.
Definition inputs (x : C.Inputs) : M.Inputs := M.mkInputs
  (C.nreset x)
  (C.nio_5Freq_5Fvalid x)
  (C.nio_5Freq_5Fbits_5Ffn x)
  (C.nio_5Freq_5Fbits_5Fdw x)
  (C.nio_5Freq_5Fbits_5Fin1 x)
  (C.nio_5Freq_5Fbits_5Fin2 x)
  (C.nio_5Freq_5Fbits_5Ftag x)
  (C.nio_5Fkill x)
  (C.nio_5Fresp_5Fready x).
Lemma inputs_nreset x : M.nreset (inputs x) = C.nreset x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fvalid x : M.nio_5Freq_5Fvalid (inputs x) = C.nio_5Freq_5Fvalid x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Ffn x : M.nio_5Freq_5Fbits_5Ffn (inputs x) = C.nio_5Freq_5Fbits_5Ffn x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Fdw x : M.nio_5Freq_5Fbits_5Fdw (inputs x) = C.nio_5Freq_5Fbits_5Fdw x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Fin1 x : M.nio_5Freq_5Fbits_5Fin1 (inputs x) = C.nio_5Freq_5Fbits_5Fin1 x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Fin2 x : M.nio_5Freq_5Fbits_5Fin2 (inputs x) = C.nio_5Freq_5Fbits_5Fin2 x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Freq_5Fbits_5Ftag x : M.nio_5Freq_5Fbits_5Ftag (inputs x) = C.nio_5Freq_5Fbits_5Ftag x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Fkill x : M.nio_5Fkill (inputs x) = C.nio_5Fkill x. Proof. reflexivity. Qed.
Lemma inputs_nio_5Fresp_5Fready x : M.nio_5Fresp_5Fready (inputs x) = C.nio_5Fresp_5Fready x. Proof. reflexivity. Qed.
Definition state (x : C.State) : M.State := M.mkState
  (C.r0_nstate x)
  (C.r1_nreq_5Fdw x)
  (C.r2_nreq_5Ftag x)
  (C.r3_ncount x)
  (C.r4_nneg_5Fout x)
  (C.r5_nisHi x)
  (C.r6_nresHi x)
  (C.r7_ndivisor x)
  (C.r8_nremainder x).
Lemma state_r0_nstate x : M.r0_nstate (state x) = C.r0_nstate x. Proof. reflexivity. Qed.
Lemma state_r1_nreq_5Fdw x : M.r1_nreq_5Fdw (state x) = C.r1_nreq_5Fdw x. Proof. reflexivity. Qed.
Lemma state_r2_nreq_5Ftag x : M.r2_nreq_5Ftag (state x) = C.r2_nreq_5Ftag x. Proof. reflexivity. Qed.
Lemma state_r3_ncount x : M.r3_ncount (state x) = C.r3_ncount x. Proof. reflexivity. Qed.
Lemma state_r4_nneg_5Fout x : M.r4_nneg_5Fout (state x) = C.r4_nneg_5Fout x. Proof. reflexivity. Qed.
Lemma state_r5_nisHi x : M.r5_nisHi (state x) = C.r5_nisHi x. Proof. reflexivity. Qed.
Lemma state_r6_nresHi x : M.r6_nresHi (state x) = C.r6_nresHi x. Proof. reflexivity. Qed.
Lemma state_r7_ndivisor x : M.r7_ndivisor (state x) = C.r7_ndivisor x. Proof. reflexivity. Qed.
Lemma state_r8_nremainder x : M.r8_nremainder (state x) = C.r8_nremainder x. Proof. reflexivity. Qed.
Definition outputs (x : C.Outputs) : M.Outputs := M.mkOutputs
  (C.nio_5Freq_5Fready x)
  (C.nio_5Fresp_5Fvalid x)
  (C.nio_5Fresp_5Fbits_5Fdata x)
  (C.nio_5Fresp_5Fbits_5Ftag x).
Lemma outputs_nio_5Freq_5Fready x : M.nio_5Freq_5Fready (outputs x) = C.nio_5Freq_5Fready x. Proof. reflexivity. Qed.
Lemma outputs_nio_5Fresp_5Fvalid x : M.nio_5Fresp_5Fvalid (outputs x) = C.nio_5Fresp_5Fvalid x. Proof. reflexivity. Qed.
Lemma outputs_nio_5Fresp_5Fbits_5Fdata x : M.nio_5Fresp_5Fbits_5Fdata (outputs x) = C.nio_5Fresp_5Fbits_5Fdata x. Proof. reflexivity. Qed.
Lemma outputs_nio_5Fresp_5Fbits_5Ftag x : M.nio_5Fresp_5Fbits_5Ftag (outputs x) = C.nio_5Fresp_5Fbits_5Ftag x. Proof. reflexivity. Qed.
Lemma projected_v0 s i : M.v0 (state s) (inputs i) = C.v0 s i.
Proof. unfold M.v0, C.v0.
  reflexivity.
Qed.
Lemma projected_v1 s i : M.v1 (state s) (inputs i) = C.v1 s i.
Proof. unfold M.v1, C.v1.
  rewrite ?projected_v0.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v2 s i : M.v2 (state s) (inputs i) = C.v2 s i.
Proof. unfold M.v2, C.v2.
  rewrite ?projected_v1.
  rewrite ?inputs_nio_5Freq_5Fvalid.
  reflexivity.
Qed.
Lemma projected_v3 s i : M.v3 (state s) (inputs i) = C.v3 s i.
Proof. unfold M.v3, C.v3.
  rewrite ?inputs_nio_5Freq_5Fbits_5Ffn.
  reflexivity.
Qed.
Lemma projected_v4 s i : M.v4 (state s) (inputs i) = C.v4 s i.
Proof. unfold M.v4, C.v4.
  reflexivity.
Qed.
Lemma projected_v5 s i : M.v5 (state s) (inputs i) = C.v5 s i.
Proof. unfold M.v5, C.v5.
  rewrite ?projected_v3.
  rewrite ?projected_v4.
  reflexivity.
Qed.
Lemma projected_v6 s i : M.v6 (state s) (inputs i) = C.v6 s i.
Proof. unfold M.v6, C.v6.
  rewrite ?projected_v5.
  reflexivity.
Qed.
Lemma projected_v7 s i : M.v7 (state s) (inputs i) = C.v7 s i.
Proof. unfold M.v7, C.v7.
  reflexivity.
Qed.
Lemma projected_v8 s i : M.v8 (state s) (inputs i) = C.v8 s i.
Proof. unfold M.v8, C.v8.
  reflexivity.
Qed.
Lemma projected_v9 s i : M.v9 (state s) (inputs i) = C.v9 s i.
Proof. unfold M.v9, C.v9.
  rewrite ?projected_v5.
  reflexivity.
Qed.
Lemma projected_v10 s i : M.v10 (state s) (inputs i) = C.v10 s i.
Proof. unfold M.v10, C.v10.
  rewrite ?projected_v5.
  reflexivity.
Qed.
Lemma projected_v11 s i : M.v11 (state s) (inputs i) = C.v11 s i.
Proof. unfold M.v11, C.v11.
  rewrite ?projected_v6.
  rewrite ?projected_v10.
  reflexivity.
Qed.
Lemma projected_v12 s i : M.v12 (state s) (inputs i) = C.v12 s i.
Proof. unfold M.v12, C.v12.
  reflexivity.
Qed.
Lemma projected_v13 s i : M.v13 (state s) (inputs i) = C.v13 s i.
Proof. unfold M.v13, C.v13.
  rewrite ?projected_v11.
  rewrite ?projected_v12.
  reflexivity.
Qed.
Lemma projected_v14 s i : M.v14 (state s) (inputs i) = C.v14 s i.
Proof. unfold M.v14, C.v14.
  rewrite ?projected_v9.
  rewrite ?projected_v13.
  reflexivity.
Qed.
Lemma projected_v15 s i : M.v15 (state s) (inputs i) = C.v15 s i.
Proof. unfold M.v15, C.v15.
  reflexivity.
Qed.
Lemma projected_v16 s i : M.v16 (state s) (inputs i) = C.v16 s i.
Proof. unfold M.v16, C.v16.
  rewrite ?projected_v14.
  rewrite ?projected_v15.
  reflexivity.
Qed.
Lemma projected_v17 s i : M.v17 (state s) (inputs i) = C.v17 s i.
Proof. unfold M.v17, C.v17.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin1.
  reflexivity.
Qed.
Lemma projected_v18 s i : M.v18 (state s) (inputs i) = C.v18 s i.
Proof. unfold M.v18, C.v18.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin1.
  reflexivity.
Qed.
Lemma projected_v19 s i : M.v19 (state s) (inputs i) = C.v19 s i.
Proof. unfold M.v19, C.v19.
  rewrite ?projected_v17.
  rewrite ?projected_v18.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fdw.
  reflexivity.
Qed.
Lemma projected_v20 s i : M.v20 (state s) (inputs i) = C.v20 s i.
Proof. unfold M.v20, C.v20.
  rewrite ?projected_v16.
  rewrite ?projected_v19.
  reflexivity.
Qed.
Lemma projected_v21 s i : M.v21 (state s) (inputs i) = C.v21 s i.
Proof. unfold M.v21, C.v21.
  rewrite ?inputs_nio_5Freq_5Fbits_5Ffn.
  reflexivity.
Qed.
Lemma projected_v22 s i : M.v22 (state s) (inputs i) = C.v22 s i.
Proof. unfold M.v22, C.v22.
  rewrite ?projected_v9.
  rewrite ?projected_v21.
  reflexivity.
Qed.
Lemma projected_v23 s i : M.v23 (state s) (inputs i) = C.v23 s i.
Proof. unfold M.v23, C.v23.
  rewrite ?projected_v12.
  rewrite ?projected_v22.
  reflexivity.
Qed.
Lemma projected_v24 s i : M.v24 (state s) (inputs i) = C.v24 s i.
Proof. unfold M.v24, C.v24.
  rewrite ?projected_v13.
  rewrite ?projected_v23.
  reflexivity.
Qed.
Lemma projected_v25 s i : M.v25 (state s) (inputs i) = C.v25 s i.
Proof. unfold M.v25, C.v25.
  rewrite ?projected_v15.
  rewrite ?projected_v24.
  reflexivity.
Qed.
Lemma projected_v26 s i : M.v26 (state s) (inputs i) = C.v26 s i.
Proof. unfold M.v26, C.v26.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin2.
  reflexivity.
Qed.
Lemma projected_v27 s i : M.v27 (state s) (inputs i) = C.v27 s i.
Proof. unfold M.v27, C.v27.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin2.
  reflexivity.
Qed.
Lemma projected_v28 s i : M.v28 (state s) (inputs i) = C.v28 s i.
Proof. unfold M.v28, C.v28.
  rewrite ?projected_v26.
  rewrite ?projected_v27.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fdw.
  reflexivity.
Qed.
Lemma projected_v29 s i : M.v29 (state s) (inputs i) = C.v29 s i.
Proof. unfold M.v29, C.v29.
  rewrite ?projected_v25.
  rewrite ?projected_v28.
  reflexivity.
Qed.
Lemma projected_v30 s i : M.v30 (state s) (inputs i) = C.v30 s i.
Proof. unfold M.v30, C.v30.
  rewrite ?projected_v20.
  rewrite ?projected_v29.
  reflexivity.
Qed.
Lemma projected_v31 s i : M.v31 (state s) (inputs i) = C.v31 s i.
Proof. unfold M.v31, C.v31.
  reflexivity.
Qed.
Lemma projected_v32 s i : M.v32 (state s) (inputs i) = C.v32 s i.
Proof. unfold M.v32, C.v32.
  rewrite ?projected_v30.
  rewrite ?projected_v31.
  reflexivity.
Qed.
Lemma projected_v33 s i : M.v33 (state s) (inputs i) = C.v33 s i.
Proof. unfold M.v33, C.v33.
  rewrite ?projected_v8.
  rewrite ?projected_v31.
  rewrite ?projected_v32.
  reflexivity.
Qed.
Lemma projected_v34 s i : M.v34 (state s) (inputs i) = C.v34 s i.
Proof. unfold M.v34, C.v34.
  rewrite ?projected_v6.
  rewrite ?projected_v7.
  rewrite ?projected_v33.
  reflexivity.
Qed.
Lemma projected_v35 s i : M.v35 (state s) (inputs i) = C.v35 s i.
Proof. unfold M.v35, C.v35.
  reflexivity.
Qed.
Lemma projected_v36 s i : M.v36 (state s) (inputs i) = C.v36 s i.
Proof. unfold M.v36, C.v36.
  rewrite ?projected_v35.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v37 s i : M.v37 (state s) (inputs i) = C.v37 s i.
Proof. unfold M.v37, C.v37.
  rewrite ?projected_v4.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v38 s i : M.v38 (state s) (inputs i) = C.v38 s i.
Proof. unfold M.v38, C.v38.
  rewrite ?projected_v36.
  rewrite ?projected_v37.
  reflexivity.
Qed.
Lemma projected_v39 s i : M.v39 (state s) (inputs i) = C.v39 s i.
Proof. unfold M.v39, C.v39.
  rewrite ?projected_v38.
  rewrite ?inputs_nio_5Fresp_5Fready.
  reflexivity.
Qed.
Lemma projected_v40 s i : M.v40 (state s) (inputs i) = C.v40 s i.
Proof. unfold M.v40, C.v40.
  rewrite ?projected_v39.
  rewrite ?inputs_nio_5Fkill.
  reflexivity.
Qed.
Lemma projected_v41 s i : M.v41 (state s) (inputs i) = C.v41 s i.
Proof. unfold M.v41, C.v41.
  reflexivity.
Qed.
Lemma projected_v42 s i : M.v42 (state s) (inputs i) = C.v42 s i.
Proof. unfold M.v42, C.v42.
  rewrite ?projected_v41.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v43 s i : M.v43 (state s) (inputs i) = C.v43 s i.
Proof. unfold M.v43, C.v43.
  reflexivity.
Qed.
Lemma projected_v44 s i : M.v44 (state s) (inputs i) = C.v44 s i.
Proof. unfold M.v44, C.v44.
  rewrite ?projected_v43.
  rewrite ?state_r3_ncount.
  reflexivity.
Qed.
Lemma projected_v45 s i : M.v45 (state s) (inputs i) = C.v95 s i.
Proof. unfold M.v45, C.v95.
  rewrite ?projected_v42.
  rewrite ?projected_v44.
  reflexivity.
Qed.
Lemma projected_v46 s i : M.v46 (state s) (inputs i) = C.v46 s i.
Proof. unfold M.v46, C.v46.
  rewrite ?projected_v31.
  rewrite ?state_r4_nneg_5Fout.
  reflexivity.
Qed.
Lemma projected_v47 s i : M.v47 (state s) (inputs i) = C.v47 s i.
Proof. unfold M.v47, C.v47.
  rewrite ?projected_v31.
  rewrite ?projected_v46.
  reflexivity.
Qed.
Lemma projected_v48 s i : M.v48 (state s) (inputs i) = C.v48 s i.
Proof. unfold M.v48, C.v48.
  rewrite ?projected_v7.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v49 s i : M.v49 (state s) (inputs i) = C.v49 s i.
Proof. unfold M.v49, C.v49.
  reflexivity.
Qed.
Lemma projected_v50 s i : M.v50 (state s) (inputs i) = C.v50 s i.
Proof. unfold M.v50, C.v50.
  rewrite ?projected_v49.
  rewrite ?state_r3_ncount.
  reflexivity.
Qed.
Lemma projected_v51 s i : M.v51 (state s) (inputs i) = C.v51 s i.
Proof. unfold M.v51, C.v51.
  rewrite ?projected_v48.
  rewrite ?projected_v50.
  reflexivity.
Qed.
Lemma projected_v52 s i : M.v52 (state s) (inputs i) = C.v52 s i.
Proof. unfold M.v52, C.v52.
  reflexivity.
Qed.
Lemma projected_v53 s i : M.v53 (state s) (inputs i) = C.v53 s i.
Proof. unfold M.v53, C.v53.
  rewrite ?projected_v52.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v54 s i : M.v54 (state s) (inputs i) = C.v54 s i.
Proof. unfold M.v54, C.v54.
  reflexivity.
Qed.
Lemma projected_v55 s i : M.v55 (state s) (inputs i) = C.v55 s i.
Proof. unfold M.v55, C.v55.
  rewrite ?projected_v54.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v56 s i : M.v56 (state s) (inputs i) = C.v56 s i.
Proof. unfold M.v56, C.v56.
  rewrite ?projected_v41.
  rewrite ?projected_v55.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v57 s i : M.v57 (state s) (inputs i) = C.v57 s i.
Proof. unfold M.v57, C.v57.
  rewrite ?projected_v4.
  rewrite ?projected_v53.
  rewrite ?projected_v56.
  reflexivity.
Qed.
Lemma projected_v58 s i : M.v58 (state s) (inputs i) = C.v58 s i.
Proof. unfold M.v58, C.v58.
  rewrite ?projected_v35.
  rewrite ?projected_v51.
  rewrite ?projected_v57.
  reflexivity.
Qed.
Lemma projected_v59 s i : M.v59 (state s) (inputs i) = C.v59 s i.
Proof. unfold M.v59, C.v59.
  rewrite ?projected_v45.
  rewrite ?projected_v47.
  rewrite ?projected_v58.
  reflexivity.
Qed.
Lemma projected_v60 s i : M.v60 (state s) (inputs i) = C.v60 s i.
Proof. unfold M.v60, C.v60.
  rewrite ?projected_v0.
  rewrite ?projected_v40.
  rewrite ?projected_v59.
  reflexivity.
Qed.
Lemma projected_v61 s i : M.v61 (state s) (inputs i) = C.v61 s i.
Proof. unfold M.v61, C.v61.
  rewrite ?projected_v2.
  rewrite ?projected_v34.
  rewrite ?projected_v60.
  reflexivity.
Qed.
Lemma projected_v62 s i : M.v62 (state s) (inputs i) = C.v62 s i.
Proof. unfold M.v62, C.v62.
  rewrite ?projected_v2.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fdw.
  rewrite ?state_r1_nreq_5Fdw.
  reflexivity.
Qed.
Lemma projected_v63 s i : M.v63 (state s) (inputs i) = C.v63 s i.
Proof. unfold M.v63, C.v63.
  rewrite ?projected_v2.
  rewrite ?inputs_nio_5Freq_5Fbits_5Ftag.
  rewrite ?state_r2_nreq_5Ftag.
  reflexivity.
Qed.
Lemma projected_v64 s i : M.v64 (state s) (inputs i) = C.v64 s i.
Proof. unfold M.v64, C.v64.
  rewrite ?projected_v31.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fdw.
  reflexivity.
Qed.
Lemma projected_v65 s i : M.v65 (state s) (inputs i) = C.v65 s i.
Proof. unfold M.v65, C.v65.
  rewrite ?projected_v6.
  rewrite ?projected_v64.
  reflexivity.
Qed.
Lemma projected_v66 s i : M.v66 (state s) (inputs i) = C.v66 s i.
Proof. unfold M.v66, C.v66.
  reflexivity.
Qed.
Lemma projected_v67 s i : M.v67 (state s) (inputs i) = C.v67 s i.
Proof. unfold M.v67, C.v67.
  rewrite ?projected_v8.
  rewrite ?projected_v65.
  rewrite ?projected_v66.
  reflexivity.
Qed.
Lemma projected_v68 s i : M.v68 (state s) (inputs i) = C.v68 s i.
Proof. unfold M.v68, C.v68.
  reflexivity.
Qed.
Lemma projected_v69 s i : M.v69 (state s) (inputs i) = C.v70 s i.
Proof. unfold M.v69, C.v70.
  rewrite ?projected_v68.
  rewrite ?state_r3_ncount.
  reflexivity.
Qed.
Lemma projected_v70 s i : M.v70 (state s) (inputs i) = C.v70 s i.
Proof. unfold M.v70, C.v70.
  rewrite ?projected_v68.
  rewrite ?state_r3_ncount.
  reflexivity.
Qed.
Lemma projected_v71 s i : M.v71 (state s) (inputs i) = C.v71 s i.
Proof. unfold M.v71, C.v71.
  rewrite ?projected_v48.
  rewrite ?projected_v70.
  rewrite ?state_r3_ncount.
  reflexivity.
Qed.
Lemma projected_v72 s i : M.v72 (state s) (inputs i) = C.v72 s i.
Proof. unfold M.v72, C.v72.
  rewrite ?projected_v42.
  rewrite ?projected_v69.
  rewrite ?projected_v71.
  reflexivity.
Qed.
Lemma projected_v73 s i : M.v73 (state s) (inputs i) = C.v73 s i.
Proof. unfold M.v73, C.v73.
  rewrite ?projected_v2.
  rewrite ?projected_v67.
  rewrite ?projected_v72.
  reflexivity.
Qed.
Lemma projected_v74 s i : M.v74 (state s) (inputs i) = C.v74 s i.
Proof. unfold M.v74, C.v74.
  rewrite ?inputs_nio_5Freq_5Fbits_5Ffn.
  reflexivity.
Qed.
Lemma projected_v75 s i : M.v75 (state s) (inputs i) = C.v75 s i.
Proof. unfold M.v75, C.v75.
  rewrite ?projected_v6.
  rewrite ?projected_v74.
  reflexivity.
Qed.
Lemma projected_v76 s i : M.v76 (state s) (inputs i) = C.v76 s i.
Proof. unfold M.v76, C.v76.
  rewrite ?projected_v12.
  rewrite ?projected_v75.
  reflexivity.
Qed.
Lemma projected_v77 s i : M.v77 (state s) (inputs i) = C.v77 s i.
Proof. unfold M.v77, C.v77.
  rewrite ?inputs_nio_5Freq_5Fbits_5Ffn.
  reflexivity.
Qed.
Lemma projected_v78 s i : M.v78 (state s) (inputs i) = C.v78 s i.
Proof. unfold M.v78, C.v78.
  rewrite ?projected_v76.
  rewrite ?projected_v77.
  reflexivity.
Qed.
Lemma projected_v79 s i : M.v79 (state s) (inputs i) = C.v79 s i.
Proof. unfold M.v79, C.v79.
  rewrite ?projected_v15.
  rewrite ?projected_v78.
  reflexivity.
Qed.
Lemma projected_v80 s i : M.v80 (state s) (inputs i) = C.v80 s i.
Proof. unfold M.v80, C.v80.
  rewrite ?projected_v20.
  rewrite ?projected_v29.
  reflexivity.
Qed.
Lemma projected_v81 s i : M.v81 (state s) (inputs i) = C.v81 s i.
Proof. unfold M.v81, C.v81.
  rewrite ?projected_v20.
  rewrite ?projected_v79.
  rewrite ?projected_v80.
  reflexivity.
Qed.
Lemma projected_v82 s i : M.v82 (state s) (inputs i) = C.v82 s i.
Proof. unfold M.v82, C.v82.
  reflexivity.
Qed.
Lemma projected_v83 s i : M.v83 (state s) (inputs i) = C.v83 s i.
Proof. unfold M.v83, C.v83.
  rewrite ?projected_v82.
  rewrite ?state_r3_ncount.
  reflexivity.
Qed.
Lemma projected_v84 s i : M.v84 (state s) (inputs i) = C.v84 s i.
Proof. unfold M.v84, C.v84.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v85 s i : M.v85 (state s) (inputs i) = C.v85 s i.
Proof. unfold M.v85, C.v85.
  rewrite ?projected_v84.
  rewrite ?state_r7_ndivisor.
  reflexivity.
Qed.
Lemma projected_v86 s i : M.v86 (state s) (inputs i) = C.v86 s i.
Proof. unfold M.v86, C.v86.
  rewrite ?projected_v85.
  reflexivity.
Qed.
Lemma projected_v87 s i : M.v87 (state s) (inputs i) = C.v120 s i.
Proof. unfold M.v87, C.v120.
  rewrite ?projected_v31.
  rewrite ?projected_v86.
  reflexivity.
Qed.
Lemma projected_v88 s i : M.v88 (state s) (inputs i) = C.v88 s i.
Proof. unfold M.v88, C.v88.
  rewrite ?projected_v31.
  rewrite ?state_r5_nisHi.
  reflexivity.
Qed.
Lemma projected_v89 s i : M.v89 (state s) (inputs i) = C.v89 s i.
Proof. unfold M.v89, C.v89.
  rewrite ?projected_v42.
  rewrite ?projected_v83.
  rewrite ?projected_v87.
  rewrite ?projected_v88.
  reflexivity.
Qed.
Lemma projected_v90 s i : M.v90 (state s) (inputs i) = C.v90 s i.
Proof. unfold M.v90, C.v90.
  rewrite ?projected_v31.
  rewrite ?projected_v89.
  reflexivity.
Qed.
Lemma projected_v91 s i : M.v91 (state s) (inputs i) = C.v91 s i.
Proof. unfold M.v91, C.v91.
  rewrite ?projected_v90.
  rewrite ?state_r4_nneg_5Fout.
  reflexivity.
Qed.
Lemma projected_v92 s i : M.v92 (state s) (inputs i) = C.v92 s i.
Proof. unfold M.v92, C.v92.
  rewrite ?projected_v2.
  rewrite ?projected_v81.
  rewrite ?projected_v91.
  reflexivity.
Qed.
Lemma projected_v93 s i : M.v93 (state s) (inputs i) = C.v93 s i.
Proof. unfold M.v93, C.v93.
  rewrite ?projected_v2.
  rewrite ?projected_v79.
  rewrite ?state_r5_nisHi.
  reflexivity.
Qed.
Lemma projected_v94 s i : M.v94 (state s) (inputs i) = C.v174 s i.
Proof. unfold M.v94, C.v174.
  rewrite ?projected_v2.
  rewrite ?projected_v31.
  reflexivity.
Qed.
Lemma projected_v95 s i : M.v95 (state s) (inputs i) = C.v95 s i.
Proof. unfold M.v95, C.v95.
  rewrite ?projected_v42.
  rewrite ?projected_v44.
  reflexivity.
Qed.
Lemma projected_v96 s i : M.v96 (state s) (inputs i) = C.v96 s i.
Proof. unfold M.v96, C.v96.
  rewrite ?projected_v51.
  rewrite ?projected_v95.
  reflexivity.
Qed.
Lemma projected_v97 s i : M.v97 (state s) (inputs i) = C.v97 s i.
Proof. unfold M.v97, C.v97.
  rewrite ?projected_v31.
  rewrite ?projected_v53.
  reflexivity.
Qed.
Lemma projected_v98 s i : M.v98 (state s) (inputs i) = C.v98 s i.
Proof. unfold M.v98, C.v98.
  rewrite ?projected_v97.
  rewrite ?state_r6_nresHi.
  reflexivity.
Qed.
Lemma projected_v99 s i : M.v99 (state s) (inputs i) = C.v99 s i.
Proof. unfold M.v99, C.v99.
  rewrite ?projected_v96.
  rewrite ?projected_v98.
  rewrite ?state_r5_nisHi.
  reflexivity.
Qed.
Lemma projected_v100 s i : M.v100 (state s) (inputs i) = C.v100 s i.
Proof. unfold M.v100, C.v100.
  rewrite ?projected_v94.
  rewrite ?projected_v99.
  reflexivity.
Qed.
Lemma projected_v101 s i : M.v101 (state s) (inputs i) = C.v101 s i.
Proof. unfold M.v101, C.v101.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin2.
  reflexivity.
Qed.
Lemma projected_v102 s i : M.v102 (state s) (inputs i) = C.v102 s i.
Proof. unfold M.v102, C.v102.
  rewrite ?projected_v29.
  reflexivity.
Qed.
Lemma projected_v103 s i : M.v103 (state s) (inputs i) = C.v103 s i.
Proof. unfold M.v103, C.v103.
  rewrite ?projected_v101.
  rewrite ?projected_v102.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fdw.
  reflexivity.
Qed.
Lemma projected_v104 s i : M.v104 (state s) (inputs i) = C.v104 s i.
Proof. unfold M.v104, C.v104.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin2.
  reflexivity.
Qed.
Lemma projected_v105 s i : M.v105 (state s) (inputs i) = C.v105 s i.
Proof. unfold M.v105, C.v105.
  rewrite ?projected_v29.
  rewrite ?projected_v103.
  rewrite ?projected_v104.
  reflexivity.
Qed.
Lemma projected_v106 s i : M.v106 (state s) (inputs i) = C.v106 s i.
Proof. unfold M.v106, C.v106.
  rewrite ?state_r7_ndivisor.
  reflexivity.
Qed.
Lemma projected_v107 s i : M.v107 (state s) (inputs i) = C.v107 s i.
Proof. unfold M.v107, C.v107.
  rewrite ?projected_v55.
  rewrite ?projected_v106.
  reflexivity.
Qed.
Lemma projected_v108 s i : M.v108 (state s) (inputs i) = C.v108 s i.
Proof. unfold M.v108, C.v108.
  rewrite ?projected_v85.
  rewrite ?projected_v107.
  rewrite ?state_r7_ndivisor.
  reflexivity.
Qed.
Lemma projected_v109 s i : M.v109 (state s) (inputs i) = C.v109 s i.
Proof. unfold M.v109, C.v109.
  rewrite ?projected_v2.
  rewrite ?projected_v105.
  rewrite ?projected_v108.
  reflexivity.
Qed.
Lemma projected_v110 s i : M.v110 (state s) (inputs i) = C.v110 s i.
Proof. unfold M.v110, C.v110.
  reflexivity.
Qed.
Lemma projected_v111 s i : M.v111 (state s) (inputs i) = C.v111 s i.
Proof. unfold M.v111, C.v111.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin1.
  reflexivity.
Qed.
Lemma projected_v112 s i : M.v112 (state s) (inputs i) = C.v112 s i.
Proof. unfold M.v112, C.v112.
  rewrite ?projected_v20.
  reflexivity.
Qed.
Lemma projected_v113 s i : M.v113 (state s) (inputs i) = C.v113 s i.
Proof. unfold M.v113, C.v113.
  rewrite ?projected_v111.
  rewrite ?projected_v112.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fdw.
  reflexivity.
Qed.
Lemma projected_v114 s i : M.v114 (state s) (inputs i) = C.v114 s i.
Proof. unfold M.v114, C.v114.
  rewrite ?inputs_nio_5Freq_5Fbits_5Fin1.
  reflexivity.
Qed.
Lemma projected_v115 s i : M.v115 (state s) (inputs i) = C.v115 s i.
Proof. unfold M.v115, C.v115.
  rewrite ?projected_v110.
  rewrite ?projected_v113.
  rewrite ?projected_v114.
  reflexivity.
Qed.
Lemma projected_v116 s i : M.v116 (state s) (inputs i) = C.v116 s i.
Proof. unfold M.v116, C.v116.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v117 s i : M.v117 (state s) (inputs i) = C.v117 s i.
Proof. unfold M.v117, C.v117.
  rewrite ?projected_v85.
  reflexivity.
Qed.
Lemma projected_v118 s i : M.v118 (state s) (inputs i) = C.v118 s i.
Proof. unfold M.v118, C.v118.
  rewrite ?projected_v86.
  rewrite ?projected_v116.
  rewrite ?projected_v117.
  reflexivity.
Qed.
Lemma projected_v119 s i : M.v119 (state s) (inputs i) = C.v119 s i.
Proof. unfold M.v119, C.v119.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v120 s i : M.v120 (state s) (inputs i) = C.v120 s i.
Proof. unfold M.v120, C.v120.
  rewrite ?projected_v31.
  rewrite ?projected_v86.
  reflexivity.
Qed.
Lemma projected_v121 s i : M.v121 (state s) (inputs i) = C.v121 s i.
Proof. unfold M.v121, C.v121.
  rewrite ?projected_v8.
  rewrite ?projected_v118.
  rewrite ?projected_v119.
  rewrite ?projected_v120.
  reflexivity.
Qed.
Lemma projected_v122 s i : M.v122 (state s) (inputs i) = C.v122 s i.
Proof. unfold M.v122, C.v122.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v123 s i : M.v123 (state s) (inputs i) = C.v123 s i.
Proof. unfold M.v123, C.v123.
  rewrite ?projected_v122.
  reflexivity.
Qed.
Lemma projected_v124 s i : M.v124 (state s) (inputs i) = C.v124 s i.
Proof. unfold M.v124, C.v124.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v125 s i : M.v125 (state s) (inputs i) = C.v125 s i.
Proof. unfold M.v125, C.v125.
  rewrite ?projected_v123.
  rewrite ?projected_v124.
  reflexivity.
Qed.
Lemma projected_v126 s i : M.v126 (state s) (inputs i) = C.v126 s i.
Proof. unfold M.v126, C.v126.
  rewrite ?state_r7_ndivisor.
  reflexivity.
Qed.
Lemma projected_v127 s i : M.v127 (state s) (inputs i) = C.v127 s i.
Proof. unfold M.v127, C.v127.
  rewrite ?projected_v126.
  rewrite ?state_r7_ndivisor.
  reflexivity.
Qed.
Lemma projected_v128 s i : M.v128 (state s) (inputs i) = C.v128 s i.
Proof. unfold M.v128, C.v128.
  rewrite ?projected_v125.
  rewrite ?projected_v127.
  reflexivity.
Qed.
Lemma projected_v129 s i : M.v129 (state s) (inputs i) = C.v129 s i.
Proof. unfold M.v129, C.v129.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v130 s i : M.v130 (state s) (inputs i) = C.v130 s i.
Proof. unfold M.v130, C.v130.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v131 s i : M.v131 (state s) (inputs i) = C.v131 s i.
Proof. unfold M.v131, C.v131.
  rewrite ?projected_v129.
  rewrite ?projected_v130.
  reflexivity.
Qed.
Lemma projected_v132 s i : M.v132 (state s) (inputs i) = C.v132 s i.
Proof. unfold M.v132, C.v132.
  rewrite ?projected_v128.
  rewrite ?projected_v131.
  reflexivity.
Qed.
Lemma projected_v133 s i : M.v133 (state s) (inputs i) = C.v133 s i.
Proof. unfold M.v133, C.v133.
  rewrite ?projected_v132.
  reflexivity.
Qed.
Lemma projected_v134 s i : M.v134 (state s) (inputs i) = C.v134 s i.
Proof. unfold M.v134, C.v134.
  reflexivity.
Qed.
Lemma projected_v135 s i : M.v135 (state s) (inputs i) = C.v135 s i.
Proof. unfold M.v135, C.v135.
  rewrite ?projected_v134.
  rewrite ?state_r3_ncount.
  reflexivity.
Qed.
Lemma projected_v136 s i : M.v136 (state s) (inputs i) = C.v136 s i.
Proof. unfold M.v136, C.v136.
  rewrite ?projected_v135.
  rewrite ?state_r4_nneg_5Fout.
  reflexivity.
Qed.
Lemma projected_v137 s i : M.v137 (state s) (inputs i) = C.v137 s i.
Proof. unfold M.v137, C.v137.
  rewrite ?projected_v132.
  reflexivity.
Qed.
Lemma projected_v138 s i : M.v138 (state s) (inputs i) = C.v138 s i.
Proof. unfold M.v138, C.v138.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v139 s i : M.v139 (state s) (inputs i) = C.v139 s i.
Proof. unfold M.v139, C.v139.
  rewrite ?projected_v133.
  rewrite ?projected_v136.
  rewrite ?projected_v137.
  rewrite ?projected_v138.
  reflexivity.
Qed.
Lemma projected_v140 s i : M.v140 (state s) (inputs i) = C.v140 s i.
Proof. unfold M.v140, C.v140.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v141 s i : M.v141 (state s) (inputs i) = C.v141 s i.
Proof. unfold M.v141, C.v141.
  rewrite ?projected_v55.
  rewrite ?projected_v140.
  reflexivity.
Qed.
Lemma projected_v142 s i : M.v142 (state s) (inputs i) = C.v142 s i.
Proof. unfold M.v142, C.v142.
  rewrite ?projected_v53.
  rewrite ?projected_v141.
  reflexivity.
Qed.
Lemma projected_v143 s i : M.v143 (state s) (inputs i) = C.v143 s i.
Proof. unfold M.v143, C.v143.
  reflexivity.
Qed.
Lemma projected_v144 s i : M.v144 (state s) (inputs i) = C.v144 s i.
Proof. unfold M.v144, C.v144.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v145 s i : M.v145 (state s) (inputs i) = C.v145 s i.
Proof. unfold M.v145, C.v145.
  rewrite ?projected_v119.
  rewrite ?projected_v144.
  rewrite ?state_r6_nresHi.
  reflexivity.
Qed.
Lemma projected_v146 s i : M.v146 (state s) (inputs i) = C.v146 s i.
Proof. unfold M.v146, C.v146.
  rewrite ?projected_v143.
  rewrite ?projected_v145.
  reflexivity.
Qed.
Lemma projected_v147 s i : M.v147 (state s) (inputs i) = C.v147 s i.
Proof. unfold M.v147, C.v147.
  rewrite ?projected_v110.
  rewrite ?projected_v146.
  reflexivity.
Qed.
Lemma projected_v148 s i : M.v148 (state s) (inputs i) = C.v148 s i.
Proof. unfold M.v148, C.v148.
  rewrite ?projected_v142.
  rewrite ?projected_v147.
  rewrite ?state_r8_nremainder.
  reflexivity.
Qed.
Lemma projected_v149 s i : M.v149 (state s) (inputs i) = C.v149 s i.
Proof. unfold M.v149, C.v149.
  rewrite ?projected_v48.
  rewrite ?projected_v139.
  rewrite ?projected_v148.
  reflexivity.
Qed.
Lemma projected_v150 s i : M.v150 (state s) (inputs i) = C.v150 s i.
Proof. unfold M.v150, C.v150.
  rewrite ?projected_v42.
  rewrite ?projected_v121.
  rewrite ?projected_v149.
  reflexivity.
Qed.
Lemma projected_v151 s i : M.v151 (state s) (inputs i) = C.v151 s i.
Proof. unfold M.v151, C.v151.
  rewrite ?projected_v2.
  rewrite ?projected_v115.
  rewrite ?projected_v150.
  reflexivity.
Qed.
Lemma projected_v152 s i : M.v152 (state s) (inputs i) = C.v179 s i.
Proof. unfold M.v152, C.v179.
  rewrite ?projected_v145.
  reflexivity.
Qed.
Lemma projected_v153 s i : M.v153 (state s) (inputs i) = C.v180 s i.
Proof. unfold M.v153, C.v180.
  rewrite ?state_r0_nstate.
  reflexivity.
Qed.
Lemma projected_v154 s i : M.v154 (state s) (inputs i) = C.v181 s i.
Proof. unfold M.v154, C.v181.
  rewrite ?projected_v153.
  rewrite ?state_r1_nreq_5Fdw.
  reflexivity.
Qed.
Lemma projected_v155 s i : M.v155 (state s) (inputs i) = C.v182 s i.
Proof. unfold M.v155, C.v182.
  rewrite ?projected_v145.
  reflexivity.
Qed.
Lemma projected_v156 s i : M.v156 (state s) (inputs i) = C.v183 s i.
Proof. unfold M.v156, C.v183.
  rewrite ?projected_v152.
  rewrite ?projected_v154.
  rewrite ?projected_v155.
  reflexivity.
Qed.
Lemma projected_v157 s i : M.v157 (state s) (inputs i) = C.v184 s i.
Proof. unfold M.v157, C.v184.
  rewrite ?projected_v156.
  reflexivity.
Qed.
Lemma projected_v158 s i : M.v158 (state s) (inputs i) = C.v185 s i.
Proof. unfold M.v158, C.v185.
  rewrite ?projected_v157.
  reflexivity.
Qed.
Lemma projected_v159 s i : M.v159 (state s) (inputs i) = C.v186 s i.
Proof. unfold M.v159, C.v186.
  rewrite ?projected_v152.
  rewrite ?projected_v158.
  rewrite ?state_r1_nreq_5Fdw.
  reflexivity.
Qed.
Lemma projected_v160 s i : M.v160 (state s) (inputs i) = C.v187 s i.
Proof. unfold M.v160, C.v187.
  rewrite ?projected_v156.
  rewrite ?projected_v159.
  reflexivity.
Qed.
Lemma state_ext (a b : M.State) :
  M.r0_nstate a = M.r0_nstate b ->
  M.r1_nreq_5Fdw a = M.r1_nreq_5Fdw b ->
  M.r2_nreq_5Ftag a = M.r2_nreq_5Ftag b ->
  M.r3_ncount a = M.r3_ncount b ->
  M.r4_nneg_5Fout a = M.r4_nneg_5Fout b ->
  M.r5_nisHi a = M.r5_nisHi b ->
  M.r6_nresHi a = M.r6_nresHi b ->
  M.r7_ndivisor a = M.r7_ndivisor b ->
  M.r8_nremainder a = M.r8_nremainder b ->
  a = b.
Proof. destruct a,b; cbn; intros; subst; reflexivity. Qed.
Lemma outputs_ext (a b : M.Outputs) :
  M.nio_5Freq_5Fready a = M.nio_5Freq_5Fready b ->
  M.nio_5Fresp_5Fvalid a = M.nio_5Fresp_5Fvalid b ->
  M.nio_5Fresp_5Fbits_5Fdata a = M.nio_5Fresp_5Fbits_5Fdata b ->
  M.nio_5Fresp_5Fbits_5Ftag a = M.nio_5Fresp_5Fbits_5Ftag b ->
  a = b.
Proof. destruct a,b; cbn; intros; subst; reflexivity. Qed.
Theorem step_projects s i : state (C.step s i) = M.step (state s) (inputs i).
Proof. apply state_ext.
  - rewrite state_r0_nstate.
    change ((if Zmod.eqb (C.nreset i) Zmod.one then C.v0 s i else C.v61 s i) =
      (if Zmod.eqb (C.nreset i) Zmod.one then M.v0 (state s) (inputs i) else M.v61 (state s) (inputs i))).
    rewrite projected_v0, projected_v61; reflexivity.
  - rewrite state_r1_nreq_5Fdw.
    change (C.v62 s i = M.v62 (state s) (inputs i)); symmetry; apply projected_v62.
  - rewrite state_r2_nreq_5Ftag.
    change (C.v63 s i = M.v63 (state s) (inputs i)); symmetry; apply projected_v63.
  - rewrite state_r3_ncount.
    change (C.v73 s i = M.v73 (state s) (inputs i)); symmetry; apply projected_v73.
  - rewrite state_r4_nneg_5Fout.
    change (C.v92 s i = M.v92 (state s) (inputs i)); symmetry; apply projected_v92.
  - rewrite state_r5_nisHi.
    change (C.v93 s i = M.v93 (state s) (inputs i)); symmetry; apply projected_v93.
  - rewrite state_r6_nresHi.
    change (C.v100 s i = M.v100 (state s) (inputs i)); symmetry; apply projected_v100.
  - rewrite state_r7_ndivisor.
    change (C.v109 s i = M.v109 (state s) (inputs i)); symmetry; apply projected_v109.
  - rewrite state_r8_nremainder.
    change (C.v151 s i = M.v151 (state s) (inputs i)); symmetry; apply projected_v151.
Qed.
Theorem observe_projects s i : outputs (C.observe s i) = M.observe (state s) (inputs i).
Proof. apply outputs_ext.
  - rewrite outputs_nio_5Freq_5Fready.
    change (C.v1 s i = M.v1 (state s) (inputs i)); symmetry; apply projected_v1.
  - rewrite outputs_nio_5Fresp_5Fvalid.
    change (C.v38 s i = M.v38 (state s) (inputs i)); symmetry; apply projected_v38.
  - rewrite outputs_nio_5Fresp_5Fbits_5Fdata.
    change (C.v187 s i = M.v160 (state s) (inputs i)); symmetry; apply projected_v160.
  - rewrite outputs_nio_5Fresp_5Fbits_5Ftag.
    reflexivity.
Qed.
Theorem run_projects s (pins : nat -> C.Inputs) n : state (C.run s pins n) = M.run (state s) (fun t => inputs (pins t)) n.
Proof. induction n; cbn [C.run M.run]; [reflexivity | rewrite step_projects, IHn; reflexivity]. Qed.
Theorem trace_projects s (pins : nat -> C.Inputs) n :
  outputs (C.observe (C.run s pins n) (pins n)) = M.observe (M.run (state s) (fun t => inputs (pins t)) n) (inputs (pins n)).
Proof. rewrite observe_projects, run_projects; reflexivity. Qed.
Print Assumptions step_projects.
Print Assumptions observe_projects.
Print Assumptions trace_projects.
End NativeCheckedProjection.

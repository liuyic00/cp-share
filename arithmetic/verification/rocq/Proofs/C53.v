From Coq Require Import ZArith Lia List Bool.
From Generated Require Import C53.
Import C53.CIRCTBits C53.nC53.
Open Scope Z_scope.

Lemma bit_cases x : word 1 x = 0 \/ word 1 x = 1.
Proof.
  unfold word. change (2^1) with 2.
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

(* All exported conservation checks, for arbitrary input integers modulo 2. *)
Theorem assertions_hold (s : State) (i : Inputs) : asserts s i.
Proof.
  unfold asserts, assertionChecks, v53, v52, v51, v50, v49, v48, v47, v46, v45, v44, v43, v42, v41, v40, v39, v38, v37, v36, v35, v34, v33, v32, v31, v30, v29, v28, v27, v26, v25, v24, v23, v22, v21, v20, v19, v18, v17, v16, v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0.
  destruct (bit_cases (nreset i)) as [Hnreset|Hnreset]; rewrite Hnreset;
  destruct (bit_cases (nio_5Fin_5F0 i)) as [Hnio_5Fin_5F0|Hnio_5Fin_5F0]; rewrite Hnio_5Fin_5F0;
  destruct (bit_cases (nio_5Fin_5F1 i)) as [Hnio_5Fin_5F1|Hnio_5Fin_5F1]; rewrite Hnio_5Fin_5F1;
  destruct (bit_cases (nio_5Fin_5F2 i)) as [Hnio_5Fin_5F2|Hnio_5Fin_5F2]; rewrite Hnio_5Fin_5F2;
  destruct (bit_cases (nio_5Fin_5F3 i)) as [Hnio_5Fin_5F3|Hnio_5Fin_5F3]; rewrite Hnio_5Fin_5F3;
  destruct (bit_cases (nio_5Fin_5F4 i)) as [Hnio_5Fin_5F4|Hnio_5Fin_5F4]; rewrite Hnio_5Fin_5F4;
    vm_compute; reflexivity.
Qed.
Print Assumptions assertions_hold.

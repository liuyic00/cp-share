(* Representation maps only.  The circuit continues to execute the original
   FIRRTL AST; these maps prepare a refinement proof to the existing theorem. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable.
From Generated Require Import Radix2Divider.
Module Reference := Radix2Divider.nRadix2Divider.
Local Open Scope N_scope.
Definition encoded_leaves (s : Reference.State) (i : Reference.Inputs) (ghost_sign : Z) : leaf_values :=
 fun id => match id with
| 0 => encode 1 1
| 45 => encode 1 ghost_sign
| 13 => encode 3 (Reference.r0_nstate s)
| 18 => encode 1 (Reference.r1_ndivBy0Reg s)
| 20 => encode 129 (Reference.r2_nshiftReg s)
| 33 => encode 1 (Reference.r3_naSignReg s)
| 38 => encode 1 (Reference.r4_nqSignReg s)
| 40 => encode 64 (Reference.r5_nbReg s)
| 43 => encode 65 (Reference.r6_naValx2Reg s)
| 46 => encode 1 (Reference.r7_nctrlReg_5FisW s)
| 47 => encode 1 (Reference.r8_nctrlReg_5FisHi s)
| 51 => encode 6 (Reference.r9_ncnt_5Fvalue s)
| 445 => encode 1 (Reference.r10_nhistoryValid s)
| 446 => encode 3 (Reference.r11_npreviousState s)
| 447 => encode 6 (Reference.r12_npreviousCount s)
| 475 => encode 1 (Reference.r13_nwasStalled s)
| 476 => encode 64 (Reference.r14_npreviousOutput s)
| 1 => encode 1 (Reference.nreset i)
| 3 => encode 1 (Reference.nio_5Fin_5Fvalid i)
| 4 => encode 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F0 i)
| 5 => encode 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i)
| 6 => encode 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F2 i)
| 7 => encode 1 (Reference.nio_5Fout_5Fready i)
| 10 => encode 1 (Reference.nctrl_5Fsign i)
| 11 => encode 1 (Reference.nctrl_5FisW i)
| 12 => encode 1 (Reference.nctrl_5FisHi i)
| _ => encode 0 0 end.
Definition project_state (v : leaf_values) : Reference.State := Reference.mkState
 (to_Zpos (v 13))
 (to_Zpos (v 18))
 (to_Zpos (v 20))
 (to_Zpos (v 33))
 (to_Zpos (v 38))
 (to_Zpos (v 40))
 (to_Zpos (v 43))
 (to_Zpos (v 46))
 (to_Zpos (v 47))
 (to_Zpos (v 51))
 (to_Zpos (v 445))
 (to_Zpos (v 446))
 (to_Zpos (v 447))
 (to_Zpos (v 475))
 (to_Zpos (v 476)).
Definition normalize_state (s : Reference.State) : Reference.State := Reference.mkState
 (normalize 3 (Reference.r0_nstate s))
 (normalize 1 (Reference.r1_ndivBy0Reg s))
 (normalize 129 (Reference.r2_nshiftReg s))
 (normalize 1 (Reference.r3_naSignReg s))
 (normalize 1 (Reference.r4_nqSignReg s))
 (normalize 64 (Reference.r5_nbReg s))
 (normalize 65 (Reference.r6_naValx2Reg s))
 (normalize 1 (Reference.r7_nctrlReg_5FisW s))
 (normalize 1 (Reference.r8_nctrlReg_5FisHi s))
 (normalize 6 (Reference.r9_ncnt_5Fvalue s))
 (normalize 1 (Reference.r10_nhistoryValid s))
 (normalize 3 (Reference.r11_npreviousState s))
 (normalize 6 (Reference.r12_npreviousCount s))
 (normalize 1 (Reference.r13_nwasStalled s))
 (normalize 64 (Reference.r14_npreviousOutput s)).
Lemma encoded_state_projection s i ghost_sign : project_state (encoded_leaves s i ghost_sign) = normalize_state s.
Proof. unfold project_state, encoded_leaves, normalize_state. rewrite !decode_encode. reflexivity. Qed.
Definition project_inputs (v : leaf_values) : Reference.Inputs := Reference.mkInputs
 (to_Zpos (v 1))
 (to_Zpos (v 3))
 (to_Zpos (v 4))
 (to_Zpos (v 5))
 (to_Zpos (v 6))
 (to_Zpos (v 7))
 (to_Zpos (v 10))
 (to_Zpos (v 11))
 (to_Zpos (v 12)).
Definition normalize_inputs (i : Reference.Inputs) : Reference.Inputs := Reference.mkInputs
 (normalize 1 (Reference.nreset i))
 (normalize 1 (Reference.nio_5Fin_5Fvalid i))
 (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F0 i))
 (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i))
 (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F2 i))
 (normalize 1 (Reference.nio_5Fout_5Fready i))
 (normalize 1 (Reference.nctrl_5Fsign i))
 (normalize 1 (Reference.nctrl_5FisW i))
 (normalize 1 (Reference.nctrl_5FisHi i)).
Lemma encoded_inputs_projection s i ghost_sign : project_inputs (encoded_leaves s i ghost_sign) = normalize_inputs i.
Proof. unfold project_inputs, encoded_leaves, normalize_inputs. rewrite !decode_encode. reflexivity. Qed.
Lemma encoded_leaf_13_size s i g : size (encoded_leaves s i g 13) = 3%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_18_size s i g : size (encoded_leaves s i g 18) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_20_size s i g : size (encoded_leaves s i g 20) = 129%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_33_size s i g : size (encoded_leaves s i g 33) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_38_size s i g : size (encoded_leaves s i g 38) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_40_size s i g : size (encoded_leaves s i g 40) = 64%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_43_size s i g : size (encoded_leaves s i g 43) = 65%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_46_size s i g : size (encoded_leaves s i g 46) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_47_size s i g : size (encoded_leaves s i g 47) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_51_size s i g : size (encoded_leaves s i g 51) = 6%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_445_size s i g : size (encoded_leaves s i g 445) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_446_size s i g : size (encoded_leaves s i g 446) = 3%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_447_size s i g : size (encoded_leaves s i g 447) = 6%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_475_size s i g : size (encoded_leaves s i g 475) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_476_size s i g : size (encoded_leaves s i g 476) = 64%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_1_size s i g : size (encoded_leaves s i g 1) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_3_size s i g : size (encoded_leaves s i g 3) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_4_size s i g : size (encoded_leaves s i g 4) = 64%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_5_size s i g : size (encoded_leaves s i g 5) = 64%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_6_size s i g : size (encoded_leaves s i g 6) = 64%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_7_size s i g : size (encoded_leaves s i g 7) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_10_size s i g : size (encoded_leaves s i g 10) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_11_size s i g : size (encoded_leaves s i g 11) = 1%nat.
Proof. apply encode_size. Qed.
Lemma encoded_leaf_12_size s i g : size (encoded_leaves s i g 12) = 1%nat.
Proof. apply encode_size. Qed.
Print Assumptions encoded_state_projection.
Print Assumptions encoded_inputs_projection.

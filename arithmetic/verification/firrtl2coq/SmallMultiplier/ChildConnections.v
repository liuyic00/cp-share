From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts GroundFrames ConnectionFacts.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.
Lemma pass_connect_bit invalid old before after stmts target source value b
 (cert : framed_write_certificate target (Sfcnct (Eid target) (Eref (Eid source))) stmts)
 (not_register : registers_frame target stmts = true)
 (different : source != target)
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target_value : VM.find target before = Some value)
 (source_value : VM.find source old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before stmts = Some after) :
 VM.find target after = Some (Gval (Fuint 1) [::b]).
Proof.
 eapply pass_framed_write_value; [exact cert|exact not_register|exact typed|exact target_value| |exact ran].
 intros position initial final found step.
 eapply bidirectional_eid_target with (old:=old) (before:=initial) (after:=final) (source:=source) (value:=Gval (Fuint 1) [::b]); [exact different| | | |].
 - cbn [eval_type_of_ref]. rewrite found. cbn. rewrite typed. reflexivity.
 - cbn [eval_href_with_memory]. exact source_value.
 - change (adapt_hvalue_as_type (Gval (Fuint 1) [::b]) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) [::b])).
   destruct b; reflexivity.
 - eapply one_statement_ref; [reflexivity|exact step].
Qed.
(* Generated child output certificates. *)
Lemma child0_output4_certificate : framed_write_certificate 4
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 4) (@Eref VarOrder.T (@Eid VarOrder.T 25))) generated_module_0_stmts_0.
Proof. unfold generated_module_0_stmts_0.
 do 21 (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma child0_output4_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find 4 before = Some value)
 (source : VM.find 25 old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 4 after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact child0_output4_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.
Lemma child0_output5_certificate : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 26))) generated_module_0_stmts_0.
Proof. unfold generated_module_0_stmts_0.
 do 22 (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma child0_output5_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find 5 before = Some value)
 (source : VM.find 26 old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_0_stmts_0 = Some after) :
 VM.find 5 after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact child0_output5_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.
Lemma child1_output5_certificate : framed_write_certificate 5
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 5) (@Eref VarOrder.T (@Eid VarOrder.T 33))) generated_module_1_stmts_0.
Proof. unfold generated_module_1_stmts_0.
 do 28 (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma child1_output5_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find 5 before = Some value)
 (source : VM.find 33 old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_1_stmts_0 = Some after) :
 VM.find 5 after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact child1_output5_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.
Lemma child1_output6_certificate : framed_write_certificate 6
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 6) (@Eref VarOrder.T (@Eid VarOrder.T 34))) generated_module_1_stmts_0.
Proof. unfold generated_module_1_stmts_0.
 do 29 (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma child1_output6_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find 6 before = Some value)
 (source : VM.find 34 old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_1_stmts_0 = Some after) :
 VM.find 6 after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact child1_output6_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.
Lemma child2_output7_certificate : framed_write_certificate 7
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 7) (@Eref VarOrder.T (@Eid VarOrder.T 41))) generated_module_2_stmts_0.
Proof. unfold generated_module_2_stmts_0.
 do 34 (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma child2_output7_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find 7 before = Some value)
 (source : VM.find 41 old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 7 after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact child2_output7_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.
Lemma child2_output8_certificate : framed_write_certificate 8
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 8) (@Eref VarOrder.T (@Eid VarOrder.T 42))) generated_module_2_stmts_0.
Proof. unfold generated_module_2_stmts_0.
 do 35 (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma child2_output8_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find 8 before = Some value)
 (source : VM.find 42 old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 8 after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact child2_output8_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.
Lemma child2_output9_certificate : framed_write_certificate 9
 (@Sfcnct VarOrder.T (@Eid VarOrder.T 9) (@Eref VarOrder.T (@Eid VarOrder.T 43))) generated_module_2_stmts_0.
Proof. unfold generated_module_2_stmts_0.
 do 36 (apply framed_write_later; [vm_compute;reflexivity|]).
 apply framed_write_here; vm_compute;reflexivity. Qed.
Lemma child2_output9_pass invalid old before after value b
 (typed : type_of_val value = Gtyp (Fuint 1))
 (target : VM.find 9 before = Some value)
 (source : VM.find 43 old = Some (Gval (Fuint 1) [::b]))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 VM.find 9 after = Some (Gval (Fuint 1) [::b]).
Proof. eapply pass_connect_bit; [exact child2_output9_certificate|vm_compute;reflexivity|reflexivity|exact typed|exact target|exact source|exact ran]. Qed.

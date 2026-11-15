From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import StatementFacts PortFieldFacts FieldStatementFacts FieldTypes FieldConnections FieldTypePreservation.
From SmallMultiplier Require Import Model FieldCertificateCheck.
Local Open Scope N_scope.
Definition field_2_10_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_2_10_0_certificate : field_write_certificate 10 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 0) field_2_10_0_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_10_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_10_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_10_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_10_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 10 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_10_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_10_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_2_10_1_certificate : field_write_certificate 10 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 1) field_2_10_1_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_10_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_10_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_10_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_10_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 10 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_10_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_10_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 2)).
Lemma field_2_10_2_certificate : field_write_certificate 10 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 2) field_2_10_2_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_10_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_10_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_10_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_10_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 10 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_10_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_10_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 3)).
Lemma field_2_10_3_certificate : field_write_certificate 10 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 3) field_2_10_3_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_10_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_10_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_10_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_10_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 10 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_10_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_10_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 4)).
Lemma field_2_10_4_certificate : field_write_certificate 10 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 4) field_2_10_4_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_10_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_10_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_10_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_10_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 10 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_10_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_11_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_2_11_0_certificate : field_write_certificate 11 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 0) field_2_11_0_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_11_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_11_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_11_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_11_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 11 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_11_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_11_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_2_11_1_certificate : field_write_certificate 11 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 1) field_2_11_1_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_11_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_11_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_11_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_11_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 11 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_11_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_11_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 38)).
Lemma field_2_11_2_certificate : field_write_certificate 11 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 2) field_2_11_2_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_11_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_11_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_11_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_11_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 11 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_11_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_11_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 39)).
Lemma field_2_11_3_certificate : field_write_certificate 11 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 3) field_2_11_3_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_11_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_11_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_11_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_11_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 11 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_11_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_2_11_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 40)).
Lemma field_2_11_4_certificate : field_write_certificate 11 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 4) field_2_11_4_rhs) generated_module_2_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_2_11_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_2_11_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_2_11_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_2_11_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_2_stmts_0 = Some after) :
 interface_field 11 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_2_11_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_7_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_7_0_certificate : field_write_certificate 7 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 0) field_3_7_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_7_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_7_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_7_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 7 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_7_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 7 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_7_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_7_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_7_1_certificate : field_write_certificate 7 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 1) field_3_7_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_7_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_7_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_7_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 7 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_7_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 7 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_7_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_7_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 201)).
Lemma field_3_7_2_certificate : field_write_certificate 7 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 2) field_3_7_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_7_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_7_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_7_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 7 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_7_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 7 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_7_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_7_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 203)).
Lemma field_3_7_3_certificate : field_write_certificate 7 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 3) field_3_7_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_7_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_7_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_7_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 7 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_7_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 7 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_7_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_8_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_8_0_certificate : field_write_certificate 8 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 0) field_3_8_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_8_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_8_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_8_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 8 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_8_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 8 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_8_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_8_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_8_1_certificate : field_write_certificate 8 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 1) field_3_8_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_8_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_8_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_8_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 8 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_8_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 8 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_8_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_8_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 205)).
Lemma field_3_8_2_certificate : field_write_certificate 8 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 2) field_3_8_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_8_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_8_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_8_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 8 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_8_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 8 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_8_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_8_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 207)).
Lemma field_3_8_3_certificate : field_write_certificate 8 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 3) field_3_8_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_8_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_8_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_8_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 8 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_8_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 8 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_8_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_9_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_9_0_certificate : field_write_certificate 9 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 0) field_3_9_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_9_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_9_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_9_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 9 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_9_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 9 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_9_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_9_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_9_1_certificate : field_write_certificate 9 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 1) field_3_9_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_9_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_9_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_9_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 9 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_9_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 9 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_9_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_9_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 209)).
Lemma field_3_9_2_certificate : field_write_certificate 9 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 2) field_3_9_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_9_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_9_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_9_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 9 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_9_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 9 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_9_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_9_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 211)).
Lemma field_3_9_3_certificate : field_write_certificate 9 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 3) field_3_9_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_9_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_9_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_9_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 9 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_9_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 9 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_9_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_9_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 213)).
Lemma field_3_9_4_certificate : field_write_certificate 9 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 4) field_3_9_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_9_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_9_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_9_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 9 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_9_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 9 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_9_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_10_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_10_0_certificate : field_write_certificate 10 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 0) field_3_10_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_10_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_10_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_10_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_10_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 10 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_10_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_10_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_10_1_certificate : field_write_certificate 10 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 1) field_3_10_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_10_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_10_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_10_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_10_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 10 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_10_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_10_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 215)).
Lemma field_3_10_2_certificate : field_write_certificate 10 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 2) field_3_10_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_10_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_10_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_10_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_10_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 10 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_10_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_10_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 217)).
Lemma field_3_10_3_certificate : field_write_certificate 10 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 3) field_3_10_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_10_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_10_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_10_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_10_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 10 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_10_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_10_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 219)).
Lemma field_3_10_4_certificate : field_write_certificate 10 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 4) field_3_10_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_10_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_10_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_10_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 10 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_10_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 10 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_10_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_11_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_11_0_certificate : field_write_certificate 11 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 0) field_3_11_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_11_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_11_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_11_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_11_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 11 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_11_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_11_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_11_1_certificate : field_write_certificate 11 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 1) field_3_11_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_11_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_11_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_11_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_11_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 11 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_11_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_11_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 221)).
Lemma field_3_11_2_certificate : field_write_certificate 11 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 2) field_3_11_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_11_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_11_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_11_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_11_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 11 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_11_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_11_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 223)).
Lemma field_3_11_3_certificate : field_write_certificate 11 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 3) field_3_11_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_11_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_11_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_11_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_11_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 11 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_11_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_11_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 225)).
Lemma field_3_11_4_certificate : field_write_certificate 11 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 4) field_3_11_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_11_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_11_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_11_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_11_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 11 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_11_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_11_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 227)).
Lemma field_3_11_5_certificate : field_write_certificate 11 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 5) field_3_11_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_11_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_11_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_11_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_11_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 11 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_11_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_11_6_rhs : @hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 1) [::false]).
Lemma field_3_11_6_certificate : field_write_certificate 11 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 6) field_3_11_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_11_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_11_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_11_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 11 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_11_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 11 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_11_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_12_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_12_0_certificate : field_write_certificate 12 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 0) field_3_12_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_12_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_12_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_12_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 12 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_12_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 12 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_12_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_12_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_12_1_certificate : field_write_certificate 12 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 1) field_3_12_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_12_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_12_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_12_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 12 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_12_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 12 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_12_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_12_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 229)).
Lemma field_3_12_2_certificate : field_write_certificate 12 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 2) field_3_12_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_12_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_12_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_12_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 12 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_12_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 12 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_12_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_12_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 231)).
Lemma field_3_12_3_certificate : field_write_certificate 12 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 3) field_3_12_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_12_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_12_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_12_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 12 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_12_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 12 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_12_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_12_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 233)).
Lemma field_3_12_4_certificate : field_write_certificate 12 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 4) field_3_12_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_12_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_12_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_12_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 12 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_12_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 12 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_12_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_12_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 235)).
Lemma field_3_12_5_certificate : field_write_certificate 12 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 5) field_3_12_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_12_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_12_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_12_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 12 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_12_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 12 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_12_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_12_6_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 314)).
Lemma field_3_12_6_certificate : field_write_certificate 12 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 6) field_3_12_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_12_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_12_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_12_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 12 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_12_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 12 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_12_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_13_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_13_0_certificate : field_write_certificate 13 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 0) field_3_13_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_13_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_13_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_13_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 13 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_13_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 13 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_13_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_13_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_13_1_certificate : field_write_certificate 13 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 1) field_3_13_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_13_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_13_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_13_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 13 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_13_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 13 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_13_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_13_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 237)).
Lemma field_3_13_2_certificate : field_write_certificate 13 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 2) field_3_13_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_13_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_13_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_13_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 13 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_13_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 13 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_13_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_13_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 239)).
Lemma field_3_13_3_certificate : field_write_certificate 13 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 3) field_3_13_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_13_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_13_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_13_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 13 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_13_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 13 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_13_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_13_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 241)).
Lemma field_3_13_4_certificate : field_write_certificate 13 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 4) field_3_13_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_13_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_13_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_13_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 13 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_13_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 13 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_13_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_13_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 243)).
Lemma field_3_13_5_certificate : field_write_certificate 13 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 5) field_3_13_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_13_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_13_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_13_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 13 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_13_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 13 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_13_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_13_6_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 317)).
Lemma field_3_13_6_certificate : field_write_certificate 13 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 6) field_3_13_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_13_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_13_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_13_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 13 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_13_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 13 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_13_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_14_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_14_0_certificate : field_write_certificate 14 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 0) field_3_14_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_14_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_14_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_14_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 14 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_14_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 14 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_14_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_14_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_14_1_certificate : field_write_certificate 14 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 1) field_3_14_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_14_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_14_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_14_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 14 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_14_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 14 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_14_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_14_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 247)).
Lemma field_3_14_2_certificate : field_write_certificate 14 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 2) field_3_14_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_14_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_14_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_14_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 14 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_14_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 14 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_14_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_14_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 249)).
Lemma field_3_14_3_certificate : field_write_certificate 14 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 3) field_3_14_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_14_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_14_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_14_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 14 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_14_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 14 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_14_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_14_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 251)).
Lemma field_3_14_4_certificate : field_write_certificate 14 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 4) field_3_14_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_14_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_14_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_14_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 14 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_14_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 14 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_14_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_14_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 253)).
Lemma field_3_14_5_certificate : field_write_certificate 14 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 5) field_3_14_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_14_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_14_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_14_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 14 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_14_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 14 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_14_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_14_6_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 320)).
Lemma field_3_14_6_certificate : field_write_certificate 14 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 6) field_3_14_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_14_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_14_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_14_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 14 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_14_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 14 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_14_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_15_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_15_0_certificate : field_write_certificate 15 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 0) field_3_15_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_15_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_15_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_15_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 15 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_15_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 15 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_15_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_15_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_15_1_certificate : field_write_certificate 15 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 1) field_3_15_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_15_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_15_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_15_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 15 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_15_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 15 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_15_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_15_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 257)).
Lemma field_3_15_2_certificate : field_write_certificate 15 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 2) field_3_15_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_15_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_15_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_15_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 15 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_15_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 15 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_15_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_15_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 259)).
Lemma field_3_15_3_certificate : field_write_certificate 15 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 3) field_3_15_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_15_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_15_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_15_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 15 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_15_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 15 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_15_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_15_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 261)).
Lemma field_3_15_4_certificate : field_write_certificate 15 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 4) field_3_15_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_15_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_15_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_15_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 15 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_15_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 15 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_15_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_15_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 263)).
Lemma field_3_15_5_certificate : field_write_certificate 15 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 5) field_3_15_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_15_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_15_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_15_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 15 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_15_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 15 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_15_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_15_6_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 323)).
Lemma field_3_15_6_certificate : field_write_certificate 15 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 6) field_3_15_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_15_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_15_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_15_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 15 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_15_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 15 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_15_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_16_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_16_0_certificate : field_write_certificate 16 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 0) field_3_16_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_16_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_16_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_16_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 16 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_16_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 16 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_16_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_16_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_16_1_certificate : field_write_certificate 16 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 1) field_3_16_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_16_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_16_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_16_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 16 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_16_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 16 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_16_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_16_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 265)).
Lemma field_3_16_2_certificate : field_write_certificate 16 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 2) field_3_16_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_16_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_16_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_16_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 16 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_16_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 16 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_16_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_16_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 267)).
Lemma field_3_16_3_certificate : field_write_certificate 16 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 3) field_3_16_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_16_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_16_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_16_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 16 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_16_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 16 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_16_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_16_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 269)).
Lemma field_3_16_4_certificate : field_write_certificate 16 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 4) field_3_16_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_16_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_16_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_16_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 16 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_16_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 16 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_16_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_16_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 271)).
Lemma field_3_16_5_certificate : field_write_certificate 16 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 5) field_3_16_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_16_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_16_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_16_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 16 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_16_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 16 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_16_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_16_6_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 326)).
Lemma field_3_16_6_certificate : field_write_certificate 16 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 6) field_3_16_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_16_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_16_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_16_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 16 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_16_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 16 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_16_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_17_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_17_0_certificate : field_write_certificate 17 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 0) field_3_17_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_17_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_17_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_17_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 17 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_17_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 17 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_17_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_17_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_17_1_certificate : field_write_certificate 17 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 1) field_3_17_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_17_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_17_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_17_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 17 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_17_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 17 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_17_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_17_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 273)).
Lemma field_3_17_2_certificate : field_write_certificate 17 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 2) field_3_17_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_17_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_17_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_17_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 17 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_17_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 17 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_17_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_17_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 275)).
Lemma field_3_17_3_certificate : field_write_certificate 17 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 3) field_3_17_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_17_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_17_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_17_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 17 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_17_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 17 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_17_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_17_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 277)).
Lemma field_3_17_4_certificate : field_write_certificate 17 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 4) field_3_17_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_17_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_17_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_17_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 17 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_17_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 17 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_17_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_17_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 279)).
Lemma field_3_17_5_certificate : field_write_certificate 17 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 5) field_3_17_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_17_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_17_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_17_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 17 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_17_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 17 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_17_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_17_6_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 329)).
Lemma field_3_17_6_certificate : field_write_certificate 17 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 6) field_3_17_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_17_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_17_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_17_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 17 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_17_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 17 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_17_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_18_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_18_0_certificate : field_write_certificate 18 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 0) field_3_18_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_18_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_18_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_18_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 18 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_18_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 18 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_18_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_18_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_18_1_certificate : field_write_certificate 18 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 1) field_3_18_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_18_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_18_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_18_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 18 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_18_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 18 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_18_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_18_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 281)).
Lemma field_3_18_2_certificate : field_write_certificate 18 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 2) field_3_18_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_18_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_18_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_18_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 18 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_18_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 18 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_18_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_18_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 283)).
Lemma field_3_18_3_certificate : field_write_certificate 18 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 3) field_3_18_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_18_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_18_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_18_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 18 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_18_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 18 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_18_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_18_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 285)).
Lemma field_3_18_4_certificate : field_write_certificate 18 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 4) field_3_18_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_18_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_18_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_18_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 18 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_18_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 18 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_18_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_18_5_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 287)).
Lemma field_3_18_5_certificate : field_write_certificate 18 5 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 5) field_3_18_5_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_18_5_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 5) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 5) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_18_5_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_18_5_value invalid old before after ground value bits initial
 (initial_field : interface_field 18 5 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_18_5_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 18 5 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_18_5_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_18_6_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 332)).
Lemma field_3_18_6_certificate : field_write_certificate 18 6 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 6) field_3_18_6_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_18_6_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 6) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 6) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_18_6_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_18_6_value invalid old before after ground value bits initial
 (initial_field : interface_field 18 6 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_18_6_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 18 6 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_18_6_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_19_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_19_0_certificate : field_write_certificate 19 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 0) field_3_19_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_19_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_19_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_19_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 19 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_19_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 19 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_19_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_19_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_19_1_certificate : field_write_certificate 19 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 1) field_3_19_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_19_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_19_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_19_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 19 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_19_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 19 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_19_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_19_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 289)).
Lemma field_3_19_2_certificate : field_write_certificate 19 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 2) field_3_19_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_19_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_19_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_19_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 19 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_19_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 19 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_19_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_19_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 291)).
Lemma field_3_19_3_certificate : field_write_certificate 19 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 3) field_3_19_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_19_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_19_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_19_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 19 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_19_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 19 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_19_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_19_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 293)).
Lemma field_3_19_4_certificate : field_write_certificate 19 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 4) field_3_19_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_19_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_19_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_19_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 19 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_19_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 19 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_19_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_20_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_20_0_certificate : field_write_certificate 20 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 0) field_3_20_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_20_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_20_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_20_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 20 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_20_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 20 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_20_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_20_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_20_1_certificate : field_write_certificate 20 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 1) field_3_20_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_20_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_20_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_20_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 20 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_20_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 20 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_20_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_20_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 295)).
Lemma field_3_20_2_certificate : field_write_certificate 20 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 2) field_3_20_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_20_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_20_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_20_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 20 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_20_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 20 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_20_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_20_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 297)).
Lemma field_3_20_3_certificate : field_write_certificate 20 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 3) field_3_20_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_20_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_20_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_20_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 20 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_20_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 20 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_20_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_21_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_21_0_certificate : field_write_certificate 21 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 0) field_3_21_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_21_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_21_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_21_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 21 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_21_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 21 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_21_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_21_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_21_1_certificate : field_write_certificate 21 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 1) field_3_21_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_21_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_21_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_21_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 21 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_21_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 21 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_21_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_21_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 299)).
Lemma field_3_21_2_certificate : field_write_certificate 21 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 2) field_3_21_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_21_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_21_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_21_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 21 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_21_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 21 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_21_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_21_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 301)).
Lemma field_3_21_3_certificate : field_write_certificate 21 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 3) field_3_21_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_21_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_21_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_21_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 21 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_21_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 21 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_21_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_22_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_22_0_certificate : field_write_certificate 22 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 0) field_3_22_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_22_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_22_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_22_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 22 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_22_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 22 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_22_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_22_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_22_1_certificate : field_write_certificate 22 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 1) field_3_22_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_22_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_22_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_22_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 22 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_22_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 22 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_22_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_22_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 307)).
Lemma field_3_22_2_certificate : field_write_certificate 22 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 2) field_3_22_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_22_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_22_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_22_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 22 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_22_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 22 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_22_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_22_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 306)).
Lemma field_3_22_3_certificate : field_write_certificate 22 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 3) field_3_22_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_22_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_22_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_22_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 22 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_22_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 22 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_22_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_23_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_23_0_certificate : field_write_certificate 23 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 0) field_3_23_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_23_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_23_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_23_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 23 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_23_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 23 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_23_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_23_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_23_1_certificate : field_write_certificate 23 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 1) field_3_23_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_23_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_23_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_23_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 23 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_23_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 23 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_23_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_23_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 309)).
Lemma field_3_23_2_certificate : field_write_certificate 23 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 2) field_3_23_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_23_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_23_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_23_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 23 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_23_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 23 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_23_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_23_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 308)).
Lemma field_3_23_3_certificate : field_write_certificate 23 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 3) field_3_23_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_23_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_23_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_23_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 23 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_23_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 23 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_23_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_24_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_24_0_certificate : field_write_certificate 24 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 0) field_3_24_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_24_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_24_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_24_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 24 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_24_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 24 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_24_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_24_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_24_1_certificate : field_write_certificate 24 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 1) field_3_24_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_24_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_24_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_24_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 24 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_24_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 24 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_24_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_24_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 311)).
Lemma field_3_24_2_certificate : field_write_certificate 24 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 2) field_3_24_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_24_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_24_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_24_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 24 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_24_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 24 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_24_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_24_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 310)).
Lemma field_3_24_3_certificate : field_write_certificate 24 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 3) field_3_24_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_24_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_24_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_24_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 24 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_24_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 24 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_24_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_25_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_25_0_certificate : field_write_certificate 25 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 0) field_3_25_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_25_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_25_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_25_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 25 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_25_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 25 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_25_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_25_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_25_1_certificate : field_write_certificate 25 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 1) field_3_25_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_25_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_25_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_25_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 25 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_25_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 25 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_25_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_25_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 313)).
Lemma field_3_25_2_certificate : field_write_certificate 25 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 2) field_3_25_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_25_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_25_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_25_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 25 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_25_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 25 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_25_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_25_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 312)).
Lemma field_3_25_3_certificate : field_write_certificate 25 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 3) field_3_25_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_25_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_25_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_25_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 25 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_25_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 25 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_25_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_26_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_26_0_certificate : field_write_certificate 26 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 0) field_3_26_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_26_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_26_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_26_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 26 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_26_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 26 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_26_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_26_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_26_1_certificate : field_write_certificate 26 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 1) field_3_26_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_26_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_26_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_26_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 26 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_26_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 26 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_26_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_26_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 316)).
Lemma field_3_26_2_certificate : field_write_certificate 26 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 2) field_3_26_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_26_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_26_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_26_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 26 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_26_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 26 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_26_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_26_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 315)).
Lemma field_3_26_3_certificate : field_write_certificate 26 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 3) field_3_26_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_26_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_26_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_26_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 26 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_26_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 26 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_26_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_27_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_27_0_certificate : field_write_certificate 27 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 0) field_3_27_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_27_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_27_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_27_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 27 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_27_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 27 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_27_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_27_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_27_1_certificate : field_write_certificate 27 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 1) field_3_27_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_27_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_27_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_27_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 27 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_27_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 27 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_27_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_27_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 319)).
Lemma field_3_27_2_certificate : field_write_certificate 27 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 2) field_3_27_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_27_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_27_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_27_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 27 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_27_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 27 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_27_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_27_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 245)).
Lemma field_3_27_3_certificate : field_write_certificate 27 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 3) field_3_27_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_27_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_27_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_27_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 27 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_27_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 27 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_27_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_27_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 318)).
Lemma field_3_27_4_certificate : field_write_certificate 27 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 4) field_3_27_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_27_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_27_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_27_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 27 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_27_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 27 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_27_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_28_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_28_0_certificate : field_write_certificate 28 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 0) field_3_28_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_28_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_28_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_28_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 28 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_28_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 28 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_28_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_28_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_28_1_certificate : field_write_certificate 28 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 1) field_3_28_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_28_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_28_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_28_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 28 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_28_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 28 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_28_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_28_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 322)).
Lemma field_3_28_2_certificate : field_write_certificate 28 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 2) field_3_28_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_28_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_28_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_28_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 28 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_28_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 28 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_28_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_28_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 255)).
Lemma field_3_28_3_certificate : field_write_certificate 28 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 3) field_3_28_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_28_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_28_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_28_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 28 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_28_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 28 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_28_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_28_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 321)).
Lemma field_3_28_4_certificate : field_write_certificate 28 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 4) field_3_28_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_28_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_28_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_28_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 28 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_28_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 28 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_28_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_29_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_29_0_certificate : field_write_certificate 29 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 0) field_3_29_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_29_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_29_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_29_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 29 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_29_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 29 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_29_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_29_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_29_1_certificate : field_write_certificate 29 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 1) field_3_29_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_29_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_29_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_29_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 29 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_29_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 29 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_29_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_29_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 325)).
Lemma field_3_29_2_certificate : field_write_certificate 29 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 2) field_3_29_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_29_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_29_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_29_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 29 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_29_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 29 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_29_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_29_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 324)).
Lemma field_3_29_3_certificate : field_write_certificate 29 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 3) field_3_29_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_29_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_29_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_29_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 29 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_29_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 29 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_29_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_30_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_30_0_certificate : field_write_certificate 30 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 0) field_3_30_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_30_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_30_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_30_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 30 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_30_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 30 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_30_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_30_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_30_1_certificate : field_write_certificate 30 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 1) field_3_30_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_30_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_30_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_30_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 30 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_30_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 30 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_30_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_30_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 328)).
Lemma field_3_30_2_certificate : field_write_certificate 30 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 2) field_3_30_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_30_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_30_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_30_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 30 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_30_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 30 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_30_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_30_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 327)).
Lemma field_3_30_3_certificate : field_write_certificate 30 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 3) field_3_30_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_30_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_30_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_30_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 30 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_30_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 30 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_30_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_31_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_31_0_certificate : field_write_certificate 31 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 0) field_3_31_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_31_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_31_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_31_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 31 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_31_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 31 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_31_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_31_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_31_1_certificate : field_write_certificate 31 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 1) field_3_31_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_31_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_31_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_31_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 31 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_31_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 31 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_31_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_31_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 331)).
Lemma field_3_31_2_certificate : field_write_certificate 31 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 2) field_3_31_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_31_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_31_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_31_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 31 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_31_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 31 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_31_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_31_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 330)).
Lemma field_3_31_3_certificate : field_write_certificate 31 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 3) field_3_31_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_31_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_31_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_31_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 31 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_31_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 31 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_31_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_32_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_32_0_certificate : field_write_certificate 32 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 0) field_3_32_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_32_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_32_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_32_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 32 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_32_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 32 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_32_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_32_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_32_1_certificate : field_write_certificate 32 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 1) field_3_32_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_32_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_32_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_32_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 32 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_32_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 32 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_32_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_32_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 334)).
Lemma field_3_32_2_certificate : field_write_certificate 32 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 2) field_3_32_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_32_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_32_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_32_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 32 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_32_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 32 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_32_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_32_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 333)).
Lemma field_3_32_3_certificate : field_write_certificate 32 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 3) field_3_32_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_32_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_32_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_32_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 32 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_32_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 32 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_32_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_33_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_33_0_certificate : field_write_certificate 33 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 0) field_3_33_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_33_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_33_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_33_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 33 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_33_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 33 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_33_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_33_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_33_1_certificate : field_write_certificate 33 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 1) field_3_33_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_33_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_33_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_33_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 33 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_33_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 33 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_33_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_33_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 337)).
Lemma field_3_33_2_certificate : field_write_certificate 33 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 2) field_3_33_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_33_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_33_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_33_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 33 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_33_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 33 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_33_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_33_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 335)).
Lemma field_3_33_3_certificate : field_write_certificate 33 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 3) field_3_33_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_33_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_33_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_33_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 33 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_33_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 33 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_33_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_33_4_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 336)).
Lemma field_3_33_4_certificate : field_write_certificate 33 4 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 4) field_3_33_4_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_33_4_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 4) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 4) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_33_4_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_33_4_value invalid old before after ground value bits initial
 (initial_field : interface_field 33 4 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_33_4_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 33 4 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_33_4_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_34_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_34_0_certificate : field_write_certificate 34 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 0) field_3_34_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_34_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_34_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_34_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 34 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_34_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 34 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_34_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_34_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_34_1_certificate : field_write_certificate 34 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 1) field_3_34_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_34_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_34_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_34_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 34 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_34_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 34 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_34_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_34_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 339)).
Lemma field_3_34_2_certificate : field_write_certificate 34 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 2) field_3_34_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_34_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_34_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_34_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 34 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_34_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 34 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_34_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_34_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 338)).
Lemma field_3_34_3_certificate : field_write_certificate 34 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 3) field_3_34_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_34_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_34_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_34_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 34 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_34_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 34 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_34_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_35_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_35_0_certificate : field_write_certificate 35 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 0) field_3_35_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_35_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_35_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_35_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 35 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_35_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 35 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_35_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_35_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_35_1_certificate : field_write_certificate 35 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 1) field_3_35_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_35_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_35_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_35_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 35 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_35_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 35 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_35_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_35_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 341)).
Lemma field_3_35_2_certificate : field_write_certificate 35 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 2) field_3_35_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_35_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_35_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_35_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 35 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_35_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 35 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_35_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_35_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 340)).
Lemma field_3_35_3_certificate : field_write_certificate 35 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 3) field_3_35_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_35_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_35_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_35_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 35 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_35_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 35 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_35_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_36_0_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Lemma field_3_36_0_certificate : field_write_certificate 36 0 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 0) field_3_36_0_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_36_0_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 0) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 0) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_36_0_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_36_0_value invalid old before after ground value bits initial
 (initial_field : interface_field 36 0 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_36_0_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 36 0 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_36_0_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_36_1_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Lemma field_3_36_1_certificate : field_write_certificate 36 1 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 1) field_3_36_1_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_36_1_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 1) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 1) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_36_1_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_36_1_value invalid old before after ground value bits initial
 (initial_field : interface_field 36 1 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_36_1_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 36 1 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_36_1_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_36_2_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 303)).
Lemma field_3_36_2_certificate : field_write_certificate 36 2 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 2) field_3_36_2_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_36_2_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 2) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 2) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_36_2_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_36_2_value invalid old before after ground value bits initial
 (initial_field : interface_field 36 2 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_36_2_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 36 2 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_36_2_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.
Definition field_3_36_3_rhs : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 342)).
Lemma field_3_36_3_certificate : field_write_certificate 36 3 (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 3) field_3_36_3_rhs) generated_module_3_stmts_0.
Proof. apply checked_field_write_sound. vm_compute. reflexivity. Qed.
Lemma field_3_36_3_type invalid old before after ground
 (initial_type : eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 3) before = Some (Gtyp ground))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 eval_type_of_ref (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 3) after = Some (Gtyp ground).
Proof. eapply pass_field_connect_type; [exact field_3_36_3_certificate|vm_compute;reflexivity|exact initial_type|reflexivity|exact ran]. Qed.
Lemma field_3_36_3_value invalid old before after ground value bits initial
 (initial_field : interface_field 36 3 before = Some initial)
 (initial_type : type_of_val initial = Gtyp ground)
 (evaluated : eval_hfexpr_with_memory empty_memory_map field_3_36_3_rhs old old = Some value)
 (adapted : adapt_hvalue_as_type value (Gtyp ground) = Some (Gval ground bits))
 (ran : value_iter_with_memory_policy invalid empty_memory_map old false before generated_module_3_stmts_0 = Some after) :
 interface_field 36 3 after = Some (Gval ground bits).
Proof. eapply pass_field_connect_value; [exact field_3_36_3_certificate|vm_compute;reflexivity|exact initial_field|exact initial_type|exact evaluated|exact adapted|reflexivity|exact ran]. Qed.

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import BundleFacts PortFieldFacts.

Definition field_type_lookup (field : VarOrder.T) := fix aux (fields : ffield) : option ftype :=
 match fields with Fnil => None | Fflips id flip ty rest =>
 if field == id then Some ty else aux rest end.
Definition type_field field ty := match ty with Btyp fields => field_type_lookup field fields | _ => None end.
Lemma bundle_lookup_type field bundle :
 option_map type_of_val (bundle_lookup field bundle) = field_type_lookup field (type_of_bundle_val bundle).
Proof.
 induction bundle as [|id flip value rest IH]; [reflexivity|].
 cbn [bundle_lookup type_of_bundle_val field_type_lookup].
 destruct (field == id); [reflexivity|exact IH].
Qed.
Lemma undef_bundle_lookup_type field fields undef
 (typed : forall ty, type_of_val (undef ty) = ty) :
 option_map type_of_val (bundle_lookup field (create_undef_bundle_value undef fields)) = field_type_lookup field fields.
Proof.
 induction fields as [|id flip ty rest IH]; [reflexivity|].
 cbn [create_undef_bundle_value bundle_lookup field_type_lookup].
 destruct (field == id); [cbn [option_map]; rewrite typed; reflexivity|exact IH].
Qed.
Lemma value_field_type field value :
 option_map type_of_val (value_field field value) = type_field field (type_of_val value).
Proof.
 destruct value as [gt bits|ty array|bundle|ty|ty|ty]; try reflexivity.
 - apply bundle_lookup_type.
 - destruct ty; try reflexivity. apply undef_bundle_lookup_type. reflexivity.
 - destruct ty; try reflexivity. apply undef_bundle_lookup_type. reflexivity.
 - destruct ty; try reflexivity. apply undef_bundle_lookup_type. reflexivity.
Qed.
Lemma interface_field_type instance field env :
 eval_type_of_ref (Esubfield (Eid instance) field) env =
 option_map type_of_val (interface_field instance field env).
Proof.
 unfold interface_field. cbn [eval_type_of_ref].
 destruct (VM.find instance env) as [value|]; [|reflexivity].
 cbn [option_map]. rewrite value_field_type. reflexivity.
Qed.
Print Assumptions interface_field_type.

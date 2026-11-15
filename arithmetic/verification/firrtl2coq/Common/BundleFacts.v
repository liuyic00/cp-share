From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Definition bundle_lookup (field : VarOrder.T) := fix aux (bundle : bundle_value) : option hvalue :=
 match bundle with Bnil => None | Bflips id flip value rest =>
 if field == id then Some value else aux rest end.
Definition bundle_replace (field : VarOrder.T) (fn : hvalue -> option hvalue) := fix aux (bundle : bundle_value) : option bundle_value :=
 match bundle with Bnil => None | Bflips id flip value rest =>
 if field == id then option_map (fun next => Bflips id flip next rest) (fn value)
 else option_map (Bflips id flip value) (aux rest) end.
Definition value_field field value :=
 match convert_to_bundle_value value with Some bundle => bundle_lookup field bundle | None => None end.

Lemma bundle_replace_other field watched fn before after
 (different : watched <> field)
 (replaced : bundle_replace field fn before = Some after) :
 bundle_lookup watched after = bundle_lookup watched before.
Proof.
 revert after replaced. induction before as [|id flip value rest IH]; intros after replaced; [discriminate|].
 cbn [bundle_replace] in replaced. destruct (field == id) eqn:Target.
 - destruct (fn value) as [next|]; inversion replaced; subst after.
   cbn [bundle_lookup]. destruct (watched == id) eqn:Watched; [|reflexivity].
   move/eqP: Target => Target. move/eqP: Watched => Watched. exfalso. apply different. congruence.
 - destruct (bundle_replace field fn rest) as [next|] eqn:Next; inversion replaced; subst after.
   cbn [bundle_lookup]. destruct (watched == id); [reflexivity|]. eapply IH; reflexivity.
Qed.
Lemma bundle_replace_constant field fn before after value
 (constant : forall old, fn old = Some value)
 (replaced : bundle_replace field fn before = Some after) :
 bundle_lookup field after = Some value.
Proof.
 revert after replaced. induction before as [|id flip old rest IH]; intros after replaced; [discriminate|].
 cbn [bundle_replace] in replaced. destruct (field == id) eqn:Target.
 - rewrite constant in replaced. inversion replaced; subst after. cbn [bundle_lookup]. rewrite Target. reflexivity.
 - destruct (bundle_replace field fn rest) as [next|] eqn:Next; inversion replaced; subst after.
   cbn [bundle_lookup]. rewrite Target. eapply IH; reflexivity.
Qed.

Lemma repl_field_other instance field watched fn old new env result
 (different : watched <> field)
 (replaced : repl_val_part (Esubfield (Eid instance) field) fn old new env = Some result) :
 value_field watched result = value_field watched old.
Proof.
 change (match convert_to_bundle_value old with
 | Some bundle => option_map Bval (bundle_replace field (fun prior => fn prior new) bundle)
 | None => None end = Some result) in replaced.
 unfold value_field. destruct (convert_to_bundle_value old) as [bundle|] eqn:B; try discriminate.
 destruct (bundle_replace field (fun prior => fn prior new) bundle) as [next|] eqn:Next; inversion replaced; subst result.
 cbn [convert_to_bundle_value]. eapply bundle_replace_other; eassumption.
Qed.
Lemma repl_field_sink_constant instance field old ground bits env result
 (replaced : repl_val_part (Esubfield (Eid instance) field) (replace_writeable Sink) old (Gval ground bits) env = Some result) :
 value_field field result = Some (Gval ground bits).
Proof.
 change (match convert_to_bundle_value old with
 | Some bundle => option_map Bval (bundle_replace field (fun prior => replace_writeable Sink prior (Gval ground bits)) bundle)
 | None => None end = Some result) in replaced.
 unfold value_field. destruct (convert_to_bundle_value old) as [bundle|] eqn:B; try discriminate.
 destruct (bundle_replace field (fun prior => replace_writeable Sink prior (Gval ground bits)) bundle) as [next|] eqn:Next; inversion replaced; subst result.
 cbn [convert_to_bundle_value]. eapply bundle_replace_constant; [intros; reflexivity|exact Next].
Qed.
Print Assumptions repl_field_sink_constant.

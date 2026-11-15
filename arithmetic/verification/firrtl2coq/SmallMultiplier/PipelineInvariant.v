From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import GlobalStable GlobalWidths GlobalContracts GlobalOutput Compression8 CaptureNumbers ColumnUpdate PipelineCommit RuntimeWords ControlEquations ExpectedProduct.
Local Open Scope Z_scope.
Lemma captured_expected v (sizes:global_leaf_sizes v) :
 weighted_registers(captured_register_numbers v) mod 65536=to_Zpos(global_word_1296 v).
Proof.
 have A:global_word_2 v=from_N 8 (to_N(global_word_2 v)).
 { rewrite -(global_size_2 v sizes). symmetry. apply from_N_to_N. }
 have B:global_word_53 v=from_N 8 (to_N(global_word_53 v)).
 { rewrite -(global_size_53 v sizes). symmetry. apply from_N_to_N. }
 have Ab:N.lt (to_N(global_word_2 v)) 256.
 { have Bound:=to_Zpos_bounded(global_word_2 v). rewrite (global_size_2 v sizes) to_Zpos_N in Bound. change (Z.of_N(to_N(global_word_2 v))<256) in Bound. lia. }
 have Bb:N.lt (to_N(global_word_53 v)) 256.
 { have Bound:=to_Zpos_bounded(global_word_53 v). rewrite (global_size_53 v sizes) to_Zpos_N in Bound. change (Z.of_N(to_N(global_word_53 v))<256) in Bound. lia. }
 rewrite (captured_columns_product v _ _ sizes A B Ab Bb).
 symmetry. exact(expected_product_integer v _ _ A B Ab Bb).
Qed.
Lemma valid_next_sources v (sizes:global_leaf_sizes v)
 (active:is_zero(next_word_410 v)=false) :
 is_zero(global_word_56 v)=false \/ is_zero(global_word_58 v)=false.
Proof.
 destruct (one_bit_word _ (global_size_1 v sizes)) as [r R].
 destruct (one_bit_word _ (global_size_56 v sizes)) as [e E].
 destruct (one_bit_word _ (global_size_58 v sizes)) as [b B].
 rewrite (control_next_410 v r e b R E B) in active. rewrite E B.
 destruct r,e,b; vm_compute in active |- *; intuition discriminate.
Qed.
Lemma holding_next_disabled v (sizes:global_leaf_sizes v)
 (active:is_zero(next_word_419 v)=false) : is_zero(global_word_56 v)=true.
Proof.
 destruct (one_bit_word _ (global_size_1 v sizes)) as [r R].
 destruct (one_bit_word _ (global_size_56 v sizes)) as [e E].
 destruct (one_bit_word _ (global_size_58 v sizes)) as [b B].
 rewrite (control_next_419 v r e b R E B) in active. rewrite E.
 destruct r,e,b; vm_compute in active |- *; congruence.
Qed.
Definition pipeline_invariant (v:global_leaves) : Prop :=
 (is_zero(global_word_58 v)=false -> weighted_registers(global_register_numbers v) mod 65536=to_Zpos(global_word_57 v)) /\
 (is_zero(global_word_60 v)=false -> weighted_registers(global_register_numbers v) mod 65536=to_Zpos(global_word_59 v)).
Local Transparent global_word_57 global_word_58 global_word_59 global_word_60.
Theorem pipeline_invariant_step v (sizes:global_leaf_sizes v)
 (invariant:pipeline_invariant v) : pipeline_invariant(next_register_leaves v).
Proof.
 destruct invariant as [Product Holding]. split.
 - change (is_zero(next_word_410 v)=false -> weighted_registers(global_register_numbers(next_register_leaves v)) mod 65536=to_Zpos(next_word_408 v)).
   intros active. have Sources:=valid_next_sources v sizes active.
   rewrite (next_columns_weight v sizes) (expected_next v sizes).
   destruct (is_zero(global_word_56 v)) eqn:Enabled.
   + apply Product. destruct Sources as [Bad|Good]; [discriminate|exact Good].
   + exact(captured_expected v sizes).
 - change (is_zero(next_word_419 v)=false -> weighted_registers(global_register_numbers(next_register_leaves v)) mod 65536=to_Zpos(next_word_416 v)).
   intros active. have Disabled:=holding_next_disabled v sizes active.
   rewrite (next_columns_weight v sizes) Disabled (previous_next v sizes).
   symmetry. exact(global_output_weight v sizes).
Qed.
Theorem pipeline_invariant_reset v (sizes:global_leaf_sizes v)
 (reset:global_word_1 v=[::true]) : pipeline_invariant(next_register_leaves v).
Proof.
 destruct (one_bit_word _ (global_size_56 v sizes)) as [e E].
 destruct (one_bit_word _ (global_size_58 v sizes)) as [b B].
 split.
 - change (is_zero(next_word_410 v)=false -> weighted_registers(global_register_numbers(next_register_leaves v)) mod 65536=to_Zpos(next_word_408 v)).
   rewrite (control_next_410 v true e b reset E B). discriminate.
 - change (is_zero(next_word_419 v)=false -> weighted_registers(global_register_numbers(next_register_leaves v)) mod 65536=to_Zpos(next_word_416 v)).
   rewrite (control_next_419 v true e b reset E B). discriminate.
Qed.
Print Assumptions pipeline_invariant_step.
Print Assumptions pipeline_invariant_reset.

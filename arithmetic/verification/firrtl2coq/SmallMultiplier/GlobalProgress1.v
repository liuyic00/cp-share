From Coq Require Import NArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts PortFieldFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalWidthFacts GlobalNodeSteps GlobalFieldSteps GlobalScalarSteps GlobalSyncSteps GlobalLeaves.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalProgressTypes.
From SmallMultiplier Require Export GlobalProgress0.
Lemma global_progress_200 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 175 final=Some (Gval (Fuint 2) (global_word_200 v)).
Proof.
 eapply global_node_200_step.
 - exact (prior 198%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 199%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_201 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 176 final=Some (Gval (Fuint 1) (global_word_201 v)).
Proof.
 eapply global_node_201_step.
 - exact (prior 146%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_202 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 177 final=Some (Gval (Fuint 2) (global_word_202 v)).
Proof.
 eapply global_node_202_step.
 - exact (prior 200%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 201%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_203 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 178 final=Some (Gval (Fuint 1) (global_word_203 v)).
Proof.
 eapply global_node_203_step.
 - exact (prior 196%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_204 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 179 final=Some (Gval (Fuint 10) (global_word_204 v)).
Proof.
 eapply global_node_204_step.
 - exact (prior 195%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact (prior 203%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (12 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_205 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 180 final=Some (Gval (Fuint 12) (global_word_205 v)).
Proof.
 eapply global_node_205_step.
 - exact (prior 202%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 204%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_206 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 181 final=Some (Gval (Fuint 1) (global_word_206 v)).
Proof.
 eapply global_node_206_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_207 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 182 final=Some (Gval (Fuint 1) (global_word_207 v)).
Proof.
 eapply global_node_207_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_208 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 183 final=Some (Gval (Fuint 1) (global_word_208 v)).
Proof.
 eapply global_node_208_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_209 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 184 final=Some (Gval (Fuint 1) (global_word_209 v)).
Proof.
 eapply global_node_209_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_210 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 185 final=Some (Gval (Fuint 1) (global_word_210 v)).
Proof.
 eapply global_node_210_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_211 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 186 final=Some (Gval (Fuint 1) (global_word_211 v)).
Proof.
 eapply global_node_211_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_212 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 187 final=Some (Gval (Fuint 1) (global_word_212 v)).
Proof.
 eapply global_node_212_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_213 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 188 final=Some (Gval (Fuint 1) (global_word_213 v)).
Proof.
 eapply global_node_213_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_214 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 189 final=Some (Gval (Fuint 1) (global_word_214 v)).
Proof.
 eapply global_node_214_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_215 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 190 final=Some (Gval (Fuint 1) (global_word_215 v)).
Proof.
 eapply global_node_215_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_216 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 191 final=Some (Gval (Fuint 1) (global_word_216 v)).
Proof.
 eapply global_node_216_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_217 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 192 final=Some (Gval (Fuint 1) (global_word_217 v)).
Proof.
 eapply global_node_217_step.
 - exact (prior 205%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_218 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 193 final=Some (Gval (Fuint 1) (global_word_218 v)).
Proof.
 eapply global_node_218_step.
 - exact (prior 183%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_219 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 194 final=Some (Gval (Fuint 2) (global_word_219 v)).
Proof.
 eapply global_node_219_step.
 - exact (prior 218%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_220 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 195 final=Some (Gval (Fuint 1) (global_word_220 v)).
Proof.
 eapply global_node_220_step.
 - exact (prior 183%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_221 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 196 final=Some (Gval (Fuint 2) (global_word_221 v)).
Proof.
 eapply global_node_221_step.
 - exact (prior 219%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 220%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_222 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 197 final=Some (Gval (Fuint 1) (global_word_222 v)).
Proof.
 eapply global_node_222_step.
 - exact (prior 183%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (1 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_223 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 198 final=Some (Gval (Fuint 2) (global_word_223 v)).
Proof.
 eapply global_node_223_step.
 - exact (prior 221%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 222%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_224 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 199 final=Some (Gval (Fuint 1) (global_word_224 v)).
Proof.
 eapply global_node_224_step.
 - exact (prior 223%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_225 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 200 final=Some (Gval (Fuint 1) (global_word_225 v)).
Proof.
 eapply global_node_225_step.
 - exact (prior 223%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_226 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 202 final=Some (Gval (Fuint 1) (global_word_226 v)).
Proof.
 eapply global_node_226_step.
 - exact (prior 3%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 97%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_227 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 204 final=Some (Gval (Fuint 1) (global_word_227 v)).
Proof.
 eapply global_node_227_step.
 - exact (prior 133%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 4%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_228 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 206 final=Some (Gval (Fuint 1) (global_word_228 v)).
Proof.
 eapply global_node_228_step.
 - exact (prior 5%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 98%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_229 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 208 final=Some (Gval (Fuint 1) (global_word_229 v)).
Proof.
 eapply global_node_229_step.
 - exact (prior 134%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 6%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_230 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 210 final=Some (Gval (Fuint 1) (global_word_230 v)).
Proof.
 eapply global_node_230_step.
 - exact (prior 7%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 99%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_231 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 212 final=Some (Gval (Fuint 1) (global_word_231 v)).
Proof.
 eapply global_node_231_step.
 - exact (prior 135%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 8%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_232 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 214 final=Some (Gval (Fuint 1) (global_word_232 v)).
Proof.
 eapply global_node_232_step.
 - exact (prior 170%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 9%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_233 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 216 final=Some (Gval (Fuint 1) (global_word_233 v)).
Proof.
 eapply global_node_233_step.
 - exact (prior 10%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 100%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_234 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 218 final=Some (Gval (Fuint 1) (global_word_234 v)).
Proof.
 eapply global_node_234_step.
 - exact (prior 136%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 11%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_235 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 220 final=Some (Gval (Fuint 1) (global_word_235 v)).
Proof.
 eapply global_node_235_step.
 - exact (prior 171%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 12%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_236 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 222 final=Some (Gval (Fuint 1) (global_word_236 v)).
Proof.
 eapply global_node_236_step.
 - exact (prior 13%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 101%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_237 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 224 final=Some (Gval (Fuint 1) (global_word_237 v)).
Proof.
 eapply global_node_237_step.
 - exact (prior 137%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 14%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_238 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 226 final=Some (Gval (Fuint 1) (global_word_238 v)).
Proof.
 eapply global_node_238_step.
 - exact (prior 172%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 15%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_239 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 228 final=Some (Gval (Fuint 1) (global_word_239 v)).
Proof.
 eapply global_node_239_step.
 - exact (prior 206%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 16%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_240 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 230 final=Some (Gval (Fuint 1) (global_word_240 v)).
Proof.
 eapply global_node_240_step.
 - exact (prior 17%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 102%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_241 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 232 final=Some (Gval (Fuint 1) (global_word_241 v)).
Proof.
 eapply global_node_241_step.
 - exact (prior 138%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 18%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_242 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 234 final=Some (Gval (Fuint 1) (global_word_242 v)).
Proof.
 eapply global_node_242_step.
 - exact (prior 173%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 19%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_243 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 236 final=Some (Gval (Fuint 1) (global_word_243 v)).
Proof.
 eapply global_node_243_step.
 - exact (prior 207%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 20%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_244 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 238 final=Some (Gval (Fuint 1) (global_word_244 v)).
Proof.
 eapply global_node_244_step.
 - exact (prior 21%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 103%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_245 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 240 final=Some (Gval (Fuint 1) (global_word_245 v)).
Proof.
 eapply global_node_245_step.
 - exact (prior 139%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 22%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_246 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 242 final=Some (Gval (Fuint 1) (global_word_246 v)).
Proof.
 eapply global_node_246_step.
 - exact (prior 174%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 23%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_247 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 244 final=Some (Gval (Fuint 1) (global_word_247 v)).
Proof.
 eapply global_node_247_step.
 - exact (prior 208%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 24%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_248 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 246 final=Some (Gval (Fuint 1) (global_word_248 v)).
Proof.
 eapply global_node_248_step.
 - exact (prior 224%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 25%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_249 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 248 final=Some (Gval (Fuint 1) (global_word_249 v)).
Proof.
 eapply global_node_249_step.
 - exact (prior 26%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 104%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_250 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 250 final=Some (Gval (Fuint 1) (global_word_250 v)).
Proof.
 eapply global_node_250_step.
 - exact (prior 140%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 27%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_251 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 252 final=Some (Gval (Fuint 1) (global_word_251 v)).
Proof.
 eapply global_node_251_step.
 - exact (prior 175%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 28%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_252 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 254 final=Some (Gval (Fuint 1) (global_word_252 v)).
Proof.
 eapply global_node_252_step.
 - exact (prior 209%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 29%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_253 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 256 final=Some (Gval (Fuint 1) (global_word_253 v)).
Proof.
 eapply global_node_253_step.
 - exact (prior 225%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 30%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_254 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 258 final=Some (Gval (Fuint 1) (global_word_254 v)).
Proof.
 eapply global_node_254_step.
 - exact (prior 31%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 105%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_255 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 260 final=Some (Gval (Fuint 1) (global_word_255 v)).
Proof.
 eapply global_node_255_step.
 - exact (prior 141%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 32%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_256 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 262 final=Some (Gval (Fuint 1) (global_word_256 v)).
Proof.
 eapply global_node_256_step.
 - exact (prior 176%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 33%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_257 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 264 final=Some (Gval (Fuint 1) (global_word_257 v)).
Proof.
 eapply global_node_257_step.
 - exact (prior 210%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 34%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_258 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 266 final=Some (Gval (Fuint 1) (global_word_258 v)).
Proof.
 eapply global_node_258_step.
 - exact (prior 35%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 106%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_259 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 268 final=Some (Gval (Fuint 1) (global_word_259 v)).
Proof.
 eapply global_node_259_step.
 - exact (prior 142%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 36%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_260 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 270 final=Some (Gval (Fuint 1) (global_word_260 v)).
Proof.
 eapply global_node_260_step.
 - exact (prior 177%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 37%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_261 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 272 final=Some (Gval (Fuint 1) (global_word_261 v)).
Proof.
 eapply global_node_261_step.
 - exact (prior 211%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 38%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_262 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 274 final=Some (Gval (Fuint 1) (global_word_262 v)).
Proof.
 eapply global_node_262_step.
 - exact (prior 39%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 107%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_263 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 276 final=Some (Gval (Fuint 1) (global_word_263 v)).
Proof.
 eapply global_node_263_step.
 - exact (prior 143%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 40%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_264 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 278 final=Some (Gval (Fuint 1) (global_word_264 v)).
Proof.
 eapply global_node_264_step.
 - exact (prior 178%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 41%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_265 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 280 final=Some (Gval (Fuint 1) (global_word_265 v)).
Proof.
 eapply global_node_265_step.
 - exact (prior 212%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 42%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_266 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 282 final=Some (Gval (Fuint 1) (global_word_266 v)).
Proof.
 eapply global_node_266_step.
 - exact (prior 43%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 108%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_267 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 284 final=Some (Gval (Fuint 1) (global_word_267 v)).
Proof.
 eapply global_node_267_step.
 - exact (prior 144%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 44%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_268 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 286 final=Some (Gval (Fuint 1) (global_word_268 v)).
Proof.
 eapply global_node_268_step.
 - exact (prior 179%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 45%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_269 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 288 final=Some (Gval (Fuint 1) (global_word_269 v)).
Proof.
 eapply global_node_269_step.
 - exact (prior 213%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 46%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_270 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 290 final=Some (Gval (Fuint 1) (global_word_270 v)).
Proof.
 eapply global_node_270_step.
 - exact (prior 145%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 47%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_271 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 292 final=Some (Gval (Fuint 1) (global_word_271 v)).
Proof.
 eapply global_node_271_step.
 - exact (prior 180%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 48%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_272 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 294 final=Some (Gval (Fuint 1) (global_word_272 v)).
Proof.
 eapply global_node_272_step.
 - exact (prior 214%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 49%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_273 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 296 final=Some (Gval (Fuint 1) (global_word_273 v)).
Proof.
 eapply global_node_273_step.
 - exact (prior 181%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 50%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_274 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 298 final=Some (Gval (Fuint 1) (global_word_274 v)).
Proof.
 eapply global_node_274_step.
 - exact (prior 215%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 51%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_275 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 300 final=Some (Gval (Fuint 1) (global_word_275 v)).
Proof.
 eapply global_node_275_step.
 - exact (prior 182%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 52%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_276 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 302 final=Some (Gval (Fuint 1) (global_word_276 v)).
Proof.
 eapply global_node_276_step.
 - exact (prior 216%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 54%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_277 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 304 final=Some (Gval (Fuint 1) (global_word_277 v)).
Proof.
 eapply global_node_277_step.
 - exact (prior 217%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (15 <= level)%coq_nat; lia))).
 - exact (prior 55%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact (prior 56%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_278 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 2 final=Some (Gval (Fuint 1) (global_word_278 v)).
Proof.
 have Typed := types 278%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_278_step.
 - exact (prior 3%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_278 v sizes).
 - exact ran.
Qed.
Lemma global_progress_279 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 2 final=Some (Gval (Fuint 1) (global_word_279 v)).
Proof.
 apply (global_sync_279_link invalid snapshot final v); [eapply global_progress_278; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_280 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 19 final=Some (Gval (Fuint 1) (global_word_280 v)).
Proof.
 eapply global_node_280_step.
 - exact (prior 279%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_281 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 3 final=Some (Gval (Fuint 1) (global_word_281 v)).
Proof.
 have Typed := types 281%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_281_step.
 - exact (prior 4%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_281 v sizes).
 - exact ran.
Qed.
Lemma global_progress_282 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 3 final=Some (Gval (Fuint 1) (global_word_282 v)).
Proof.
 apply (global_sync_282_link invalid snapshot final v); [eapply global_progress_281; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_283 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 20 final=Some (Gval (Fuint 1) (global_word_283 v)).
Proof.
 eapply global_node_283_step.
 - exact (prior 282%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_284 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 21 final=Some (Gval (Fuint 1) (global_word_284 v)).
Proof.
 eapply global_node_284_step.
 - exact (prior 280%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 283%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_285 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 22 final=Some (Gval (Fuint 1) (global_word_285 v)).
Proof.
 eapply global_node_285_step.
 - exact (prior 280%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 283%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_286 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 23 final=Some (Gval (Fuint 2) (global_word_286 v)).
Proof.
 eapply global_node_286_step.
 - exact (prior 284%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 285%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_287 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 24 final=Some (Gval (Fuint 2) (global_word_287 v)).
Proof.
 eapply global_node_287_step.
 - exact (prior 286%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_288 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 25 final=Some (Gval (Fuint 1) (global_word_288 v)).
Proof.
 eapply global_node_288_step.
 - exact (prior 287%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_289.
Lemma global_connect_289_alias v : global_word_289 v = global_word_288 v.
Proof. unfold global_word_289, global_closed_289, global_expr_289, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_289.
Lemma global_progress_289 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 4 final=Some (Gval (Fuint 1) (global_word_289 v)).
Proof.
 have Typed := types 289%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_289_step.
 - exact (prior 288%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_289_alias. apply adapt_uint_same. exact (global_size_288 v sizes).
 - exact ran.
Qed.
Lemma global_progress_290 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 4 final=Some (Gval (Fuint 1) (global_word_290 v)).
Proof.
 apply (global_sync_290_link invalid snapshot final v); [eapply global_progress_289; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_291 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 305 final=Some (Gval (Fuint 1) (global_word_291 v)).
Proof.
 eapply global_node_291_step.
 - exact (prior 290%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_292 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 26 final=Some (Gval (Fuint 1) (global_word_292 v)).
Proof.
 eapply global_node_292_step.
 - exact (prior 287%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_293.
Lemma global_connect_293_alias v : global_word_293 v = global_word_292 v.
Proof. unfold global_word_293, global_closed_293, global_expr_293, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_293.
Lemma global_progress_293 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::7] 5 final=Some (Gval (Fuint 1) (global_word_293 v)).
Proof.
 have Typed := types 293%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_293_step.
 - exact (prior 292%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_293_alias. apply adapt_uint_same. exact (global_size_292 v sizes).
 - exact ran.
Qed.
Lemma global_progress_294 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 7 5 final=Some (Gval (Fuint 1) (global_word_294 v)).
Proof.
 apply (global_sync_294_link invalid snapshot final v); [eapply global_progress_293; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_295 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 306 final=Some (Gval (Fuint 1) (global_word_295 v)).
Proof.
 eapply global_node_295_step.
 - exact (prior 294%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_296 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 2 final=Some (Gval (Fuint 1) (global_word_296 v)).
Proof.
 have Typed := types 296%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_296_step.
 - exact (prior 5%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_296 v sizes).
 - exact ran.
Qed.
Lemma global_progress_297 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 2 final=Some (Gval (Fuint 1) (global_word_297 v)).
Proof.
 apply (global_sync_297_link invalid snapshot final v); [eapply global_progress_296; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_298 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 19 final=Some (Gval (Fuint 1) (global_word_298 v)).
Proof.
 eapply global_node_298_step.
 - exact (prior 297%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_299 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 3 final=Some (Gval (Fuint 1) (global_word_299 v)).
Proof.
 have Typed := types 299%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_299_step.
 - exact (prior 6%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_299 v sizes).
 - exact ran.
Qed.
Lemma global_progress_300 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 3 final=Some (Gval (Fuint 1) (global_word_300 v)).
Proof.
 apply (global_sync_300_link invalid snapshot final v); [eapply global_progress_299; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_301 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 20 final=Some (Gval (Fuint 1) (global_word_301 v)).
Proof.
 eapply global_node_301_step.
 - exact (prior 300%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_302 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 21 final=Some (Gval (Fuint 1) (global_word_302 v)).
Proof.
 eapply global_node_302_step.
 - exact (prior 298%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 301%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_303 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 22 final=Some (Gval (Fuint 1) (global_word_303 v)).
Proof.
 eapply global_node_303_step.
 - exact (prior 298%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 301%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_304 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 23 final=Some (Gval (Fuint 2) (global_word_304 v)).
Proof.
 eapply global_node_304_step.
 - exact (prior 302%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 303%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_305 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 24 final=Some (Gval (Fuint 2) (global_word_305 v)).
Proof.
 eapply global_node_305_step.
 - exact (prior 304%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_306 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 25 final=Some (Gval (Fuint 1) (global_word_306 v)).
Proof.
 eapply global_node_306_step.
 - exact (prior 305%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_307.
Lemma global_connect_307_alias v : global_word_307 v = global_word_306 v.
Proof. unfold global_word_307, global_closed_307, global_expr_307, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_307.
Lemma global_progress_307 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 4 final=Some (Gval (Fuint 1) (global_word_307 v)).
Proof.
 have Typed := types 307%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_307_step.
 - exact (prior 306%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_307_alias. apply adapt_uint_same. exact (global_size_306 v sizes).
 - exact ran.
Qed.
Lemma global_progress_308 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 4 final=Some (Gval (Fuint 1) (global_word_308 v)).
Proof.
 apply (global_sync_308_link invalid snapshot final v); [eapply global_progress_307; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_309 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 307 final=Some (Gval (Fuint 1) (global_word_309 v)).
Proof.
 eapply global_node_309_step.
 - exact (prior 308%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_310 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 26 final=Some (Gval (Fuint 1) (global_word_310 v)).
Proof.
 eapply global_node_310_step.
 - exact (prior 305%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_311.
Lemma global_connect_311_alias v : global_word_311 v = global_word_310 v.
Proof. unfold global_word_311, global_closed_311, global_expr_311, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_311.
Lemma global_progress_311 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::8] 5 final=Some (Gval (Fuint 1) (global_word_311 v)).
Proof.
 have Typed := types 311%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_311_step.
 - exact (prior 310%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_311_alias. apply adapt_uint_same. exact (global_size_310 v sizes).
 - exact ran.
Qed.
Lemma global_progress_312 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 8 5 final=Some (Gval (Fuint 1) (global_word_312 v)).
Proof.
 apply (global_sync_312_link invalid snapshot final v); [eapply global_progress_311; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_313 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 308 final=Some (Gval (Fuint 1) (global_word_313 v)).
Proof.
 eapply global_node_313_step.
 - exact (prior 312%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_314 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 4 final=Some (Gval (Fuint 1) (global_word_314 v)).
Proof.
 have Typed := types 314%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_314_step.
 - exact (prior 9%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_314 v sizes).
 - exact ran.
Qed.
Lemma global_progress_315 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 4 final=Some (Gval (Fuint 1) (global_word_315 v)).
Proof.
 apply (global_sync_315_link invalid snapshot final v); [eapply global_progress_314; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_316 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 25 final=Some (Gval (Fuint 1) (global_word_316 v)).
Proof.
 eapply global_node_316_step.
 - exact (prior 315%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_317 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 2 final=Some (Gval (Fuint 1) (global_word_317 v)).
Proof.
 have Typed := types 317%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_317_step.
 - exact (prior 7%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_317 v sizes).
 - exact ran.
Qed.
Lemma global_progress_318 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 2 final=Some (Gval (Fuint 1) (global_word_318 v)).
Proof.
 apply (global_sync_318_link invalid snapshot final v); [eapply global_progress_317; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_319 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 23 final=Some (Gval (Fuint 1) (global_word_319 v)).
Proof.
 eapply global_node_319_step.
 - exact (prior 318%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_320 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 3 final=Some (Gval (Fuint 1) (global_word_320 v)).
Proof.
 have Typed := types 320%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_320_step.
 - exact (prior 8%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_320 v sizes).
 - exact ran.
Qed.
Lemma global_progress_321 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 3 final=Some (Gval (Fuint 1) (global_word_321 v)).
Proof.
 apply (global_sync_321_link invalid snapshot final v); [eapply global_progress_320; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_322 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 24 final=Some (Gval (Fuint 1) (global_word_322 v)).
Proof.
 eapply global_node_322_step.
 - exact (prior 321%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_323 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 26 final=Some (Gval (Fuint 1) (global_word_323 v)).
Proof.
 eapply global_node_323_step.
 - exact (prior 319%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 322%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_324 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 28 final=Some (Gval (Fuint 1) (global_word_324 v)).
Proof.
 eapply global_node_324_step.
 - exact (prior 316%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 323%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_325 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 27 final=Some (Gval (Fuint 1) (global_word_325 v)).
Proof.
 eapply global_node_325_step.
 - exact (prior 319%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 322%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_326 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 29 final=Some (Gval (Fuint 1) (global_word_326 v)).
Proof.
 eapply global_node_326_step.
 - exact (prior 316%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 323%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_327 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 30 final=Some (Gval (Fuint 1) (global_word_327 v)).
Proof.
 eapply global_node_327_step.
 - exact (prior 325%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 326%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_328 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 31 final=Some (Gval (Fuint 2) (global_word_328 v)).
Proof.
 eapply global_node_328_step.
 - exact (prior 324%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 327%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_329 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 32 final=Some (Gval (Fuint 2) (global_word_329 v)).
Proof.
 eapply global_node_329_step.
 - exact (prior 328%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_330 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 33 final=Some (Gval (Fuint 1) (global_word_330 v)).
Proof.
 eapply global_node_330_step.
 - exact (prior 329%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_331.
Lemma global_connect_331_alias v : global_word_331 v = global_word_330 v.
Proof. unfold global_word_331, global_closed_331, global_expr_331, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_331.
Lemma global_progress_331 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 5 final=Some (Gval (Fuint 1) (global_word_331 v)).
Proof.
 have Typed := types 331%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_331_step.
 - exact (prior 330%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_331_alias. apply adapt_uint_same. exact (global_size_330 v sizes).
 - exact ran.
Qed.
Lemma global_progress_332 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 5 final=Some (Gval (Fuint 1) (global_word_332 v)).
Proof.
 apply (global_sync_332_link invalid snapshot final v); [eapply global_progress_331; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_333 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 309 final=Some (Gval (Fuint 1) (global_word_333 v)).
Proof.
 eapply global_node_333_step.
 - exact (prior 332%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_334 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 34 final=Some (Gval (Fuint 1) (global_word_334 v)).
Proof.
 eapply global_node_334_step.
 - exact (prior 329%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_335.
Lemma global_connect_335_alias v : global_word_335 v = global_word_334 v.
Proof. unfold global_word_335, global_closed_335, global_expr_335, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_335.
Lemma global_progress_335 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::9] 6 final=Some (Gval (Fuint 1) (global_word_335 v)).
Proof.
 have Typed := types 335%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_335_step.
 - exact (prior 334%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_335_alias. apply adapt_uint_same. exact (global_size_334 v sizes).
 - exact ran.
Qed.
Lemma global_progress_336 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 9 6 final=Some (Gval (Fuint 1) (global_word_336 v)).
Proof.
 apply (global_sync_336_link invalid snapshot final v); [eapply global_progress_335; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_337 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 310 final=Some (Gval (Fuint 1) (global_word_337 v)).
Proof.
 eapply global_node_337_step.
 - exact (prior 336%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_338 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 4 final=Some (Gval (Fuint 1) (global_word_338 v)).
Proof.
 have Typed := types 338%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_338_step.
 - exact (prior 12%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_338 v sizes).
 - exact ran.
Qed.
Lemma global_progress_339 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 4 final=Some (Gval (Fuint 1) (global_word_339 v)).
Proof.
 apply (global_sync_339_link invalid snapshot final v); [eapply global_progress_338; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_340 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 25 final=Some (Gval (Fuint 1) (global_word_340 v)).
Proof.
 eapply global_node_340_step.
 - exact (prior 339%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_341 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 2 final=Some (Gval (Fuint 1) (global_word_341 v)).
Proof.
 have Typed := types 341%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_341_step.
 - exact (prior 10%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_341 v sizes).
 - exact ran.
Qed.
Lemma global_progress_342 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 2 final=Some (Gval (Fuint 1) (global_word_342 v)).
Proof.
 apply (global_sync_342_link invalid snapshot final v); [eapply global_progress_341; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_343 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 23 final=Some (Gval (Fuint 1) (global_word_343 v)).
Proof.
 eapply global_node_343_step.
 - exact (prior 342%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_344 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 3 final=Some (Gval (Fuint 1) (global_word_344 v)).
Proof.
 have Typed := types 344%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_344_step.
 - exact (prior 11%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_344 v sizes).
 - exact ran.
Qed.
Lemma global_progress_345 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 3 final=Some (Gval (Fuint 1) (global_word_345 v)).
Proof.
 apply (global_sync_345_link invalid snapshot final v); [eapply global_progress_344; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_346 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 24 final=Some (Gval (Fuint 1) (global_word_346 v)).
Proof.
 eapply global_node_346_step.
 - exact (prior 345%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_347 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 26 final=Some (Gval (Fuint 1) (global_word_347 v)).
Proof.
 eapply global_node_347_step.
 - exact (prior 343%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 346%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_348 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 28 final=Some (Gval (Fuint 1) (global_word_348 v)).
Proof.
 eapply global_node_348_step.
 - exact (prior 340%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 347%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_349 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 27 final=Some (Gval (Fuint 1) (global_word_349 v)).
Proof.
 eapply global_node_349_step.
 - exact (prior 343%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 346%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_350 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 29 final=Some (Gval (Fuint 1) (global_word_350 v)).
Proof.
 eapply global_node_350_step.
 - exact (prior 340%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact (prior 347%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_351 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 30 final=Some (Gval (Fuint 1) (global_word_351 v)).
Proof.
 eapply global_node_351_step.
 - exact (prior 349%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact (prior 350%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_352 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 31 final=Some (Gval (Fuint 2) (global_word_352 v)).
Proof.
 eapply global_node_352_step.
 - exact (prior 348%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 351%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_353 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 32 final=Some (Gval (Fuint 2) (global_word_353 v)).
Proof.
 eapply global_node_353_step.
 - exact (prior 352%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_354 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 33 final=Some (Gval (Fuint 1) (global_word_354 v)).
Proof.
 eapply global_node_354_step.
 - exact (prior 353%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_355.
Lemma global_connect_355_alias v : global_word_355 v = global_word_354 v.
Proof. unfold global_word_355, global_closed_355, global_expr_355, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_355.
Lemma global_progress_355 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 5 final=Some (Gval (Fuint 1) (global_word_355 v)).
Proof.
 have Typed := types 355%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_355_step.
 - exact (prior 354%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_355_alias. apply adapt_uint_same. exact (global_size_354 v sizes).
 - exact ran.
Qed.
Lemma global_progress_356 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 5 final=Some (Gval (Fuint 1) (global_word_356 v)).
Proof.
 apply (global_sync_356_link invalid snapshot final v); [eapply global_progress_355; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_357 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 311 final=Some (Gval (Fuint 1) (global_word_357 v)).
Proof.
 eapply global_node_357_step.
 - exact (prior 356%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_358 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 34 final=Some (Gval (Fuint 1) (global_word_358 v)).
Proof.
 eapply global_node_358_step.
 - exact (prior 353%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_359.
Lemma global_connect_359_alias v : global_word_359 v = global_word_358 v.
Proof. unfold global_word_359, global_closed_359, global_expr_359, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_359.
Lemma global_progress_359 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10] 6 final=Some (Gval (Fuint 1) (global_word_359 v)).
Proof.
 have Typed := types 359%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_359_step.
 - exact (prior 358%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_359_alias. apply adapt_uint_same. exact (global_size_358 v sizes).
 - exact ran.
Qed.
Lemma global_progress_360 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 10 6 final=Some (Gval (Fuint 1) (global_word_360 v)).
Proof.
 apply (global_sync_360_link invalid snapshot final v); [eapply global_progress_359; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_361 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::] 312 final=Some (Gval (Fuint 1) (global_word_361 v)).
Proof.
 eapply global_node_361_step.
 - exact (prior 360%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_362 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 6 final=Some (Gval (Fuint 1) (global_word_362 v)).
Proof.
 have Typed := types 362%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_362_step.
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_362 v sizes).
 - exact ran.
Qed.
Lemma global_progress_363 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 6 final=Some (Gval (Fuint 1) (global_word_363 v)).
Proof.
 apply (global_sync_363_link invalid snapshot final v); [eapply global_progress_362; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_364 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 40 final=Some (Gval (Fuint 1) (global_word_364 v)).
Proof.
 eapply global_node_364_step.
 - exact (prior 363%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_365 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 11 4 final=Some (Gval (Fuint 1) (global_word_365 v)).
Proof.
 have Typed := types 365%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_365_step.
 - exact (prior 364%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (3 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_365 v sizes).
 - exact ran.
Qed.
Lemma global_progress_366 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 4 final=Some (Gval (Fuint 1) (global_word_366 v)).
Proof.
 apply (global_sync_366_link invalid snapshot final v); [eapply global_progress_365; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_367 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 25 final=Some (Gval (Fuint 1) (global_word_367 v)).
Proof.
 eapply global_node_367_step.
 - exact (prior 366%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_368 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 4 final=Some (Gval (Fuint 1) (global_word_368 v)).
Proof.
 have Typed := types 368%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_368_step.
 - exact (prior 15%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_368 v sizes).
 - exact ran.
Qed.
Lemma global_progress_369 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 4 final=Some (Gval (Fuint 1) (global_word_369 v)).
Proof.
 apply (global_sync_369_link invalid snapshot final v); [eapply global_progress_368; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_370 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 10 4 final=Some (Gval (Fuint 1) (global_word_370 v)).
Proof.
 have Typed := types 370%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_370_step.
 - exact (prior 369%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_370 v sizes).
 - exact ran.
Qed.
Lemma global_progress_371 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 4 final=Some (Gval (Fuint 1) (global_word_371 v)).
Proof.
 apply (global_sync_371_link invalid snapshot final v); [eapply global_progress_370; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_372 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 25 final=Some (Gval (Fuint 1) (global_word_372 v)).
Proof.
 eapply global_node_372_step.
 - exact (prior 371%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_373 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 2 final=Some (Gval (Fuint 1) (global_word_373 v)).
Proof.
 have Typed := types 373%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_373_step.
 - exact (prior 13%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_373 v sizes).
 - exact ran.
Qed.
Lemma global_progress_374 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 2 final=Some (Gval (Fuint 1) (global_word_374 v)).
Proof.
 apply (global_sync_374_link invalid snapshot final v); [eapply global_progress_373; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_375 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 10 2 final=Some (Gval (Fuint 1) (global_word_375 v)).
Proof.
 have Typed := types 375%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_375_step.
 - exact (prior 374%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_375 v sizes).
 - exact ran.
Qed.
Lemma global_progress_376 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 2 final=Some (Gval (Fuint 1) (global_word_376 v)).
Proof.
 apply (global_sync_376_link invalid snapshot final v); [eapply global_progress_375; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_377 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 23 final=Some (Gval (Fuint 1) (global_word_377 v)).
Proof.
 eapply global_node_377_step.
 - exact (prior 376%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_378 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 3 final=Some (Gval (Fuint 1) (global_word_378 v)).
Proof.
 have Typed := types 378%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_378_step.
 - exact (prior 14%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_378 v sizes).
 - exact ran.
Qed.
Lemma global_progress_379 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 3 final=Some (Gval (Fuint 1) (global_word_379 v)).
Proof.
 apply (global_sync_379_link invalid snapshot final v); [eapply global_progress_378; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_380 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 10 3 final=Some (Gval (Fuint 1) (global_word_380 v)).
Proof.
 have Typed := types 380%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_380_step.
 - exact (prior 379%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_380 v sizes).
 - exact ran.
Qed.
Lemma global_progress_381 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(4 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 3 final=Some (Gval (Fuint 1) (global_word_381 v)).
Proof.
 apply (global_sync_381_link invalid snapshot final v); [eapply global_progress_380; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_382 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(5 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 24 final=Some (Gval (Fuint 1) (global_word_382 v)).
Proof.
 eapply global_node_382_step.
 - exact (prior 381%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (4 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_383 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 26 final=Some (Gval (Fuint 1) (global_word_383 v)).
Proof.
 eapply global_node_383_step.
 - exact (prior 377%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 382%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_384 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 28 final=Some (Gval (Fuint 1) (global_word_384 v)).
Proof.
 eapply global_node_384_step.
 - exact (prior 372%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 383%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_385 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(6 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 27 final=Some (Gval (Fuint 1) (global_word_385 v)).
Proof.
 eapply global_node_385_step.
 - exact (prior 377%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 382%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_386 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(7 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 29 final=Some (Gval (Fuint 1) (global_word_386 v)).
Proof.
 eapply global_node_386_step.
 - exact (prior 372%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (5 <= level)%coq_nat; lia))).
 - exact (prior 383%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_387 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(8 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 30 final=Some (Gval (Fuint 1) (global_word_387 v)).
Proof.
 eapply global_node_387_step.
 - exact (prior 385%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (6 <= level)%coq_nat; lia))).
 - exact (prior 386%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_388 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(9 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 31 final=Some (Gval (Fuint 2) (global_word_388 v)).
Proof.
 eapply global_node_388_step.
 - exact (prior 384%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (7 <= level)%coq_nat; lia))).
 - exact (prior 387%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (8 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_389 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(10 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 32 final=Some (Gval (Fuint 2) (global_word_389 v)).
Proof.
 eapply global_node_389_step.
 - exact (prior 388%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (9 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_390 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(11 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 33 final=Some (Gval (Fuint 1) (global_word_390 v)).
Proof.
 eapply global_node_390_step.
 - exact (prior 389%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (10 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Transparent global_word_391.
Lemma global_connect_391_alias v : global_word_391 v = global_word_390 v.
Proof. unfold global_word_391, global_closed_391, global_expr_391, Stable.word_of_eval. cbn [eval_hfexpr eval_href]. rewrite VM.Lemmas.find_add_eq; reflexivity. Qed.
Opaque global_word_391.
Lemma global_progress_391 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(12 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::10;11] 5 final=Some (Gval (Fuint 1) (global_word_391 v)).
Proof.
 have Typed := types 391%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_scalar_391_step.
 - exact (prior 390%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (11 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - rewrite global_connect_391_alias. apply adapt_uint_same. exact (global_size_390 v sizes).
 - exact ran.
Qed.
Lemma global_progress_392 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(13 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 10 5 final=Some (Gval (Fuint 1) (global_word_392 v)).
Proof.
 apply (global_sync_392_link invalid snapshot final v); [eapply global_progress_391; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_393 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(14 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 38 final=Some (Gval (Fuint 1) (global_word_393 v)).
Proof.
 eapply global_node_393_step.
 - exact (prior 392%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (13 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_394 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(15 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::11] 11 2 final=Some (Gval (Fuint 1) (global_word_394 v)).
Proof.
 have Typed := types 394%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_394_step.
 - exact (prior 393%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (14 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_394 v sizes).
 - exact ran.
Qed.
Lemma global_progress_395 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(16 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 2 final=Some (Gval (Fuint 1) (global_word_395 v)).
Proof.
 apply (global_sync_395_link invalid snapshot final v); [eapply global_progress_394; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_396 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(17 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11;11] 23 final=Some (Gval (Fuint 1) (global_word_396 v)).
Proof.
 eapply global_node_396_step.
 - exact (prior 395%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (16 <= level)%coq_nat; lia))).
 - exact ran.
Qed.
Lemma global_progress_397 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(1 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_interface [::] 11 5 final=Some (Gval (Fuint 1) (global_word_397 v)).
Proof.
 have Typed := types 397%nat (ltac:(lia)) (Logic.eq_refl true).
 destruct (option_ground_value _ _ Typed) as [initial [Initial TypedInitial]].
 eapply global_field_397_step.
 - exact (prior 16%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (0 <= level)%coq_nat; lia))).
 - exact Initial.
 - exact TypedInitial.
 - apply adapt_uint_same. exact (global_size_397 v sizes).
 - exact ran.
Qed.
Lemma global_progress_398 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(2 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 5 final=Some (Gval (Fuint 1) (global_word_398 v)).
Proof.
 apply (global_sync_398_link invalid snapshot final v); [eapply global_progress_397; try eassumption; lia|exact ran].
Qed.
Lemma global_progress_399 invalid snapshot final v level
 (prior:global_ranked v level snapshot) (types:global_port_types snapshot) (sizes:global_leaf_sizes v)
 (enough:(3 <= S level)%coq_nat)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 circuit_lookup [::11] 39 final=Some (Gval (Fuint 1) (global_word_399 v)).
Proof.
 eapply global_node_399_step.
 - exact (prior 398%nat (ltac:(clear prior types sizes ran; lia)) (ltac:(clear prior types sizes ran; change (2 <= level)%coq_nat; lia))).
 - exact ran.
Qed.

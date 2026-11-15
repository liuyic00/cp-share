From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalInitialLocal PipelineCommit GlobalCommit ObservationBridge.
Local Open Scope N_scope.
Local Opaque circuit_initial_map_with_memory circuit_iter_count_with_memory circuit_formal_iterations circuit_value_iter_with_memory_policy.
Lemma multiplier_cycle_decompose previous inputs final
 (ran:circuit_formal_cycle generated_modules generated_top (Some previous) inputs=Some final) :
 exists stable, multiplier_observe previous inputs=Some stable /\
 circuit_value_iter_with_memory_policy (formal_invalid_policy inputs) generated_modules generated_top stable true=Some final.
Proof.
 unfold circuit_formal_cycle in ran. unfold multiplier_observe.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Initial; [|discriminate].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count) as [count|] eqn:Count; [|discriminate].
 destruct (circuit_formal_iterations generated_modules generated_top inputs count initial) as [stable|] eqn:Settled; [|discriminate].
 exists stable. split; [reflexivity|exact ran].
Qed.
Theorem multiplier_cycle_registers v previous old inputs final
 (sized:global_leaf_sizes v)
 (old_found:SVM.find [::] previous=Some old)
 (registers:multiplier_register_values v old)
 (ports:multiplier_input_values v (formal_external_inputs inputs))
 (ran:circuit_formal_cycle generated_modules generated_top (Some previous) inputs=Some final) :
 exists after,SVM.find [::] final=Some after /\ multiplier_committed v after.
Proof.
 destruct (multiplier_cycle_decompose previous inputs final ran) as [stable [Observed Committed]].
 have Values:=multiplier_observation_values v previous old inputs stable sized old_found registers ports Observed.
 have First:=global_commit_201 (formal_invalid_policy inputs) v stable final Values Committed.
 unfold circuit_lookup in First.
 destruct (SVM.find [::] final) as [after|] eqn:Found; [|discriminate].
 exists after. split; [reflexivity|].
 unfold multiplier_committed. intros id inside.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_201 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_203 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_205 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_207 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_209 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_211 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_213 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_215 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_217 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_219 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_221 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_223 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_225 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_227 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_229 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_231 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_233 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_235 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_237 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_239 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_241 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_243 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_245 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_247 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_249 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_251 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_253 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_255 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_257 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_259 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_261 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_263 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_265 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_267 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_269 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_271 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_273 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_275 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_277 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_279 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_281 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_283 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_285 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_287 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_289 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_291 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_293 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_295 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_297 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_299 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_301 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_303 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_408 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_410 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_416 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 destruct inside as [same|inside].
 - subst id. have Value:=global_commit_419 (formal_invalid_policy inputs) v stable final Values Committed.
   unfold circuit_lookup in Value. rewrite Found in Value. exact Value.
 contradiction.
Qed.
Print Assumptions multiplier_cycle_registers.

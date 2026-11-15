From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From ArithmeticCommon Require Import HierarchyFacts.
From SmallMultiplier Require Import GlobalStable GlobalWidths GlobalProgressTypes GlobalInitialLocal PipelineCommit.
Local Open Scope N_scope.
Lemma register_adapt_size width word : size (zext_to width (take width word))=width.
Proof.
 unfold zext_to. rewrite size_zext size_take.
 have Bound: (minn width (size word) <= width)%nat by apply geq_minl.
 rewrite subnKC; [reflexivity|exact Bound].
Qed.
Lemma next_word_201_size v : size(next_word_201 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_203_size v : size(next_word_203 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_205_size v : size(next_word_205 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_207_size v : size(next_word_207 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_209_size v : size(next_word_209 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_211_size v : size(next_word_211 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_213_size v : size(next_word_213 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_215_size v : size(next_word_215 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_217_size v : size(next_word_217 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_219_size v : size(next_word_219 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_221_size v : size(next_word_221 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_223_size v : size(next_word_223 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_225_size v : size(next_word_225 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_227_size v : size(next_word_227 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_229_size v : size(next_word_229 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_231_size v : size(next_word_231 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_233_size v : size(next_word_233 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_235_size v : size(next_word_235 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_237_size v : size(next_word_237 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_239_size v : size(next_word_239 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_241_size v : size(next_word_241 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_243_size v : size(next_word_243 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_245_size v : size(next_word_245 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_247_size v : size(next_word_247 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_249_size v : size(next_word_249 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_251_size v : size(next_word_251 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_253_size v : size(next_word_253 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_255_size v : size(next_word_255 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_257_size v : size(next_word_257 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_259_size v : size(next_word_259 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_261_size v : size(next_word_261 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_263_size v : size(next_word_263 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_265_size v : size(next_word_265 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_267_size v : size(next_word_267 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_269_size v : size(next_word_269 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_271_size v : size(next_word_271 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_273_size v : size(next_word_273 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_275_size v : size(next_word_275 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_277_size v : size(next_word_277 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_279_size v : size(next_word_279 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_281_size v : size(next_word_281 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_283_size v : size(next_word_283 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_285_size v : size(next_word_285 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_287_size v : size(next_word_287 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_289_size v : size(next_word_289 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_291_size v : size(next_word_291 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_293_size v : size(next_word_293 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_295_size v : size(next_word_295 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_297_size v : size(next_word_297 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_299_size v : size(next_word_299 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_301_size v : size(next_word_301 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_303_size v : size(next_word_303 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_408_size v : size(next_word_408 v)=16%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_410_size v : size(next_word_410 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_416_size v : size(next_word_416 v)=16%nat.
Proof. apply register_adapt_size. Qed.
Lemma next_word_419_size v : size(next_word_419 v)=1%nat.
Proof. apply register_adapt_size. Qed.
Definition next_register_leaves (v:global_leaves) : global_leaves := fun index => match N.of_nat index with
| 3 => next_word_201 v
| 4 => next_word_203 v
| 5 => next_word_205 v
| 6 => next_word_207 v
| 7 => next_word_209 v
| 8 => next_word_211 v
| 9 => next_word_213 v
| 10 => next_word_215 v
| 11 => next_word_217 v
| 12 => next_word_219 v
| 13 => next_word_221 v
| 14 => next_word_223 v
| 15 => next_word_225 v
| 16 => next_word_227 v
| 17 => next_word_229 v
| 18 => next_word_231 v
| 19 => next_word_233 v
| 20 => next_word_235 v
| 21 => next_word_237 v
| 22 => next_word_239 v
| 23 => next_word_241 v
| 24 => next_word_243 v
| 25 => next_word_245 v
| 26 => next_word_247 v
| 27 => next_word_249 v
| 28 => next_word_251 v
| 29 => next_word_253 v
| 30 => next_word_255 v
| 31 => next_word_257 v
| 32 => next_word_259 v
| 33 => next_word_261 v
| 34 => next_word_263 v
| 35 => next_word_265 v
| 36 => next_word_267 v
| 37 => next_word_269 v
| 38 => next_word_271 v
| 39 => next_word_273 v
| 40 => next_word_275 v
| 41 => next_word_277 v
| 42 => next_word_279 v
| 43 => next_word_281 v
| 44 => next_word_283 v
| 45 => next_word_285 v
| 46 => next_word_287 v
| 47 => next_word_289 v
| 48 => next_word_291 v
| 49 => next_word_293 v
| 50 => next_word_295 v
| 51 => next_word_297 v
| 52 => next_word_299 v
| 54 => next_word_301 v
| 55 => next_word_303 v
| 57 => next_word_408 v
| 58 => next_word_410 v
| 59 => next_word_416 v
| 60 => next_word_419 v
| _ => v index end.
Lemma next_register_leaves_sizes v (sized:global_leaf_sizes v) : global_leaf_sizes (next_register_leaves v).
Proof. intros index inside.
 have Member:List.In index (List.seq 0 62) by apply List.in_seq; move/ltP:inside;lia.
 change (List.In index [::0%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat;48%nat;49%nat;50%nat;51%nat;52%nat;53%nat;54%nat;55%nat;56%nat;57%nat;58%nat;59%nat;60%nat;61%nat]) in Member.
 destruct Member as [same|Member].
 - subst index. exact(sized 0%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 1%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(sized 2%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(next_word_201_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_203_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_205_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_207_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_209_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_211_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_213_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_215_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_217_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_219_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_221_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_223_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_225_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_227_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_229_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_231_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_233_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_235_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_237_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_239_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_241_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_243_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_245_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_247_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_249_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_251_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_253_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_255_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_257_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_259_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_261_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_263_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_265_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_267_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_269_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_271_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_273_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_275_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_277_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_279_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_281_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_283_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_285_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_287_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_289_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_291_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_293_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_295_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_297_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_299_size v).
 destruct Member as [same|Member].
 - subst index. exact(sized 53%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(next_word_301_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_303_size v).
 destruct Member as [same|Member].
 - subst index. exact(sized 56%nat (ltac:(reflexivity))).
 destruct Member as [same|Member].
 - subst index. exact(next_word_408_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_410_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_416_size v).
 destruct Member as [same|Member].
 - subst index. exact(next_word_419_size v).
 destruct Member as [same|Member].
 - subst index. exact(sized 61%nat (ltac:(reflexivity))).
 contradiction.
Qed.
Lemma committed_register_leaves v env (committed:multiplier_committed v env) : multiplier_register_values (next_register_leaves v) env.
Proof. intros index inside.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 201 (ltac:(unfold List.In;tauto)).
   change (VM.find 201 env=Some(next_register_value v 201)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 203 (ltac:(unfold List.In;tauto)).
   change (VM.find 203 env=Some(next_register_value v 203)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 205 (ltac:(unfold List.In;tauto)).
   change (VM.find 205 env=Some(next_register_value v 205)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 207 (ltac:(unfold List.In;tauto)).
   change (VM.find 207 env=Some(next_register_value v 207)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 209 (ltac:(unfold List.In;tauto)).
   change (VM.find 209 env=Some(next_register_value v 209)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 211 (ltac:(unfold List.In;tauto)).
   change (VM.find 211 env=Some(next_register_value v 211)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 213 (ltac:(unfold List.In;tauto)).
   change (VM.find 213 env=Some(next_register_value v 213)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 215 (ltac:(unfold List.In;tauto)).
   change (VM.find 215 env=Some(next_register_value v 215)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 217 (ltac:(unfold List.In;tauto)).
   change (VM.find 217 env=Some(next_register_value v 217)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 219 (ltac:(unfold List.In;tauto)).
   change (VM.find 219 env=Some(next_register_value v 219)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 221 (ltac:(unfold List.In;tauto)).
   change (VM.find 221 env=Some(next_register_value v 221)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 223 (ltac:(unfold List.In;tauto)).
   change (VM.find 223 env=Some(next_register_value v 223)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 225 (ltac:(unfold List.In;tauto)).
   change (VM.find 225 env=Some(next_register_value v 225)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 227 (ltac:(unfold List.In;tauto)).
   change (VM.find 227 env=Some(next_register_value v 227)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 229 (ltac:(unfold List.In;tauto)).
   change (VM.find 229 env=Some(next_register_value v 229)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 231 (ltac:(unfold List.In;tauto)).
   change (VM.find 231 env=Some(next_register_value v 231)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 233 (ltac:(unfold List.In;tauto)).
   change (VM.find 233 env=Some(next_register_value v 233)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 235 (ltac:(unfold List.In;tauto)).
   change (VM.find 235 env=Some(next_register_value v 235)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 237 (ltac:(unfold List.In;tauto)).
   change (VM.find 237 env=Some(next_register_value v 237)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 239 (ltac:(unfold List.In;tauto)).
   change (VM.find 239 env=Some(next_register_value v 239)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 241 (ltac:(unfold List.In;tauto)).
   change (VM.find 241 env=Some(next_register_value v 241)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 243 (ltac:(unfold List.In;tauto)).
   change (VM.find 243 env=Some(next_register_value v 243)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 245 (ltac:(unfold List.In;tauto)).
   change (VM.find 245 env=Some(next_register_value v 245)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 247 (ltac:(unfold List.In;tauto)).
   change (VM.find 247 env=Some(next_register_value v 247)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 249 (ltac:(unfold List.In;tauto)).
   change (VM.find 249 env=Some(next_register_value v 249)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 251 (ltac:(unfold List.In;tauto)).
   change (VM.find 251 env=Some(next_register_value v 251)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 253 (ltac:(unfold List.In;tauto)).
   change (VM.find 253 env=Some(next_register_value v 253)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 255 (ltac:(unfold List.In;tauto)).
   change (VM.find 255 env=Some(next_register_value v 255)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 257 (ltac:(unfold List.In;tauto)).
   change (VM.find 257 env=Some(next_register_value v 257)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 259 (ltac:(unfold List.In;tauto)).
   change (VM.find 259 env=Some(next_register_value v 259)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 261 (ltac:(unfold List.In;tauto)).
   change (VM.find 261 env=Some(next_register_value v 261)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 263 (ltac:(unfold List.In;tauto)).
   change (VM.find 263 env=Some(next_register_value v 263)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 265 (ltac:(unfold List.In;tauto)).
   change (VM.find 265 env=Some(next_register_value v 265)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 267 (ltac:(unfold List.In;tauto)).
   change (VM.find 267 env=Some(next_register_value v 267)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 269 (ltac:(unfold List.In;tauto)).
   change (VM.find 269 env=Some(next_register_value v 269)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 271 (ltac:(unfold List.In;tauto)).
   change (VM.find 271 env=Some(next_register_value v 271)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 273 (ltac:(unfold List.In;tauto)).
   change (VM.find 273 env=Some(next_register_value v 273)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 275 (ltac:(unfold List.In;tauto)).
   change (VM.find 275 env=Some(next_register_value v 275)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 277 (ltac:(unfold List.In;tauto)).
   change (VM.find 277 env=Some(next_register_value v 277)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 279 (ltac:(unfold List.In;tauto)).
   change (VM.find 279 env=Some(next_register_value v 279)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 281 (ltac:(unfold List.In;tauto)).
   change (VM.find 281 env=Some(next_register_value v 281)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 283 (ltac:(unfold List.In;tauto)).
   change (VM.find 283 env=Some(next_register_value v 283)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 285 (ltac:(unfold List.In;tauto)).
   change (VM.find 285 env=Some(next_register_value v 285)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 287 (ltac:(unfold List.In;tauto)).
   change (VM.find 287 env=Some(next_register_value v 287)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 289 (ltac:(unfold List.In;tauto)).
   change (VM.find 289 env=Some(next_register_value v 289)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 291 (ltac:(unfold List.In;tauto)).
   change (VM.find 291 env=Some(next_register_value v 291)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 293 (ltac:(unfold List.In;tauto)).
   change (VM.find 293 env=Some(next_register_value v 293)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 295 (ltac:(unfold List.In;tauto)).
   change (VM.find 295 env=Some(next_register_value v 295)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 297 (ltac:(unfold List.In;tauto)).
   change (VM.find 297 env=Some(next_register_value v 297)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 299 (ltac:(unfold List.In;tauto)).
   change (VM.find 299 env=Some(next_register_value v 299)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 301 (ltac:(unfold List.In;tauto)).
   change (VM.find 301 env=Some(next_register_value v 301)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 303 (ltac:(unfold List.In;tauto)).
   change (VM.find 303 env=Some(next_register_value v 303)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 408 (ltac:(unfold List.In;tauto)).
   change (VM.find 408 env=Some(next_register_value v 408)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 410 (ltac:(unfold List.In;tauto)).
   change (VM.find 410 env=Some(next_register_value v 410)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 416 (ltac:(unfold List.In;tauto)).
   change (VM.find 416 env=Some(next_register_value v 416)). exact Known.
 destruct inside as [same|inside].
 - subst index. have Known:=committed 419 (ltac:(unfold List.In;tauto)).
   change (VM.find 419 env=Some(next_register_value v 419)). exact Known.
 contradiction.
Qed.
Print Assumptions committed_register_leaves.

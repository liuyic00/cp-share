From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
From ArithmeticCommon Require Import SymbolicInitialFacts HierarchyFacts.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalInstances GlobalProgressTypes GlobalInitialLocal RuntimeState.
Local Open Scope N_scope.
Definition seed_bits (inputs:formal_inputs) (id:N) width := proj1_sig(formal_symbolic_inputs inputs [::] [::0%nat;N.to_nat id] [::] width).
Lemma seed_bits_size inputs id width : size(seed_bits inputs id width)=width.
Proof. exact(proj2_sig(formal_symbolic_inputs inputs [::] [::0%nat;N.to_nat id] [::] width)). Qed.
Definition seed_leaves inputs : global_leaves := fun index=>match N.of_nat index with
| 0=>zeros 1
| 1=>zeros 1
| 2=>zeros 8
| 3=>seed_bits inputs 201 1
| 4=>seed_bits inputs 203 1
| 5=>seed_bits inputs 205 1
| 6=>seed_bits inputs 207 1
| 7=>seed_bits inputs 209 1
| 8=>seed_bits inputs 211 1
| 9=>seed_bits inputs 213 1
| 10=>seed_bits inputs 215 1
| 11=>seed_bits inputs 217 1
| 12=>seed_bits inputs 219 1
| 13=>seed_bits inputs 221 1
| 14=>seed_bits inputs 223 1
| 15=>seed_bits inputs 225 1
| 16=>seed_bits inputs 227 1
| 17=>seed_bits inputs 229 1
| 18=>seed_bits inputs 231 1
| 19=>seed_bits inputs 233 1
| 20=>seed_bits inputs 235 1
| 21=>seed_bits inputs 237 1
| 22=>seed_bits inputs 239 1
| 23=>seed_bits inputs 241 1
| 24=>seed_bits inputs 243 1
| 25=>seed_bits inputs 245 1
| 26=>seed_bits inputs 247 1
| 27=>seed_bits inputs 249 1
| 28=>seed_bits inputs 251 1
| 29=>seed_bits inputs 253 1
| 30=>seed_bits inputs 255 1
| 31=>seed_bits inputs 257 1
| 32=>seed_bits inputs 259 1
| 33=>seed_bits inputs 261 1
| 34=>seed_bits inputs 263 1
| 35=>seed_bits inputs 265 1
| 36=>seed_bits inputs 267 1
| 37=>seed_bits inputs 269 1
| 38=>seed_bits inputs 271 1
| 39=>seed_bits inputs 273 1
| 40=>seed_bits inputs 275 1
| 41=>seed_bits inputs 277 1
| 42=>seed_bits inputs 279 1
| 43=>seed_bits inputs 281 1
| 44=>seed_bits inputs 283 1
| 45=>seed_bits inputs 285 1
| 46=>seed_bits inputs 287 1
| 47=>seed_bits inputs 289 1
| 48=>seed_bits inputs 291 1
| 49=>seed_bits inputs 293 1
| 50=>seed_bits inputs 295 1
| 51=>seed_bits inputs 297 1
| 52=>seed_bits inputs 299 1
| 53=>zeros 8
| 54=>seed_bits inputs 301 1
| 55=>seed_bits inputs 303 1
| 56=>zeros 1
| 57=>seed_bits inputs 408 16
| 58=>seed_bits inputs 410 1
| 59=>seed_bits inputs 416 16
| 60=>seed_bits inputs 419 1
| 61=>zeros 1
| _=>[::]end.
Lemma seed_registers_expanded inputs env : initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env=
(VM.add 419 (Gval(Fuint 1)(seed_bits inputs 419 1)) (VM.add 416 (Gval(Fuint 16)(seed_bits inputs 416 16)) (VM.add 410 (Gval(Fuint 1)(seed_bits inputs 410 1)) (VM.add 408 (Gval(Fuint 16)(seed_bits inputs 408 16)) (VM.add 303 (Gval(Fuint 1)(seed_bits inputs 303 1)) (VM.add 301 (Gval(Fuint 1)(seed_bits inputs 301 1)) (VM.add 299 (Gval(Fuint 1)(seed_bits inputs 299 1)) (VM.add 297 (Gval(Fuint 1)(seed_bits inputs 297 1)) (VM.add 295 (Gval(Fuint 1)(seed_bits inputs 295 1)) (VM.add 293 (Gval(Fuint 1)(seed_bits inputs 293 1)) (VM.add 291 (Gval(Fuint 1)(seed_bits inputs 291 1)) (VM.add 289 (Gval(Fuint 1)(seed_bits inputs 289 1)) (VM.add 287 (Gval(Fuint 1)(seed_bits inputs 287 1)) (VM.add 285 (Gval(Fuint 1)(seed_bits inputs 285 1)) (VM.add 283 (Gval(Fuint 1)(seed_bits inputs 283 1)) (VM.add 281 (Gval(Fuint 1)(seed_bits inputs 281 1)) (VM.add 279 (Gval(Fuint 1)(seed_bits inputs 279 1)) (VM.add 277 (Gval(Fuint 1)(seed_bits inputs 277 1)) (VM.add 275 (Gval(Fuint 1)(seed_bits inputs 275 1)) (VM.add 273 (Gval(Fuint 1)(seed_bits inputs 273 1)) (VM.add 271 (Gval(Fuint 1)(seed_bits inputs 271 1)) (VM.add 269 (Gval(Fuint 1)(seed_bits inputs 269 1)) (VM.add 267 (Gval(Fuint 1)(seed_bits inputs 267 1)) (VM.add 265 (Gval(Fuint 1)(seed_bits inputs 265 1)) (VM.add 263 (Gval(Fuint 1)(seed_bits inputs 263 1)) (VM.add 261 (Gval(Fuint 1)(seed_bits inputs 261 1)) (VM.add 259 (Gval(Fuint 1)(seed_bits inputs 259 1)) (VM.add 257 (Gval(Fuint 1)(seed_bits inputs 257 1)) (VM.add 255 (Gval(Fuint 1)(seed_bits inputs 255 1)) (VM.add 253 (Gval(Fuint 1)(seed_bits inputs 253 1)) (VM.add 251 (Gval(Fuint 1)(seed_bits inputs 251 1)) (VM.add 249 (Gval(Fuint 1)(seed_bits inputs 249 1)) (VM.add 247 (Gval(Fuint 1)(seed_bits inputs 247 1)) (VM.add 245 (Gval(Fuint 1)(seed_bits inputs 245 1)) (VM.add 243 (Gval(Fuint 1)(seed_bits inputs 243 1)) (VM.add 241 (Gval(Fuint 1)(seed_bits inputs 241 1)) (VM.add 239 (Gval(Fuint 1)(seed_bits inputs 239 1)) (VM.add 237 (Gval(Fuint 1)(seed_bits inputs 237 1)) (VM.add 235 (Gval(Fuint 1)(seed_bits inputs 235 1)) (VM.add 233 (Gval(Fuint 1)(seed_bits inputs 233 1)) (VM.add 231 (Gval(Fuint 1)(seed_bits inputs 231 1)) (VM.add 229 (Gval(Fuint 1)(seed_bits inputs 229 1)) (VM.add 227 (Gval(Fuint 1)(seed_bits inputs 227 1)) (VM.add 225 (Gval(Fuint 1)(seed_bits inputs 225 1)) (VM.add 223 (Gval(Fuint 1)(seed_bits inputs 223 1)) (VM.add 221 (Gval(Fuint 1)(seed_bits inputs 221 1)) (VM.add 219 (Gval(Fuint 1)(seed_bits inputs 219 1)) (VM.add 217 (Gval(Fuint 1)(seed_bits inputs 217 1)) (VM.add 215 (Gval(Fuint 1)(seed_bits inputs 215 1)) (VM.add 213 (Gval(Fuint 1)(seed_bits inputs 213 1)) (VM.add 211 (Gval(Fuint 1)(seed_bits inputs 211 1)) (VM.add 209 (Gval(Fuint 1)(seed_bits inputs 209 1)) (VM.add 207 (Gval(Fuint 1)(seed_bits inputs 207 1)) (VM.add 205 (Gval(Fuint 1)(seed_bits inputs 205 1)) (VM.add 203 (Gval(Fuint 1)(seed_bits inputs 203 1)) (VM.add 201 (Gval(Fuint 1)(seed_bits inputs 201 1)) env)))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Proof. reflexivity. Qed.
Lemma seed_registers_match inputs env : multiplier_register_values (seed_leaves inputs) (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env).
Proof. intros index inside.
 destruct inside as [same|inside].
 - subst index. change (VM.find 201 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 201 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 203 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 203 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 205 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 205 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 207 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 207 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 209 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 209 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 211 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 211 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 213 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 213 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 215 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 215 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 217 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 217 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 219 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 219 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 221 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 221 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 223 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 223 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 225 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 225 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 227 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 227 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 229 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 229 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 231 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 231 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 233 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 233 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 235 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 235 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 237 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 237 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 239 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 239 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 241 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 241 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 243 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 243 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 245 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 245 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 247 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 247 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 249 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 249 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 251 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 251 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 253 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 253 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 255 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 255 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 257 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 257 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 259 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 259 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 261 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 261 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 263 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 263 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 265 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 265 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 267 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 267 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 269 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 269 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 271 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 271 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 273 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 273 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 275 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 275 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 277 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 277 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 279 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 279 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 281 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 281 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 283 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 283 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 285 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 285 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 287 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 287 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 289 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 289 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 291 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 291 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 293 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 293 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 295 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 295 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 297 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 297 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 299 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 299 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 301 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 301 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 303 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 303 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 408 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 16)(seed_bits inputs 408 16))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 410 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 410 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 416 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 16)(seed_bits inputs 416 16))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 destruct inside as [same|inside].
 - subst index. change (VM.find 419 (initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env)=Some(Gval(Fuint 1)(seed_bits inputs 419 1))).
   rewrite seed_registers_expanded.
   repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. reflexivity.
 contradiction.
Qed.
Lemma seed_leaf_sizes inputs : global_leaf_sizes(seed_leaves inputs).
Proof. intros index inside.
 have Member:List.In index (List.seq 0 62) by apply List.in_seq;move/ltP:inside;lia.
 change (List.In index [::0%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat;48%nat;49%nat;50%nat;51%nat;52%nat;53%nat;54%nat;55%nat;56%nat;57%nat;58%nat;59%nat;60%nat;61%nat]) in Member.
 destruct Member as [same|Member].
 - subst index. apply size_zeros.
 destruct Member as [same|Member].
 - subst index. apply size_zeros.
 destruct Member as [same|Member].
 - subst index. apply size_zeros.
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 201 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 203 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 205 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 207 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 209 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 211 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 213 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 215 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 217 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 219 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 221 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 223 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 225 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 227 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 229 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 231 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 233 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 235 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 237 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 239 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 241 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 243 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 245 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 247 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 249 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 251 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 253 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 255 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 257 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 259 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 261 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 263 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 265 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 267 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 269 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 271 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 273 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 275 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 277 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 279 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 281 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 283 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 285 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 287 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 289 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 291 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 293 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 295 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 297 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 299 1).
 destruct Member as [same|Member].
 - subst index. apply size_zeros.
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 301 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 303 1).
 destruct Member as [same|Member].
 - subst index. apply size_zeros.
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 408 16).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 410 1).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 416 16).
 destruct Member as [same|Member].
 - subst index. exact(seed_bits_size inputs 419 1).
 destruct Member as [same|Member].
 - subst index. apply size_zeros.
 contradiction.
Qed.
Local Opaque circuit_symbolic_initial_state.
Theorem represented_symbolic_initial contents inputs states
 (ran:circuit_symbolic_initial_state generated_modules generated_top contents inputs=Some states) : represented_state states.
Proof.
 destruct (symbolic_initial_local generated_modules generated_top contents inputs states multiplier_instances [::] 3 (multiplier_ports 3) generated_module_3_stmts_0 multiplier_instances_correct (Logic.eq_refl _) (Logic.eq_refl _) ran) as [env Found].
 exists (seed_leaves inputs),(initialize_symbolic_registers inputs [::] generated_module_3_stmts_0 env).
 split;[exact Found|]. split;[apply seed_leaf_sizes|apply seed_registers_match].
Qed.

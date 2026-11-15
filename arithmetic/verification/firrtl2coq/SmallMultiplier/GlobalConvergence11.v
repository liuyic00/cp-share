From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_11 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 2200 62).
Proof.
 constructor.
 - intro enough. exact (global_progress_2200 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2201 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2202 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2203 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2204 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2205 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2206 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2207 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2208 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2209 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2210 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2211 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2212 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2213 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2214 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2215 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2216 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2217 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2218 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2219 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2220 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2221 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2222 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2223 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2224 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2225 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2226 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2227 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2228 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2229 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2230 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2231 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2232 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2233 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2234 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2235 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2236 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2237 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2238 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2239 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2240 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2241 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2242 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2243 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2244 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2245 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2246 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2247 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2248 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2249 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2250 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2251 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2252 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2253 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2254 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2255 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2256 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2257 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2258 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2259 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2260 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_2261 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_11 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 2200 62).
Proof.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
Qed.

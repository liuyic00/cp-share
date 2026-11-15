(* Generated local certificates from the unchanged deep AST. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model.
Local Open Scope N_scope.
Lemma refine_ground known t b : refine_boolean_result known (Some (Gval t b)) = Some (Gval t b).
Proof. destruct known; reflexivity. Qed.
Definition leaf_values := N -> N -> bits.
Definition word_of_eval (v : option hvalue) : bits := match v with Some (Gval _ b) => b | _ => [::] end.

Definition word_0 (v : leaf_values) := v 0 0.
Definition word_1 (v : leaf_values) := v 0 1.
Definition word_2 (v : leaf_values) := v 0 2.
Definition word_3 (v : leaf_values) := v 0 3.
Definition word_4 (v : leaf_values) := v 0 4.
Definition word_5 (v : leaf_values) := v 0 5.
Definition word_201 (v : leaf_values) := v 0 201.
Definition word_203 (v : leaf_values) := v 0 203.
Definition word_205 (v : leaf_values) := v 0 205.
Definition word_207 (v : leaf_values) := v 0 207.
Definition word_209 (v : leaf_values) := v 0 209.
Definition word_211 (v : leaf_values) := v 0 211.
Definition word_213 (v : leaf_values) := v 0 213.
Definition word_215 (v : leaf_values) := v 0 215.
Definition word_217 (v : leaf_values) := v 0 217.
Definition word_219 (v : leaf_values) := v 0 219.
Definition word_221 (v : leaf_values) := v 0 221.
Definition word_223 (v : leaf_values) := v 0 223.
Definition word_225 (v : leaf_values) := v 0 225.
Definition word_227 (v : leaf_values) := v 0 227.
Definition word_229 (v : leaf_values) := v 0 229.
Definition word_231 (v : leaf_values) := v 0 231.
Definition word_233 (v : leaf_values) := v 0 233.
Definition word_235 (v : leaf_values) := v 0 235.
Definition word_237 (v : leaf_values) := v 0 237.
Definition word_239 (v : leaf_values) := v 0 239.
Definition word_241 (v : leaf_values) := v 0 241.
Definition word_243 (v : leaf_values) := v 0 243.
Definition word_245 (v : leaf_values) := v 0 245.
Definition word_247 (v : leaf_values) := v 0 247.
Definition word_249 (v : leaf_values) := v 0 249.
Definition word_251 (v : leaf_values) := v 0 251.
Definition word_253 (v : leaf_values) := v 0 253.
Definition word_255 (v : leaf_values) := v 0 255.
Definition word_257 (v : leaf_values) := v 0 257.
Definition word_259 (v : leaf_values) := v 0 259.
Definition word_261 (v : leaf_values) := v 0 261.
Definition word_263 (v : leaf_values) := v 0 263.
Definition word_265 (v : leaf_values) := v 0 265.
Definition word_267 (v : leaf_values) := v 0 267.
Definition word_269 (v : leaf_values) := v 0 269.
Definition word_271 (v : leaf_values) := v 0 271.
Definition word_273 (v : leaf_values) := v 0 273.
Definition word_275 (v : leaf_values) := v 0 275.
Definition word_277 (v : leaf_values) := v 0 277.
Definition word_279 (v : leaf_values) := v 0 279.
Definition word_281 (v : leaf_values) := v 0 281.
Definition word_283 (v : leaf_values) := v 0 283.
Definition word_285 (v : leaf_values) := v 0 285.
Definition word_287 (v : leaf_values) := v 0 287.
Definition word_289 (v : leaf_values) := v 0 289.
Definition word_291 (v : leaf_values) := v 0 291.
Definition word_293 (v : leaf_values) := v 0 293.
Definition word_295 (v : leaf_values) := v 0 295.
Definition word_297 (v : leaf_values) := v 0 297.
Definition word_299 (v : leaf_values) := v 0 299.
Definition word_301 (v : leaf_values) := v 0 301.
Definition word_303 (v : leaf_values) := v 0 303.
Definition word_408 (v : leaf_values) := v 0 408.
Definition word_410 (v : leaf_values) := v 0 410.
Definition word_416 (v : leaf_values) := v 0 416.
Definition word_419 (v : leaf_values) := v 0 419.
Definition port_7_4 (v : leaf_values) := v 7 4.
Definition port_7_5 (v : leaf_values) := v 7 5.
Definition port_8_4 (v : leaf_values) := v 8 4.
Definition port_8_5 (v : leaf_values) := v 8 5.
Definition port_9_5 (v : leaf_values) := v 9 5.
Definition port_9_6 (v : leaf_values) := v 9 6.
Definition port_10_5 (v : leaf_values) := v 10 5.
Definition port_10_6 (v : leaf_values) := v 10 6.
Definition port_11_7 (v : leaf_values) := v 11 7.
Definition port_11_8 (v : leaf_values) := v 11 8.
Definition port_11_9 (v : leaf_values) := v 11 9.
Definition port_12_7 (v : leaf_values) := v 12 7.
Definition port_12_8 (v : leaf_values) := v 12 8.
Definition port_12_9 (v : leaf_values) := v 12 9.
Definition port_13_7 (v : leaf_values) := v 13 7.
Definition port_13_8 (v : leaf_values) := v 13 8.
Definition port_13_9 (v : leaf_values) := v 13 9.
Definition port_14_7 (v : leaf_values) := v 14 7.
Definition port_14_8 (v : leaf_values) := v 14 8.
Definition port_14_9 (v : leaf_values) := v 14 9.
Definition port_15_7 (v : leaf_values) := v 15 7.
Definition port_15_8 (v : leaf_values) := v 15 8.
Definition port_15_9 (v : leaf_values) := v 15 9.
Definition port_16_7 (v : leaf_values) := v 16 7.
Definition port_16_8 (v : leaf_values) := v 16 8.
Definition port_16_9 (v : leaf_values) := v 16 9.
Definition port_17_7 (v : leaf_values) := v 17 7.
Definition port_17_8 (v : leaf_values) := v 17 8.
Definition port_17_9 (v : leaf_values) := v 17 9.
Definition port_18_7 (v : leaf_values) := v 18 7.
Definition port_18_8 (v : leaf_values) := v 18 8.
Definition port_18_9 (v : leaf_values) := v 18 9.
Definition port_19_5 (v : leaf_values) := v 19 5.
Definition port_19_6 (v : leaf_values) := v 19 6.
Definition port_20_4 (v : leaf_values) := v 20 4.
Definition port_20_5 (v : leaf_values) := v 20 5.
Definition port_21_4 (v : leaf_values) := v 21 4.
Definition port_21_5 (v : leaf_values) := v 21 5.
Definition port_22_4 (v : leaf_values) := v 22 4.
Definition port_22_5 (v : leaf_values) := v 22 5.
Definition port_23_4 (v : leaf_values) := v 23 4.
Definition port_23_5 (v : leaf_values) := v 23 5.
Definition port_24_4 (v : leaf_values) := v 24 4.
Definition port_24_5 (v : leaf_values) := v 24 5.
Definition port_25_4 (v : leaf_values) := v 25 4.
Definition port_25_5 (v : leaf_values) := v 25 5.
Definition port_26_4 (v : leaf_values) := v 26 4.
Definition port_26_5 (v : leaf_values) := v 26 5.
Definition port_27_5 (v : leaf_values) := v 27 5.
Definition port_27_6 (v : leaf_values) := v 27 6.
Definition port_28_5 (v : leaf_values) := v 28 5.
Definition port_28_6 (v : leaf_values) := v 28 6.
Definition port_29_4 (v : leaf_values) := v 29 4.
Definition port_29_5 (v : leaf_values) := v 29 5.
Definition port_30_4 (v : leaf_values) := v 30 4.
Definition port_30_5 (v : leaf_values) := v 30 5.
Definition port_31_4 (v : leaf_values) := v 31 4.
Definition port_31_5 (v : leaf_values) := v 31 5.
Definition port_32_4 (v : leaf_values) := v 32 4.
Definition port_32_5 (v : leaf_values) := v 32 5.
Definition port_33_5 (v : leaf_values) := v 33 5.
Definition port_33_6 (v : leaf_values) := v 33 6.
Definition port_34_4 (v : leaf_values) := v 34 4.
Definition port_34_5 (v : leaf_values) := v 34 5.
Definition port_35_4 (v : leaf_values) := v 35 4.
Definition port_35_5 (v : leaf_values) := v 35 5.
Definition port_36_4 (v : leaf_values) := v 36 4.
Definition port_36_5 (v : leaf_values) := v 36 5.
Definition expr_word_37 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 3))).
Definition closed_word_37 (v : leaf_values) : VM.t hvalue := (VM.add 3 (Gval (Fuint 8) (word_3 v)) (VM.empty hvalue)).
Definition word_37 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_37 (closed_word_37 v) (closed_word_37 v)).
Definition expr_word_38 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 37)) (@Eref VarOrder.T (@Eid VarOrder.T 3))).
Definition closed_word_38 (v : leaf_values) : VM.t hvalue := (VM.add 37 (Gval (Fuint 1) (word_37 v)) (VM.add 3 (Gval (Fuint 8) (word_3 v)) (VM.empty hvalue))).
Definition word_38 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_38 (closed_word_38 v) (closed_word_38 v)).
Definition expr_word_39 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 38)).
Definition closed_word_39 (v : leaf_values) : VM.t hvalue := (VM.add 38 (Gval (Fuint 9) (word_38 v)) (VM.empty hvalue)).
Definition word_39 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_39 (closed_word_39 v) (closed_word_39 v)).
Definition expr_word_40 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 39))).
Definition closed_word_40 (v : leaf_values) : VM.t hvalue := (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue)).
Definition word_40 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_40 (closed_word_40 v) (closed_word_40 v)).
Definition expr_word_41 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 39))).
Definition closed_word_41 (v : leaf_values) : VM.t hvalue := (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue)).
Definition word_41 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_41 (closed_word_41 v) (closed_word_41 v)).
Definition expr_word_42 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 41)).
Definition closed_word_42 (v : leaf_values) : VM.t hvalue := (VM.add 41 (Gval (Fuint 9) (word_41 v)) (VM.empty hvalue)).
Definition word_42 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_42 (closed_word_42 v) (closed_word_42 v)).
Definition expr_word_43 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 42))).
Definition closed_word_43 (v : leaf_values) : VM.t hvalue := (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)).
Definition word_43 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_43 (closed_word_43 v) (closed_word_43 v)).
Definition expr_word_44 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_44 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 8) (word_2 v)) (VM.empty hvalue)).
Definition word_44 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_44 (closed_word_44 v) (closed_word_44 v)).
Definition expr_word_45 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 44)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_45 (v : leaf_values) : VM.t hvalue := (VM.add 44 (Gval (Fuint 2) (word_44 v)) (VM.empty hvalue)).
Definition word_45 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_45 (closed_word_45 v) (closed_word_45 v)).
Definition expr_word_46 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_46 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_46 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_46 (closed_word_46 v) (closed_word_46 v)).
Definition expr_word_47 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 46)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_47 (v : leaf_values) : VM.t hvalue := (VM.add 46 (Gval (Fuint 1) (word_46 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue))).
Definition word_47 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_47 (closed_word_47 v) (closed_word_47 v)).
Definition expr_word_48 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_48 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_48 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_48 (closed_word_48 v) (closed_word_48 v)).
Definition expr_word_49 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 48)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Eref VarOrder.T (@Eid VarOrder.T 47))).
Definition closed_word_49 (v : leaf_values) : VM.t hvalue := (VM.add 48 (Gval (Fuint 1) (word_48 v)) (VM.add 47 (Gval (Fuint 9) (word_47 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue)))).
Definition word_49 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_49 (closed_word_49 v) (closed_word_49 v)).
Definition expr_word_50 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_50 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_50 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_50 (closed_word_50 v) (closed_word_50 v)).
Definition expr_word_51 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 0) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_word_51 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 10) (word_40 v)) (VM.empty hvalue)).
Definition word_51 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_51 (closed_word_51 v) (closed_word_51 v)).
Definition expr_word_52 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 50)) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Eref VarOrder.T (@Eid VarOrder.T 49))).
Definition closed_word_52 (v : leaf_values) : VM.t hvalue := (VM.add 51 (Gval (Fuint 9) (word_51 v)) (VM.add 50 (Gval (Fuint 1) (word_50 v)) (VM.add 49 (Gval (Fuint 9) (word_49 v)) (VM.empty hvalue)))).
Definition word_52 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_52 (closed_word_52 v) (closed_word_52 v)).
Definition expr_word_53 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_53 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_53 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_53 (closed_word_53 v) (closed_word_53 v)).
Definition expr_word_54 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 0) (@Eref VarOrder.T (@Eid VarOrder.T 43))).
Definition closed_word_54 (v : leaf_values) : VM.t hvalue := (VM.add 43 (Gval (Fuint 10) (word_43 v)) (VM.empty hvalue)).
Definition word_54 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_54 (closed_word_54 v) (closed_word_54 v)).
Definition expr_word_55 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 53)) (@Eref VarOrder.T (@Eid VarOrder.T 54)) (@Eref VarOrder.T (@Eid VarOrder.T 52))).
Definition closed_word_55 (v : leaf_values) : VM.t hvalue := (VM.add 54 (Gval (Fuint 9) (word_54 v)) (VM.add 53 (Gval (Fuint 1) (word_53 v)) (VM.add 52 (Gval (Fuint 9) (word_52 v)) (VM.empty hvalue)))).
Definition word_55 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_55 (closed_word_55 v) (closed_word_55 v)).
Definition expr_word_56 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_56 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_56 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_56 (closed_word_56 v) (closed_word_56 v)).
Definition expr_word_57 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 56)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 55))).
Definition closed_word_57 (v : leaf_values) : VM.t hvalue := (VM.add 56 (Gval (Fuint 1) (word_56 v)) (VM.add 55 (Gval (Fuint 9) (word_55 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_57 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_57 (closed_word_57 v) (closed_word_57 v)).
Definition expr_word_58 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_58 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_58 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_58 (closed_word_58 v) (closed_word_58 v)).
Definition expr_word_59 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 58)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 57))).
Definition closed_word_59 (v : leaf_values) : VM.t hvalue := (VM.add 58 (Gval (Fuint 1) (word_58 v)) (VM.add 57 (Gval (Fuint 9) (word_57 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_59 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_59 (closed_word_59 v) (closed_word_59 v)).
Definition expr_word_60 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 59))).
Definition closed_word_60 (v : leaf_values) : VM.t hvalue := (VM.add 59 (Gval (Fuint 9) (word_59 v)) (VM.empty hvalue)).
Definition word_60 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_60 (closed_word_60 v) (closed_word_60 v)).
Definition expr_word_61 : @hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 3) [::false; false; false]).
Definition closed_word_61 (v : leaf_values) : VM.t hvalue := (VM.empty hvalue).
Definition word_61 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_61 (closed_word_61 v) (closed_word_61 v)).
Definition expr_word_62 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 61))).
Definition closed_word_62 (v : leaf_values) : VM.t hvalue := (VM.add 61 (Gval (Fuint 3) (word_61 v)) (VM.empty hvalue)).
Definition word_62 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_62 (closed_word_62 v) (closed_word_62 v)).
Definition expr_word_63 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 62)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Definition closed_word_63 (v : leaf_values) : VM.t hvalue := (VM.add 62 (Gval (Fuint 1) (word_62 v)) (VM.empty hvalue)).
Definition word_63 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_63 (closed_word_63 v) (closed_word_63 v)).
Definition expr_word_64 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 61))).
Definition closed_word_64 (v : leaf_values) : VM.t hvalue := (VM.add 61 (Gval (Fuint 3) (word_61 v)) (VM.empty hvalue)).
Definition word_64 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_64 (closed_word_64 v) (closed_word_64 v)).
Definition expr_word_65 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 64)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 63))).
Definition closed_word_65 (v : leaf_values) : VM.t hvalue := (VM.add 64 (Gval (Fuint 1) (word_64 v)) (VM.add 63 (Gval (Fuint 2) (word_63 v)) (VM.empty hvalue))).
Definition word_65 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_65 (closed_word_65 v) (closed_word_65 v)).
Definition expr_word_66 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 61))).
Definition closed_word_66 (v : leaf_values) : VM.t hvalue := (VM.add 61 (Gval (Fuint 3) (word_61 v)) (VM.empty hvalue)).
Definition word_66 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_66 (closed_word_66 v) (closed_word_66 v)).
Definition expr_word_67 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 66)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 65))).
Definition closed_word_67 (v : leaf_values) : VM.t hvalue := (VM.add 66 (Gval (Fuint 1) (word_66 v)) (VM.add 65 (Gval (Fuint 2) (word_65 v)) (VM.empty hvalue))).
Definition word_67 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_67 (closed_word_67 v) (closed_word_67 v)).
Definition expr_word_68 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 60))).
Definition closed_word_68 (v : leaf_values) : VM.t hvalue := (VM.add 60 (Gval (Fuint 1) (word_60 v)) (VM.empty hvalue)).
Definition word_68 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_68 (closed_word_68 v) (closed_word_68 v)).
Definition expr_word_69 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 60)) (@Eref VarOrder.T (@Eid VarOrder.T 59))).
Definition closed_word_69 (v : leaf_values) : VM.t hvalue := (VM.add 60 (Gval (Fuint 1) (word_60 v)) (VM.add 59 (Gval (Fuint 9) (word_59 v)) (VM.empty hvalue))).
Definition word_69 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_69 (closed_word_69 v) (closed_word_69 v)).
Definition expr_word_70 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 68)) (@Eref VarOrder.T (@Eid VarOrder.T 60))).
Definition closed_word_70 (v : leaf_values) : VM.t hvalue := (VM.add 68 (Gval (Fuint 1) (word_68 v)) (VM.add 60 (Gval (Fuint 1) (word_60 v)) (VM.empty hvalue))).
Definition word_70 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_70 (closed_word_70 v) (closed_word_70 v)).
Definition expr_word_71 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 70)) (@Eref VarOrder.T (@Eid VarOrder.T 69))).
Definition closed_word_71 (v : leaf_values) : VM.t hvalue := (VM.add 70 (Gval (Fuint 2) (word_70 v)) (VM.add 69 (Gval (Fuint 10) (word_69 v)) (VM.empty hvalue))).
Definition word_71 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_71 (closed_word_71 v) (closed_word_71 v)).
Definition expr_word_72 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_72 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_72 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_72 (closed_word_72 v) (closed_word_72 v)).
Definition expr_word_73 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_73 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_73 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_73 (closed_word_73 v) (closed_word_73 v)).
Definition expr_word_74 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_74 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_74 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_74 (closed_word_74 v) (closed_word_74 v)).
Definition expr_word_75 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_75 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_75 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_75 (closed_word_75 v) (closed_word_75 v)).
Definition expr_word_76 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 4 4) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_76 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_76 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_76 (closed_word_76 v) (closed_word_76 v)).
Definition expr_word_77 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 5 5) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_77 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_77 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_77 (closed_word_77 v) (closed_word_77 v)).
Definition expr_word_78 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 6 6) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_78 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_78 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_78 (closed_word_78 v) (closed_word_78 v)).
Definition expr_word_79 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_79 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_79 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_79 (closed_word_79 v) (closed_word_79 v)).
Definition expr_word_80 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_80 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_80 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_80 (closed_word_80 v) (closed_word_80 v)).
Definition expr_word_81 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 9 9) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_81 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_81 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_81 (closed_word_81 v) (closed_word_81 v)).
Definition expr_word_82 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 10 10) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_82 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_82 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_82 (closed_word_82 v) (closed_word_82 v)).
Definition expr_word_83 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 11) (@Eref VarOrder.T (@Eid VarOrder.T 71))).
Definition closed_word_83 (v : leaf_values) : VM.t hvalue := (VM.add 71 (Gval (Fuint 12) (word_71 v)) (VM.empty hvalue)).
Definition word_83 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_83 (closed_word_83 v) (closed_word_83 v)).
Definition expr_word_84 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 1) (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_84 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 8) (word_2 v)) (VM.empty hvalue)).
Definition word_84 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_84 (closed_word_84 v) (closed_word_84 v)).
Definition expr_word_85 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_85 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_85 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_85 (closed_word_85 v) (closed_word_85 v)).
Definition expr_word_86 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 85)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_86 (v : leaf_values) : VM.t hvalue := (VM.add 85 (Gval (Fuint 1) (word_85 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue))).
Definition word_86 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_86 (closed_word_86 v) (closed_word_86 v)).
Definition expr_word_87 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_87 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_87 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_87 (closed_word_87 v) (closed_word_87 v)).
Definition expr_word_88 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 87)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Eref VarOrder.T (@Eid VarOrder.T 86))).
Definition closed_word_88 (v : leaf_values) : VM.t hvalue := (VM.add 87 (Gval (Fuint 1) (word_87 v)) (VM.add 86 (Gval (Fuint 9) (word_86 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue)))).
Definition word_88 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_88 (closed_word_88 v) (closed_word_88 v)).
Definition expr_word_89 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_89 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_89 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_89 (closed_word_89 v) (closed_word_89 v)).
Definition expr_word_90 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 89)) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Eref VarOrder.T (@Eid VarOrder.T 88))).
Definition closed_word_90 (v : leaf_values) : VM.t hvalue := (VM.add 89 (Gval (Fuint 1) (word_89 v)) (VM.add 88 (Gval (Fuint 9) (word_88 v)) (VM.add 51 (Gval (Fuint 9) (word_51 v)) (VM.empty hvalue)))).
Definition word_90 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_90 (closed_word_90 v) (closed_word_90 v)).
Definition expr_word_91 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_91 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_91 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_91 (closed_word_91 v) (closed_word_91 v)).
Definition expr_word_92 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 91)) (@Eref VarOrder.T (@Eid VarOrder.T 54)) (@Eref VarOrder.T (@Eid VarOrder.T 90))).
Definition closed_word_92 (v : leaf_values) : VM.t hvalue := (VM.add 91 (Gval (Fuint 1) (word_91 v)) (VM.add 90 (Gval (Fuint 9) (word_90 v)) (VM.add 54 (Gval (Fuint 9) (word_54 v)) (VM.empty hvalue)))).
Definition word_92 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_92 (closed_word_92 v) (closed_word_92 v)).
Definition expr_word_93 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_93 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_93 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_93 (closed_word_93 v) (closed_word_93 v)).
Definition expr_word_94 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 93)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 92))).
Definition closed_word_94 (v : leaf_values) : VM.t hvalue := (VM.add 93 (Gval (Fuint 1) (word_93 v)) (VM.add 92 (Gval (Fuint 9) (word_92 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_94 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_94 (closed_word_94 v) (closed_word_94 v)).
Definition expr_word_95 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_95 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_95 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_95 (closed_word_95 v) (closed_word_95 v)).
Definition expr_word_96 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 95)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 94))).
Definition closed_word_96 (v : leaf_values) : VM.t hvalue := (VM.add 95 (Gval (Fuint 1) (word_95 v)) (VM.add 94 (Gval (Fuint 9) (word_94 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_96 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_96 (closed_word_96 v) (closed_word_96 v)).
Definition expr_word_97 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 96))).
Definition closed_word_97 (v : leaf_values) : VM.t hvalue := (VM.add 96 (Gval (Fuint 9) (word_96 v)) (VM.empty hvalue)).
Definition word_97 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_97 (closed_word_97 v) (closed_word_97 v)).
Definition expr_word_98 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_98 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_98 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_98 (closed_word_98 v) (closed_word_98 v)).
Definition expr_word_99 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 98)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Definition closed_word_99 (v : leaf_values) : VM.t hvalue := (VM.add 98 (Gval (Fuint 1) (word_98 v)) (VM.empty hvalue)).
Definition word_99 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_99 (closed_word_99 v) (closed_word_99 v)).
Definition expr_word_100 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_100 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_100 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_100 (closed_word_100 v) (closed_word_100 v)).
Definition expr_word_101 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 100)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 99))).
Definition closed_word_101 (v : leaf_values) : VM.t hvalue := (VM.add 100 (Gval (Fuint 1) (word_100 v)) (VM.add 99 (Gval (Fuint 2) (word_99 v)) (VM.empty hvalue))).
Definition word_101 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_101 (closed_word_101 v) (closed_word_101 v)).
Definition expr_word_102 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_word_102 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 3) (word_45 v)) (VM.empty hvalue)).
Definition word_102 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_102 (closed_word_102 v) (closed_word_102 v)).
Definition expr_word_103 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 102)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 101))).
Definition closed_word_103 (v : leaf_values) : VM.t hvalue := (VM.add 102 (Gval (Fuint 1) (word_102 v)) (VM.add 101 (Gval (Fuint 2) (word_101 v)) (VM.empty hvalue))).
Definition word_103 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_103 (closed_word_103 v) (closed_word_103 v)).
Definition expr_word_104 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 97))).
Definition closed_word_104 (v : leaf_values) : VM.t hvalue := (VM.add 97 (Gval (Fuint 1) (word_97 v)) (VM.empty hvalue)).
Definition word_104 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_104 (closed_word_104 v) (closed_word_104 v)).
Definition expr_word_105 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 96)) (@Eref VarOrder.T (@Eid VarOrder.T 103))).
Definition closed_word_105 (v : leaf_values) : VM.t hvalue := (VM.add 103 (Gval (Fuint 2) (word_103 v)) (VM.add 96 (Gval (Fuint 9) (word_96 v)) (VM.empty hvalue))).
Definition word_105 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_105 (closed_word_105 v) (closed_word_105 v)).
Definition expr_word_106 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 104))).
Definition closed_word_106 (v : leaf_values) : VM.t hvalue := (VM.add 104 (Gval (Fuint 1) (word_104 v)) (VM.empty hvalue)).
Definition word_106 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_106 (closed_word_106 v) (closed_word_106 v)).
Definition expr_word_107 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 106)) (@Eref VarOrder.T (@Eid VarOrder.T 105))).
Definition closed_word_107 (v : leaf_values) : VM.t hvalue := (VM.add 106 (Gval (Fuint 2) (word_106 v)) (VM.add 105 (Gval (Fuint 11) (word_105 v)) (VM.empty hvalue))).
Definition word_107 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_107 (closed_word_107 v) (closed_word_107 v)).
Definition expr_word_108 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_108 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_108 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_108 (closed_word_108 v) (closed_word_108 v)).
Definition expr_word_109 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_109 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_109 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_109 (closed_word_109 v) (closed_word_109 v)).
Definition expr_word_110 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_110 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_110 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_110 (closed_word_110 v) (closed_word_110 v)).
Definition expr_word_111 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_111 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_111 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_111 (closed_word_111 v) (closed_word_111 v)).
Definition expr_word_112 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 4 4) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_112 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_112 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_112 (closed_word_112 v) (closed_word_112 v)).
Definition expr_word_113 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 5 5) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_113 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_113 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_113 (closed_word_113 v) (closed_word_113 v)).
Definition expr_word_114 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 6 6) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_114 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_114 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_114 (closed_word_114 v) (closed_word_114 v)).
Definition expr_word_115 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_115 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_115 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_115 (closed_word_115 v) (closed_word_115 v)).
Definition expr_word_116 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_116 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_116 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_116 (closed_word_116 v) (closed_word_116 v)).
Definition expr_word_117 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 9 9) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_117 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_117 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_117 (closed_word_117 v) (closed_word_117 v)).
Definition expr_word_118 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 10 10) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_118 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_118 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_118 (closed_word_118 v) (closed_word_118 v)).
Definition expr_word_119 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 11) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_119 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_119 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_119 (closed_word_119 v) (closed_word_119 v)).
Definition expr_word_120 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 12 12) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_word_120 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 13) (word_107 v)) (VM.empty hvalue)).
Definition word_120 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_120 (closed_word_120 v) (closed_word_120 v)).
Definition expr_word_121 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 5 3) (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_121 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 8) (word_2 v)) (VM.empty hvalue)).
Definition word_121 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_121 (closed_word_121 v) (closed_word_121 v)).
Definition expr_word_122 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_122 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_122 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_122 (closed_word_122 v) (closed_word_122 v)).
Definition expr_word_123 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 122)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_123 (v : leaf_values) : VM.t hvalue := (VM.add 122 (Gval (Fuint 1) (word_122 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue))).
Definition word_123 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_123 (closed_word_123 v) (closed_word_123 v)).
Definition expr_word_124 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_124 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_124 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_124 (closed_word_124 v) (closed_word_124 v)).
Definition expr_word_125 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 124)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Eref VarOrder.T (@Eid VarOrder.T 123))).
Definition closed_word_125 (v : leaf_values) : VM.t hvalue := (VM.add 124 (Gval (Fuint 1) (word_124 v)) (VM.add 123 (Gval (Fuint 9) (word_123 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue)))).
Definition word_125 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_125 (closed_word_125 v) (closed_word_125 v)).
Definition expr_word_126 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_126 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_126 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_126 (closed_word_126 v) (closed_word_126 v)).
Definition expr_word_127 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 126)) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Eref VarOrder.T (@Eid VarOrder.T 125))).
Definition closed_word_127 (v : leaf_values) : VM.t hvalue := (VM.add 126 (Gval (Fuint 1) (word_126 v)) (VM.add 125 (Gval (Fuint 9) (word_125 v)) (VM.add 51 (Gval (Fuint 9) (word_51 v)) (VM.empty hvalue)))).
Definition word_127 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_127 (closed_word_127 v) (closed_word_127 v)).
Definition expr_word_128 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_128 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_128 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_128 (closed_word_128 v) (closed_word_128 v)).
Definition expr_word_129 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 54)) (@Eref VarOrder.T (@Eid VarOrder.T 127))).
Definition closed_word_129 (v : leaf_values) : VM.t hvalue := (VM.add 128 (Gval (Fuint 1) (word_128 v)) (VM.add 127 (Gval (Fuint 9) (word_127 v)) (VM.add 54 (Gval (Fuint 9) (word_54 v)) (VM.empty hvalue)))).
Definition word_129 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_129 (closed_word_129 v) (closed_word_129 v)).
Definition expr_word_130 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_130 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_130 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_130 (closed_word_130 v) (closed_word_130 v)).
Definition expr_word_131 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 130)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 129))).
Definition closed_word_131 (v : leaf_values) : VM.t hvalue := (VM.add 130 (Gval (Fuint 1) (word_130 v)) (VM.add 129 (Gval (Fuint 9) (word_129 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_131 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_131 (closed_word_131 v) (closed_word_131 v)).
Definition expr_word_132 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_132 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_132 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_132 (closed_word_132 v) (closed_word_132 v)).
Definition expr_word_133 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 132)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 131))).
Definition closed_word_133 (v : leaf_values) : VM.t hvalue := (VM.add 132 (Gval (Fuint 1) (word_132 v)) (VM.add 131 (Gval (Fuint 9) (word_131 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_133 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_133 (closed_word_133 v) (closed_word_133 v)).
Definition expr_word_134 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 133))).
Definition closed_word_134 (v : leaf_values) : VM.t hvalue := (VM.add 133 (Gval (Fuint 9) (word_133 v)) (VM.empty hvalue)).
Definition word_134 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_134 (closed_word_134 v) (closed_word_134 v)).
Definition expr_word_135 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_135 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_135 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_135 (closed_word_135 v) (closed_word_135 v)).
Definition expr_word_136 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 135)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Definition closed_word_136 (v : leaf_values) : VM.t hvalue := (VM.add 135 (Gval (Fuint 1) (word_135 v)) (VM.empty hvalue)).
Definition word_136 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_136 (closed_word_136 v) (closed_word_136 v)).
Definition expr_word_137 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_137 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_137 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_137 (closed_word_137 v) (closed_word_137 v)).
Definition expr_word_138 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 137)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 136))).
Definition closed_word_138 (v : leaf_values) : VM.t hvalue := (VM.add 137 (Gval (Fuint 1) (word_137 v)) (VM.add 136 (Gval (Fuint 2) (word_136 v)) (VM.empty hvalue))).
Definition word_138 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_138 (closed_word_138 v) (closed_word_138 v)).
Definition expr_word_139 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 84))).
Definition closed_word_139 (v : leaf_values) : VM.t hvalue := (VM.add 84 (Gval (Fuint 3) (word_84 v)) (VM.empty hvalue)).
Definition word_139 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_139 (closed_word_139 v) (closed_word_139 v)).
Definition expr_word_140 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 139)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 138))).
Definition closed_word_140 (v : leaf_values) : VM.t hvalue := (VM.add 139 (Gval (Fuint 1) (word_139 v)) (VM.add 138 (Gval (Fuint 2) (word_138 v)) (VM.empty hvalue))).
Definition word_140 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_140 (closed_word_140 v) (closed_word_140 v)).
Definition expr_word_141 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 134))).
Definition closed_word_141 (v : leaf_values) : VM.t hvalue := (VM.add 134 (Gval (Fuint 1) (word_134 v)) (VM.empty hvalue)).
Definition word_141 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_141 (closed_word_141 v) (closed_word_141 v)).
Definition expr_word_142 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 133)) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Definition closed_word_142 (v : leaf_values) : VM.t hvalue := (VM.add 140 (Gval (Fuint 2) (word_140 v)) (VM.add 133 (Gval (Fuint 9) (word_133 v)) (VM.empty hvalue))).
Definition word_142 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_142 (closed_word_142 v) (closed_word_142 v)).
Definition expr_word_143 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 141))).
Definition closed_word_143 (v : leaf_values) : VM.t hvalue := (VM.add 141 (Gval (Fuint 1) (word_141 v)) (VM.empty hvalue)).
Definition word_143 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_143 (closed_word_143 v) (closed_word_143 v)).
Definition expr_word_144 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 143)) (@Eref VarOrder.T (@Eid VarOrder.T 142))).
Definition closed_word_144 (v : leaf_values) : VM.t hvalue := (VM.add 143 (Gval (Fuint 2) (word_143 v)) (VM.add 142 (Gval (Fuint 11) (word_142 v)) (VM.empty hvalue))).
Definition word_144 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_144 (closed_word_144 v) (closed_word_144 v)).
Definition expr_word_145 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_145 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_145 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_145 (closed_word_145 v) (closed_word_145 v)).
Definition expr_word_146 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_146 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_146 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_146 (closed_word_146 v) (closed_word_146 v)).
Definition expr_word_147 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_147 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_147 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_147 (closed_word_147 v) (closed_word_147 v)).
Definition expr_word_148 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_148 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_148 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_148 (closed_word_148 v) (closed_word_148 v)).
Definition expr_word_149 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 4 4) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_149 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_149 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_149 (closed_word_149 v) (closed_word_149 v)).
Definition expr_word_150 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 5 5) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_150 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_150 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_150 (closed_word_150 v) (closed_word_150 v)).
Definition expr_word_151 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 6 6) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_151 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_151 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_151 (closed_word_151 v) (closed_word_151 v)).
Definition expr_word_152 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_152 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_152 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_152 (closed_word_152 v) (closed_word_152 v)).
Definition expr_word_153 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_153 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_153 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_153 (closed_word_153 v) (closed_word_153 v)).
Definition expr_word_154 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 9 9) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_154 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_154 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_154 (closed_word_154 v) (closed_word_154 v)).
Definition expr_word_155 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 10 10) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_155 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_155 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_155 (closed_word_155 v) (closed_word_155 v)).
Definition expr_word_156 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 11) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_156 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_156 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_156 (closed_word_156 v) (closed_word_156 v)).
Definition expr_word_157 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 12 12) (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Definition closed_word_157 (v : leaf_values) : VM.t hvalue := (VM.add 144 (Gval (Fuint 13) (word_144 v)) (VM.empty hvalue)).
Definition word_157 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_157 (closed_word_157 v) (closed_word_157 v)).
Definition expr_word_158 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 5) (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_158 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 8) (word_2 v)) (VM.empty hvalue)).
Definition word_158 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_158 (closed_word_158 v) (closed_word_158 v)).
Definition expr_word_159 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_159 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_159 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_159 (closed_word_159 v) (closed_word_159 v)).
Definition expr_word_160 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 159)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_160 (v : leaf_values) : VM.t hvalue := (VM.add 159 (Gval (Fuint 1) (word_159 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue))).
Definition word_160 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_160 (closed_word_160 v) (closed_word_160 v)).
Definition expr_word_161 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_161 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_161 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_161 (closed_word_161 v) (closed_word_161 v)).
Definition expr_word_162 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 161)) (@Eref VarOrder.T (@Eid VarOrder.T 39)) (@Eref VarOrder.T (@Eid VarOrder.T 160))).
Definition closed_word_162 (v : leaf_values) : VM.t hvalue := (VM.add 161 (Gval (Fuint 1) (word_161 v)) (VM.add 160 (Gval (Fuint 9) (word_160 v)) (VM.add 39 (Gval (Fuint 9) (word_39 v)) (VM.empty hvalue)))).
Definition word_162 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_162 (closed_word_162 v) (closed_word_162 v)).
Definition expr_word_163 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_163 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_163 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_163 (closed_word_163 v) (closed_word_163 v)).
Definition expr_word_164 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 163)) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Eref VarOrder.T (@Eid VarOrder.T 162))).
Definition closed_word_164 (v : leaf_values) : VM.t hvalue := (VM.add 163 (Gval (Fuint 1) (word_163 v)) (VM.add 162 (Gval (Fuint 9) (word_162 v)) (VM.add 51 (Gval (Fuint 9) (word_51 v)) (VM.empty hvalue)))).
Definition word_164 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_164 (closed_word_164 v) (closed_word_164 v)).
Definition expr_word_165 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_165 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_165 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_165 (closed_word_165 v) (closed_word_165 v)).
Definition expr_word_166 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 165)) (@Eref VarOrder.T (@Eid VarOrder.T 54)) (@Eref VarOrder.T (@Eid VarOrder.T 164))).
Definition closed_word_166 (v : leaf_values) : VM.t hvalue := (VM.add 165 (Gval (Fuint 1) (word_165 v)) (VM.add 164 (Gval (Fuint 9) (word_164 v)) (VM.add 54 (Gval (Fuint 9) (word_54 v)) (VM.empty hvalue)))).
Definition word_166 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_166 (closed_word_166 v) (closed_word_166 v)).
Definition expr_word_167 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_167 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_167 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_167 (closed_word_167 v) (closed_word_167 v)).
Definition expr_word_168 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 167)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 166))).
Definition closed_word_168 (v : leaf_values) : VM.t hvalue := (VM.add 167 (Gval (Fuint 1) (word_167 v)) (VM.add 166 (Gval (Fuint 9) (word_166 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_168 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_168 (closed_word_168 v) (closed_word_168 v)).
Definition expr_word_169 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_169 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_169 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_169 (closed_word_169 v) (closed_word_169 v)).
Definition expr_word_170 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 169)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 168))).
Definition closed_word_170 (v : leaf_values) : VM.t hvalue := (VM.add 169 (Gval (Fuint 1) (word_169 v)) (VM.add 168 (Gval (Fuint 9) (word_168 v)) (VM.add 42 (Gval (Fuint 9) (word_42 v)) (VM.empty hvalue)))).
Definition word_170 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_170 (closed_word_170 v) (closed_word_170 v)).
Definition expr_word_171 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 170))).
Definition closed_word_171 (v : leaf_values) : VM.t hvalue := (VM.add 170 (Gval (Fuint 9) (word_170 v)) (VM.empty hvalue)).
Definition word_171 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_171 (closed_word_171 v) (closed_word_171 v)).
Definition expr_word_172 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_172 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_172 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_172 (closed_word_172 v) (closed_word_172 v)).
Definition expr_word_173 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 172)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Definition closed_word_173 (v : leaf_values) : VM.t hvalue := (VM.add 172 (Gval (Fuint 1) (word_172 v)) (VM.empty hvalue)).
Definition word_173 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_173 (closed_word_173 v) (closed_word_173 v)).
Definition expr_word_174 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_174 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_174 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_174 (closed_word_174 v) (closed_word_174 v)).
Definition expr_word_175 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 174)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 173))).
Definition closed_word_175 (v : leaf_values) : VM.t hvalue := (VM.add 174 (Gval (Fuint 1) (word_174 v)) (VM.add 173 (Gval (Fuint 2) (word_173 v)) (VM.empty hvalue))).
Definition word_175 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_175 (closed_word_175 v) (closed_word_175 v)).
Definition expr_word_176 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Definition closed_word_176 (v : leaf_values) : VM.t hvalue := (VM.add 121 (Gval (Fuint 3) (word_121 v)) (VM.empty hvalue)).
Definition word_176 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_176 (closed_word_176 v) (closed_word_176 v)).
Definition expr_word_177 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 176)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 175))).
Definition closed_word_177 (v : leaf_values) : VM.t hvalue := (VM.add 176 (Gval (Fuint 1) (word_176 v)) (VM.add 175 (Gval (Fuint 2) (word_175 v)) (VM.empty hvalue))).
Definition word_177 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_177 (closed_word_177 v) (closed_word_177 v)).
Definition expr_word_178 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 171))).
Definition closed_word_178 (v : leaf_values) : VM.t hvalue := (VM.add 171 (Gval (Fuint 1) (word_171 v)) (VM.empty hvalue)).
Definition word_178 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_178 (closed_word_178 v) (closed_word_178 v)).
Definition expr_word_179 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 178)) (@Eref VarOrder.T (@Eid VarOrder.T 170))).
Definition closed_word_179 (v : leaf_values) : VM.t hvalue := (VM.add 178 (Gval (Fuint 1) (word_178 v)) (VM.add 170 (Gval (Fuint 9) (word_170 v)) (VM.empty hvalue))).
Definition word_179 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_179 (closed_word_179 v) (closed_word_179 v)).
Definition expr_word_180 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 179)) (@Eref VarOrder.T (@Eid VarOrder.T 177))).
Definition closed_word_180 (v : leaf_values) : VM.t hvalue := (VM.add 179 (Gval (Fuint 10) (word_179 v)) (VM.add 177 (Gval (Fuint 2) (word_177 v)) (VM.empty hvalue))).
Definition word_180 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_180 (closed_word_180 v) (closed_word_180 v)).
Definition expr_word_181 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_181 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_181 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_181 (closed_word_181 v) (closed_word_181 v)).
Definition expr_word_182 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_182 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_182 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_182 (closed_word_182 v) (closed_word_182 v)).
Definition expr_word_183 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_183 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_183 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_183 (closed_word_183 v) (closed_word_183 v)).
Definition expr_word_184 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_184 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_184 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_184 (closed_word_184 v) (closed_word_184 v)).
Definition expr_word_185 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 4 4) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_185 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_185 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_185 (closed_word_185 v) (closed_word_185 v)).
Definition expr_word_186 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 5 5) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_186 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_186 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_186 (closed_word_186 v) (closed_word_186 v)).
Definition expr_word_187 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 6 6) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_187 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_187 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_187 (closed_word_187 v) (closed_word_187 v)).
Definition expr_word_188 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_188 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_188 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_188 (closed_word_188 v) (closed_word_188 v)).
Definition expr_word_189 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_189 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_189 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_189 (closed_word_189 v) (closed_word_189 v)).
Definition expr_word_190 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 9 9) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_190 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_190 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_190 (closed_word_190 v) (closed_word_190 v)).
Definition expr_word_191 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 10 10) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_191 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_191 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_191 (closed_word_191 v) (closed_word_191 v)).
Definition expr_word_192 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 11) (@Eref VarOrder.T (@Eid VarOrder.T 180))).
Definition closed_word_192 (v : leaf_values) : VM.t hvalue := (VM.add 180 (Gval (Fuint 12) (word_180 v)) (VM.empty hvalue)).
Definition word_192 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_192 (closed_word_192 v) (closed_word_192 v)).
Definition expr_word_193 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_193 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_193 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_193 (closed_word_193 v) (closed_word_193 v)).
Definition expr_word_194 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 193)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Definition closed_word_194 (v : leaf_values) : VM.t hvalue := (VM.add 193 (Gval (Fuint 1) (word_193 v)) (VM.empty hvalue)).
Definition word_194 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_194 (closed_word_194 v) (closed_word_194 v)).
Definition expr_word_195 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_195 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_195 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_195 (closed_word_195 v) (closed_word_195 v)).
Definition expr_word_196 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 195)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 194))).
Definition closed_word_196 (v : leaf_values) : VM.t hvalue := (VM.add 195 (Gval (Fuint 1) (word_195 v)) (VM.add 194 (Gval (Fuint 2) (word_194 v)) (VM.empty hvalue))).
Definition word_196 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_196 (closed_word_196 v) (closed_word_196 v)).
Definition expr_word_197 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_word_197 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 3) (word_158 v)) (VM.empty hvalue)).
Definition word_197 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_197 (closed_word_197 v) (closed_word_197 v)).
Definition expr_word_198 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 197)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 196))).
Definition closed_word_198 (v : leaf_values) : VM.t hvalue := (VM.add 197 (Gval (Fuint 1) (word_197 v)) (VM.add 196 (Gval (Fuint 2) (word_196 v)) (VM.empty hvalue))).
Definition word_198 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_198 (closed_word_198 v) (closed_word_198 v)).
Definition expr_word_199 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 198))).
Definition closed_word_199 (v : leaf_values) : VM.t hvalue := (VM.add 198 (Gval (Fuint 2) (word_198 v)) (VM.empty hvalue)).
Definition word_199 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_199 (closed_word_199 v) (closed_word_199 v)).
Definition expr_word_200 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 198))).
Definition closed_word_200 (v : leaf_values) : VM.t hvalue := (VM.add 198 (Gval (Fuint 2) (word_198 v)) (VM.empty hvalue)).
Definition word_200 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_200 (closed_word_200 v) (closed_word_200 v)).
Definition expr_word_202 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 72)) (@Eref VarOrder.T (@Eid VarOrder.T 201))).
Definition closed_word_202 (v : leaf_values) : VM.t hvalue := (VM.add 201 (Gval (Fuint 1) (word_201 v)) (VM.add 72 (Gval (Fuint 1) (word_72 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_202 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_202 (closed_word_202 v) (closed_word_202 v)).
Definition expr_word_204 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 108)) (@Eref VarOrder.T (@Eid VarOrder.T 203))).
Definition closed_word_204 (v : leaf_values) : VM.t hvalue := (VM.add 203 (Gval (Fuint 1) (word_203 v)) (VM.add 108 (Gval (Fuint 1) (word_108 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_204 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_204 (closed_word_204 v) (closed_word_204 v)).
Definition expr_word_206 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 73)) (@Eref VarOrder.T (@Eid VarOrder.T 205))).
Definition closed_word_206 (v : leaf_values) : VM.t hvalue := (VM.add 205 (Gval (Fuint 1) (word_205 v)) (VM.add 73 (Gval (Fuint 1) (word_73 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_206 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_206 (closed_word_206 v) (closed_word_206 v)).
Definition expr_word_208 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 109)) (@Eref VarOrder.T (@Eid VarOrder.T 207))).
Definition closed_word_208 (v : leaf_values) : VM.t hvalue := (VM.add 207 (Gval (Fuint 1) (word_207 v)) (VM.add 109 (Gval (Fuint 1) (word_109 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_208 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_208 (closed_word_208 v) (closed_word_208 v)).
Definition expr_word_210 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 74)) (@Eref VarOrder.T (@Eid VarOrder.T 209))).
Definition closed_word_210 (v : leaf_values) : VM.t hvalue := (VM.add 209 (Gval (Fuint 1) (word_209 v)) (VM.add 74 (Gval (Fuint 1) (word_74 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_210 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_210 (closed_word_210 v) (closed_word_210 v)).
Definition expr_word_212 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 110)) (@Eref VarOrder.T (@Eid VarOrder.T 211))).
Definition closed_word_212 (v : leaf_values) : VM.t hvalue := (VM.add 211 (Gval (Fuint 1) (word_211 v)) (VM.add 110 (Gval (Fuint 1) (word_110 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_212 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_212 (closed_word_212 v) (closed_word_212 v)).
Definition expr_word_214 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 145)) (@Eref VarOrder.T (@Eid VarOrder.T 213))).
Definition closed_word_214 (v : leaf_values) : VM.t hvalue := (VM.add 213 (Gval (Fuint 1) (word_213 v)) (VM.add 145 (Gval (Fuint 1) (word_145 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_214 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_214 (closed_word_214 v) (closed_word_214 v)).
Definition expr_word_216 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 75)) (@Eref VarOrder.T (@Eid VarOrder.T 215))).
Definition closed_word_216 (v : leaf_values) : VM.t hvalue := (VM.add 215 (Gval (Fuint 1) (word_215 v)) (VM.add 75 (Gval (Fuint 1) (word_75 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_216 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_216 (closed_word_216 v) (closed_word_216 v)).
Definition expr_word_218 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 111)) (@Eref VarOrder.T (@Eid VarOrder.T 217))).
Definition closed_word_218 (v : leaf_values) : VM.t hvalue := (VM.add 217 (Gval (Fuint 1) (word_217 v)) (VM.add 111 (Gval (Fuint 1) (word_111 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_218 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_218 (closed_word_218 v) (closed_word_218 v)).
Definition expr_word_220 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 146)) (@Eref VarOrder.T (@Eid VarOrder.T 219))).
Definition closed_word_220 (v : leaf_values) : VM.t hvalue := (VM.add 219 (Gval (Fuint 1) (word_219 v)) (VM.add 146 (Gval (Fuint 1) (word_146 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_220 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_220 (closed_word_220 v) (closed_word_220 v)).
Definition expr_word_222 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 76)) (@Eref VarOrder.T (@Eid VarOrder.T 221))).
Definition closed_word_222 (v : leaf_values) : VM.t hvalue := (VM.add 221 (Gval (Fuint 1) (word_221 v)) (VM.add 76 (Gval (Fuint 1) (word_76 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_222 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_222 (closed_word_222 v) (closed_word_222 v)).
Definition expr_word_224 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 112)) (@Eref VarOrder.T (@Eid VarOrder.T 223))).
Definition closed_word_224 (v : leaf_values) : VM.t hvalue := (VM.add 223 (Gval (Fuint 1) (word_223 v)) (VM.add 112 (Gval (Fuint 1) (word_112 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_224 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_224 (closed_word_224 v) (closed_word_224 v)).
Definition expr_word_226 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 147)) (@Eref VarOrder.T (@Eid VarOrder.T 225))).
Definition closed_word_226 (v : leaf_values) : VM.t hvalue := (VM.add 225 (Gval (Fuint 1) (word_225 v)) (VM.add 147 (Gval (Fuint 1) (word_147 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_226 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_226 (closed_word_226 v) (closed_word_226 v)).
Definition expr_word_228 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 181)) (@Eref VarOrder.T (@Eid VarOrder.T 227))).
Definition closed_word_228 (v : leaf_values) : VM.t hvalue := (VM.add 227 (Gval (Fuint 1) (word_227 v)) (VM.add 181 (Gval (Fuint 1) (word_181 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_228 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_228 (closed_word_228 v) (closed_word_228 v)).
Definition expr_word_230 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 77)) (@Eref VarOrder.T (@Eid VarOrder.T 229))).
Definition closed_word_230 (v : leaf_values) : VM.t hvalue := (VM.add 229 (Gval (Fuint 1) (word_229 v)) (VM.add 77 (Gval (Fuint 1) (word_77 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_230 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_230 (closed_word_230 v) (closed_word_230 v)).
Definition expr_word_232 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 113)) (@Eref VarOrder.T (@Eid VarOrder.T 231))).
Definition closed_word_232 (v : leaf_values) : VM.t hvalue := (VM.add 231 (Gval (Fuint 1) (word_231 v)) (VM.add 113 (Gval (Fuint 1) (word_113 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_232 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_232 (closed_word_232 v) (closed_word_232 v)).
Definition expr_word_234 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 148)) (@Eref VarOrder.T (@Eid VarOrder.T 233))).
Definition closed_word_234 (v : leaf_values) : VM.t hvalue := (VM.add 233 (Gval (Fuint 1) (word_233 v)) (VM.add 148 (Gval (Fuint 1) (word_148 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_234 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_234 (closed_word_234 v) (closed_word_234 v)).
Definition expr_word_236 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 182)) (@Eref VarOrder.T (@Eid VarOrder.T 235))).
Definition closed_word_236 (v : leaf_values) : VM.t hvalue := (VM.add 235 (Gval (Fuint 1) (word_235 v)) (VM.add 182 (Gval (Fuint 1) (word_182 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_236 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_236 (closed_word_236 v) (closed_word_236 v)).
Definition expr_word_238 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 78)) (@Eref VarOrder.T (@Eid VarOrder.T 237))).
Definition closed_word_238 (v : leaf_values) : VM.t hvalue := (VM.add 237 (Gval (Fuint 1) (word_237 v)) (VM.add 78 (Gval (Fuint 1) (word_78 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_238 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_238 (closed_word_238 v) (closed_word_238 v)).
Definition expr_word_240 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 114)) (@Eref VarOrder.T (@Eid VarOrder.T 239))).
Definition closed_word_240 (v : leaf_values) : VM.t hvalue := (VM.add 239 (Gval (Fuint 1) (word_239 v)) (VM.add 114 (Gval (Fuint 1) (word_114 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_240 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_240 (closed_word_240 v) (closed_word_240 v)).
Definition expr_word_242 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 149)) (@Eref VarOrder.T (@Eid VarOrder.T 241))).
Definition closed_word_242 (v : leaf_values) : VM.t hvalue := (VM.add 241 (Gval (Fuint 1) (word_241 v)) (VM.add 149 (Gval (Fuint 1) (word_149 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_242 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_242 (closed_word_242 v) (closed_word_242 v)).
Definition expr_word_244 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 183)) (@Eref VarOrder.T (@Eid VarOrder.T 243))).
Definition closed_word_244 (v : leaf_values) : VM.t hvalue := (VM.add 243 (Gval (Fuint 1) (word_243 v)) (VM.add 183 (Gval (Fuint 1) (word_183 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_244 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_244 (closed_word_244 v) (closed_word_244 v)).
Definition expr_word_246 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 199)) (@Eref VarOrder.T (@Eid VarOrder.T 245))).
Definition closed_word_246 (v : leaf_values) : VM.t hvalue := (VM.add 245 (Gval (Fuint 1) (word_245 v)) (VM.add 199 (Gval (Fuint 1) (word_199 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_246 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_246 (closed_word_246 v) (closed_word_246 v)).
Definition expr_word_248 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 79)) (@Eref VarOrder.T (@Eid VarOrder.T 247))).
Definition closed_word_248 (v : leaf_values) : VM.t hvalue := (VM.add 247 (Gval (Fuint 1) (word_247 v)) (VM.add 79 (Gval (Fuint 1) (word_79 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_248 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_248 (closed_word_248 v) (closed_word_248 v)).
Definition expr_word_250 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (@Eref VarOrder.T (@Eid VarOrder.T 249))).
Definition closed_word_250 (v : leaf_values) : VM.t hvalue := (VM.add 249 (Gval (Fuint 1) (word_249 v)) (VM.add 115 (Gval (Fuint 1) (word_115 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_250 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_250 (closed_word_250 v) (closed_word_250 v)).
Definition expr_word_252 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 150)) (@Eref VarOrder.T (@Eid VarOrder.T 251))).
Definition closed_word_252 (v : leaf_values) : VM.t hvalue := (VM.add 251 (Gval (Fuint 1) (word_251 v)) (VM.add 150 (Gval (Fuint 1) (word_150 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_252 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_252 (closed_word_252 v) (closed_word_252 v)).
Definition expr_word_254 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 184)) (@Eref VarOrder.T (@Eid VarOrder.T 253))).
Definition closed_word_254 (v : leaf_values) : VM.t hvalue := (VM.add 253 (Gval (Fuint 1) (word_253 v)) (VM.add 184 (Gval (Fuint 1) (word_184 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_254 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_254 (closed_word_254 v) (closed_word_254 v)).
Definition expr_word_256 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 200)) (@Eref VarOrder.T (@Eid VarOrder.T 255))).
Definition closed_word_256 (v : leaf_values) : VM.t hvalue := (VM.add 255 (Gval (Fuint 1) (word_255 v)) (VM.add 200 (Gval (Fuint 1) (word_200 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_256 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_256 (closed_word_256 v) (closed_word_256 v)).
Definition expr_word_258 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 80)) (@Eref VarOrder.T (@Eid VarOrder.T 257))).
Definition closed_word_258 (v : leaf_values) : VM.t hvalue := (VM.add 257 (Gval (Fuint 1) (word_257 v)) (VM.add 80 (Gval (Fuint 1) (word_80 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_258 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_258 (closed_word_258 v) (closed_word_258 v)).
Definition expr_word_260 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Eref VarOrder.T (@Eid VarOrder.T 259))).
Definition closed_word_260 (v : leaf_values) : VM.t hvalue := (VM.add 259 (Gval (Fuint 1) (word_259 v)) (VM.add 116 (Gval (Fuint 1) (word_116 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_260 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_260 (closed_word_260 v) (closed_word_260 v)).
Definition expr_word_262 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 151)) (@Eref VarOrder.T (@Eid VarOrder.T 261))).
Definition closed_word_262 (v : leaf_values) : VM.t hvalue := (VM.add 261 (Gval (Fuint 1) (word_261 v)) (VM.add 151 (Gval (Fuint 1) (word_151 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_262 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_262 (closed_word_262 v) (closed_word_262 v)).
Definition expr_word_264 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 185)) (@Eref VarOrder.T (@Eid VarOrder.T 263))).
Definition closed_word_264 (v : leaf_values) : VM.t hvalue := (VM.add 263 (Gval (Fuint 1) (word_263 v)) (VM.add 185 (Gval (Fuint 1) (word_185 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_264 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_264 (closed_word_264 v) (closed_word_264 v)).
Definition expr_word_266 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 81)) (@Eref VarOrder.T (@Eid VarOrder.T 265))).
Definition closed_word_266 (v : leaf_values) : VM.t hvalue := (VM.add 265 (Gval (Fuint 1) (word_265 v)) (VM.add 81 (Gval (Fuint 1) (word_81 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_266 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_266 (closed_word_266 v) (closed_word_266 v)).
Definition expr_word_268 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 117)) (@Eref VarOrder.T (@Eid VarOrder.T 267))).
Definition closed_word_268 (v : leaf_values) : VM.t hvalue := (VM.add 267 (Gval (Fuint 1) (word_267 v)) (VM.add 117 (Gval (Fuint 1) (word_117 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_268 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_268 (closed_word_268 v) (closed_word_268 v)).
Definition expr_word_270 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 152)) (@Eref VarOrder.T (@Eid VarOrder.T 269))).
Definition closed_word_270 (v : leaf_values) : VM.t hvalue := (VM.add 269 (Gval (Fuint 1) (word_269 v)) (VM.add 152 (Gval (Fuint 1) (word_152 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_270 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_270 (closed_word_270 v) (closed_word_270 v)).
Definition expr_word_272 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 186)) (@Eref VarOrder.T (@Eid VarOrder.T 271))).
Definition closed_word_272 (v : leaf_values) : VM.t hvalue := (VM.add 271 (Gval (Fuint 1) (word_271 v)) (VM.add 186 (Gval (Fuint 1) (word_186 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_272 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_272 (closed_word_272 v) (closed_word_272 v)).
Definition expr_word_274 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 82)) (@Eref VarOrder.T (@Eid VarOrder.T 273))).
Definition closed_word_274 (v : leaf_values) : VM.t hvalue := (VM.add 273 (Gval (Fuint 1) (word_273 v)) (VM.add 82 (Gval (Fuint 1) (word_82 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_274 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_274 (closed_word_274 v) (closed_word_274 v)).
Definition expr_word_276 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 118)) (@Eref VarOrder.T (@Eid VarOrder.T 275))).
Definition closed_word_276 (v : leaf_values) : VM.t hvalue := (VM.add 275 (Gval (Fuint 1) (word_275 v)) (VM.add 118 (Gval (Fuint 1) (word_118 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_276 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_276 (closed_word_276 v) (closed_word_276 v)).
Definition expr_word_278 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 153)) (@Eref VarOrder.T (@Eid VarOrder.T 277))).
Definition closed_word_278 (v : leaf_values) : VM.t hvalue := (VM.add 277 (Gval (Fuint 1) (word_277 v)) (VM.add 153 (Gval (Fuint 1) (word_153 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_278 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_278 (closed_word_278 v) (closed_word_278 v)).
Definition expr_word_280 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 279))).
Definition closed_word_280 (v : leaf_values) : VM.t hvalue := (VM.add 279 (Gval (Fuint 1) (word_279 v)) (VM.add 187 (Gval (Fuint 1) (word_187 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_280 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_280 (closed_word_280 v) (closed_word_280 v)).
Definition expr_word_282 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 83)) (@Eref VarOrder.T (@Eid VarOrder.T 281))).
Definition closed_word_282 (v : leaf_values) : VM.t hvalue := (VM.add 281 (Gval (Fuint 1) (word_281 v)) (VM.add 83 (Gval (Fuint 1) (word_83 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_282 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_282 (closed_word_282 v) (closed_word_282 v)).
Definition expr_word_284 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 119)) (@Eref VarOrder.T (@Eid VarOrder.T 283))).
Definition closed_word_284 (v : leaf_values) : VM.t hvalue := (VM.add 283 (Gval (Fuint 1) (word_283 v)) (VM.add 119 (Gval (Fuint 1) (word_119 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_284 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_284 (closed_word_284 v) (closed_word_284 v)).
Definition expr_word_286 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 154)) (@Eref VarOrder.T (@Eid VarOrder.T 285))).
Definition closed_word_286 (v : leaf_values) : VM.t hvalue := (VM.add 285 (Gval (Fuint 1) (word_285 v)) (VM.add 154 (Gval (Fuint 1) (word_154 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_286 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_286 (closed_word_286 v) (closed_word_286 v)).
Definition expr_word_288 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 287))).
Definition closed_word_288 (v : leaf_values) : VM.t hvalue := (VM.add 287 (Gval (Fuint 1) (word_287 v)) (VM.add 188 (Gval (Fuint 1) (word_188 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_288 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_288 (closed_word_288 v) (closed_word_288 v)).
Definition expr_word_290 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 120)) (@Eref VarOrder.T (@Eid VarOrder.T 289))).
Definition closed_word_290 (v : leaf_values) : VM.t hvalue := (VM.add 289 (Gval (Fuint 1) (word_289 v)) (VM.add 120 (Gval (Fuint 1) (word_120 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_290 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_290 (closed_word_290 v) (closed_word_290 v)).
Definition expr_word_292 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 155)) (@Eref VarOrder.T (@Eid VarOrder.T 291))).
Definition closed_word_292 (v : leaf_values) : VM.t hvalue := (VM.add 291 (Gval (Fuint 1) (word_291 v)) (VM.add 155 (Gval (Fuint 1) (word_155 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_292 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_292 (closed_word_292 v) (closed_word_292 v)).
Definition expr_word_294 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 293))).
Definition closed_word_294 (v : leaf_values) : VM.t hvalue := (VM.add 293 (Gval (Fuint 1) (word_293 v)) (VM.add 189 (Gval (Fuint 1) (word_189 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_294 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_294 (closed_word_294 v) (closed_word_294 v)).
Definition expr_word_296 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 156)) (@Eref VarOrder.T (@Eid VarOrder.T 295))).
Definition closed_word_296 (v : leaf_values) : VM.t hvalue := (VM.add 295 (Gval (Fuint 1) (word_295 v)) (VM.add 156 (Gval (Fuint 1) (word_156 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_296 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_296 (closed_word_296 v) (closed_word_296 v)).
Definition expr_word_298 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 297))).
Definition closed_word_298 (v : leaf_values) : VM.t hvalue := (VM.add 297 (Gval (Fuint 1) (word_297 v)) (VM.add 190 (Gval (Fuint 1) (word_190 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_298 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_298 (closed_word_298 v) (closed_word_298 v)).
Definition expr_word_300 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 157)) (@Eref VarOrder.T (@Eid VarOrder.T 299))).
Definition closed_word_300 (v : leaf_values) : VM.t hvalue := (VM.add 299 (Gval (Fuint 1) (word_299 v)) (VM.add 157 (Gval (Fuint 1) (word_157 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_300 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_300 (closed_word_300 v) (closed_word_300 v)).
Definition expr_word_302 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 301))).
Definition closed_word_302 (v : leaf_values) : VM.t hvalue := (VM.add 301 (Gval (Fuint 1) (word_301 v)) (VM.add 191 (Gval (Fuint 1) (word_191 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_302 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_302 (closed_word_302 v) (closed_word_302 v)).
Definition expr_word_304 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 303))).
Definition closed_word_304 (v : leaf_values) : VM.t hvalue := (VM.add 303 (Gval (Fuint 1) (word_303 v)) (VM.add 192 (Gval (Fuint 1) (word_192 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_304 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_304 (closed_word_304 v) (closed_word_304 v)).
Definition expr_word_305 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 4))).
Definition closed_word_305 (v : leaf_values) : VM.t hvalue := (VM.add 7 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_7_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_305 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_305 (closed_word_305 v) (closed_word_305 v)).
Definition expr_word_306 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 7) 5))).
Definition closed_word_306 (v : leaf_values) : VM.t hvalue := (VM.add 7 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_7_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_306 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_306 (closed_word_306 v) (closed_word_306 v)).
Definition expr_word_307 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 4))).
Definition closed_word_307 (v : leaf_values) : VM.t hvalue := (VM.add 8 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_8_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_307 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_307 (closed_word_307 v) (closed_word_307 v)).
Definition expr_word_308 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 8) 5))).
Definition closed_word_308 (v : leaf_values) : VM.t hvalue := (VM.add 8 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_8_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_308 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_308 (closed_word_308 v) (closed_word_308 v)).
Definition expr_word_309 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 5))).
Definition closed_word_309 (v : leaf_values) : VM.t hvalue := (VM.add 9 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_9_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_309 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_309 (closed_word_309 v) (closed_word_309 v)).
Definition expr_word_310 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9) 6))).
Definition closed_word_310 (v : leaf_values) : VM.t hvalue := (VM.add 9 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_9_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_310 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_310 (closed_word_310 v) (closed_word_310 v)).
Definition expr_word_311 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 5))).
Definition closed_word_311 (v : leaf_values) : VM.t hvalue := (VM.add 10 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_10_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_311 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_311 (closed_word_311 v) (closed_word_311 v)).
Definition expr_word_312 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 6))).
Definition closed_word_312 (v : leaf_values) : VM.t hvalue := (VM.add 10 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_10_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_312 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_312 (closed_word_312 v) (closed_word_312 v)).
Definition expr_word_313 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 7))).
Definition closed_word_313 (v : leaf_values) : VM.t hvalue := (VM.add 11 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_11_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_313 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_313 (closed_word_313 v) (closed_word_313 v)).
Definition expr_word_314 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 8))).
Definition closed_word_314 (v : leaf_values) : VM.t hvalue := (VM.add 11 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_11_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_314 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_314 (closed_word_314 v) (closed_word_314 v)).
Definition expr_word_315 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 9))).
Definition closed_word_315 (v : leaf_values) : VM.t hvalue := (VM.add 11 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_11_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_315 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_315 (closed_word_315 v) (closed_word_315 v)).
Definition expr_word_316 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 7))).
Definition closed_word_316 (v : leaf_values) : VM.t hvalue := (VM.add 12 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_12_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_316 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_316 (closed_word_316 v) (closed_word_316 v)).
Definition expr_word_317 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 8))).
Definition closed_word_317 (v : leaf_values) : VM.t hvalue := (VM.add 12 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_12_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_317 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_317 (closed_word_317 v) (closed_word_317 v)).
Definition expr_word_318 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 12) 9))).
Definition closed_word_318 (v : leaf_values) : VM.t hvalue := (VM.add 12 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_12_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_318 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_318 (closed_word_318 v) (closed_word_318 v)).
Definition expr_word_319 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 7))).
Definition closed_word_319 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_13_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_319 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_319 (closed_word_319 v) (closed_word_319 v)).
Definition expr_word_320 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 8))).
Definition closed_word_320 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_13_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_320 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_320 (closed_word_320 v) (closed_word_320 v)).
Definition expr_word_321 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 13) 9))).
Definition closed_word_321 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_13_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_321 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_321 (closed_word_321 v) (closed_word_321 v)).
Definition expr_word_322 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 7))).
Definition closed_word_322 (v : leaf_values) : VM.t hvalue := (VM.add 14 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_14_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_322 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_322 (closed_word_322 v) (closed_word_322 v)).
Definition expr_word_323 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 8))).
Definition closed_word_323 (v : leaf_values) : VM.t hvalue := (VM.add 14 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_14_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_323 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_323 (closed_word_323 v) (closed_word_323 v)).
Definition expr_word_324 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 14) 9))).
Definition closed_word_324 (v : leaf_values) : VM.t hvalue := (VM.add 14 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_14_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_324 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_324 (closed_word_324 v) (closed_word_324 v)).
Definition expr_word_325 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 7))).
Definition closed_word_325 (v : leaf_values) : VM.t hvalue := (VM.add 15 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_15_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_325 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_325 (closed_word_325 v) (closed_word_325 v)).
Definition expr_word_326 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 8))).
Definition closed_word_326 (v : leaf_values) : VM.t hvalue := (VM.add 15 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_15_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_326 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_326 (closed_word_326 v) (closed_word_326 v)).
Definition expr_word_327 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 15) 9))).
Definition closed_word_327 (v : leaf_values) : VM.t hvalue := (VM.add 15 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_15_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_327 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_327 (closed_word_327 v) (closed_word_327 v)).
Definition expr_word_328 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 7))).
Definition closed_word_328 (v : leaf_values) : VM.t hvalue := (VM.add 16 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_16_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_328 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_328 (closed_word_328 v) (closed_word_328 v)).
Definition expr_word_329 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 8))).
Definition closed_word_329 (v : leaf_values) : VM.t hvalue := (VM.add 16 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_16_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_329 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_329 (closed_word_329 v) (closed_word_329 v)).
Definition expr_word_330 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 16) 9))).
Definition closed_word_330 (v : leaf_values) : VM.t hvalue := (VM.add 16 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_16_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_330 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_330 (closed_word_330 v) (closed_word_330 v)).
Definition expr_word_331 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 7))).
Definition closed_word_331 (v : leaf_values) : VM.t hvalue := (VM.add 17 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_17_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_331 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_331 (closed_word_331 v) (closed_word_331 v)).
Definition expr_word_332 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 8))).
Definition closed_word_332 (v : leaf_values) : VM.t hvalue := (VM.add 17 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_17_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_332 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_332 (closed_word_332 v) (closed_word_332 v)).
Definition expr_word_333 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 17) 9))).
Definition closed_word_333 (v : leaf_values) : VM.t hvalue := (VM.add 17 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_17_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_333 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_333 (closed_word_333 v) (closed_word_333 v)).
Definition expr_word_334 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 7))).
Definition closed_word_334 (v : leaf_values) : VM.t hvalue := (VM.add 18 (Bval (Bflips 7 Nflip (Gval (Fuint 1) (port_18_7 v)) Bnil)) (VM.empty hvalue)).
Definition word_334 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_334 (closed_word_334 v) (closed_word_334 v)).
Definition expr_word_335 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 8))).
Definition closed_word_335 (v : leaf_values) : VM.t hvalue := (VM.add 18 (Bval (Bflips 8 Nflip (Gval (Fuint 1) (port_18_8 v)) Bnil)) (VM.empty hvalue)).
Definition word_335 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_335 (closed_word_335 v) (closed_word_335 v)).
Definition expr_word_336 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 18) 9))).
Definition closed_word_336 (v : leaf_values) : VM.t hvalue := (VM.add 18 (Bval (Bflips 9 Nflip (Gval (Fuint 1) (port_18_9 v)) Bnil)) (VM.empty hvalue)).
Definition word_336 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_336 (closed_word_336 v) (closed_word_336 v)).
Definition expr_word_337 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 5))).
Definition closed_word_337 (v : leaf_values) : VM.t hvalue := (VM.add 19 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_19_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_337 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_337 (closed_word_337 v) (closed_word_337 v)).
Definition expr_word_338 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 19) 6))).
Definition closed_word_338 (v : leaf_values) : VM.t hvalue := (VM.add 19 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_19_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_338 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_338 (closed_word_338 v) (closed_word_338 v)).
Definition expr_word_339 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 4))).
Definition closed_word_339 (v : leaf_values) : VM.t hvalue := (VM.add 20 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_20_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_339 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_339 (closed_word_339 v) (closed_word_339 v)).
Definition expr_word_340 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 20) 5))).
Definition closed_word_340 (v : leaf_values) : VM.t hvalue := (VM.add 20 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_20_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_340 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_340 (closed_word_340 v) (closed_word_340 v)).
Definition expr_word_341 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 4))).
Definition closed_word_341 (v : leaf_values) : VM.t hvalue := (VM.add 21 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_21_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_341 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_341 (closed_word_341 v) (closed_word_341 v)).
Definition expr_word_342 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 21) 5))).
Definition closed_word_342 (v : leaf_values) : VM.t hvalue := (VM.add 21 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_21_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_342 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_342 (closed_word_342 v) (closed_word_342 v)).
Definition expr_word_343 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 4))).
Definition closed_word_343 (v : leaf_values) : VM.t hvalue := (VM.add 22 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_22_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_343 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_343 (closed_word_343 v) (closed_word_343 v)).
Definition expr_word_344 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 22) 5))).
Definition closed_word_344 (v : leaf_values) : VM.t hvalue := (VM.add 22 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_22_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_344 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_344 (closed_word_344 v) (closed_word_344 v)).
Definition expr_word_345 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 4))).
Definition closed_word_345 (v : leaf_values) : VM.t hvalue := (VM.add 23 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_23_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_345 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_345 (closed_word_345 v) (closed_word_345 v)).
Definition expr_word_346 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 23) 5))).
Definition closed_word_346 (v : leaf_values) : VM.t hvalue := (VM.add 23 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_23_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_346 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_346 (closed_word_346 v) (closed_word_346 v)).
Definition expr_word_347 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 4))).
Definition closed_word_347 (v : leaf_values) : VM.t hvalue := (VM.add 24 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_24_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_347 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_347 (closed_word_347 v) (closed_word_347 v)).
Definition expr_word_348 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 24) 5))).
Definition closed_word_348 (v : leaf_values) : VM.t hvalue := (VM.add 24 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_24_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_348 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_348 (closed_word_348 v) (closed_word_348 v)).
Definition expr_word_349 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 4))).
Definition closed_word_349 (v : leaf_values) : VM.t hvalue := (VM.add 25 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_25_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_349 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_349 (closed_word_349 v) (closed_word_349 v)).
Definition expr_word_350 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 25) 5))).
Definition closed_word_350 (v : leaf_values) : VM.t hvalue := (VM.add 25 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_25_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_350 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_350 (closed_word_350 v) (closed_word_350 v)).
Definition expr_word_351 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 4))).
Definition closed_word_351 (v : leaf_values) : VM.t hvalue := (VM.add 26 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_26_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_351 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_351 (closed_word_351 v) (closed_word_351 v)).
Definition expr_word_352 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 26) 5))).
Definition closed_word_352 (v : leaf_values) : VM.t hvalue := (VM.add 26 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_26_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_352 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_352 (closed_word_352 v) (closed_word_352 v)).
Definition expr_word_353 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 5))).
Definition closed_word_353 (v : leaf_values) : VM.t hvalue := (VM.add 27 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_27_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_353 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_353 (closed_word_353 v) (closed_word_353 v)).
Definition expr_word_354 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 27) 6))).
Definition closed_word_354 (v : leaf_values) : VM.t hvalue := (VM.add 27 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_27_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_354 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_354 (closed_word_354 v) (closed_word_354 v)).
Definition expr_word_355 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 5))).
Definition closed_word_355 (v : leaf_values) : VM.t hvalue := (VM.add 28 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_28_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_355 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_355 (closed_word_355 v) (closed_word_355 v)).
Definition expr_word_356 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 28) 6))).
Definition closed_word_356 (v : leaf_values) : VM.t hvalue := (VM.add 28 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_28_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_356 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_356 (closed_word_356 v) (closed_word_356 v)).
Definition expr_word_357 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 4))).
Definition closed_word_357 (v : leaf_values) : VM.t hvalue := (VM.add 29 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_29_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_357 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_357 (closed_word_357 v) (closed_word_357 v)).
Definition expr_word_358 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 29) 5))).
Definition closed_word_358 (v : leaf_values) : VM.t hvalue := (VM.add 29 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_29_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_358 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_358 (closed_word_358 v) (closed_word_358 v)).
Definition expr_word_359 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 4))).
Definition closed_word_359 (v : leaf_values) : VM.t hvalue := (VM.add 30 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_30_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_359 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_359 (closed_word_359 v) (closed_word_359 v)).
Definition expr_word_360 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 30) 5))).
Definition closed_word_360 (v : leaf_values) : VM.t hvalue := (VM.add 30 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_30_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_360 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_360 (closed_word_360 v) (closed_word_360 v)).
Definition expr_word_361 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 4))).
Definition closed_word_361 (v : leaf_values) : VM.t hvalue := (VM.add 31 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_31_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_361 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_361 (closed_word_361 v) (closed_word_361 v)).
Definition expr_word_362 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 31) 5))).
Definition closed_word_362 (v : leaf_values) : VM.t hvalue := (VM.add 31 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_31_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_362 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_362 (closed_word_362 v) (closed_word_362 v)).
Definition expr_word_363 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 4))).
Definition closed_word_363 (v : leaf_values) : VM.t hvalue := (VM.add 32 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_32_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_363 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_363 (closed_word_363 v) (closed_word_363 v)).
Definition expr_word_364 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 32) 5))).
Definition closed_word_364 (v : leaf_values) : VM.t hvalue := (VM.add 32 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_32_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_364 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_364 (closed_word_364 v) (closed_word_364 v)).
Definition expr_word_365 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 5))).
Definition closed_word_365 (v : leaf_values) : VM.t hvalue := (VM.add 33 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_33_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_365 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_365 (closed_word_365 v) (closed_word_365 v)).
Definition expr_word_366 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 33) 6))).
Definition closed_word_366 (v : leaf_values) : VM.t hvalue := (VM.add 33 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_33_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_366 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_366 (closed_word_366 v) (closed_word_366 v)).
Definition expr_word_367 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 4))).
Definition closed_word_367 (v : leaf_values) : VM.t hvalue := (VM.add 34 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_34_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_367 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_367 (closed_word_367 v) (closed_word_367 v)).
Definition expr_word_368 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 34) 5))).
Definition closed_word_368 (v : leaf_values) : VM.t hvalue := (VM.add 34 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_34_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_368 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_368 (closed_word_368 v) (closed_word_368 v)).
Definition expr_word_369 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 4))).
Definition closed_word_369 (v : leaf_values) : VM.t hvalue := (VM.add 35 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_35_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_369 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_369 (closed_word_369 v) (closed_word_369 v)).
Definition expr_word_370 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 35) 5))).
Definition closed_word_370 (v : leaf_values) : VM.t hvalue := (VM.add 35 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_35_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_370 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_370 (closed_word_370 v) (closed_word_370 v)).
Definition expr_word_371 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 4))).
Definition closed_word_371 (v : leaf_values) : VM.t hvalue := (VM.add 36 (Bval (Bflips 4 Nflip (Gval (Fuint 1) (port_36_4 v)) Bnil)) (VM.empty hvalue)).
Definition word_371 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_371 (closed_word_371 v) (closed_word_371 v)).
Definition expr_word_372 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 36) 5))).
Definition closed_word_372 (v : leaf_values) : VM.t hvalue := (VM.add 36 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_36_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_372 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_372 (closed_word_372 v) (closed_word_372 v)).
Definition expr_word_373 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 343)) (@Eref VarOrder.T (@Eid VarOrder.T 305))).
Definition closed_word_373 (v : leaf_values) : VM.t hvalue := (VM.add 343 (Gval (Fuint 1) (word_343 v)) (VM.add 305 (Gval (Fuint 1) (word_305 v)) (VM.empty hvalue))).
Definition word_373 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_373 (closed_word_373 v) (closed_word_373 v)).
Definition expr_word_374 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 347)) (@Eref VarOrder.T (@Eid VarOrder.T 345))).
Definition closed_word_374 (v : leaf_values) : VM.t hvalue := (VM.add 347 (Gval (Fuint 1) (word_347 v)) (VM.add 345 (Gval (Fuint 1) (word_345 v)) (VM.empty hvalue))).
Definition word_374 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_374 (closed_word_374 v) (closed_word_374 v)).
Definition expr_word_375 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 374)) (@Eref VarOrder.T (@Eid VarOrder.T 373))).
Definition closed_word_375 (v : leaf_values) : VM.t hvalue := (VM.add 374 (Gval (Fuint 2) (word_374 v)) (VM.add 373 (Gval (Fuint 2) (word_373 v)) (VM.empty hvalue))).
Definition word_375 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_375 (closed_word_375 v) (closed_word_375 v)).
Definition expr_word_376 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 351)) (@Eref VarOrder.T (@Eid VarOrder.T 349))).
Definition closed_word_376 (v : leaf_values) : VM.t hvalue := (VM.add 351 (Gval (Fuint 1) (word_351 v)) (VM.add 349 (Gval (Fuint 1) (word_349 v)) (VM.empty hvalue))).
Definition word_376 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_376 (closed_word_376 v) (closed_word_376 v)).
Definition expr_word_377 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 355)) (@Eref VarOrder.T (@Eid VarOrder.T 353))).
Definition closed_word_377 (v : leaf_values) : VM.t hvalue := (VM.add 355 (Gval (Fuint 1) (word_355 v)) (VM.add 353 (Gval (Fuint 1) (word_353 v)) (VM.empty hvalue))).
Definition word_377 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_377 (closed_word_377 v) (closed_word_377 v)).
Definition expr_word_378 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 377)) (@Eref VarOrder.T (@Eid VarOrder.T 376))).
Definition closed_word_378 (v : leaf_values) : VM.t hvalue := (VM.add 377 (Gval (Fuint 2) (word_377 v)) (VM.add 376 (Gval (Fuint 2) (word_376 v)) (VM.empty hvalue))).
Definition word_378 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_378 (closed_word_378 v) (closed_word_378 v)).
Definition expr_word_379 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 378)) (@Eref VarOrder.T (@Eid VarOrder.T 375))).
Definition closed_word_379 (v : leaf_values) : VM.t hvalue := (VM.add 378 (Gval (Fuint 4) (word_378 v)) (VM.add 375 (Gval (Fuint 4) (word_375 v)) (VM.empty hvalue))).
Definition word_379 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_379 (closed_word_379 v) (closed_word_379 v)).
Definition expr_word_380 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 359)) (@Eref VarOrder.T (@Eid VarOrder.T 357))).
Definition closed_word_380 (v : leaf_values) : VM.t hvalue := (VM.add 359 (Gval (Fuint 1) (word_359 v)) (VM.add 357 (Gval (Fuint 1) (word_357 v)) (VM.empty hvalue))).
Definition word_380 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_380 (closed_word_380 v) (closed_word_380 v)).
Definition expr_word_381 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 363)) (@Eref VarOrder.T (@Eid VarOrder.T 361))).
Definition closed_word_381 (v : leaf_values) : VM.t hvalue := (VM.add 363 (Gval (Fuint 1) (word_363 v)) (VM.add 361 (Gval (Fuint 1) (word_361 v)) (VM.empty hvalue))).
Definition word_381 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_381 (closed_word_381 v) (closed_word_381 v)).
Definition expr_word_382 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 381)) (@Eref VarOrder.T (@Eid VarOrder.T 380))).
Definition closed_word_382 (v : leaf_values) : VM.t hvalue := (VM.add 381 (Gval (Fuint 2) (word_381 v)) (VM.add 380 (Gval (Fuint 2) (word_380 v)) (VM.empty hvalue))).
Definition word_382 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_382 (closed_word_382 v) (closed_word_382 v)).
Definition expr_word_383 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 367)) (@Eref VarOrder.T (@Eid VarOrder.T 365))).
Definition closed_word_383 (v : leaf_values) : VM.t hvalue := (VM.add 367 (Gval (Fuint 1) (word_367 v)) (VM.add 365 (Gval (Fuint 1) (word_365 v)) (VM.empty hvalue))).
Definition word_383 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_383 (closed_word_383 v) (closed_word_383 v)).
Definition expr_word_384 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 371)) (@Eref VarOrder.T (@Eid VarOrder.T 369))).
Definition closed_word_384 (v : leaf_values) : VM.t hvalue := (VM.add 371 (Gval (Fuint 1) (word_371 v)) (VM.add 369 (Gval (Fuint 1) (word_369 v)) (VM.empty hvalue))).
Definition word_384 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_384 (closed_word_384 v) (closed_word_384 v)).
Definition expr_word_385 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 384)) (@Eref VarOrder.T (@Eid VarOrder.T 383))).
Definition closed_word_385 (v : leaf_values) : VM.t hvalue := (VM.add 384 (Gval (Fuint 2) (word_384 v)) (VM.add 383 (Gval (Fuint 2) (word_383 v)) (VM.empty hvalue))).
Definition word_385 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_385 (closed_word_385 v) (closed_word_385 v)).
Definition expr_word_386 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 385)) (@Eref VarOrder.T (@Eid VarOrder.T 382))).
Definition closed_word_386 (v : leaf_values) : VM.t hvalue := (VM.add 385 (Gval (Fuint 4) (word_385 v)) (VM.add 382 (Gval (Fuint 4) (word_382 v)) (VM.empty hvalue))).
Definition word_386 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_386 (closed_word_386 v) (closed_word_386 v)).
Definition expr_word_387 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 386)) (@Eref VarOrder.T (@Eid VarOrder.T 379))).
Definition closed_word_387 (v : leaf_values) : VM.t hvalue := (VM.add 386 (Gval (Fuint 8) (word_386 v)) (VM.add 379 (Gval (Fuint 8) (word_379 v)) (VM.empty hvalue))).
Definition word_387 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_387 (closed_word_387 v) (closed_word_387 v)).
Definition expr_word_388 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 348)) (@Eref VarOrder.T (@Eid VarOrder.T 346))).
Definition closed_word_388 (v : leaf_values) : VM.t hvalue := (VM.add 348 (Gval (Fuint 1) (word_348 v)) (VM.add 346 (Gval (Fuint 1) (word_346 v)) (VM.empty hvalue))).
Definition word_388 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_388 (closed_word_388 v) (closed_word_388 v)).
Definition expr_word_389 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 388)) (@Eref VarOrder.T (@Eid VarOrder.T 344))).
Definition closed_word_389 (v : leaf_values) : VM.t hvalue := (VM.add 388 (Gval (Fuint 2) (word_388 v)) (VM.add 344 (Gval (Fuint 1) (word_344 v)) (VM.empty hvalue))).
Definition word_389 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_389 (closed_word_389 v) (closed_word_389 v)).
Definition expr_word_390 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 352)) (@Eref VarOrder.T (@Eid VarOrder.T 350))).
Definition closed_word_390 (v : leaf_values) : VM.t hvalue := (VM.add 352 (Gval (Fuint 1) (word_352 v)) (VM.add 350 (Gval (Fuint 1) (word_350 v)) (VM.empty hvalue))).
Definition word_390 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_390 (closed_word_390 v) (closed_word_390 v)).
Definition expr_word_391 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 356)) (@Eref VarOrder.T (@Eid VarOrder.T 354))).
Definition closed_word_391 (v : leaf_values) : VM.t hvalue := (VM.add 356 (Gval (Fuint 1) (word_356 v)) (VM.add 354 (Gval (Fuint 1) (word_354 v)) (VM.empty hvalue))).
Definition word_391 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_391 (closed_word_391 v) (closed_word_391 v)).
Definition expr_word_392 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 391)) (@Eref VarOrder.T (@Eid VarOrder.T 390))).
Definition closed_word_392 (v : leaf_values) : VM.t hvalue := (VM.add 391 (Gval (Fuint 2) (word_391 v)) (VM.add 390 (Gval (Fuint 2) (word_390 v)) (VM.empty hvalue))).
Definition word_392 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_392 (closed_word_392 v) (closed_word_392 v)).
Definition expr_word_393 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 392)) (@Eref VarOrder.T (@Eid VarOrder.T 389))).
Definition closed_word_393 (v : leaf_values) : VM.t hvalue := (VM.add 392 (Gval (Fuint 4) (word_392 v)) (VM.add 389 (Gval (Fuint 3) (word_389 v)) (VM.empty hvalue))).
Definition word_393 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_393 (closed_word_393 v) (closed_word_393 v)).
Definition expr_word_394 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 362)) (@Eref VarOrder.T (@Eid VarOrder.T 360))).
Definition closed_word_394 (v : leaf_values) : VM.t hvalue := (VM.add 362 (Gval (Fuint 1) (word_362 v)) (VM.add 360 (Gval (Fuint 1) (word_360 v)) (VM.empty hvalue))).
Definition word_394 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_394 (closed_word_394 v) (closed_word_394 v)).
Definition expr_word_395 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 394)) (@Eref VarOrder.T (@Eid VarOrder.T 358))).
Definition closed_word_395 (v : leaf_values) : VM.t hvalue := (VM.add 394 (Gval (Fuint 2) (word_394 v)) (VM.add 358 (Gval (Fuint 1) (word_358 v)) (VM.empty hvalue))).
Definition word_395 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_395 (closed_word_395 v) (closed_word_395 v)).
Definition expr_word_396 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 366)) (@Eref VarOrder.T (@Eid VarOrder.T 364))).
Definition closed_word_396 (v : leaf_values) : VM.t hvalue := (VM.add 366 (Gval (Fuint 1) (word_366 v)) (VM.add 364 (Gval (Fuint 1) (word_364 v)) (VM.empty hvalue))).
Definition word_396 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_396 (closed_word_396 v) (closed_word_396 v)).
Definition expr_word_397 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 370)) (@Eref VarOrder.T (@Eid VarOrder.T 368))).
Definition closed_word_397 (v : leaf_values) : VM.t hvalue := (VM.add 370 (Gval (Fuint 1) (word_370 v)) (VM.add 368 (Gval (Fuint 1) (word_368 v)) (VM.empty hvalue))).
Definition word_397 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_397 (closed_word_397 v) (closed_word_397 v)).
Definition expr_word_398 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 396))).
Definition closed_word_398 (v : leaf_values) : VM.t hvalue := (VM.add 397 (Gval (Fuint 2) (word_397 v)) (VM.add 396 (Gval (Fuint 2) (word_396 v)) (VM.empty hvalue))).
Definition word_398 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_398 (closed_word_398 v) (closed_word_398 v)).
Definition expr_word_399 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 398)) (@Eref VarOrder.T (@Eid VarOrder.T 395))).
Definition closed_word_399 (v : leaf_values) : VM.t hvalue := (VM.add 398 (Gval (Fuint 4) (word_398 v)) (VM.add 395 (Gval (Fuint 3) (word_395 v)) (VM.empty hvalue))).
Definition word_399 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_399 (closed_word_399 v) (closed_word_399 v)).
Definition expr_word_400 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 399)) (@Eref VarOrder.T (@Eid VarOrder.T 393))).
Definition closed_word_400 (v : leaf_values) : VM.t hvalue := (VM.add 399 (Gval (Fuint 7) (word_399 v)) (VM.add 393 (Gval (Fuint 7) (word_393 v)) (VM.empty hvalue))).
Definition word_400 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_400 (closed_word_400 v) (closed_word_400 v)).
Definition expr_word_401 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 400)) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Definition closed_word_401 (v : leaf_values) : VM.t hvalue := (VM.add 400 (Gval (Fuint 14) (word_400 v)) (VM.empty hvalue)).
Definition word_401 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_401 (closed_word_401 v) (closed_word_401 v)).
Definition expr_word_402 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 387)) (@Eref VarOrder.T (@Eid VarOrder.T 401))).
Definition closed_word_402 (v : leaf_values) : VM.t hvalue := (VM.add 401 (Gval (Fuint 16) (word_401 v)) (VM.add 387 (Gval (Fuint 16) (word_387 v)) (VM.empty hvalue))).
Definition word_402 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_402 (closed_word_402 v) (closed_word_402 v)).
Definition expr_word_403 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 402))).
Definition closed_word_403 (v : leaf_values) : VM.t hvalue := (VM.add 402 (Gval (Fuint 17) (word_402 v)) (VM.empty hvalue)).
Definition word_403 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_403 (closed_word_403 v) (closed_word_403 v)).
Definition expr_word_404 : @hfexpr VarOrder.T := (@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_404 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 8) (word_2 v)) (VM.empty hvalue)).
Definition word_404 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_404 (closed_word_404 v) (closed_word_404 v)).
Definition expr_word_405 : @hfexpr VarOrder.T := (@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 3))).
Definition closed_word_405 (v : leaf_values) : VM.t hvalue := (VM.add 3 (Gval (Fuint 8) (word_3 v)) (VM.empty hvalue)).
Definition word_405 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_405 (closed_word_405 v) (closed_word_405 v)).
Definition expr_word_406 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bmul (@Eref VarOrder.T (@Eid VarOrder.T 404)) (@Eref VarOrder.T (@Eid VarOrder.T 405))).
Definition closed_word_406 (v : leaf_values) : VM.t hvalue := (VM.add 405 (Gval (Fsint 8) (word_405 v)) (VM.add 404 (Gval (Fsint 8) (word_404 v)) (VM.empty hvalue))).
Definition word_406 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_406 (closed_word_406 v) (closed_word_406 v)).
Definition expr_word_407 : @hfexpr VarOrder.T := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Definition closed_word_407 (v : leaf_values) : VM.t hvalue := (VM.add 406 (Gval (Fsint 16) (word_406 v)) (VM.empty hvalue)).
Definition word_407 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_407 (closed_word_407 v) (closed_word_407 v)).
Definition expr_word_409 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Eref VarOrder.T (@Eid VarOrder.T 407)) (@Eref VarOrder.T (@Eid VarOrder.T 408))).
Definition closed_word_409 (v : leaf_values) : VM.t hvalue := (VM.add 408 (Gval (Fuint 16) (word_408 v)) (VM.add 407 (Gval (Fuint 16) (word_407 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)))).
Definition word_409 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_409 (closed_word_409 v) (closed_word_409 v)).
Definition expr_word_411 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 410))).
Definition closed_word_411 (v : leaf_values) : VM.t hvalue := (VM.add 410 (Gval (Fuint 1) (word_410 v)) (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue))).
Definition word_411 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_411 (closed_word_411 v) (closed_word_411 v)).
Definition expr_word_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 403)).
Definition closed_word_6 (v : leaf_values) : VM.t hvalue := (VM.add 403 (Gval (Fuint 16) (word_403 v)) (VM.empty hvalue)).
Definition word_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_6 (closed_word_6 v) (closed_word_6 v)).
Definition expr_word_412 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 6)) (@Eref VarOrder.T (@Eid VarOrder.T 408))).
Definition closed_word_412 (v : leaf_values) : VM.t hvalue := (VM.add 408 (Gval (Fuint 16) (word_408 v)) (VM.add 6 (Gval (Fuint 16) (word_6 v)) (VM.empty hvalue))).
Definition word_412 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_412 (closed_word_412 v) (closed_word_412 v)).
Definition expr_word_413 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_word_413 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_413 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_413 (closed_word_413 v) (closed_word_413 v)).
Definition expr_word_414 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 413)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_414 (v : leaf_values) : VM.t hvalue := (VM.add 413 (Gval (Fuint 1) (word_413 v)) (VM.empty hvalue)).
Definition word_414 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_414 (closed_word_414 v) (closed_word_414 v)).
Definition expr_word_415 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 412)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_415 (v : leaf_values) : VM.t hvalue := (VM.add 412 (Gval (Fuint 1) (word_412 v)) (VM.empty hvalue)).
Definition word_415 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_415 (closed_word_415 v) (closed_word_415 v)).
Definition expr_word_417 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 4)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_417 (v : leaf_values) : VM.t hvalue := (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)).
Definition word_417 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_417 (closed_word_417 v) (closed_word_417 v)).
Definition expr_word_418 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 410)) (@Eref VarOrder.T (@Eid VarOrder.T 417))).
Definition closed_word_418 (v : leaf_values) : VM.t hvalue := (VM.add 417 (Gval (Fuint 1) (word_417 v)) (VM.add 410 (Gval (Fuint 1) (word_410 v)) (VM.empty hvalue))).
Definition word_418 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_418 (closed_word_418 v) (closed_word_418 v)).
Definition expr_word_420 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 6)) (@Eref VarOrder.T (@Eid VarOrder.T 416))).
Definition closed_word_420 (v : leaf_values) : VM.t hvalue := (VM.add 416 (Gval (Fuint 16) (word_416 v)) (VM.add 6 (Gval (Fuint 16) (word_6 v)) (VM.empty hvalue))).
Definition word_420 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_420 (closed_word_420 v) (closed_word_420 v)).
Definition expr_word_421 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_word_421 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_421 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_421 (closed_word_421 v) (closed_word_421 v)).
Definition expr_word_422 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 421)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_422 (v : leaf_values) : VM.t hvalue := (VM.add 421 (Gval (Fuint 1) (word_421 v)) (VM.empty hvalue)).
Definition word_422 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_422 (closed_word_422 v) (closed_word_422 v)).
Definition expr_word_423 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 420)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_423 (v : leaf_values) : VM.t hvalue := (VM.add 420 (Gval (Fuint 1) (word_420 v)) (VM.empty hvalue)).
Definition word_423 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_423 (closed_word_423 v) (closed_word_423 v)).
Definition expr_port_7_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_7_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_7_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_7_0 (closed_port_7_0 v) (closed_port_7_0 v)).
Definition expr_port_7_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_7_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_7_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_7_1 (closed_port_7_1 v) (closed_port_7_1 v)).
Definition expr_port_7_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 201)).
Definition closed_port_7_2 (v : leaf_values) : VM.t hvalue := (VM.add 201 (Gval (Fuint 1) (word_201 v)) (VM.empty hvalue)).
Definition port_7_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_7_2 (closed_port_7_2 v) (closed_port_7_2 v)).
Definition expr_port_7_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 203)).
Definition closed_port_7_3 (v : leaf_values) : VM.t hvalue := (VM.add 203 (Gval (Fuint 1) (word_203 v)) (VM.empty hvalue)).
Definition port_7_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_7_3 (closed_port_7_3 v) (closed_port_7_3 v)).
Definition expr_port_8_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_8_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_8_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_8_0 (closed_port_8_0 v) (closed_port_8_0 v)).
Definition expr_port_8_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_8_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_8_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_8_1 (closed_port_8_1 v) (closed_port_8_1 v)).
Definition expr_port_8_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 205)).
Definition closed_port_8_2 (v : leaf_values) : VM.t hvalue := (VM.add 205 (Gval (Fuint 1) (word_205 v)) (VM.empty hvalue)).
Definition port_8_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_8_2 (closed_port_8_2 v) (closed_port_8_2 v)).
Definition expr_port_8_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 207)).
Definition closed_port_8_3 (v : leaf_values) : VM.t hvalue := (VM.add 207 (Gval (Fuint 1) (word_207 v)) (VM.empty hvalue)).
Definition port_8_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_8_3 (closed_port_8_3 v) (closed_port_8_3 v)).
Definition expr_port_9_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_9_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_9_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_9_0 (closed_port_9_0 v) (closed_port_9_0 v)).
Definition expr_port_9_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_9_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_9_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_9_1 (closed_port_9_1 v) (closed_port_9_1 v)).
Definition expr_port_9_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 209)).
Definition closed_port_9_2 (v : leaf_values) : VM.t hvalue := (VM.add 209 (Gval (Fuint 1) (word_209 v)) (VM.empty hvalue)).
Definition port_9_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_9_2 (closed_port_9_2 v) (closed_port_9_2 v)).
Definition expr_port_9_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 211)).
Definition closed_port_9_3 (v : leaf_values) : VM.t hvalue := (VM.add 211 (Gval (Fuint 1) (word_211 v)) (VM.empty hvalue)).
Definition port_9_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_9_3 (closed_port_9_3 v) (closed_port_9_3 v)).
Definition expr_port_9_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 213)).
Definition closed_port_9_4 (v : leaf_values) : VM.t hvalue := (VM.add 213 (Gval (Fuint 1) (word_213 v)) (VM.empty hvalue)).
Definition port_9_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_9_4 (closed_port_9_4 v) (closed_port_9_4 v)).
Definition expr_port_10_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_10_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_10_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_0 (closed_port_10_0 v) (closed_port_10_0 v)).
Definition expr_port_10_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_10_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_10_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_1 (closed_port_10_1 v) (closed_port_10_1 v)).
Definition expr_port_10_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 215)).
Definition closed_port_10_2 (v : leaf_values) : VM.t hvalue := (VM.add 215 (Gval (Fuint 1) (word_215 v)) (VM.empty hvalue)).
Definition port_10_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_2 (closed_port_10_2 v) (closed_port_10_2 v)).
Definition expr_port_10_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 217)).
Definition closed_port_10_3 (v : leaf_values) : VM.t hvalue := (VM.add 217 (Gval (Fuint 1) (word_217 v)) (VM.empty hvalue)).
Definition port_10_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_3 (closed_port_10_3 v) (closed_port_10_3 v)).
Definition expr_port_10_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 219)).
Definition closed_port_10_4 (v : leaf_values) : VM.t hvalue := (VM.add 219 (Gval (Fuint 1) (word_219 v)) (VM.empty hvalue)).
Definition port_10_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_4 (closed_port_10_4 v) (closed_port_10_4 v)).
Definition expr_port_11_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_11_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_11_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_0 (closed_port_11_0 v) (closed_port_11_0 v)).
Definition expr_port_11_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_11_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_11_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_1 (closed_port_11_1 v) (closed_port_11_1 v)).
Definition expr_port_11_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 221)).
Definition closed_port_11_2 (v : leaf_values) : VM.t hvalue := (VM.add 221 (Gval (Fuint 1) (word_221 v)) (VM.empty hvalue)).
Definition port_11_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_2 (closed_port_11_2 v) (closed_port_11_2 v)).
Definition expr_port_11_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 223)).
Definition closed_port_11_3 (v : leaf_values) : VM.t hvalue := (VM.add 223 (Gval (Fuint 1) (word_223 v)) (VM.empty hvalue)).
Definition port_11_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_3 (closed_port_11_3 v) (closed_port_11_3 v)).
Definition expr_port_11_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 225)).
Definition closed_port_11_4 (v : leaf_values) : VM.t hvalue := (VM.add 225 (Gval (Fuint 1) (word_225 v)) (VM.empty hvalue)).
Definition port_11_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_4 (closed_port_11_4 v) (closed_port_11_4 v)).
Definition expr_port_11_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 227)).
Definition closed_port_11_5 (v : leaf_values) : VM.t hvalue := (VM.add 227 (Gval (Fuint 1) (word_227 v)) (VM.empty hvalue)).
Definition port_11_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_5 (closed_port_11_5 v) (closed_port_11_5 v)).
Definition expr_port_11_6 : @hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 1) [::false]).
Definition closed_port_11_6 (v : leaf_values) : VM.t hvalue := (VM.empty hvalue).
Definition port_11_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_6 (closed_port_11_6 v) (closed_port_11_6 v)).
Definition expr_port_12_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_12_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_12_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_12_0 (closed_port_12_0 v) (closed_port_12_0 v)).
Definition expr_port_12_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_12_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_12_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_12_1 (closed_port_12_1 v) (closed_port_12_1 v)).
Definition expr_port_12_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 229)).
Definition closed_port_12_2 (v : leaf_values) : VM.t hvalue := (VM.add 229 (Gval (Fuint 1) (word_229 v)) (VM.empty hvalue)).
Definition port_12_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_12_2 (closed_port_12_2 v) (closed_port_12_2 v)).
Definition expr_port_12_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 231)).
Definition closed_port_12_3 (v : leaf_values) : VM.t hvalue := (VM.add 231 (Gval (Fuint 1) (word_231 v)) (VM.empty hvalue)).
Definition port_12_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_12_3 (closed_port_12_3 v) (closed_port_12_3 v)).
Definition expr_port_12_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 233)).
Definition closed_port_12_4 (v : leaf_values) : VM.t hvalue := (VM.add 233 (Gval (Fuint 1) (word_233 v)) (VM.empty hvalue)).
Definition port_12_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_12_4 (closed_port_12_4 v) (closed_port_12_4 v)).
Definition expr_port_12_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 235)).
Definition closed_port_12_5 (v : leaf_values) : VM.t hvalue := (VM.add 235 (Gval (Fuint 1) (word_235 v)) (VM.empty hvalue)).
Definition port_12_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_12_5 (closed_port_12_5 v) (closed_port_12_5 v)).
Definition expr_port_12_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 314)).
Definition closed_port_12_6 (v : leaf_values) : VM.t hvalue := (VM.add 314 (Gval (Fuint 1) (word_314 v)) (VM.empty hvalue)).
Definition port_12_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_12_6 (closed_port_12_6 v) (closed_port_12_6 v)).
Definition expr_port_13_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_13_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_13_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_13_0 (closed_port_13_0 v) (closed_port_13_0 v)).
Definition expr_port_13_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_13_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_13_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_13_1 (closed_port_13_1 v) (closed_port_13_1 v)).
Definition expr_port_13_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 237)).
Definition closed_port_13_2 (v : leaf_values) : VM.t hvalue := (VM.add 237 (Gval (Fuint 1) (word_237 v)) (VM.empty hvalue)).
Definition port_13_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_13_2 (closed_port_13_2 v) (closed_port_13_2 v)).
Definition expr_port_13_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 239)).
Definition closed_port_13_3 (v : leaf_values) : VM.t hvalue := (VM.add 239 (Gval (Fuint 1) (word_239 v)) (VM.empty hvalue)).
Definition port_13_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_13_3 (closed_port_13_3 v) (closed_port_13_3 v)).
Definition expr_port_13_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 241)).
Definition closed_port_13_4 (v : leaf_values) : VM.t hvalue := (VM.add 241 (Gval (Fuint 1) (word_241 v)) (VM.empty hvalue)).
Definition port_13_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_13_4 (closed_port_13_4 v) (closed_port_13_4 v)).
Definition expr_port_13_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 243)).
Definition closed_port_13_5 (v : leaf_values) : VM.t hvalue := (VM.add 243 (Gval (Fuint 1) (word_243 v)) (VM.empty hvalue)).
Definition port_13_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_13_5 (closed_port_13_5 v) (closed_port_13_5 v)).
Definition expr_port_13_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 317)).
Definition closed_port_13_6 (v : leaf_values) : VM.t hvalue := (VM.add 317 (Gval (Fuint 1) (word_317 v)) (VM.empty hvalue)).
Definition port_13_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_13_6 (closed_port_13_6 v) (closed_port_13_6 v)).
Definition expr_port_14_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_14_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_14_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_14_0 (closed_port_14_0 v) (closed_port_14_0 v)).
Definition expr_port_14_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_14_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_14_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_14_1 (closed_port_14_1 v) (closed_port_14_1 v)).
Definition expr_port_14_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 247)).
Definition closed_port_14_2 (v : leaf_values) : VM.t hvalue := (VM.add 247 (Gval (Fuint 1) (word_247 v)) (VM.empty hvalue)).
Definition port_14_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_14_2 (closed_port_14_2 v) (closed_port_14_2 v)).
Definition expr_port_14_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 249)).
Definition closed_port_14_3 (v : leaf_values) : VM.t hvalue := (VM.add 249 (Gval (Fuint 1) (word_249 v)) (VM.empty hvalue)).
Definition port_14_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_14_3 (closed_port_14_3 v) (closed_port_14_3 v)).
Definition expr_port_14_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 251)).
Definition closed_port_14_4 (v : leaf_values) : VM.t hvalue := (VM.add 251 (Gval (Fuint 1) (word_251 v)) (VM.empty hvalue)).
Definition port_14_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_14_4 (closed_port_14_4 v) (closed_port_14_4 v)).
Definition expr_port_14_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 253)).
Definition closed_port_14_5 (v : leaf_values) : VM.t hvalue := (VM.add 253 (Gval (Fuint 1) (word_253 v)) (VM.empty hvalue)).
Definition port_14_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_14_5 (closed_port_14_5 v) (closed_port_14_5 v)).
Definition expr_port_14_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 320)).
Definition closed_port_14_6 (v : leaf_values) : VM.t hvalue := (VM.add 320 (Gval (Fuint 1) (word_320 v)) (VM.empty hvalue)).
Definition port_14_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_14_6 (closed_port_14_6 v) (closed_port_14_6 v)).
Definition expr_port_15_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_15_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_15_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_15_0 (closed_port_15_0 v) (closed_port_15_0 v)).
Definition expr_port_15_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_15_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_15_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_15_1 (closed_port_15_1 v) (closed_port_15_1 v)).
Definition expr_port_15_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 257)).
Definition closed_port_15_2 (v : leaf_values) : VM.t hvalue := (VM.add 257 (Gval (Fuint 1) (word_257 v)) (VM.empty hvalue)).
Definition port_15_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_15_2 (closed_port_15_2 v) (closed_port_15_2 v)).
Definition expr_port_15_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 259)).
Definition closed_port_15_3 (v : leaf_values) : VM.t hvalue := (VM.add 259 (Gval (Fuint 1) (word_259 v)) (VM.empty hvalue)).
Definition port_15_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_15_3 (closed_port_15_3 v) (closed_port_15_3 v)).
Definition expr_port_15_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 261)).
Definition closed_port_15_4 (v : leaf_values) : VM.t hvalue := (VM.add 261 (Gval (Fuint 1) (word_261 v)) (VM.empty hvalue)).
Definition port_15_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_15_4 (closed_port_15_4 v) (closed_port_15_4 v)).
Definition expr_port_15_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 263)).
Definition closed_port_15_5 (v : leaf_values) : VM.t hvalue := (VM.add 263 (Gval (Fuint 1) (word_263 v)) (VM.empty hvalue)).
Definition port_15_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_15_5 (closed_port_15_5 v) (closed_port_15_5 v)).
Definition expr_port_15_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 323)).
Definition closed_port_15_6 (v : leaf_values) : VM.t hvalue := (VM.add 323 (Gval (Fuint 1) (word_323 v)) (VM.empty hvalue)).
Definition port_15_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_15_6 (closed_port_15_6 v) (closed_port_15_6 v)).
Definition expr_port_16_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_16_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_16_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_16_0 (closed_port_16_0 v) (closed_port_16_0 v)).
Definition expr_port_16_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_16_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_16_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_16_1 (closed_port_16_1 v) (closed_port_16_1 v)).
Definition expr_port_16_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 265)).
Definition closed_port_16_2 (v : leaf_values) : VM.t hvalue := (VM.add 265 (Gval (Fuint 1) (word_265 v)) (VM.empty hvalue)).
Definition port_16_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_16_2 (closed_port_16_2 v) (closed_port_16_2 v)).
Definition expr_port_16_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 267)).
Definition closed_port_16_3 (v : leaf_values) : VM.t hvalue := (VM.add 267 (Gval (Fuint 1) (word_267 v)) (VM.empty hvalue)).
Definition port_16_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_16_3 (closed_port_16_3 v) (closed_port_16_3 v)).
Definition expr_port_16_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 269)).
Definition closed_port_16_4 (v : leaf_values) : VM.t hvalue := (VM.add 269 (Gval (Fuint 1) (word_269 v)) (VM.empty hvalue)).
Definition port_16_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_16_4 (closed_port_16_4 v) (closed_port_16_4 v)).
Definition expr_port_16_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 271)).
Definition closed_port_16_5 (v : leaf_values) : VM.t hvalue := (VM.add 271 (Gval (Fuint 1) (word_271 v)) (VM.empty hvalue)).
Definition port_16_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_16_5 (closed_port_16_5 v) (closed_port_16_5 v)).
Definition expr_port_16_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 326)).
Definition closed_port_16_6 (v : leaf_values) : VM.t hvalue := (VM.add 326 (Gval (Fuint 1) (word_326 v)) (VM.empty hvalue)).
Definition port_16_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_16_6 (closed_port_16_6 v) (closed_port_16_6 v)).
Definition expr_port_17_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_17_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_17_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_17_0 (closed_port_17_0 v) (closed_port_17_0 v)).
Definition expr_port_17_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_17_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_17_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_17_1 (closed_port_17_1 v) (closed_port_17_1 v)).
Definition expr_port_17_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 273)).
Definition closed_port_17_2 (v : leaf_values) : VM.t hvalue := (VM.add 273 (Gval (Fuint 1) (word_273 v)) (VM.empty hvalue)).
Definition port_17_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_17_2 (closed_port_17_2 v) (closed_port_17_2 v)).
Definition expr_port_17_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 275)).
Definition closed_port_17_3 (v : leaf_values) : VM.t hvalue := (VM.add 275 (Gval (Fuint 1) (word_275 v)) (VM.empty hvalue)).
Definition port_17_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_17_3 (closed_port_17_3 v) (closed_port_17_3 v)).
Definition expr_port_17_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 277)).
Definition closed_port_17_4 (v : leaf_values) : VM.t hvalue := (VM.add 277 (Gval (Fuint 1) (word_277 v)) (VM.empty hvalue)).
Definition port_17_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_17_4 (closed_port_17_4 v) (closed_port_17_4 v)).
Definition expr_port_17_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 279)).
Definition closed_port_17_5 (v : leaf_values) : VM.t hvalue := (VM.add 279 (Gval (Fuint 1) (word_279 v)) (VM.empty hvalue)).
Definition port_17_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_17_5 (closed_port_17_5 v) (closed_port_17_5 v)).
Definition expr_port_17_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 329)).
Definition closed_port_17_6 (v : leaf_values) : VM.t hvalue := (VM.add 329 (Gval (Fuint 1) (word_329 v)) (VM.empty hvalue)).
Definition port_17_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_17_6 (closed_port_17_6 v) (closed_port_17_6 v)).
Definition expr_port_18_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_18_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_18_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_18_0 (closed_port_18_0 v) (closed_port_18_0 v)).
Definition expr_port_18_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_18_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_18_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_18_1 (closed_port_18_1 v) (closed_port_18_1 v)).
Definition expr_port_18_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 281)).
Definition closed_port_18_2 (v : leaf_values) : VM.t hvalue := (VM.add 281 (Gval (Fuint 1) (word_281 v)) (VM.empty hvalue)).
Definition port_18_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_18_2 (closed_port_18_2 v) (closed_port_18_2 v)).
Definition expr_port_18_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 283)).
Definition closed_port_18_3 (v : leaf_values) : VM.t hvalue := (VM.add 283 (Gval (Fuint 1) (word_283 v)) (VM.empty hvalue)).
Definition port_18_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_18_3 (closed_port_18_3 v) (closed_port_18_3 v)).
Definition expr_port_18_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 285)).
Definition closed_port_18_4 (v : leaf_values) : VM.t hvalue := (VM.add 285 (Gval (Fuint 1) (word_285 v)) (VM.empty hvalue)).
Definition port_18_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_18_4 (closed_port_18_4 v) (closed_port_18_4 v)).
Definition expr_port_18_5 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 287)).
Definition closed_port_18_5 (v : leaf_values) : VM.t hvalue := (VM.add 287 (Gval (Fuint 1) (word_287 v)) (VM.empty hvalue)).
Definition port_18_5 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_18_5 (closed_port_18_5 v) (closed_port_18_5 v)).
Definition expr_port_18_6 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 332)).
Definition closed_port_18_6 (v : leaf_values) : VM.t hvalue := (VM.add 332 (Gval (Fuint 1) (word_332 v)) (VM.empty hvalue)).
Definition port_18_6 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_18_6 (closed_port_18_6 v) (closed_port_18_6 v)).
Definition expr_port_19_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_19_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_19_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_19_0 (closed_port_19_0 v) (closed_port_19_0 v)).
Definition expr_port_19_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_19_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_19_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_19_1 (closed_port_19_1 v) (closed_port_19_1 v)).
Definition expr_port_19_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 289)).
Definition closed_port_19_2 (v : leaf_values) : VM.t hvalue := (VM.add 289 (Gval (Fuint 1) (word_289 v)) (VM.empty hvalue)).
Definition port_19_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_19_2 (closed_port_19_2 v) (closed_port_19_2 v)).
Definition expr_port_19_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 291)).
Definition closed_port_19_3 (v : leaf_values) : VM.t hvalue := (VM.add 291 (Gval (Fuint 1) (word_291 v)) (VM.empty hvalue)).
Definition port_19_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_19_3 (closed_port_19_3 v) (closed_port_19_3 v)).
Definition expr_port_19_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 293)).
Definition closed_port_19_4 (v : leaf_values) : VM.t hvalue := (VM.add 293 (Gval (Fuint 1) (word_293 v)) (VM.empty hvalue)).
Definition port_19_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_19_4 (closed_port_19_4 v) (closed_port_19_4 v)).
Definition expr_port_20_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_20_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_20_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_20_0 (closed_port_20_0 v) (closed_port_20_0 v)).
Definition expr_port_20_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_20_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_20_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_20_1 (closed_port_20_1 v) (closed_port_20_1 v)).
Definition expr_port_20_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 295)).
Definition closed_port_20_2 (v : leaf_values) : VM.t hvalue := (VM.add 295 (Gval (Fuint 1) (word_295 v)) (VM.empty hvalue)).
Definition port_20_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_20_2 (closed_port_20_2 v) (closed_port_20_2 v)).
Definition expr_port_20_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 297)).
Definition closed_port_20_3 (v : leaf_values) : VM.t hvalue := (VM.add 297 (Gval (Fuint 1) (word_297 v)) (VM.empty hvalue)).
Definition port_20_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_20_3 (closed_port_20_3 v) (closed_port_20_3 v)).
Definition expr_port_21_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_21_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_21_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_21_0 (closed_port_21_0 v) (closed_port_21_0 v)).
Definition expr_port_21_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_21_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_21_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_21_1 (closed_port_21_1 v) (closed_port_21_1 v)).
Definition expr_port_21_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 299)).
Definition closed_port_21_2 (v : leaf_values) : VM.t hvalue := (VM.add 299 (Gval (Fuint 1) (word_299 v)) (VM.empty hvalue)).
Definition port_21_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_21_2 (closed_port_21_2 v) (closed_port_21_2 v)).
Definition expr_port_21_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 301)).
Definition closed_port_21_3 (v : leaf_values) : VM.t hvalue := (VM.add 301 (Gval (Fuint 1) (word_301 v)) (VM.empty hvalue)).
Definition port_21_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_21_3 (closed_port_21_3 v) (closed_port_21_3 v)).
Definition expr_port_22_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_22_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_22_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_22_0 (closed_port_22_0 v) (closed_port_22_0 v)).
Definition expr_port_22_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_22_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_22_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_22_1 (closed_port_22_1 v) (closed_port_22_1 v)).
Definition expr_port_22_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 307)).
Definition closed_port_22_2 (v : leaf_values) : VM.t hvalue := (VM.add 307 (Gval (Fuint 1) (word_307 v)) (VM.empty hvalue)).
Definition port_22_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_22_2 (closed_port_22_2 v) (closed_port_22_2 v)).
Definition expr_port_22_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 306)).
Definition closed_port_22_3 (v : leaf_values) : VM.t hvalue := (VM.add 306 (Gval (Fuint 1) (word_306 v)) (VM.empty hvalue)).
Definition port_22_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_22_3 (closed_port_22_3 v) (closed_port_22_3 v)).
Definition expr_port_23_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_23_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_23_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_23_0 (closed_port_23_0 v) (closed_port_23_0 v)).
Definition expr_port_23_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_23_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_23_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_23_1 (closed_port_23_1 v) (closed_port_23_1 v)).
Definition expr_port_23_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 309)).
Definition closed_port_23_2 (v : leaf_values) : VM.t hvalue := (VM.add 309 (Gval (Fuint 1) (word_309 v)) (VM.empty hvalue)).
Definition port_23_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_23_2 (closed_port_23_2 v) (closed_port_23_2 v)).
Definition expr_port_23_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 308)).
Definition closed_port_23_3 (v : leaf_values) : VM.t hvalue := (VM.add 308 (Gval (Fuint 1) (word_308 v)) (VM.empty hvalue)).
Definition port_23_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_23_3 (closed_port_23_3 v) (closed_port_23_3 v)).
Definition expr_port_24_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_24_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_24_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_24_0 (closed_port_24_0 v) (closed_port_24_0 v)).
Definition expr_port_24_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_24_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_24_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_24_1 (closed_port_24_1 v) (closed_port_24_1 v)).
Definition expr_port_24_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 311)).
Definition closed_port_24_2 (v : leaf_values) : VM.t hvalue := (VM.add 311 (Gval (Fuint 1) (word_311 v)) (VM.empty hvalue)).
Definition port_24_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_24_2 (closed_port_24_2 v) (closed_port_24_2 v)).
Definition expr_port_24_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 310)).
Definition closed_port_24_3 (v : leaf_values) : VM.t hvalue := (VM.add 310 (Gval (Fuint 1) (word_310 v)) (VM.empty hvalue)).
Definition port_24_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_24_3 (closed_port_24_3 v) (closed_port_24_3 v)).
Definition expr_port_25_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_25_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_25_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_25_0 (closed_port_25_0 v) (closed_port_25_0 v)).
Definition expr_port_25_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_25_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_25_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_25_1 (closed_port_25_1 v) (closed_port_25_1 v)).
Definition expr_port_25_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 313)).
Definition closed_port_25_2 (v : leaf_values) : VM.t hvalue := (VM.add 313 (Gval (Fuint 1) (word_313 v)) (VM.empty hvalue)).
Definition port_25_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_25_2 (closed_port_25_2 v) (closed_port_25_2 v)).
Definition expr_port_25_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 312)).
Definition closed_port_25_3 (v : leaf_values) : VM.t hvalue := (VM.add 312 (Gval (Fuint 1) (word_312 v)) (VM.empty hvalue)).
Definition port_25_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_25_3 (closed_port_25_3 v) (closed_port_25_3 v)).
Definition expr_port_26_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_26_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_26_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_26_0 (closed_port_26_0 v) (closed_port_26_0 v)).
Definition expr_port_26_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_26_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_26_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_26_1 (closed_port_26_1 v) (closed_port_26_1 v)).
Definition expr_port_26_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 316)).
Definition closed_port_26_2 (v : leaf_values) : VM.t hvalue := (VM.add 316 (Gval (Fuint 1) (word_316 v)) (VM.empty hvalue)).
Definition port_26_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_26_2 (closed_port_26_2 v) (closed_port_26_2 v)).
Definition expr_port_26_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 315)).
Definition closed_port_26_3 (v : leaf_values) : VM.t hvalue := (VM.add 315 (Gval (Fuint 1) (word_315 v)) (VM.empty hvalue)).
Definition port_26_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_26_3 (closed_port_26_3 v) (closed_port_26_3 v)).
Definition expr_port_27_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_27_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_27_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_27_0 (closed_port_27_0 v) (closed_port_27_0 v)).
Definition expr_port_27_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_27_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_27_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_27_1 (closed_port_27_1 v) (closed_port_27_1 v)).
Definition expr_port_27_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 319)).
Definition closed_port_27_2 (v : leaf_values) : VM.t hvalue := (VM.add 319 (Gval (Fuint 1) (word_319 v)) (VM.empty hvalue)).
Definition port_27_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_27_2 (closed_port_27_2 v) (closed_port_27_2 v)).
Definition expr_port_27_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 245)).
Definition closed_port_27_3 (v : leaf_values) : VM.t hvalue := (VM.add 245 (Gval (Fuint 1) (word_245 v)) (VM.empty hvalue)).
Definition port_27_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_27_3 (closed_port_27_3 v) (closed_port_27_3 v)).
Definition expr_port_27_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 318)).
Definition closed_port_27_4 (v : leaf_values) : VM.t hvalue := (VM.add 318 (Gval (Fuint 1) (word_318 v)) (VM.empty hvalue)).
Definition port_27_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_27_4 (closed_port_27_4 v) (closed_port_27_4 v)).
Definition expr_port_28_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_28_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_28_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_28_0 (closed_port_28_0 v) (closed_port_28_0 v)).
Definition expr_port_28_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_28_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_28_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_28_1 (closed_port_28_1 v) (closed_port_28_1 v)).
Definition expr_port_28_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 322)).
Definition closed_port_28_2 (v : leaf_values) : VM.t hvalue := (VM.add 322 (Gval (Fuint 1) (word_322 v)) (VM.empty hvalue)).
Definition port_28_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_28_2 (closed_port_28_2 v) (closed_port_28_2 v)).
Definition expr_port_28_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 255)).
Definition closed_port_28_3 (v : leaf_values) : VM.t hvalue := (VM.add 255 (Gval (Fuint 1) (word_255 v)) (VM.empty hvalue)).
Definition port_28_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_28_3 (closed_port_28_3 v) (closed_port_28_3 v)).
Definition expr_port_28_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 321)).
Definition closed_port_28_4 (v : leaf_values) : VM.t hvalue := (VM.add 321 (Gval (Fuint 1) (word_321 v)) (VM.empty hvalue)).
Definition port_28_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_28_4 (closed_port_28_4 v) (closed_port_28_4 v)).
Definition expr_port_29_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_29_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_29_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_29_0 (closed_port_29_0 v) (closed_port_29_0 v)).
Definition expr_port_29_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_29_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_29_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_29_1 (closed_port_29_1 v) (closed_port_29_1 v)).
Definition expr_port_29_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 325)).
Definition closed_port_29_2 (v : leaf_values) : VM.t hvalue := (VM.add 325 (Gval (Fuint 1) (word_325 v)) (VM.empty hvalue)).
Definition port_29_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_29_2 (closed_port_29_2 v) (closed_port_29_2 v)).
Definition expr_port_29_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 324)).
Definition closed_port_29_3 (v : leaf_values) : VM.t hvalue := (VM.add 324 (Gval (Fuint 1) (word_324 v)) (VM.empty hvalue)).
Definition port_29_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_29_3 (closed_port_29_3 v) (closed_port_29_3 v)).
Definition expr_port_30_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_30_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_30_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_30_0 (closed_port_30_0 v) (closed_port_30_0 v)).
Definition expr_port_30_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_30_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_30_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_30_1 (closed_port_30_1 v) (closed_port_30_1 v)).
Definition expr_port_30_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 328)).
Definition closed_port_30_2 (v : leaf_values) : VM.t hvalue := (VM.add 328 (Gval (Fuint 1) (word_328 v)) (VM.empty hvalue)).
Definition port_30_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_30_2 (closed_port_30_2 v) (closed_port_30_2 v)).
Definition expr_port_30_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 327)).
Definition closed_port_30_3 (v : leaf_values) : VM.t hvalue := (VM.add 327 (Gval (Fuint 1) (word_327 v)) (VM.empty hvalue)).
Definition port_30_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_30_3 (closed_port_30_3 v) (closed_port_30_3 v)).
Definition expr_port_31_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_31_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_31_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_31_0 (closed_port_31_0 v) (closed_port_31_0 v)).
Definition expr_port_31_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_31_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_31_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_31_1 (closed_port_31_1 v) (closed_port_31_1 v)).
Definition expr_port_31_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 331)).
Definition closed_port_31_2 (v : leaf_values) : VM.t hvalue := (VM.add 331 (Gval (Fuint 1) (word_331 v)) (VM.empty hvalue)).
Definition port_31_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_31_2 (closed_port_31_2 v) (closed_port_31_2 v)).
Definition expr_port_31_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 330)).
Definition closed_port_31_3 (v : leaf_values) : VM.t hvalue := (VM.add 330 (Gval (Fuint 1) (word_330 v)) (VM.empty hvalue)).
Definition port_31_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_31_3 (closed_port_31_3 v) (closed_port_31_3 v)).
Definition expr_port_32_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_32_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_32_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_32_0 (closed_port_32_0 v) (closed_port_32_0 v)).
Definition expr_port_32_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_32_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_32_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_32_1 (closed_port_32_1 v) (closed_port_32_1 v)).
Definition expr_port_32_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 334)).
Definition closed_port_32_2 (v : leaf_values) : VM.t hvalue := (VM.add 334 (Gval (Fuint 1) (word_334 v)) (VM.empty hvalue)).
Definition port_32_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_32_2 (closed_port_32_2 v) (closed_port_32_2 v)).
Definition expr_port_32_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 333)).
Definition closed_port_32_3 (v : leaf_values) : VM.t hvalue := (VM.add 333 (Gval (Fuint 1) (word_333 v)) (VM.empty hvalue)).
Definition port_32_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_32_3 (closed_port_32_3 v) (closed_port_32_3 v)).
Definition expr_port_33_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_33_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_33_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_33_0 (closed_port_33_0 v) (closed_port_33_0 v)).
Definition expr_port_33_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_33_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_33_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_33_1 (closed_port_33_1 v) (closed_port_33_1 v)).
Definition expr_port_33_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 337)).
Definition closed_port_33_2 (v : leaf_values) : VM.t hvalue := (VM.add 337 (Gval (Fuint 1) (word_337 v)) (VM.empty hvalue)).
Definition port_33_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_33_2 (closed_port_33_2 v) (closed_port_33_2 v)).
Definition expr_port_33_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 335)).
Definition closed_port_33_3 (v : leaf_values) : VM.t hvalue := (VM.add 335 (Gval (Fuint 1) (word_335 v)) (VM.empty hvalue)).
Definition port_33_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_33_3 (closed_port_33_3 v) (closed_port_33_3 v)).
Definition expr_port_33_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 336)).
Definition closed_port_33_4 (v : leaf_values) : VM.t hvalue := (VM.add 336 (Gval (Fuint 1) (word_336 v)) (VM.empty hvalue)).
Definition port_33_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_33_4 (closed_port_33_4 v) (closed_port_33_4 v)).
Definition expr_port_34_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_34_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_34_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_34_0 (closed_port_34_0 v) (closed_port_34_0 v)).
Definition expr_port_34_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_34_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_34_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_34_1 (closed_port_34_1 v) (closed_port_34_1 v)).
Definition expr_port_34_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 339)).
Definition closed_port_34_2 (v : leaf_values) : VM.t hvalue := (VM.add 339 (Gval (Fuint 1) (word_339 v)) (VM.empty hvalue)).
Definition port_34_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_34_2 (closed_port_34_2 v) (closed_port_34_2 v)).
Definition expr_port_34_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 338)).
Definition closed_port_34_3 (v : leaf_values) : VM.t hvalue := (VM.add 338 (Gval (Fuint 1) (word_338 v)) (VM.empty hvalue)).
Definition port_34_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_34_3 (closed_port_34_3 v) (closed_port_34_3 v)).
Definition expr_port_35_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_35_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_35_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_35_0 (closed_port_35_0 v) (closed_port_35_0 v)).
Definition expr_port_35_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_35_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_35_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_35_1 (closed_port_35_1 v) (closed_port_35_1 v)).
Definition expr_port_35_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 341)).
Definition closed_port_35_2 (v : leaf_values) : VM.t hvalue := (VM.add 341 (Gval (Fuint 1) (word_341 v)) (VM.empty hvalue)).
Definition port_35_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_35_2 (closed_port_35_2 v) (closed_port_35_2 v)).
Definition expr_port_35_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 340)).
Definition closed_port_35_3 (v : leaf_values) : VM.t hvalue := (VM.add 340 (Gval (Fuint 1) (word_340 v)) (VM.empty hvalue)).
Definition port_35_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_35_3 (closed_port_35_3 v) (closed_port_35_3 v)).
Definition expr_port_36_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_36_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_36_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_36_0 (closed_port_36_0 v) (closed_port_36_0 v)).
Definition expr_port_36_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_36_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_36_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_36_1 (closed_port_36_1 v) (closed_port_36_1 v)).
Definition expr_port_36_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 303)).
Definition closed_port_36_2 (v : leaf_values) : VM.t hvalue := (VM.add 303 (Gval (Fuint 1) (word_303 v)) (VM.empty hvalue)).
Definition port_36_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_36_2 (closed_port_36_2 v) (closed_port_36_2 v)).
Definition expr_port_36_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 342)).
Definition closed_port_36_3 (v : leaf_values) : VM.t hvalue := (VM.add 342 (Gval (Fuint 1) (word_342 v)) (VM.empty hvalue)).
Definition port_36_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_36_3 (closed_port_36_3 v) (closed_port_36_3 v)).
Opaque word_0 word_1 word_2 word_3 word_4 word_5 word_6 word_37 word_38 word_39 word_40 word_41 word_42 word_43 word_44 word_45 word_46 word_47 word_48 word_49 word_50 word_51 word_52 word_53 word_54 word_55 word_56 word_57 word_58 word_59 word_60 word_61 word_62 word_63 word_64 word_65 word_66 word_67 word_68 word_69 word_70 word_71 word_72 word_73 word_74 word_75 word_76 word_77 word_78 word_79 word_80 word_81 word_82 word_83 word_84 word_85 word_86 word_87 word_88 word_89 word_90 word_91 word_92 word_93 word_94 word_95 word_96 word_97 word_98 word_99 word_100 word_101 word_102 word_103 word_104 word_105 word_106 word_107 word_108 word_109 word_110 word_111 word_112 word_113 word_114 word_115 word_116 word_117 word_118 word_119 word_120 word_121 word_122 word_123 word_124 word_125 word_126 word_127 word_128 word_129 word_130 word_131 word_132 word_133 word_134 word_135 word_136 word_137 word_138 word_139 word_140 word_141 word_142 word_143 word_144 word_145 word_146 word_147 word_148 word_149 word_150 word_151 word_152 word_153 word_154 word_155 word_156 word_157 word_158 word_159 word_160 word_161 word_162 word_163 word_164 word_165 word_166 word_167 word_168 word_169 word_170 word_171 word_172 word_173 word_174 word_175 word_176 word_177 word_178 word_179 word_180 word_181 word_182 word_183 word_184 word_185 word_186 word_187 word_188 word_189 word_190 word_191 word_192 word_193 word_194 word_195 word_196 word_197 word_198 word_199 word_200 word_201 word_202 word_203 word_204 word_205 word_206 word_207 word_208 word_209 word_210 word_211 word_212 word_213 word_214 word_215 word_216 word_217 word_218 word_219 word_220 word_221 word_222 word_223 word_224 word_225 word_226 word_227 word_228 word_229 word_230 word_231 word_232 word_233 word_234 word_235 word_236 word_237 word_238 word_239 word_240 word_241 word_242 word_243 word_244 word_245 word_246 word_247 word_248 word_249 word_250 word_251 word_252 word_253 word_254 word_255 word_256 word_257 word_258 word_259 word_260 word_261 word_262 word_263 word_264 word_265 word_266 word_267 word_268 word_269 word_270 word_271 word_272 word_273 word_274 word_275 word_276 word_277 word_278 word_279 word_280 word_281 word_282 word_283 word_284 word_285 word_286 word_287 word_288 word_289 word_290 word_291 word_292 word_293 word_294 word_295 word_296 word_297 word_298 word_299 word_300 word_301 word_302 word_303 word_304 word_305 word_306 word_307 word_308 word_309 word_310 word_311 word_312 word_313 word_314 word_315 word_316 word_317 word_318 word_319 word_320 word_321 word_322 word_323 word_324 word_325 word_326 word_327 word_328 word_329 word_330 word_331 word_332 word_333 word_334 word_335 word_336 word_337 word_338 word_339 word_340 word_341 word_342 word_343 word_344 word_345 word_346 word_347 word_348 word_349 word_350 word_351 word_352 word_353 word_354 word_355 word_356 word_357 word_358 word_359 word_360 word_361 word_362 word_363 word_364 word_365 word_366 word_367 word_368 word_369 word_370 word_371 word_372 word_373 word_374 word_375 word_376 word_377 word_378 word_379 word_380 word_381 word_382 word_383 word_384 word_385 word_386 word_387 word_388 word_389 word_390 word_391 word_392 word_393 word_394 word_395 word_396 word_397 word_398 word_399 word_400 word_401 word_402 word_403 word_404 word_405 word_406 word_407 word_408 word_409 word_410 word_411 word_412 word_413 word_414 word_415 word_416 word_417 word_418 word_419 word_420 word_421 word_422 word_423 port_7_0 port_7_1 port_7_2 port_7_3 port_7_4 port_7_5 port_8_0 port_8_1 port_8_2 port_8_3 port_8_4 port_8_5 port_9_0 port_9_1 port_9_2 port_9_3 port_9_4 port_9_5 port_9_6 port_10_0 port_10_1 port_10_2 port_10_3 port_10_4 port_10_5 port_10_6 port_11_0 port_11_1 port_11_2 port_11_3 port_11_4 port_11_5 port_11_6 port_11_7 port_11_8 port_11_9 port_12_0 port_12_1 port_12_2 port_12_3 port_12_4 port_12_5 port_12_6 port_12_7 port_12_8 port_12_9 port_13_0 port_13_1 port_13_2 port_13_3 port_13_4 port_13_5 port_13_6 port_13_7 port_13_8 port_13_9 port_14_0 port_14_1 port_14_2 port_14_3 port_14_4 port_14_5 port_14_6 port_14_7 port_14_8 port_14_9 port_15_0 port_15_1 port_15_2 port_15_3 port_15_4 port_15_5 port_15_6 port_15_7 port_15_8 port_15_9 port_16_0 port_16_1 port_16_2 port_16_3 port_16_4 port_16_5 port_16_6 port_16_7 port_16_8 port_16_9 port_17_0 port_17_1 port_17_2 port_17_3 port_17_4 port_17_5 port_17_6 port_17_7 port_17_8 port_17_9 port_18_0 port_18_1 port_18_2 port_18_3 port_18_4 port_18_5 port_18_6 port_18_7 port_18_8 port_18_9 port_19_0 port_19_1 port_19_2 port_19_3 port_19_4 port_19_5 port_19_6 port_20_0 port_20_1 port_20_2 port_20_3 port_20_4 port_20_5 port_21_0 port_21_1 port_21_2 port_21_3 port_21_4 port_21_5 port_22_0 port_22_1 port_22_2 port_22_3 port_22_4 port_22_5 port_23_0 port_23_1 port_23_2 port_23_3 port_23_4 port_23_5 port_24_0 port_24_1 port_24_2 port_24_3 port_24_4 port_24_5 port_25_0 port_25_1 port_25_2 port_25_3 port_25_4 port_25_5 port_26_0 port_26_1 port_26_2 port_26_3 port_26_4 port_26_5 port_27_0 port_27_1 port_27_2 port_27_3 port_27_4 port_27_5 port_27_6 port_28_0 port_28_1 port_28_2 port_28_3 port_28_4 port_28_5 port_28_6 port_29_0 port_29_1 port_29_2 port_29_3 port_29_4 port_29_5 port_30_0 port_30_1 port_30_2 port_30_3 port_30_4 port_30_5 port_31_0 port_31_1 port_31_2 port_31_3 port_31_4 port_31_5 port_32_0 port_32_1 port_32_2 port_32_3 port_32_4 port_32_5 port_33_0 port_33_1 port_33_2 port_33_3 port_33_4 port_33_5 port_33_6 port_34_0 port_34_1 port_34_2 port_34_3 port_34_4 port_34_5 port_35_0 port_35_1 port_35_2 port_35_3 port_35_4 port_35_5 port_36_0 port_36_1 port_36_2 port_36_3 port_36_4 port_36_5.
Definition stable_shape (values : N -> hvalue) : VM.t hvalue := Eval vm_compute in
 (VM.add 423 (values 423) (VM.add 422 (values 422) (VM.add 421 (values 421) (VM.add 420 (values 420) (VM.add 419 (values 419) (VM.add 418 (values 418) (VM.add 417 (values 417) (VM.add 416 (values 416) (VM.add 415 (values 415) (VM.add 414 (values 414) (VM.add 413 (values 413) (VM.add 412 (values 412) (VM.add 411 (values 411) (VM.add 410 (values 410) (VM.add 409 (values 409) (VM.add 408 (values 408) (VM.add 407 (values 407) (VM.add 406 (values 406) (VM.add 405 (values 405) (VM.add 404 (values 404) (VM.add 403 (values 403) (VM.add 402 (values 402) (VM.add 401 (values 401) (VM.add 400 (values 400) (VM.add 399 (values 399) (VM.add 398 (values 398) (VM.add 397 (values 397) (VM.add 396 (values 396) (VM.add 395 (values 395) (VM.add 394 (values 394) (VM.add 393 (values 393) (VM.add 392 (values 392) (VM.add 391 (values 391) (VM.add 390 (values 390) (VM.add 389 (values 389) (VM.add 388 (values 388) (VM.add 387 (values 387) (VM.add 386 (values 386) (VM.add 385 (values 385) (VM.add 384 (values 384) (VM.add 383 (values 383) (VM.add 382 (values 382) (VM.add 381 (values 381) (VM.add 380 (values 380) (VM.add 379 (values 379) (VM.add 378 (values 378) (VM.add 377 (values 377) (VM.add 376 (values 376) (VM.add 375 (values 375) (VM.add 374 (values 374) (VM.add 373 (values 373) (VM.add 372 (values 372) (VM.add 371 (values 371) (VM.add 370 (values 370) (VM.add 369 (values 369) (VM.add 368 (values 368) (VM.add 367 (values 367) (VM.add 366 (values 366) (VM.add 365 (values 365) (VM.add 364 (values 364) (VM.add 363 (values 363) (VM.add 362 (values 362) (VM.add 361 (values 361) (VM.add 360 (values 360) (VM.add 359 (values 359) (VM.add 358 (values 358) (VM.add 357 (values 357) (VM.add 356 (values 356) (VM.add 355 (values 355) (VM.add 354 (values 354) (VM.add 353 (values 353) (VM.add 352 (values 352) (VM.add 351 (values 351) (VM.add 350 (values 350) (VM.add 349 (values 349) (VM.add 348 (values 348) (VM.add 347 (values 347) (VM.add 346 (values 346) (VM.add 345 (values 345) (VM.add 344 (values 344) (VM.add 343 (values 343) (VM.add 342 (values 342) (VM.add 341 (values 341) (VM.add 340 (values 340) (VM.add 339 (values 339) (VM.add 338 (values 338) (VM.add 337 (values 337) (VM.add 336 (values 336) (VM.add 335 (values 335) (VM.add 334 (values 334) (VM.add 333 (values 333) (VM.add 332 (values 332) (VM.add 331 (values 331) (VM.add 330 (values 330) (VM.add 329 (values 329) (VM.add 328 (values 328) (VM.add 327 (values 327) (VM.add 326 (values 326) (VM.add 325 (values 325) (VM.add 324 (values 324) (VM.add 323 (values 323) (VM.add 322 (values 322) (VM.add 321 (values 321) (VM.add 320 (values 320) (VM.add 319 (values 319) (VM.add 318 (values 318) (VM.add 317 (values 317) (VM.add 316 (values 316) (VM.add 315 (values 315) (VM.add 314 (values 314) (VM.add 313 (values 313) (VM.add 312 (values 312) (VM.add 311 (values 311) (VM.add 310 (values 310) (VM.add 309 (values 309) (VM.add 308 (values 308) (VM.add 307 (values 307) (VM.add 306 (values 306) (VM.add 305 (values 305) (VM.add 304 (values 304) (VM.add 303 (values 303) (VM.add 302 (values 302) (VM.add 301 (values 301) (VM.add 300 (values 300) (VM.add 299 (values 299) (VM.add 298 (values 298) (VM.add 297 (values 297) (VM.add 296 (values 296) (VM.add 295 (values 295) (VM.add 294 (values 294) (VM.add 293 (values 293) (VM.add 292 (values 292) (VM.add 291 (values 291) (VM.add 290 (values 290) (VM.add 289 (values 289) (VM.add 288 (values 288) (VM.add 287 (values 287) (VM.add 286 (values 286) (VM.add 285 (values 285) (VM.add 284 (values 284) (VM.add 283 (values 283) (VM.add 282 (values 282) (VM.add 281 (values 281) (VM.add 280 (values 280) (VM.add 279 (values 279) (VM.add 278 (values 278) (VM.add 277 (values 277) (VM.add 276 (values 276) (VM.add 275 (values 275) (VM.add 274 (values 274) (VM.add 273 (values 273) (VM.add 272 (values 272) (VM.add 271 (values 271) (VM.add 270 (values 270) (VM.add 269 (values 269) (VM.add 268 (values 268) (VM.add 267 (values 267) (VM.add 266 (values 266) (VM.add 265 (values 265) (VM.add 264 (values 264) (VM.add 263 (values 263) (VM.add 262 (values 262) (VM.add 261 (values 261) (VM.add 260 (values 260) (VM.add 259 (values 259) (VM.add 258 (values 258) (VM.add 257 (values 257) (VM.add 256 (values 256) (VM.add 255 (values 255) (VM.add 254 (values 254) (VM.add 253 (values 253) (VM.add 252 (values 252) (VM.add 251 (values 251) (VM.add 250 (values 250) (VM.add 249 (values 249) (VM.add 248 (values 248) (VM.add 247 (values 247) (VM.add 246 (values 246) (VM.add 245 (values 245) (VM.add 244 (values 244) (VM.add 243 (values 243) (VM.add 242 (values 242) (VM.add 241 (values 241) (VM.add 240 (values 240) (VM.add 239 (values 239) (VM.add 238 (values 238) (VM.add 237 (values 237) (VM.add 236 (values 236) (VM.add 235 (values 235) (VM.add 234 (values 234) (VM.add 233 (values 233) (VM.add 232 (values 232) (VM.add 231 (values 231) (VM.add 230 (values 230) (VM.add 229 (values 229) (VM.add 228 (values 228) (VM.add 227 (values 227) (VM.add 226 (values 226) (VM.add 225 (values 225) (VM.add 224 (values 224) (VM.add 223 (values 223) (VM.add 222 (values 222) (VM.add 221 (values 221) (VM.add 220 (values 220) (VM.add 219 (values 219) (VM.add 218 (values 218) (VM.add 217 (values 217) (VM.add 216 (values 216) (VM.add 215 (values 215) (VM.add 214 (values 214) (VM.add 213 (values 213) (VM.add 212 (values 212) (VM.add 211 (values 211) (VM.add 210 (values 210) (VM.add 209 (values 209) (VM.add 208 (values 208) (VM.add 207 (values 207) (VM.add 206 (values 206) (VM.add 205 (values 205) (VM.add 204 (values 204) (VM.add 203 (values 203) (VM.add 202 (values 202) (VM.add 201 (values 201) (VM.add 200 (values 200) (VM.add 199 (values 199) (VM.add 198 (values 198) (VM.add 197 (values 197) (VM.add 196 (values 196) (VM.add 195 (values 195) (VM.add 194 (values 194) (VM.add 193 (values 193) (VM.add 192 (values 192) (VM.add 191 (values 191) (VM.add 190 (values 190) (VM.add 189 (values 189) (VM.add 188 (values 188) (VM.add 187 (values 187) (VM.add 186 (values 186) (VM.add 185 (values 185) (VM.add 184 (values 184) (VM.add 183 (values 183) (VM.add 182 (values 182) (VM.add 181 (values 181) (VM.add 180 (values 180) (VM.add 179 (values 179) (VM.add 178 (values 178) (VM.add 177 (values 177) (VM.add 176 (values 176) (VM.add 175 (values 175) (VM.add 174 (values 174) (VM.add 173 (values 173) (VM.add 172 (values 172) (VM.add 171 (values 171) (VM.add 170 (values 170) (VM.add 169 (values 169) (VM.add 168 (values 168) (VM.add 167 (values 167) (VM.add 166 (values 166) (VM.add 165 (values 165) (VM.add 164 (values 164) (VM.add 163 (values 163) (VM.add 162 (values 162) (VM.add 161 (values 161) (VM.add 160 (values 160) (VM.add 159 (values 159) (VM.add 158 (values 158) (VM.add 157 (values 157) (VM.add 156 (values 156) (VM.add 155 (values 155) (VM.add 154 (values 154) (VM.add 153 (values 153) (VM.add 152 (values 152) (VM.add 151 (values 151) (VM.add 150 (values 150) (VM.add 149 (values 149) (VM.add 148 (values 148) (VM.add 147 (values 147) (VM.add 146 (values 146) (VM.add 145 (values 145) (VM.add 144 (values 144) (VM.add 143 (values 143) (VM.add 142 (values 142) (VM.add 141 (values 141) (VM.add 140 (values 140) (VM.add 139 (values 139) (VM.add 138 (values 138) (VM.add 137 (values 137) (VM.add 136 (values 136) (VM.add 135 (values 135) (VM.add 134 (values 134) (VM.add 133 (values 133) (VM.add 132 (values 132) (VM.add 131 (values 131) (VM.add 130 (values 130) (VM.add 129 (values 129) (VM.add 128 (values 128) (VM.add 127 (values 127) (VM.add 126 (values 126) (VM.add 125 (values 125) (VM.add 124 (values 124) (VM.add 123 (values 123) (VM.add 122 (values 122) (VM.add 121 (values 121) (VM.add 120 (values 120) (VM.add 119 (values 119) (VM.add 118 (values 118) (VM.add 117 (values 117) (VM.add 116 (values 116) (VM.add 115 (values 115) (VM.add 114 (values 114) (VM.add 113 (values 113) (VM.add 112 (values 112) (VM.add 111 (values 111) (VM.add 110 (values 110) (VM.add 109 (values 109) (VM.add 108 (values 108) (VM.add 107 (values 107) (VM.add 106 (values 106) (VM.add 105 (values 105) (VM.add 104 (values 104) (VM.add 103 (values 103) (VM.add 102 (values 102) (VM.add 101 (values 101) (VM.add 100 (values 100) (VM.add 99 (values 99) (VM.add 98 (values 98) (VM.add 97 (values 97) (VM.add 96 (values 96) (VM.add 95 (values 95) (VM.add 94 (values 94) (VM.add 93 (values 93) (VM.add 92 (values 92) (VM.add 91 (values 91) (VM.add 90 (values 90) (VM.add 89 (values 89) (VM.add 88 (values 88) (VM.add 87 (values 87) (VM.add 86 (values 86) (VM.add 85 (values 85) (VM.add 84 (values 84) (VM.add 83 (values 83) (VM.add 82 (values 82) (VM.add 81 (values 81) (VM.add 80 (values 80) (VM.add 79 (values 79) (VM.add 78 (values 78) (VM.add 77 (values 77) (VM.add 76 (values 76) (VM.add 75 (values 75) (VM.add 74 (values 74) (VM.add 73 (values 73) (VM.add 72 (values 72) (VM.add 71 (values 71) (VM.add 70 (values 70) (VM.add 69 (values 69) (VM.add 68 (values 68) (VM.add 67 (values 67) (VM.add 66 (values 66) (VM.add 65 (values 65) (VM.add 64 (values 64) (VM.add 63 (values 63) (VM.add 62 (values 62) (VM.add 61 (values 61) (VM.add 60 (values 60) (VM.add 59 (values 59) (VM.add 58 (values 58) (VM.add 57 (values 57) (VM.add 56 (values 56) (VM.add 55 (values 55) (VM.add 54 (values 54) (VM.add 53 (values 53) (VM.add 52 (values 52) (VM.add 51 (values 51) (VM.add 50 (values 50) (VM.add 49 (values 49) (VM.add 48 (values 48) (VM.add 47 (values 47) (VM.add 46 (values 46) (VM.add 45 (values 45) (VM.add 44 (values 44) (VM.add 43 (values 43) (VM.add 42 (values 42) (VM.add 41 (values 41) (VM.add 40 (values 40) (VM.add 39 (values 39) (VM.add 38 (values 38) (VM.add 37 (values 37) (VM.add 36 (values 36) (VM.add 35 (values 35) (VM.add 34 (values 34) (VM.add 33 (values 33) (VM.add 32 (values 32) (VM.add 31 (values 31) (VM.add 30 (values 30) (VM.add 29 (values 29) (VM.add 28 (values 28) (VM.add 27 (values 27) (VM.add 26 (values 26) (VM.add 25 (values 25) (VM.add 24 (values 24) (VM.add 23 (values 23) (VM.add 22 (values 22) (VM.add 21 (values 21) (VM.add 20 (values 20) (VM.add 19 (values 19) (VM.add 18 (values 18) (VM.add 17 (values 17) (VM.add 16 (values 16) (VM.add 15 (values 15) (VM.add 14 (values 14) (VM.add 13 (values 13) (VM.add 12 (values 12) (VM.add 11 (values 11) (VM.add 10 (values 10) (VM.add 9 (values 9) (VM.add 8 (values 8) (VM.add 7 (values 7) (VM.add 6 (values 6) (VM.add 5 (values 5) (VM.add 4 (values 4) (VM.add 3 (values 3) (VM.add 2 (values 2) (VM.add 1 (values 1) (VM.add 0 (values 0) (VM.empty hvalue))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition stable_values (v : leaf_values) (id : N) : hvalue := match id with
| 0 => (Gval Fclock (word_0 v))
| 1 => (Gval (Fuint 1) (word_1 v))
| 2 => (Gval (Fuint 8) (word_2 v))
| 3 => (Gval (Fuint 8) (word_3 v))
| 4 => (Gval (Fuint 1) (word_4 v))
| 5 => (Gval (Fuint 1) (word_5 v))
| 6 => (Gval (Fuint 16) (word_6 v))
| 7 => (Bval (Bflips 0 Flipped (Gval Fclock (port_7_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_7_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_7_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_7_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_7_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_7_5 v)) Bnil)))))))
| 8 => (Bval (Bflips 0 Flipped (Gval Fclock (port_8_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_8_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_8_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_8_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_8_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_8_5 v)) Bnil)))))))
| 9 => (Bval (Bflips 0 Flipped (Gval Fclock (port_9_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_9_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_9_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_9_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_9_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_9_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_9_6 v)) Bnil))))))))
| 10 => (Bval (Bflips 0 Flipped (Gval Fclock (port_10_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_10_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_10_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_10_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_10_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_10_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_10_6 v)) Bnil))))))))
| 11 => (Bval (Bflips 0 Flipped (Gval Fclock (port_11_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_11_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_11_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_11_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_11_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_11_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_11_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_11_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_11_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_11_9 v)) Bnil)))))))))))
| 12 => (Bval (Bflips 0 Flipped (Gval Fclock (port_12_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_12_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_12_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_12_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_12_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_12_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_12_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_12_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_12_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_12_9 v)) Bnil)))))))))))
| 13 => (Bval (Bflips 0 Flipped (Gval Fclock (port_13_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_13_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_13_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_13_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_13_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_13_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_13_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_13_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_13_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_13_9 v)) Bnil)))))))))))
| 14 => (Bval (Bflips 0 Flipped (Gval Fclock (port_14_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_14_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_14_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_14_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_14_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_14_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_14_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_14_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_14_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_14_9 v)) Bnil)))))))))))
| 15 => (Bval (Bflips 0 Flipped (Gval Fclock (port_15_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_15_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_15_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_15_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_15_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_15_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_15_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_15_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_15_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_15_9 v)) Bnil)))))))))))
| 16 => (Bval (Bflips 0 Flipped (Gval Fclock (port_16_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_16_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_16_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_16_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_16_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_16_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_16_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_16_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_16_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_16_9 v)) Bnil)))))))))))
| 17 => (Bval (Bflips 0 Flipped (Gval Fclock (port_17_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_17_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_17_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_17_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_17_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_17_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_17_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_17_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_17_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_17_9 v)) Bnil)))))))))))
| 18 => (Bval (Bflips 0 Flipped (Gval Fclock (port_18_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_18_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_18_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_18_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_18_4 v)) (Bflips 5 Flipped (Gval (Fuint 1) (port_18_5 v)) (Bflips 6 Flipped (Gval (Fuint 1) (port_18_6 v)) (Bflips 7 Nflip (Gval (Fuint 1) (port_18_7 v)) (Bflips 8 Nflip (Gval (Fuint 1) (port_18_8 v)) (Bflips 9 Nflip (Gval (Fuint 1) (port_18_9 v)) Bnil)))))))))))
| 19 => (Bval (Bflips 0 Flipped (Gval Fclock (port_19_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_19_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_19_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_19_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_19_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_19_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_19_6 v)) Bnil))))))))
| 20 => (Bval (Bflips 0 Flipped (Gval Fclock (port_20_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_20_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_20_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_20_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_20_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_20_5 v)) Bnil)))))))
| 21 => (Bval (Bflips 0 Flipped (Gval Fclock (port_21_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_21_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_21_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_21_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_21_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_21_5 v)) Bnil)))))))
| 22 => (Bval (Bflips 0 Flipped (Gval Fclock (port_22_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_22_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_22_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_22_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_22_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_22_5 v)) Bnil)))))))
| 23 => (Bval (Bflips 0 Flipped (Gval Fclock (port_23_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_23_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_23_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_23_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_23_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_23_5 v)) Bnil)))))))
| 24 => (Bval (Bflips 0 Flipped (Gval Fclock (port_24_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_24_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_24_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_24_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_24_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_24_5 v)) Bnil)))))))
| 25 => (Bval (Bflips 0 Flipped (Gval Fclock (port_25_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_25_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_25_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_25_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_25_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_25_5 v)) Bnil)))))))
| 26 => (Bval (Bflips 0 Flipped (Gval Fclock (port_26_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_26_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_26_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_26_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_26_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_26_5 v)) Bnil)))))))
| 27 => (Bval (Bflips 0 Flipped (Gval Fclock (port_27_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_27_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_27_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_27_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_27_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_27_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_27_6 v)) Bnil))))))))
| 28 => (Bval (Bflips 0 Flipped (Gval Fclock (port_28_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_28_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_28_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_28_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_28_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_28_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_28_6 v)) Bnil))))))))
| 29 => (Bval (Bflips 0 Flipped (Gval Fclock (port_29_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_29_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_29_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_29_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_29_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_29_5 v)) Bnil)))))))
| 30 => (Bval (Bflips 0 Flipped (Gval Fclock (port_30_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_30_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_30_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_30_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_30_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_30_5 v)) Bnil)))))))
| 31 => (Bval (Bflips 0 Flipped (Gval Fclock (port_31_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_31_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_31_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_31_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_31_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_31_5 v)) Bnil)))))))
| 32 => (Bval (Bflips 0 Flipped (Gval Fclock (port_32_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_32_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_32_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_32_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_32_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_32_5 v)) Bnil)))))))
| 33 => (Bval (Bflips 0 Flipped (Gval Fclock (port_33_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_33_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_33_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_33_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_33_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_33_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_33_6 v)) Bnil))))))))
| 34 => (Bval (Bflips 0 Flipped (Gval Fclock (port_34_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_34_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_34_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_34_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_34_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_34_5 v)) Bnil)))))))
| 35 => (Bval (Bflips 0 Flipped (Gval Fclock (port_35_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_35_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_35_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_35_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_35_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_35_5 v)) Bnil)))))))
| 36 => (Bval (Bflips 0 Flipped (Gval Fclock (port_36_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_36_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_36_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_36_3 v)) (Bflips 4 Nflip (Gval (Fuint 1) (port_36_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_36_5 v)) Bnil)))))))
| 37 => (Gval (Fuint 1) (word_37 v))
| 38 => (Gval (Fuint 9) (word_38 v))
| 39 => (Gval (Fuint 9) (word_39 v))
| 40 => (Gval (Fuint 10) (word_40 v))
| 41 => (Gval (Fuint 9) (word_41 v))
| 42 => (Gval (Fuint 9) (word_42 v))
| 43 => (Gval (Fuint 10) (word_43 v))
| 44 => (Gval (Fuint 2) (word_44 v))
| 45 => (Gval (Fuint 3) (word_45 v))
| 46 => (Gval (Fuint 1) (word_46 v))
| 47 => (Gval (Fuint 9) (word_47 v))
| 48 => (Gval (Fuint 1) (word_48 v))
| 49 => (Gval (Fuint 9) (word_49 v))
| 50 => (Gval (Fuint 1) (word_50 v))
| 51 => (Gval (Fuint 9) (word_51 v))
| 52 => (Gval (Fuint 9) (word_52 v))
| 53 => (Gval (Fuint 1) (word_53 v))
| 54 => (Gval (Fuint 9) (word_54 v))
| 55 => (Gval (Fuint 9) (word_55 v))
| 56 => (Gval (Fuint 1) (word_56 v))
| 57 => (Gval (Fuint 9) (word_57 v))
| 58 => (Gval (Fuint 1) (word_58 v))
| 59 => (Gval (Fuint 9) (word_59 v))
| 60 => (Gval (Fuint 1) (word_60 v))
| 61 => (Gval (Fuint 3) (word_61 v))
| 62 => (Gval (Fuint 1) (word_62 v))
| 63 => (Gval (Fuint 2) (word_63 v))
| 64 => (Gval (Fuint 1) (word_64 v))
| 65 => (Gval (Fuint 2) (word_65 v))
| 66 => (Gval (Fuint 1) (word_66 v))
| 67 => (Gval (Fuint 2) (word_67 v))
| 68 => (Gval (Fuint 1) (word_68 v))
| 69 => (Gval (Fuint 10) (word_69 v))
| 70 => (Gval (Fuint 2) (word_70 v))
| 71 => (Gval (Fuint 12) (word_71 v))
| 72 => (Gval (Fuint 1) (word_72 v))
| 73 => (Gval (Fuint 1) (word_73 v))
| 74 => (Gval (Fuint 1) (word_74 v))
| 75 => (Gval (Fuint 1) (word_75 v))
| 76 => (Gval (Fuint 1) (word_76 v))
| 77 => (Gval (Fuint 1) (word_77 v))
| 78 => (Gval (Fuint 1) (word_78 v))
| 79 => (Gval (Fuint 1) (word_79 v))
| 80 => (Gval (Fuint 1) (word_80 v))
| 81 => (Gval (Fuint 1) (word_81 v))
| 82 => (Gval (Fuint 1) (word_82 v))
| 83 => (Gval (Fuint 1) (word_83 v))
| 84 => (Gval (Fuint 3) (word_84 v))
| 85 => (Gval (Fuint 1) (word_85 v))
| 86 => (Gval (Fuint 9) (word_86 v))
| 87 => (Gval (Fuint 1) (word_87 v))
| 88 => (Gval (Fuint 9) (word_88 v))
| 89 => (Gval (Fuint 1) (word_89 v))
| 90 => (Gval (Fuint 9) (word_90 v))
| 91 => (Gval (Fuint 1) (word_91 v))
| 92 => (Gval (Fuint 9) (word_92 v))
| 93 => (Gval (Fuint 1) (word_93 v))
| 94 => (Gval (Fuint 9) (word_94 v))
| 95 => (Gval (Fuint 1) (word_95 v))
| 96 => (Gval (Fuint 9) (word_96 v))
| 97 => (Gval (Fuint 1) (word_97 v))
| 98 => (Gval (Fuint 1) (word_98 v))
| 99 => (Gval (Fuint 2) (word_99 v))
| 100 => (Gval (Fuint 1) (word_100 v))
| 101 => (Gval (Fuint 2) (word_101 v))
| 102 => (Gval (Fuint 1) (word_102 v))
| 103 => (Gval (Fuint 2) (word_103 v))
| 104 => (Gval (Fuint 1) (word_104 v))
| 105 => (Gval (Fuint 11) (word_105 v))
| 106 => (Gval (Fuint 2) (word_106 v))
| 107 => (Gval (Fuint 13) (word_107 v))
| 108 => (Gval (Fuint 1) (word_108 v))
| 109 => (Gval (Fuint 1) (word_109 v))
| 110 => (Gval (Fuint 1) (word_110 v))
| 111 => (Gval (Fuint 1) (word_111 v))
| 112 => (Gval (Fuint 1) (word_112 v))
| 113 => (Gval (Fuint 1) (word_113 v))
| 114 => (Gval (Fuint 1) (word_114 v))
| 115 => (Gval (Fuint 1) (word_115 v))
| 116 => (Gval (Fuint 1) (word_116 v))
| 117 => (Gval (Fuint 1) (word_117 v))
| 118 => (Gval (Fuint 1) (word_118 v))
| 119 => (Gval (Fuint 1) (word_119 v))
| 120 => (Gval (Fuint 1) (word_120 v))
| 121 => (Gval (Fuint 3) (word_121 v))
| 122 => (Gval (Fuint 1) (word_122 v))
| 123 => (Gval (Fuint 9) (word_123 v))
| 124 => (Gval (Fuint 1) (word_124 v))
| 125 => (Gval (Fuint 9) (word_125 v))
| 126 => (Gval (Fuint 1) (word_126 v))
| 127 => (Gval (Fuint 9) (word_127 v))
| 128 => (Gval (Fuint 1) (word_128 v))
| 129 => (Gval (Fuint 9) (word_129 v))
| 130 => (Gval (Fuint 1) (word_130 v))
| 131 => (Gval (Fuint 9) (word_131 v))
| 132 => (Gval (Fuint 1) (word_132 v))
| 133 => (Gval (Fuint 9) (word_133 v))
| 134 => (Gval (Fuint 1) (word_134 v))
| 135 => (Gval (Fuint 1) (word_135 v))
| 136 => (Gval (Fuint 2) (word_136 v))
| 137 => (Gval (Fuint 1) (word_137 v))
| 138 => (Gval (Fuint 2) (word_138 v))
| 139 => (Gval (Fuint 1) (word_139 v))
| 140 => (Gval (Fuint 2) (word_140 v))
| 141 => (Gval (Fuint 1) (word_141 v))
| 142 => (Gval (Fuint 11) (word_142 v))
| 143 => (Gval (Fuint 2) (word_143 v))
| 144 => (Gval (Fuint 13) (word_144 v))
| 145 => (Gval (Fuint 1) (word_145 v))
| 146 => (Gval (Fuint 1) (word_146 v))
| 147 => (Gval (Fuint 1) (word_147 v))
| 148 => (Gval (Fuint 1) (word_148 v))
| 149 => (Gval (Fuint 1) (word_149 v))
| 150 => (Gval (Fuint 1) (word_150 v))
| 151 => (Gval (Fuint 1) (word_151 v))
| 152 => (Gval (Fuint 1) (word_152 v))
| 153 => (Gval (Fuint 1) (word_153 v))
| 154 => (Gval (Fuint 1) (word_154 v))
| 155 => (Gval (Fuint 1) (word_155 v))
| 156 => (Gval (Fuint 1) (word_156 v))
| 157 => (Gval (Fuint 1) (word_157 v))
| 158 => (Gval (Fuint 3) (word_158 v))
| 159 => (Gval (Fuint 1) (word_159 v))
| 160 => (Gval (Fuint 9) (word_160 v))
| 161 => (Gval (Fuint 1) (word_161 v))
| 162 => (Gval (Fuint 9) (word_162 v))
| 163 => (Gval (Fuint 1) (word_163 v))
| 164 => (Gval (Fuint 9) (word_164 v))
| 165 => (Gval (Fuint 1) (word_165 v))
| 166 => (Gval (Fuint 9) (word_166 v))
| 167 => (Gval (Fuint 1) (word_167 v))
| 168 => (Gval (Fuint 9) (word_168 v))
| 169 => (Gval (Fuint 1) (word_169 v))
| 170 => (Gval (Fuint 9) (word_170 v))
| 171 => (Gval (Fuint 1) (word_171 v))
| 172 => (Gval (Fuint 1) (word_172 v))
| 173 => (Gval (Fuint 2) (word_173 v))
| 174 => (Gval (Fuint 1) (word_174 v))
| 175 => (Gval (Fuint 2) (word_175 v))
| 176 => (Gval (Fuint 1) (word_176 v))
| 177 => (Gval (Fuint 2) (word_177 v))
| 178 => (Gval (Fuint 1) (word_178 v))
| 179 => (Gval (Fuint 10) (word_179 v))
| 180 => (Gval (Fuint 12) (word_180 v))
| 181 => (Gval (Fuint 1) (word_181 v))
| 182 => (Gval (Fuint 1) (word_182 v))
| 183 => (Gval (Fuint 1) (word_183 v))
| 184 => (Gval (Fuint 1) (word_184 v))
| 185 => (Gval (Fuint 1) (word_185 v))
| 186 => (Gval (Fuint 1) (word_186 v))
| 187 => (Gval (Fuint 1) (word_187 v))
| 188 => (Gval (Fuint 1) (word_188 v))
| 189 => (Gval (Fuint 1) (word_189 v))
| 190 => (Gval (Fuint 1) (word_190 v))
| 191 => (Gval (Fuint 1) (word_191 v))
| 192 => (Gval (Fuint 1) (word_192 v))
| 193 => (Gval (Fuint 1) (word_193 v))
| 194 => (Gval (Fuint 2) (word_194 v))
| 195 => (Gval (Fuint 1) (word_195 v))
| 196 => (Gval (Fuint 2) (word_196 v))
| 197 => (Gval (Fuint 1) (word_197 v))
| 198 => (Gval (Fuint 2) (word_198 v))
| 199 => (Gval (Fuint 1) (word_199 v))
| 200 => (Gval (Fuint 1) (word_200 v))
| 201 => (Gval (Fuint 1) (word_201 v))
| 202 => (Gval (Fuint 1) (word_202 v))
| 203 => (Gval (Fuint 1) (word_203 v))
| 204 => (Gval (Fuint 1) (word_204 v))
| 205 => (Gval (Fuint 1) (word_205 v))
| 206 => (Gval (Fuint 1) (word_206 v))
| 207 => (Gval (Fuint 1) (word_207 v))
| 208 => (Gval (Fuint 1) (word_208 v))
| 209 => (Gval (Fuint 1) (word_209 v))
| 210 => (Gval (Fuint 1) (word_210 v))
| 211 => (Gval (Fuint 1) (word_211 v))
| 212 => (Gval (Fuint 1) (word_212 v))
| 213 => (Gval (Fuint 1) (word_213 v))
| 214 => (Gval (Fuint 1) (word_214 v))
| 215 => (Gval (Fuint 1) (word_215 v))
| 216 => (Gval (Fuint 1) (word_216 v))
| 217 => (Gval (Fuint 1) (word_217 v))
| 218 => (Gval (Fuint 1) (word_218 v))
| 219 => (Gval (Fuint 1) (word_219 v))
| 220 => (Gval (Fuint 1) (word_220 v))
| 221 => (Gval (Fuint 1) (word_221 v))
| 222 => (Gval (Fuint 1) (word_222 v))
| 223 => (Gval (Fuint 1) (word_223 v))
| 224 => (Gval (Fuint 1) (word_224 v))
| 225 => (Gval (Fuint 1) (word_225 v))
| 226 => (Gval (Fuint 1) (word_226 v))
| 227 => (Gval (Fuint 1) (word_227 v))
| 228 => (Gval (Fuint 1) (word_228 v))
| 229 => (Gval (Fuint 1) (word_229 v))
| 230 => (Gval (Fuint 1) (word_230 v))
| 231 => (Gval (Fuint 1) (word_231 v))
| 232 => (Gval (Fuint 1) (word_232 v))
| 233 => (Gval (Fuint 1) (word_233 v))
| 234 => (Gval (Fuint 1) (word_234 v))
| 235 => (Gval (Fuint 1) (word_235 v))
| 236 => (Gval (Fuint 1) (word_236 v))
| 237 => (Gval (Fuint 1) (word_237 v))
| 238 => (Gval (Fuint 1) (word_238 v))
| 239 => (Gval (Fuint 1) (word_239 v))
| 240 => (Gval (Fuint 1) (word_240 v))
| 241 => (Gval (Fuint 1) (word_241 v))
| 242 => (Gval (Fuint 1) (word_242 v))
| 243 => (Gval (Fuint 1) (word_243 v))
| 244 => (Gval (Fuint 1) (word_244 v))
| 245 => (Gval (Fuint 1) (word_245 v))
| 246 => (Gval (Fuint 1) (word_246 v))
| 247 => (Gval (Fuint 1) (word_247 v))
| 248 => (Gval (Fuint 1) (word_248 v))
| 249 => (Gval (Fuint 1) (word_249 v))
| 250 => (Gval (Fuint 1) (word_250 v))
| 251 => (Gval (Fuint 1) (word_251 v))
| 252 => (Gval (Fuint 1) (word_252 v))
| 253 => (Gval (Fuint 1) (word_253 v))
| 254 => (Gval (Fuint 1) (word_254 v))
| 255 => (Gval (Fuint 1) (word_255 v))
| 256 => (Gval (Fuint 1) (word_256 v))
| 257 => (Gval (Fuint 1) (word_257 v))
| 258 => (Gval (Fuint 1) (word_258 v))
| 259 => (Gval (Fuint 1) (word_259 v))
| 260 => (Gval (Fuint 1) (word_260 v))
| 261 => (Gval (Fuint 1) (word_261 v))
| 262 => (Gval (Fuint 1) (word_262 v))
| 263 => (Gval (Fuint 1) (word_263 v))
| 264 => (Gval (Fuint 1) (word_264 v))
| 265 => (Gval (Fuint 1) (word_265 v))
| 266 => (Gval (Fuint 1) (word_266 v))
| 267 => (Gval (Fuint 1) (word_267 v))
| 268 => (Gval (Fuint 1) (word_268 v))
| 269 => (Gval (Fuint 1) (word_269 v))
| 270 => (Gval (Fuint 1) (word_270 v))
| 271 => (Gval (Fuint 1) (word_271 v))
| 272 => (Gval (Fuint 1) (word_272 v))
| 273 => (Gval (Fuint 1) (word_273 v))
| 274 => (Gval (Fuint 1) (word_274 v))
| 275 => (Gval (Fuint 1) (word_275 v))
| 276 => (Gval (Fuint 1) (word_276 v))
| 277 => (Gval (Fuint 1) (word_277 v))
| 278 => (Gval (Fuint 1) (word_278 v))
| 279 => (Gval (Fuint 1) (word_279 v))
| 280 => (Gval (Fuint 1) (word_280 v))
| 281 => (Gval (Fuint 1) (word_281 v))
| 282 => (Gval (Fuint 1) (word_282 v))
| 283 => (Gval (Fuint 1) (word_283 v))
| 284 => (Gval (Fuint 1) (word_284 v))
| 285 => (Gval (Fuint 1) (word_285 v))
| 286 => (Gval (Fuint 1) (word_286 v))
| 287 => (Gval (Fuint 1) (word_287 v))
| 288 => (Gval (Fuint 1) (word_288 v))
| 289 => (Gval (Fuint 1) (word_289 v))
| 290 => (Gval (Fuint 1) (word_290 v))
| 291 => (Gval (Fuint 1) (word_291 v))
| 292 => (Gval (Fuint 1) (word_292 v))
| 293 => (Gval (Fuint 1) (word_293 v))
| 294 => (Gval (Fuint 1) (word_294 v))
| 295 => (Gval (Fuint 1) (word_295 v))
| 296 => (Gval (Fuint 1) (word_296 v))
| 297 => (Gval (Fuint 1) (word_297 v))
| 298 => (Gval (Fuint 1) (word_298 v))
| 299 => (Gval (Fuint 1) (word_299 v))
| 300 => (Gval (Fuint 1) (word_300 v))
| 301 => (Gval (Fuint 1) (word_301 v))
| 302 => (Gval (Fuint 1) (word_302 v))
| 303 => (Gval (Fuint 1) (word_303 v))
| 304 => (Gval (Fuint 1) (word_304 v))
| 305 => (Gval (Fuint 1) (word_305 v))
| 306 => (Gval (Fuint 1) (word_306 v))
| 307 => (Gval (Fuint 1) (word_307 v))
| 308 => (Gval (Fuint 1) (word_308 v))
| 309 => (Gval (Fuint 1) (word_309 v))
| 310 => (Gval (Fuint 1) (word_310 v))
| 311 => (Gval (Fuint 1) (word_311 v))
| 312 => (Gval (Fuint 1) (word_312 v))
| 313 => (Gval (Fuint 1) (word_313 v))
| 314 => (Gval (Fuint 1) (word_314 v))
| 315 => (Gval (Fuint 1) (word_315 v))
| 316 => (Gval (Fuint 1) (word_316 v))
| 317 => (Gval (Fuint 1) (word_317 v))
| 318 => (Gval (Fuint 1) (word_318 v))
| 319 => (Gval (Fuint 1) (word_319 v))
| 320 => (Gval (Fuint 1) (word_320 v))
| 321 => (Gval (Fuint 1) (word_321 v))
| 322 => (Gval (Fuint 1) (word_322 v))
| 323 => (Gval (Fuint 1) (word_323 v))
| 324 => (Gval (Fuint 1) (word_324 v))
| 325 => (Gval (Fuint 1) (word_325 v))
| 326 => (Gval (Fuint 1) (word_326 v))
| 327 => (Gval (Fuint 1) (word_327 v))
| 328 => (Gval (Fuint 1) (word_328 v))
| 329 => (Gval (Fuint 1) (word_329 v))
| 330 => (Gval (Fuint 1) (word_330 v))
| 331 => (Gval (Fuint 1) (word_331 v))
| 332 => (Gval (Fuint 1) (word_332 v))
| 333 => (Gval (Fuint 1) (word_333 v))
| 334 => (Gval (Fuint 1) (word_334 v))
| 335 => (Gval (Fuint 1) (word_335 v))
| 336 => (Gval (Fuint 1) (word_336 v))
| 337 => (Gval (Fuint 1) (word_337 v))
| 338 => (Gval (Fuint 1) (word_338 v))
| 339 => (Gval (Fuint 1) (word_339 v))
| 340 => (Gval (Fuint 1) (word_340 v))
| 341 => (Gval (Fuint 1) (word_341 v))
| 342 => (Gval (Fuint 1) (word_342 v))
| 343 => (Gval (Fuint 1) (word_343 v))
| 344 => (Gval (Fuint 1) (word_344 v))
| 345 => (Gval (Fuint 1) (word_345 v))
| 346 => (Gval (Fuint 1) (word_346 v))
| 347 => (Gval (Fuint 1) (word_347 v))
| 348 => (Gval (Fuint 1) (word_348 v))
| 349 => (Gval (Fuint 1) (word_349 v))
| 350 => (Gval (Fuint 1) (word_350 v))
| 351 => (Gval (Fuint 1) (word_351 v))
| 352 => (Gval (Fuint 1) (word_352 v))
| 353 => (Gval (Fuint 1) (word_353 v))
| 354 => (Gval (Fuint 1) (word_354 v))
| 355 => (Gval (Fuint 1) (word_355 v))
| 356 => (Gval (Fuint 1) (word_356 v))
| 357 => (Gval (Fuint 1) (word_357 v))
| 358 => (Gval (Fuint 1) (word_358 v))
| 359 => (Gval (Fuint 1) (word_359 v))
| 360 => (Gval (Fuint 1) (word_360 v))
| 361 => (Gval (Fuint 1) (word_361 v))
| 362 => (Gval (Fuint 1) (word_362 v))
| 363 => (Gval (Fuint 1) (word_363 v))
| 364 => (Gval (Fuint 1) (word_364 v))
| 365 => (Gval (Fuint 1) (word_365 v))
| 366 => (Gval (Fuint 1) (word_366 v))
| 367 => (Gval (Fuint 1) (word_367 v))
| 368 => (Gval (Fuint 1) (word_368 v))
| 369 => (Gval (Fuint 1) (word_369 v))
| 370 => (Gval (Fuint 1) (word_370 v))
| 371 => (Gval (Fuint 1) (word_371 v))
| 372 => (Gval (Fuint 1) (word_372 v))
| 373 => (Gval (Fuint 2) (word_373 v))
| 374 => (Gval (Fuint 2) (word_374 v))
| 375 => (Gval (Fuint 4) (word_375 v))
| 376 => (Gval (Fuint 2) (word_376 v))
| 377 => (Gval (Fuint 2) (word_377 v))
| 378 => (Gval (Fuint 4) (word_378 v))
| 379 => (Gval (Fuint 8) (word_379 v))
| 380 => (Gval (Fuint 2) (word_380 v))
| 381 => (Gval (Fuint 2) (word_381 v))
| 382 => (Gval (Fuint 4) (word_382 v))
| 383 => (Gval (Fuint 2) (word_383 v))
| 384 => (Gval (Fuint 2) (word_384 v))
| 385 => (Gval (Fuint 4) (word_385 v))
| 386 => (Gval (Fuint 8) (word_386 v))
| 387 => (Gval (Fuint 16) (word_387 v))
| 388 => (Gval (Fuint 2) (word_388 v))
| 389 => (Gval (Fuint 3) (word_389 v))
| 390 => (Gval (Fuint 2) (word_390 v))
| 391 => (Gval (Fuint 2) (word_391 v))
| 392 => (Gval (Fuint 4) (word_392 v))
| 393 => (Gval (Fuint 7) (word_393 v))
| 394 => (Gval (Fuint 2) (word_394 v))
| 395 => (Gval (Fuint 3) (word_395 v))
| 396 => (Gval (Fuint 2) (word_396 v))
| 397 => (Gval (Fuint 2) (word_397 v))
| 398 => (Gval (Fuint 4) (word_398 v))
| 399 => (Gval (Fuint 7) (word_399 v))
| 400 => (Gval (Fuint 14) (word_400 v))
| 401 => (Gval (Fuint 16) (word_401 v))
| 402 => (Gval (Fuint 17) (word_402 v))
| 403 => (Gval (Fuint 16) (word_403 v))
| 404 => (Gval (Fsint 8) (word_404 v))
| 405 => (Gval (Fsint 8) (word_405 v))
| 406 => (Gval (Fsint 16) (word_406 v))
| 407 => (Gval (Fuint 16) (word_407 v))
| 408 => (Gval (Fuint 16) (word_408 v))
| 409 => (Gval (Fuint 16) (word_409 v))
| 410 => (Gval (Fuint 1) (word_410 v))
| 411 => (Gval (Fuint 1) (word_411 v))
| 412 => (Gval (Fuint 1) (word_412 v))
| 413 => (Gval (Fuint 1) (word_413 v))
| 414 => (Gval (Fuint 1) (word_414 v))
| 415 => (Gval (Fuint 1) (word_415 v))
| 416 => (Gval (Fuint 16) (word_416 v))
| 417 => (Gval (Fuint 1) (word_417 v))
| 418 => (Gval (Fuint 1) (word_418 v))
| 419 => (Gval (Fuint 1) (word_419 v))
| 420 => (Gval (Fuint 1) (word_420 v))
| 421 => (Gval (Fuint 1) (word_421 v))
| 422 => (Gval (Fuint 1) (word_422 v))
| 423 => (Gval (Fuint 1) (word_423 v))
| _ => Needtobedefined (Gtyp (Fuint 0)) end.
Definition stable_env v := stable_shape (stable_values v).
Transparent word_37.
Lemma closed_word_37_value v : eval_hfexpr expr_word_37 (closed_word_37 v) (closed_word_37 v) = Some (Gval (Fuint 1) (word_37 v)).
Proof. unfold word_37, closed_word_37, expr_word_37, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_37.
Lemma node_word_37_value v : eval_hfexpr expr_word_37 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_37 v)).
Proof. change (eval_hfexpr expr_word_37 (closed_word_37 v) (closed_word_37 v) = Some (Gval (Fuint 1) (word_37 v))). apply closed_word_37_value. Qed.
Transparent word_38.
Lemma closed_word_38_value v : eval_hfexpr expr_word_38 (closed_word_38 v) (closed_word_38 v) = Some (Gval (Fuint 9) (word_38 v)).
Proof. unfold word_38, closed_word_38, expr_word_38, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_38.
Lemma node_word_38_value v : eval_hfexpr expr_word_38 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_38 v)).
Proof. change (eval_hfexpr expr_word_38 (closed_word_38 v) (closed_word_38 v) = Some (Gval (Fuint 9) (word_38 v))). apply closed_word_38_value. Qed.
Transparent word_39.
Lemma closed_word_39_value v : eval_hfexpr expr_word_39 (closed_word_39 v) (closed_word_39 v) = Some (Gval (Fuint 9) (word_39 v)).
Proof. unfold word_39, closed_word_39, expr_word_39, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_39.
Lemma node_word_39_value v : eval_hfexpr expr_word_39 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_39 v)).
Proof. change (eval_hfexpr expr_word_39 (closed_word_39 v) (closed_word_39 v) = Some (Gval (Fuint 9) (word_39 v))). apply closed_word_39_value. Qed.
Transparent word_40.
Lemma closed_word_40_value v : eval_hfexpr expr_word_40 (closed_word_40 v) (closed_word_40 v) = Some (Gval (Fuint 10) (word_40 v)).
Proof. unfold word_40, closed_word_40, expr_word_40, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_40.
Lemma node_word_40_value v : eval_hfexpr expr_word_40 (stable_env v) (stable_env v) = Some (Gval (Fuint 10) (word_40 v)).
Proof. change (eval_hfexpr expr_word_40 (closed_word_40 v) (closed_word_40 v) = Some (Gval (Fuint 10) (word_40 v))). apply closed_word_40_value. Qed.
Transparent word_41.
Lemma closed_word_41_value v : eval_hfexpr expr_word_41 (closed_word_41 v) (closed_word_41 v) = Some (Gval (Fuint 9) (word_41 v)).
Proof. unfold word_41, closed_word_41, expr_word_41, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_41.
Lemma node_word_41_value v : eval_hfexpr expr_word_41 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_41 v)).
Proof. change (eval_hfexpr expr_word_41 (closed_word_41 v) (closed_word_41 v) = Some (Gval (Fuint 9) (word_41 v))). apply closed_word_41_value. Qed.
Transparent word_42.
Lemma closed_word_42_value v : eval_hfexpr expr_word_42 (closed_word_42 v) (closed_word_42 v) = Some (Gval (Fuint 9) (word_42 v)).
Proof. unfold word_42, closed_word_42, expr_word_42, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_42.
Lemma node_word_42_value v : eval_hfexpr expr_word_42 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_42 v)).
Proof. change (eval_hfexpr expr_word_42 (closed_word_42 v) (closed_word_42 v) = Some (Gval (Fuint 9) (word_42 v))). apply closed_word_42_value. Qed.
Transparent word_43.
Lemma closed_word_43_value v : eval_hfexpr expr_word_43 (closed_word_43 v) (closed_word_43 v) = Some (Gval (Fuint 10) (word_43 v)).
Proof. unfold word_43, closed_word_43, expr_word_43, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_43.
Lemma node_word_43_value v : eval_hfexpr expr_word_43 (stable_env v) (stable_env v) = Some (Gval (Fuint 10) (word_43 v)).
Proof. change (eval_hfexpr expr_word_43 (closed_word_43 v) (closed_word_43 v) = Some (Gval (Fuint 10) (word_43 v))). apply closed_word_43_value. Qed.
Transparent word_44.
Lemma closed_word_44_value v : eval_hfexpr expr_word_44 (closed_word_44 v) (closed_word_44 v) = Some (Gval (Fuint 2) (word_44 v)).
Proof. unfold word_44, closed_word_44, expr_word_44, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_44.
Lemma node_word_44_value v : eval_hfexpr expr_word_44 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_44 v)).
Proof. change (eval_hfexpr expr_word_44 (closed_word_44 v) (closed_word_44 v) = Some (Gval (Fuint 2) (word_44 v))). apply closed_word_44_value. Qed.
Transparent word_45.
Lemma closed_word_45_value v : eval_hfexpr expr_word_45 (closed_word_45 v) (closed_word_45 v) = Some (Gval (Fuint 3) (word_45 v)).
Proof. unfold word_45, closed_word_45, expr_word_45, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_45.
Lemma node_word_45_value v : eval_hfexpr expr_word_45 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_45 v)).
Proof. change (eval_hfexpr expr_word_45 (closed_word_45 v) (closed_word_45 v) = Some (Gval (Fuint 3) (word_45 v))). apply closed_word_45_value. Qed.
Transparent word_46.
Lemma closed_word_46_value v : eval_hfexpr expr_word_46 (closed_word_46 v) (closed_word_46 v) = Some (Gval (Fuint 1) (word_46 v)).
Proof. unfold word_46, closed_word_46, expr_word_46, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_46.
Lemma node_word_46_value v : eval_hfexpr expr_word_46 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_46 v)).
Proof. change (eval_hfexpr expr_word_46 (closed_word_46 v) (closed_word_46 v) = Some (Gval (Fuint 1) (word_46 v))). apply closed_word_46_value. Qed.
Transparent word_47.
Lemma closed_word_47_value v : eval_hfexpr expr_word_47 (closed_word_47 v) (closed_word_47 v) = Some (Gval (Fuint 9) (word_47 v)).
Proof. unfold word_47, closed_word_47, expr_word_47, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_47.
Lemma node_word_47_value v : eval_hfexpr expr_word_47 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_47 v)).
Proof. change (eval_hfexpr expr_word_47 (closed_word_47 v) (closed_word_47 v) = Some (Gval (Fuint 9) (word_47 v))). apply closed_word_47_value. Qed.
Transparent word_48.
Lemma closed_word_48_value v : eval_hfexpr expr_word_48 (closed_word_48 v) (closed_word_48 v) = Some (Gval (Fuint 1) (word_48 v)).
Proof. unfold word_48, closed_word_48, expr_word_48, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_48.
Lemma node_word_48_value v : eval_hfexpr expr_word_48 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_48 v)).
Proof. change (eval_hfexpr expr_word_48 (closed_word_48 v) (closed_word_48 v) = Some (Gval (Fuint 1) (word_48 v))). apply closed_word_48_value. Qed.
Transparent word_49.
Lemma closed_word_49_value v : eval_hfexpr expr_word_49 (closed_word_49 v) (closed_word_49 v) = Some (Gval (Fuint 9) (word_49 v)).
Proof. unfold word_49, closed_word_49, expr_word_49, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_49.
Lemma node_word_49_value v : eval_hfexpr expr_word_49 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_49 v)).
Proof. change (eval_hfexpr expr_word_49 (closed_word_49 v) (closed_word_49 v) = Some (Gval (Fuint 9) (word_49 v))). apply closed_word_49_value. Qed.
Transparent word_50.
Lemma closed_word_50_value v : eval_hfexpr expr_word_50 (closed_word_50 v) (closed_word_50 v) = Some (Gval (Fuint 1) (word_50 v)).
Proof. unfold word_50, closed_word_50, expr_word_50, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_50.
Lemma node_word_50_value v : eval_hfexpr expr_word_50 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_50 v)).
Proof. change (eval_hfexpr expr_word_50 (closed_word_50 v) (closed_word_50 v) = Some (Gval (Fuint 1) (word_50 v))). apply closed_word_50_value. Qed.
Transparent word_51.
Lemma closed_word_51_value v : eval_hfexpr expr_word_51 (closed_word_51 v) (closed_word_51 v) = Some (Gval (Fuint 9) (word_51 v)).
Proof. unfold word_51, closed_word_51, expr_word_51, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_51.
Lemma node_word_51_value v : eval_hfexpr expr_word_51 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_51 v)).
Proof. change (eval_hfexpr expr_word_51 (closed_word_51 v) (closed_word_51 v) = Some (Gval (Fuint 9) (word_51 v))). apply closed_word_51_value. Qed.
Transparent word_52.
Lemma closed_word_52_value v : eval_hfexpr expr_word_52 (closed_word_52 v) (closed_word_52 v) = Some (Gval (Fuint 9) (word_52 v)).
Proof. unfold word_52, closed_word_52, expr_word_52, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_52.
Lemma node_word_52_value v : eval_hfexpr expr_word_52 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_52 v)).
Proof. change (eval_hfexpr expr_word_52 (closed_word_52 v) (closed_word_52 v) = Some (Gval (Fuint 9) (word_52 v))). apply closed_word_52_value. Qed.
Transparent word_53.
Lemma closed_word_53_value v : eval_hfexpr expr_word_53 (closed_word_53 v) (closed_word_53 v) = Some (Gval (Fuint 1) (word_53 v)).
Proof. unfold word_53, closed_word_53, expr_word_53, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_53.
Lemma node_word_53_value v : eval_hfexpr expr_word_53 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_53 v)).
Proof. change (eval_hfexpr expr_word_53 (closed_word_53 v) (closed_word_53 v) = Some (Gval (Fuint 1) (word_53 v))). apply closed_word_53_value. Qed.
Transparent word_54.
Lemma closed_word_54_value v : eval_hfexpr expr_word_54 (closed_word_54 v) (closed_word_54 v) = Some (Gval (Fuint 9) (word_54 v)).
Proof. unfold word_54, closed_word_54, expr_word_54, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_54.
Lemma node_word_54_value v : eval_hfexpr expr_word_54 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_54 v)).
Proof. change (eval_hfexpr expr_word_54 (closed_word_54 v) (closed_word_54 v) = Some (Gval (Fuint 9) (word_54 v))). apply closed_word_54_value. Qed.
Transparent word_55.
Lemma closed_word_55_value v : eval_hfexpr expr_word_55 (closed_word_55 v) (closed_word_55 v) = Some (Gval (Fuint 9) (word_55 v)).
Proof. unfold word_55, closed_word_55, expr_word_55, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_55.
Lemma node_word_55_value v : eval_hfexpr expr_word_55 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_55 v)).
Proof. change (eval_hfexpr expr_word_55 (closed_word_55 v) (closed_word_55 v) = Some (Gval (Fuint 9) (word_55 v))). apply closed_word_55_value. Qed.
Transparent word_56.
Lemma closed_word_56_value v : eval_hfexpr expr_word_56 (closed_word_56 v) (closed_word_56 v) = Some (Gval (Fuint 1) (word_56 v)).
Proof. unfold word_56, closed_word_56, expr_word_56, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_56.
Lemma node_word_56_value v : eval_hfexpr expr_word_56 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_56 v)).
Proof. change (eval_hfexpr expr_word_56 (closed_word_56 v) (closed_word_56 v) = Some (Gval (Fuint 1) (word_56 v))). apply closed_word_56_value. Qed.
Transparent word_57.
Lemma closed_word_57_value v : eval_hfexpr expr_word_57 (closed_word_57 v) (closed_word_57 v) = Some (Gval (Fuint 9) (word_57 v)).
Proof. unfold word_57, closed_word_57, expr_word_57, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_57.
Lemma node_word_57_value v : eval_hfexpr expr_word_57 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_57 v)).
Proof. change (eval_hfexpr expr_word_57 (closed_word_57 v) (closed_word_57 v) = Some (Gval (Fuint 9) (word_57 v))). apply closed_word_57_value. Qed.
Transparent word_58.
Lemma closed_word_58_value v : eval_hfexpr expr_word_58 (closed_word_58 v) (closed_word_58 v) = Some (Gval (Fuint 1) (word_58 v)).
Proof. unfold word_58, closed_word_58, expr_word_58, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_58.
Lemma node_word_58_value v : eval_hfexpr expr_word_58 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_58 v)).
Proof. change (eval_hfexpr expr_word_58 (closed_word_58 v) (closed_word_58 v) = Some (Gval (Fuint 1) (word_58 v))). apply closed_word_58_value. Qed.
Transparent word_59.
Lemma closed_word_59_value v : eval_hfexpr expr_word_59 (closed_word_59 v) (closed_word_59 v) = Some (Gval (Fuint 9) (word_59 v)).
Proof. unfold word_59, closed_word_59, expr_word_59, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_59.
Lemma node_word_59_value v : eval_hfexpr expr_word_59 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_59 v)).
Proof. change (eval_hfexpr expr_word_59 (closed_word_59 v) (closed_word_59 v) = Some (Gval (Fuint 9) (word_59 v))). apply closed_word_59_value. Qed.
Transparent word_60.
Lemma closed_word_60_value v : eval_hfexpr expr_word_60 (closed_word_60 v) (closed_word_60 v) = Some (Gval (Fuint 1) (word_60 v)).
Proof. unfold word_60, closed_word_60, expr_word_60, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_60.
Lemma node_word_60_value v : eval_hfexpr expr_word_60 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_60 v)).
Proof. change (eval_hfexpr expr_word_60 (closed_word_60 v) (closed_word_60 v) = Some (Gval (Fuint 1) (word_60 v))). apply closed_word_60_value. Qed.
Transparent word_61.
Lemma closed_word_61_value v : eval_hfexpr expr_word_61 (closed_word_61 v) (closed_word_61 v) = Some (Gval (Fuint 3) (word_61 v)).
Proof. unfold word_61, closed_word_61, expr_word_61, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_61.
Lemma node_word_61_value v : eval_hfexpr expr_word_61 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_61 v)).
Proof. change (eval_hfexpr expr_word_61 (closed_word_61 v) (closed_word_61 v) = Some (Gval (Fuint 3) (word_61 v))). apply closed_word_61_value. Qed.
Transparent word_62.
Lemma closed_word_62_value v : eval_hfexpr expr_word_62 (closed_word_62 v) (closed_word_62 v) = Some (Gval (Fuint 1) (word_62 v)).
Proof. unfold word_62, closed_word_62, expr_word_62, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_62.
Lemma node_word_62_value v : eval_hfexpr expr_word_62 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_62 v)).
Proof. change (eval_hfexpr expr_word_62 (closed_word_62 v) (closed_word_62 v) = Some (Gval (Fuint 1) (word_62 v))). apply closed_word_62_value. Qed.
Transparent word_63.
Lemma closed_word_63_value v : eval_hfexpr expr_word_63 (closed_word_63 v) (closed_word_63 v) = Some (Gval (Fuint 2) (word_63 v)).
Proof. unfold word_63, closed_word_63, expr_word_63, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_63.
Lemma node_word_63_value v : eval_hfexpr expr_word_63 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_63 v)).
Proof. change (eval_hfexpr expr_word_63 (closed_word_63 v) (closed_word_63 v) = Some (Gval (Fuint 2) (word_63 v))). apply closed_word_63_value. Qed.
Transparent word_64.
Lemma closed_word_64_value v : eval_hfexpr expr_word_64 (closed_word_64 v) (closed_word_64 v) = Some (Gval (Fuint 1) (word_64 v)).
Proof. unfold word_64, closed_word_64, expr_word_64, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_64.
Lemma node_word_64_value v : eval_hfexpr expr_word_64 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_64 v)).
Proof. change (eval_hfexpr expr_word_64 (closed_word_64 v) (closed_word_64 v) = Some (Gval (Fuint 1) (word_64 v))). apply closed_word_64_value. Qed.
Transparent word_65.
Lemma closed_word_65_value v : eval_hfexpr expr_word_65 (closed_word_65 v) (closed_word_65 v) = Some (Gval (Fuint 2) (word_65 v)).
Proof. unfold word_65, closed_word_65, expr_word_65, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_65.
Lemma node_word_65_value v : eval_hfexpr expr_word_65 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_65 v)).
Proof. change (eval_hfexpr expr_word_65 (closed_word_65 v) (closed_word_65 v) = Some (Gval (Fuint 2) (word_65 v))). apply closed_word_65_value. Qed.
Transparent word_66.
Lemma closed_word_66_value v : eval_hfexpr expr_word_66 (closed_word_66 v) (closed_word_66 v) = Some (Gval (Fuint 1) (word_66 v)).
Proof. unfold word_66, closed_word_66, expr_word_66, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_66.
Lemma node_word_66_value v : eval_hfexpr expr_word_66 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_66 v)).
Proof. change (eval_hfexpr expr_word_66 (closed_word_66 v) (closed_word_66 v) = Some (Gval (Fuint 1) (word_66 v))). apply closed_word_66_value. Qed.
Transparent word_67.
Lemma closed_word_67_value v : eval_hfexpr expr_word_67 (closed_word_67 v) (closed_word_67 v) = Some (Gval (Fuint 2) (word_67 v)).
Proof. unfold word_67, closed_word_67, expr_word_67, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_67.
Lemma node_word_67_value v : eval_hfexpr expr_word_67 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_67 v)).
Proof. change (eval_hfexpr expr_word_67 (closed_word_67 v) (closed_word_67 v) = Some (Gval (Fuint 2) (word_67 v))). apply closed_word_67_value. Qed.
Transparent word_68.
Lemma closed_word_68_value v : eval_hfexpr expr_word_68 (closed_word_68 v) (closed_word_68 v) = Some (Gval (Fuint 1) (word_68 v)).
Proof. unfold word_68, closed_word_68, expr_word_68, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_68.
Lemma node_word_68_value v : eval_hfexpr expr_word_68 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_68 v)).
Proof. change (eval_hfexpr expr_word_68 (closed_word_68 v) (closed_word_68 v) = Some (Gval (Fuint 1) (word_68 v))). apply closed_word_68_value. Qed.
Transparent word_69.
Lemma closed_word_69_value v : eval_hfexpr expr_word_69 (closed_word_69 v) (closed_word_69 v) = Some (Gval (Fuint 10) (word_69 v)).
Proof. unfold word_69, closed_word_69, expr_word_69, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_69.
Lemma node_word_69_value v : eval_hfexpr expr_word_69 (stable_env v) (stable_env v) = Some (Gval (Fuint 10) (word_69 v)).
Proof. change (eval_hfexpr expr_word_69 (closed_word_69 v) (closed_word_69 v) = Some (Gval (Fuint 10) (word_69 v))). apply closed_word_69_value. Qed.
Transparent word_70.
Lemma closed_word_70_value v : eval_hfexpr expr_word_70 (closed_word_70 v) (closed_word_70 v) = Some (Gval (Fuint 2) (word_70 v)).
Proof. unfold word_70, closed_word_70, expr_word_70, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_70.
Lemma node_word_70_value v : eval_hfexpr expr_word_70 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_70 v)).
Proof. change (eval_hfexpr expr_word_70 (closed_word_70 v) (closed_word_70 v) = Some (Gval (Fuint 2) (word_70 v))). apply closed_word_70_value. Qed.
Transparent word_71.
Lemma closed_word_71_value v : eval_hfexpr expr_word_71 (closed_word_71 v) (closed_word_71 v) = Some (Gval (Fuint 12) (word_71 v)).
Proof. unfold word_71, closed_word_71, expr_word_71, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_71.
Lemma node_word_71_value v : eval_hfexpr expr_word_71 (stable_env v) (stable_env v) = Some (Gval (Fuint 12) (word_71 v)).
Proof. change (eval_hfexpr expr_word_71 (closed_word_71 v) (closed_word_71 v) = Some (Gval (Fuint 12) (word_71 v))). apply closed_word_71_value. Qed.
Transparent word_72.
Lemma closed_word_72_value v : eval_hfexpr expr_word_72 (closed_word_72 v) (closed_word_72 v) = Some (Gval (Fuint 1) (word_72 v)).
Proof. unfold word_72, closed_word_72, expr_word_72, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_72.
Lemma node_word_72_value v : eval_hfexpr expr_word_72 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_72 v)).
Proof. change (eval_hfexpr expr_word_72 (closed_word_72 v) (closed_word_72 v) = Some (Gval (Fuint 1) (word_72 v))). apply closed_word_72_value. Qed.
Transparent word_73.
Lemma closed_word_73_value v : eval_hfexpr expr_word_73 (closed_word_73 v) (closed_word_73 v) = Some (Gval (Fuint 1) (word_73 v)).
Proof. unfold word_73, closed_word_73, expr_word_73, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_73.
Lemma node_word_73_value v : eval_hfexpr expr_word_73 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_73 v)).
Proof. change (eval_hfexpr expr_word_73 (closed_word_73 v) (closed_word_73 v) = Some (Gval (Fuint 1) (word_73 v))). apply closed_word_73_value. Qed.
Transparent word_74.
Lemma closed_word_74_value v : eval_hfexpr expr_word_74 (closed_word_74 v) (closed_word_74 v) = Some (Gval (Fuint 1) (word_74 v)).
Proof. unfold word_74, closed_word_74, expr_word_74, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_74.
Lemma node_word_74_value v : eval_hfexpr expr_word_74 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_74 v)).
Proof. change (eval_hfexpr expr_word_74 (closed_word_74 v) (closed_word_74 v) = Some (Gval (Fuint 1) (word_74 v))). apply closed_word_74_value. Qed.
Transparent word_75.
Lemma closed_word_75_value v : eval_hfexpr expr_word_75 (closed_word_75 v) (closed_word_75 v) = Some (Gval (Fuint 1) (word_75 v)).
Proof. unfold word_75, closed_word_75, expr_word_75, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_75.
Lemma node_word_75_value v : eval_hfexpr expr_word_75 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_75 v)).
Proof. change (eval_hfexpr expr_word_75 (closed_word_75 v) (closed_word_75 v) = Some (Gval (Fuint 1) (word_75 v))). apply closed_word_75_value. Qed.
Transparent word_76.
Lemma closed_word_76_value v : eval_hfexpr expr_word_76 (closed_word_76 v) (closed_word_76 v) = Some (Gval (Fuint 1) (word_76 v)).
Proof. unfold word_76, closed_word_76, expr_word_76, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_76.
Lemma node_word_76_value v : eval_hfexpr expr_word_76 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_76 v)).
Proof. change (eval_hfexpr expr_word_76 (closed_word_76 v) (closed_word_76 v) = Some (Gval (Fuint 1) (word_76 v))). apply closed_word_76_value. Qed.
Transparent word_77.
Lemma closed_word_77_value v : eval_hfexpr expr_word_77 (closed_word_77 v) (closed_word_77 v) = Some (Gval (Fuint 1) (word_77 v)).
Proof. unfold word_77, closed_word_77, expr_word_77, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_77.
Lemma node_word_77_value v : eval_hfexpr expr_word_77 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_77 v)).
Proof. change (eval_hfexpr expr_word_77 (closed_word_77 v) (closed_word_77 v) = Some (Gval (Fuint 1) (word_77 v))). apply closed_word_77_value. Qed.
Transparent word_78.
Lemma closed_word_78_value v : eval_hfexpr expr_word_78 (closed_word_78 v) (closed_word_78 v) = Some (Gval (Fuint 1) (word_78 v)).
Proof. unfold word_78, closed_word_78, expr_word_78, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_78.
Lemma node_word_78_value v : eval_hfexpr expr_word_78 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_78 v)).
Proof. change (eval_hfexpr expr_word_78 (closed_word_78 v) (closed_word_78 v) = Some (Gval (Fuint 1) (word_78 v))). apply closed_word_78_value. Qed.
Transparent word_79.
Lemma closed_word_79_value v : eval_hfexpr expr_word_79 (closed_word_79 v) (closed_word_79 v) = Some (Gval (Fuint 1) (word_79 v)).
Proof. unfold word_79, closed_word_79, expr_word_79, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_79.
Lemma node_word_79_value v : eval_hfexpr expr_word_79 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_79 v)).
Proof. change (eval_hfexpr expr_word_79 (closed_word_79 v) (closed_word_79 v) = Some (Gval (Fuint 1) (word_79 v))). apply closed_word_79_value. Qed.
Transparent word_80.
Lemma closed_word_80_value v : eval_hfexpr expr_word_80 (closed_word_80 v) (closed_word_80 v) = Some (Gval (Fuint 1) (word_80 v)).
Proof. unfold word_80, closed_word_80, expr_word_80, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_80.
Lemma node_word_80_value v : eval_hfexpr expr_word_80 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_80 v)).
Proof. change (eval_hfexpr expr_word_80 (closed_word_80 v) (closed_word_80 v) = Some (Gval (Fuint 1) (word_80 v))). apply closed_word_80_value. Qed.
Transparent word_81.
Lemma closed_word_81_value v : eval_hfexpr expr_word_81 (closed_word_81 v) (closed_word_81 v) = Some (Gval (Fuint 1) (word_81 v)).
Proof. unfold word_81, closed_word_81, expr_word_81, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_81.
Lemma node_word_81_value v : eval_hfexpr expr_word_81 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_81 v)).
Proof. change (eval_hfexpr expr_word_81 (closed_word_81 v) (closed_word_81 v) = Some (Gval (Fuint 1) (word_81 v))). apply closed_word_81_value. Qed.
Transparent word_82.
Lemma closed_word_82_value v : eval_hfexpr expr_word_82 (closed_word_82 v) (closed_word_82 v) = Some (Gval (Fuint 1) (word_82 v)).
Proof. unfold word_82, closed_word_82, expr_word_82, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_82.
Lemma node_word_82_value v : eval_hfexpr expr_word_82 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_82 v)).
Proof. change (eval_hfexpr expr_word_82 (closed_word_82 v) (closed_word_82 v) = Some (Gval (Fuint 1) (word_82 v))). apply closed_word_82_value. Qed.
Transparent word_83.
Lemma closed_word_83_value v : eval_hfexpr expr_word_83 (closed_word_83 v) (closed_word_83 v) = Some (Gval (Fuint 1) (word_83 v)).
Proof. unfold word_83, closed_word_83, expr_word_83, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_83.
Lemma node_word_83_value v : eval_hfexpr expr_word_83 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_83 v)).
Proof. change (eval_hfexpr expr_word_83 (closed_word_83 v) (closed_word_83 v) = Some (Gval (Fuint 1) (word_83 v))). apply closed_word_83_value. Qed.
Transparent word_84.
Lemma closed_word_84_value v : eval_hfexpr expr_word_84 (closed_word_84 v) (closed_word_84 v) = Some (Gval (Fuint 3) (word_84 v)).
Proof. unfold word_84, closed_word_84, expr_word_84, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_84.
Lemma node_word_84_value v : eval_hfexpr expr_word_84 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_84 v)).
Proof. change (eval_hfexpr expr_word_84 (closed_word_84 v) (closed_word_84 v) = Some (Gval (Fuint 3) (word_84 v))). apply closed_word_84_value. Qed.
Transparent word_85.
Lemma closed_word_85_value v : eval_hfexpr expr_word_85 (closed_word_85 v) (closed_word_85 v) = Some (Gval (Fuint 1) (word_85 v)).
Proof. unfold word_85, closed_word_85, expr_word_85, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_85.
Lemma node_word_85_value v : eval_hfexpr expr_word_85 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_85 v)).
Proof. change (eval_hfexpr expr_word_85 (closed_word_85 v) (closed_word_85 v) = Some (Gval (Fuint 1) (word_85 v))). apply closed_word_85_value. Qed.
Transparent word_86.
Lemma closed_word_86_value v : eval_hfexpr expr_word_86 (closed_word_86 v) (closed_word_86 v) = Some (Gval (Fuint 9) (word_86 v)).
Proof. unfold word_86, closed_word_86, expr_word_86, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_86.
Lemma node_word_86_value v : eval_hfexpr expr_word_86 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_86 v)).
Proof. change (eval_hfexpr expr_word_86 (closed_word_86 v) (closed_word_86 v) = Some (Gval (Fuint 9) (word_86 v))). apply closed_word_86_value. Qed.
Transparent word_87.
Lemma closed_word_87_value v : eval_hfexpr expr_word_87 (closed_word_87 v) (closed_word_87 v) = Some (Gval (Fuint 1) (word_87 v)).
Proof. unfold word_87, closed_word_87, expr_word_87, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_87.
Lemma node_word_87_value v : eval_hfexpr expr_word_87 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_87 v)).
Proof. change (eval_hfexpr expr_word_87 (closed_word_87 v) (closed_word_87 v) = Some (Gval (Fuint 1) (word_87 v))). apply closed_word_87_value. Qed.
Transparent word_88.
Lemma closed_word_88_value v : eval_hfexpr expr_word_88 (closed_word_88 v) (closed_word_88 v) = Some (Gval (Fuint 9) (word_88 v)).
Proof. unfold word_88, closed_word_88, expr_word_88, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_88.
Lemma node_word_88_value v : eval_hfexpr expr_word_88 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_88 v)).
Proof. change (eval_hfexpr expr_word_88 (closed_word_88 v) (closed_word_88 v) = Some (Gval (Fuint 9) (word_88 v))). apply closed_word_88_value. Qed.
Transparent word_89.
Lemma closed_word_89_value v : eval_hfexpr expr_word_89 (closed_word_89 v) (closed_word_89 v) = Some (Gval (Fuint 1) (word_89 v)).
Proof. unfold word_89, closed_word_89, expr_word_89, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_89.
Lemma node_word_89_value v : eval_hfexpr expr_word_89 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_89 v)).
Proof. change (eval_hfexpr expr_word_89 (closed_word_89 v) (closed_word_89 v) = Some (Gval (Fuint 1) (word_89 v))). apply closed_word_89_value. Qed.
Transparent word_90.
Lemma closed_word_90_value v : eval_hfexpr expr_word_90 (closed_word_90 v) (closed_word_90 v) = Some (Gval (Fuint 9) (word_90 v)).
Proof. unfold word_90, closed_word_90, expr_word_90, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_90.
Lemma node_word_90_value v : eval_hfexpr expr_word_90 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_90 v)).
Proof. change (eval_hfexpr expr_word_90 (closed_word_90 v) (closed_word_90 v) = Some (Gval (Fuint 9) (word_90 v))). apply closed_word_90_value. Qed.
Transparent word_91.
Lemma closed_word_91_value v : eval_hfexpr expr_word_91 (closed_word_91 v) (closed_word_91 v) = Some (Gval (Fuint 1) (word_91 v)).
Proof. unfold word_91, closed_word_91, expr_word_91, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_91.
Lemma node_word_91_value v : eval_hfexpr expr_word_91 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_91 v)).
Proof. change (eval_hfexpr expr_word_91 (closed_word_91 v) (closed_word_91 v) = Some (Gval (Fuint 1) (word_91 v))). apply closed_word_91_value. Qed.
Transparent word_92.
Lemma closed_word_92_value v : eval_hfexpr expr_word_92 (closed_word_92 v) (closed_word_92 v) = Some (Gval (Fuint 9) (word_92 v)).
Proof. unfold word_92, closed_word_92, expr_word_92, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_92.
Lemma node_word_92_value v : eval_hfexpr expr_word_92 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_92 v)).
Proof. change (eval_hfexpr expr_word_92 (closed_word_92 v) (closed_word_92 v) = Some (Gval (Fuint 9) (word_92 v))). apply closed_word_92_value. Qed.
Transparent word_93.
Lemma closed_word_93_value v : eval_hfexpr expr_word_93 (closed_word_93 v) (closed_word_93 v) = Some (Gval (Fuint 1) (word_93 v)).
Proof. unfold word_93, closed_word_93, expr_word_93, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_93.
Lemma node_word_93_value v : eval_hfexpr expr_word_93 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_93 v)).
Proof. change (eval_hfexpr expr_word_93 (closed_word_93 v) (closed_word_93 v) = Some (Gval (Fuint 1) (word_93 v))). apply closed_word_93_value. Qed.
Transparent word_94.
Lemma closed_word_94_value v : eval_hfexpr expr_word_94 (closed_word_94 v) (closed_word_94 v) = Some (Gval (Fuint 9) (word_94 v)).
Proof. unfold word_94, closed_word_94, expr_word_94, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_94.
Lemma node_word_94_value v : eval_hfexpr expr_word_94 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_94 v)).
Proof. change (eval_hfexpr expr_word_94 (closed_word_94 v) (closed_word_94 v) = Some (Gval (Fuint 9) (word_94 v))). apply closed_word_94_value. Qed.
Transparent word_95.
Lemma closed_word_95_value v : eval_hfexpr expr_word_95 (closed_word_95 v) (closed_word_95 v) = Some (Gval (Fuint 1) (word_95 v)).
Proof. unfold word_95, closed_word_95, expr_word_95, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_95.
Lemma node_word_95_value v : eval_hfexpr expr_word_95 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_95 v)).
Proof. change (eval_hfexpr expr_word_95 (closed_word_95 v) (closed_word_95 v) = Some (Gval (Fuint 1) (word_95 v))). apply closed_word_95_value. Qed.
Transparent word_96.
Lemma closed_word_96_value v : eval_hfexpr expr_word_96 (closed_word_96 v) (closed_word_96 v) = Some (Gval (Fuint 9) (word_96 v)).
Proof. unfold word_96, closed_word_96, expr_word_96, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_96.
Lemma node_word_96_value v : eval_hfexpr expr_word_96 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_96 v)).
Proof. change (eval_hfexpr expr_word_96 (closed_word_96 v) (closed_word_96 v) = Some (Gval (Fuint 9) (word_96 v))). apply closed_word_96_value. Qed.
Transparent word_97.
Lemma closed_word_97_value v : eval_hfexpr expr_word_97 (closed_word_97 v) (closed_word_97 v) = Some (Gval (Fuint 1) (word_97 v)).
Proof. unfold word_97, closed_word_97, expr_word_97, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_97.
Lemma node_word_97_value v : eval_hfexpr expr_word_97 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_97 v)).
Proof. change (eval_hfexpr expr_word_97 (closed_word_97 v) (closed_word_97 v) = Some (Gval (Fuint 1) (word_97 v))). apply closed_word_97_value. Qed.
Transparent word_98.
Lemma closed_word_98_value v : eval_hfexpr expr_word_98 (closed_word_98 v) (closed_word_98 v) = Some (Gval (Fuint 1) (word_98 v)).
Proof. unfold word_98, closed_word_98, expr_word_98, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_98.
Lemma node_word_98_value v : eval_hfexpr expr_word_98 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_98 v)).
Proof. change (eval_hfexpr expr_word_98 (closed_word_98 v) (closed_word_98 v) = Some (Gval (Fuint 1) (word_98 v))). apply closed_word_98_value. Qed.
Transparent word_99.
Lemma closed_word_99_value v : eval_hfexpr expr_word_99 (closed_word_99 v) (closed_word_99 v) = Some (Gval (Fuint 2) (word_99 v)).
Proof. unfold word_99, closed_word_99, expr_word_99, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_99.
Lemma node_word_99_value v : eval_hfexpr expr_word_99 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_99 v)).
Proof. change (eval_hfexpr expr_word_99 (closed_word_99 v) (closed_word_99 v) = Some (Gval (Fuint 2) (word_99 v))). apply closed_word_99_value. Qed.
Transparent word_100.
Lemma closed_word_100_value v : eval_hfexpr expr_word_100 (closed_word_100 v) (closed_word_100 v) = Some (Gval (Fuint 1) (word_100 v)).
Proof. unfold word_100, closed_word_100, expr_word_100, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_100.
Lemma node_word_100_value v : eval_hfexpr expr_word_100 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_100 v)).
Proof. change (eval_hfexpr expr_word_100 (closed_word_100 v) (closed_word_100 v) = Some (Gval (Fuint 1) (word_100 v))). apply closed_word_100_value. Qed.
Transparent word_101.
Lemma closed_word_101_value v : eval_hfexpr expr_word_101 (closed_word_101 v) (closed_word_101 v) = Some (Gval (Fuint 2) (word_101 v)).
Proof. unfold word_101, closed_word_101, expr_word_101, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_101.
Lemma node_word_101_value v : eval_hfexpr expr_word_101 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_101 v)).
Proof. change (eval_hfexpr expr_word_101 (closed_word_101 v) (closed_word_101 v) = Some (Gval (Fuint 2) (word_101 v))). apply closed_word_101_value. Qed.
Transparent word_102.
Lemma closed_word_102_value v : eval_hfexpr expr_word_102 (closed_word_102 v) (closed_word_102 v) = Some (Gval (Fuint 1) (word_102 v)).
Proof. unfold word_102, closed_word_102, expr_word_102, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_102.
Lemma node_word_102_value v : eval_hfexpr expr_word_102 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_102 v)).
Proof. change (eval_hfexpr expr_word_102 (closed_word_102 v) (closed_word_102 v) = Some (Gval (Fuint 1) (word_102 v))). apply closed_word_102_value. Qed.
Transparent word_103.
Lemma closed_word_103_value v : eval_hfexpr expr_word_103 (closed_word_103 v) (closed_word_103 v) = Some (Gval (Fuint 2) (word_103 v)).
Proof. unfold word_103, closed_word_103, expr_word_103, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_103.
Lemma node_word_103_value v : eval_hfexpr expr_word_103 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_103 v)).
Proof. change (eval_hfexpr expr_word_103 (closed_word_103 v) (closed_word_103 v) = Some (Gval (Fuint 2) (word_103 v))). apply closed_word_103_value. Qed.
Transparent word_104.
Lemma closed_word_104_value v : eval_hfexpr expr_word_104 (closed_word_104 v) (closed_word_104 v) = Some (Gval (Fuint 1) (word_104 v)).
Proof. unfold word_104, closed_word_104, expr_word_104, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_104.
Lemma node_word_104_value v : eval_hfexpr expr_word_104 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_104 v)).
Proof. change (eval_hfexpr expr_word_104 (closed_word_104 v) (closed_word_104 v) = Some (Gval (Fuint 1) (word_104 v))). apply closed_word_104_value. Qed.
Transparent word_105.
Lemma closed_word_105_value v : eval_hfexpr expr_word_105 (closed_word_105 v) (closed_word_105 v) = Some (Gval (Fuint 11) (word_105 v)).
Proof. unfold word_105, closed_word_105, expr_word_105, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_105.
Lemma node_word_105_value v : eval_hfexpr expr_word_105 (stable_env v) (stable_env v) = Some (Gval (Fuint 11) (word_105 v)).
Proof. change (eval_hfexpr expr_word_105 (closed_word_105 v) (closed_word_105 v) = Some (Gval (Fuint 11) (word_105 v))). apply closed_word_105_value. Qed.
Transparent word_106.
Lemma closed_word_106_value v : eval_hfexpr expr_word_106 (closed_word_106 v) (closed_word_106 v) = Some (Gval (Fuint 2) (word_106 v)).
Proof. unfold word_106, closed_word_106, expr_word_106, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_106.
Lemma node_word_106_value v : eval_hfexpr expr_word_106 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_106 v)).
Proof. change (eval_hfexpr expr_word_106 (closed_word_106 v) (closed_word_106 v) = Some (Gval (Fuint 2) (word_106 v))). apply closed_word_106_value. Qed.
Transparent word_107.
Lemma closed_word_107_value v : eval_hfexpr expr_word_107 (closed_word_107 v) (closed_word_107 v) = Some (Gval (Fuint 13) (word_107 v)).
Proof. unfold word_107, closed_word_107, expr_word_107, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_107.
Lemma node_word_107_value v : eval_hfexpr expr_word_107 (stable_env v) (stable_env v) = Some (Gval (Fuint 13) (word_107 v)).
Proof. change (eval_hfexpr expr_word_107 (closed_word_107 v) (closed_word_107 v) = Some (Gval (Fuint 13) (word_107 v))). apply closed_word_107_value. Qed.
Transparent word_108.
Lemma closed_word_108_value v : eval_hfexpr expr_word_108 (closed_word_108 v) (closed_word_108 v) = Some (Gval (Fuint 1) (word_108 v)).
Proof. unfold word_108, closed_word_108, expr_word_108, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_108.
Lemma node_word_108_value v : eval_hfexpr expr_word_108 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_108 v)).
Proof. change (eval_hfexpr expr_word_108 (closed_word_108 v) (closed_word_108 v) = Some (Gval (Fuint 1) (word_108 v))). apply closed_word_108_value. Qed.
Transparent word_109.
Lemma closed_word_109_value v : eval_hfexpr expr_word_109 (closed_word_109 v) (closed_word_109 v) = Some (Gval (Fuint 1) (word_109 v)).
Proof. unfold word_109, closed_word_109, expr_word_109, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_109.
Lemma node_word_109_value v : eval_hfexpr expr_word_109 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_109 v)).
Proof. change (eval_hfexpr expr_word_109 (closed_word_109 v) (closed_word_109 v) = Some (Gval (Fuint 1) (word_109 v))). apply closed_word_109_value. Qed.
Transparent word_110.
Lemma closed_word_110_value v : eval_hfexpr expr_word_110 (closed_word_110 v) (closed_word_110 v) = Some (Gval (Fuint 1) (word_110 v)).
Proof. unfold word_110, closed_word_110, expr_word_110, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_110.
Lemma node_word_110_value v : eval_hfexpr expr_word_110 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_110 v)).
Proof. change (eval_hfexpr expr_word_110 (closed_word_110 v) (closed_word_110 v) = Some (Gval (Fuint 1) (word_110 v))). apply closed_word_110_value. Qed.
Transparent word_111.
Lemma closed_word_111_value v : eval_hfexpr expr_word_111 (closed_word_111 v) (closed_word_111 v) = Some (Gval (Fuint 1) (word_111 v)).
Proof. unfold word_111, closed_word_111, expr_word_111, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_111.
Lemma node_word_111_value v : eval_hfexpr expr_word_111 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_111 v)).
Proof. change (eval_hfexpr expr_word_111 (closed_word_111 v) (closed_word_111 v) = Some (Gval (Fuint 1) (word_111 v))). apply closed_word_111_value. Qed.
Transparent word_112.
Lemma closed_word_112_value v : eval_hfexpr expr_word_112 (closed_word_112 v) (closed_word_112 v) = Some (Gval (Fuint 1) (word_112 v)).
Proof. unfold word_112, closed_word_112, expr_word_112, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_112.
Lemma node_word_112_value v : eval_hfexpr expr_word_112 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_112 v)).
Proof. change (eval_hfexpr expr_word_112 (closed_word_112 v) (closed_word_112 v) = Some (Gval (Fuint 1) (word_112 v))). apply closed_word_112_value. Qed.
Transparent word_113.
Lemma closed_word_113_value v : eval_hfexpr expr_word_113 (closed_word_113 v) (closed_word_113 v) = Some (Gval (Fuint 1) (word_113 v)).
Proof. unfold word_113, closed_word_113, expr_word_113, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_113.
Lemma node_word_113_value v : eval_hfexpr expr_word_113 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_113 v)).
Proof. change (eval_hfexpr expr_word_113 (closed_word_113 v) (closed_word_113 v) = Some (Gval (Fuint 1) (word_113 v))). apply closed_word_113_value. Qed.
Transparent word_114.
Lemma closed_word_114_value v : eval_hfexpr expr_word_114 (closed_word_114 v) (closed_word_114 v) = Some (Gval (Fuint 1) (word_114 v)).
Proof. unfold word_114, closed_word_114, expr_word_114, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_114.
Lemma node_word_114_value v : eval_hfexpr expr_word_114 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_114 v)).
Proof. change (eval_hfexpr expr_word_114 (closed_word_114 v) (closed_word_114 v) = Some (Gval (Fuint 1) (word_114 v))). apply closed_word_114_value. Qed.
Transparent word_115.
Lemma closed_word_115_value v : eval_hfexpr expr_word_115 (closed_word_115 v) (closed_word_115 v) = Some (Gval (Fuint 1) (word_115 v)).
Proof. unfold word_115, closed_word_115, expr_word_115, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_115.
Lemma node_word_115_value v : eval_hfexpr expr_word_115 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_115 v)).
Proof. change (eval_hfexpr expr_word_115 (closed_word_115 v) (closed_word_115 v) = Some (Gval (Fuint 1) (word_115 v))). apply closed_word_115_value. Qed.
Transparent word_116.
Lemma closed_word_116_value v : eval_hfexpr expr_word_116 (closed_word_116 v) (closed_word_116 v) = Some (Gval (Fuint 1) (word_116 v)).
Proof. unfold word_116, closed_word_116, expr_word_116, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_116.
Lemma node_word_116_value v : eval_hfexpr expr_word_116 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_116 v)).
Proof. change (eval_hfexpr expr_word_116 (closed_word_116 v) (closed_word_116 v) = Some (Gval (Fuint 1) (word_116 v))). apply closed_word_116_value. Qed.
Transparent word_117.
Lemma closed_word_117_value v : eval_hfexpr expr_word_117 (closed_word_117 v) (closed_word_117 v) = Some (Gval (Fuint 1) (word_117 v)).
Proof. unfold word_117, closed_word_117, expr_word_117, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_117.
Lemma node_word_117_value v : eval_hfexpr expr_word_117 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_117 v)).
Proof. change (eval_hfexpr expr_word_117 (closed_word_117 v) (closed_word_117 v) = Some (Gval (Fuint 1) (word_117 v))). apply closed_word_117_value. Qed.
Transparent word_118.
Lemma closed_word_118_value v : eval_hfexpr expr_word_118 (closed_word_118 v) (closed_word_118 v) = Some (Gval (Fuint 1) (word_118 v)).
Proof. unfold word_118, closed_word_118, expr_word_118, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_118.
Lemma node_word_118_value v : eval_hfexpr expr_word_118 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_118 v)).
Proof. change (eval_hfexpr expr_word_118 (closed_word_118 v) (closed_word_118 v) = Some (Gval (Fuint 1) (word_118 v))). apply closed_word_118_value. Qed.
Transparent word_119.
Lemma closed_word_119_value v : eval_hfexpr expr_word_119 (closed_word_119 v) (closed_word_119 v) = Some (Gval (Fuint 1) (word_119 v)).
Proof. unfold word_119, closed_word_119, expr_word_119, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_119.
Lemma node_word_119_value v : eval_hfexpr expr_word_119 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_119 v)).
Proof. change (eval_hfexpr expr_word_119 (closed_word_119 v) (closed_word_119 v) = Some (Gval (Fuint 1) (word_119 v))). apply closed_word_119_value. Qed.
Transparent word_120.
Lemma closed_word_120_value v : eval_hfexpr expr_word_120 (closed_word_120 v) (closed_word_120 v) = Some (Gval (Fuint 1) (word_120 v)).
Proof. unfold word_120, closed_word_120, expr_word_120, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_120.
Lemma node_word_120_value v : eval_hfexpr expr_word_120 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_120 v)).
Proof. change (eval_hfexpr expr_word_120 (closed_word_120 v) (closed_word_120 v) = Some (Gval (Fuint 1) (word_120 v))). apply closed_word_120_value. Qed.
Transparent word_121.
Lemma closed_word_121_value v : eval_hfexpr expr_word_121 (closed_word_121 v) (closed_word_121 v) = Some (Gval (Fuint 3) (word_121 v)).
Proof. unfold word_121, closed_word_121, expr_word_121, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_121.
Lemma node_word_121_value v : eval_hfexpr expr_word_121 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_121 v)).
Proof. change (eval_hfexpr expr_word_121 (closed_word_121 v) (closed_word_121 v) = Some (Gval (Fuint 3) (word_121 v))). apply closed_word_121_value. Qed.
Transparent word_122.
Lemma closed_word_122_value v : eval_hfexpr expr_word_122 (closed_word_122 v) (closed_word_122 v) = Some (Gval (Fuint 1) (word_122 v)).
Proof. unfold word_122, closed_word_122, expr_word_122, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_122.
Lemma node_word_122_value v : eval_hfexpr expr_word_122 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_122 v)).
Proof. change (eval_hfexpr expr_word_122 (closed_word_122 v) (closed_word_122 v) = Some (Gval (Fuint 1) (word_122 v))). apply closed_word_122_value. Qed.
Transparent word_123.
Lemma closed_word_123_value v : eval_hfexpr expr_word_123 (closed_word_123 v) (closed_word_123 v) = Some (Gval (Fuint 9) (word_123 v)).
Proof. unfold word_123, closed_word_123, expr_word_123, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_123.
Lemma node_word_123_value v : eval_hfexpr expr_word_123 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_123 v)).
Proof. change (eval_hfexpr expr_word_123 (closed_word_123 v) (closed_word_123 v) = Some (Gval (Fuint 9) (word_123 v))). apply closed_word_123_value. Qed.
Transparent word_124.
Lemma closed_word_124_value v : eval_hfexpr expr_word_124 (closed_word_124 v) (closed_word_124 v) = Some (Gval (Fuint 1) (word_124 v)).
Proof. unfold word_124, closed_word_124, expr_word_124, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_124.
Lemma node_word_124_value v : eval_hfexpr expr_word_124 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_124 v)).
Proof. change (eval_hfexpr expr_word_124 (closed_word_124 v) (closed_word_124 v) = Some (Gval (Fuint 1) (word_124 v))). apply closed_word_124_value. Qed.
Transparent word_125.
Lemma closed_word_125_value v : eval_hfexpr expr_word_125 (closed_word_125 v) (closed_word_125 v) = Some (Gval (Fuint 9) (word_125 v)).
Proof. unfold word_125, closed_word_125, expr_word_125, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_125.
Lemma node_word_125_value v : eval_hfexpr expr_word_125 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_125 v)).
Proof. change (eval_hfexpr expr_word_125 (closed_word_125 v) (closed_word_125 v) = Some (Gval (Fuint 9) (word_125 v))). apply closed_word_125_value. Qed.
Transparent word_126.
Lemma closed_word_126_value v : eval_hfexpr expr_word_126 (closed_word_126 v) (closed_word_126 v) = Some (Gval (Fuint 1) (word_126 v)).
Proof. unfold word_126, closed_word_126, expr_word_126, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_126.
Lemma node_word_126_value v : eval_hfexpr expr_word_126 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_126 v)).
Proof. change (eval_hfexpr expr_word_126 (closed_word_126 v) (closed_word_126 v) = Some (Gval (Fuint 1) (word_126 v))). apply closed_word_126_value. Qed.
Transparent word_127.
Lemma closed_word_127_value v : eval_hfexpr expr_word_127 (closed_word_127 v) (closed_word_127 v) = Some (Gval (Fuint 9) (word_127 v)).
Proof. unfold word_127, closed_word_127, expr_word_127, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_127.
Lemma node_word_127_value v : eval_hfexpr expr_word_127 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_127 v)).
Proof. change (eval_hfexpr expr_word_127 (closed_word_127 v) (closed_word_127 v) = Some (Gval (Fuint 9) (word_127 v))). apply closed_word_127_value. Qed.
Transparent word_128.
Lemma closed_word_128_value v : eval_hfexpr expr_word_128 (closed_word_128 v) (closed_word_128 v) = Some (Gval (Fuint 1) (word_128 v)).
Proof. unfold word_128, closed_word_128, expr_word_128, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_128.
Lemma node_word_128_value v : eval_hfexpr expr_word_128 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_128 v)).
Proof. change (eval_hfexpr expr_word_128 (closed_word_128 v) (closed_word_128 v) = Some (Gval (Fuint 1) (word_128 v))). apply closed_word_128_value. Qed.
Transparent word_129.
Lemma closed_word_129_value v : eval_hfexpr expr_word_129 (closed_word_129 v) (closed_word_129 v) = Some (Gval (Fuint 9) (word_129 v)).
Proof. unfold word_129, closed_word_129, expr_word_129, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_129.
Lemma node_word_129_value v : eval_hfexpr expr_word_129 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_129 v)).
Proof. change (eval_hfexpr expr_word_129 (closed_word_129 v) (closed_word_129 v) = Some (Gval (Fuint 9) (word_129 v))). apply closed_word_129_value. Qed.
Transparent word_130.
Lemma closed_word_130_value v : eval_hfexpr expr_word_130 (closed_word_130 v) (closed_word_130 v) = Some (Gval (Fuint 1) (word_130 v)).
Proof. unfold word_130, closed_word_130, expr_word_130, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_130.
Lemma node_word_130_value v : eval_hfexpr expr_word_130 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_130 v)).
Proof. change (eval_hfexpr expr_word_130 (closed_word_130 v) (closed_word_130 v) = Some (Gval (Fuint 1) (word_130 v))). apply closed_word_130_value. Qed.
Transparent word_131.
Lemma closed_word_131_value v : eval_hfexpr expr_word_131 (closed_word_131 v) (closed_word_131 v) = Some (Gval (Fuint 9) (word_131 v)).
Proof. unfold word_131, closed_word_131, expr_word_131, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_131.
Lemma node_word_131_value v : eval_hfexpr expr_word_131 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_131 v)).
Proof. change (eval_hfexpr expr_word_131 (closed_word_131 v) (closed_word_131 v) = Some (Gval (Fuint 9) (word_131 v))). apply closed_word_131_value. Qed.
Transparent word_132.
Lemma closed_word_132_value v : eval_hfexpr expr_word_132 (closed_word_132 v) (closed_word_132 v) = Some (Gval (Fuint 1) (word_132 v)).
Proof. unfold word_132, closed_word_132, expr_word_132, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_132.
Lemma node_word_132_value v : eval_hfexpr expr_word_132 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_132 v)).
Proof. change (eval_hfexpr expr_word_132 (closed_word_132 v) (closed_word_132 v) = Some (Gval (Fuint 1) (word_132 v))). apply closed_word_132_value. Qed.
Transparent word_133.
Lemma closed_word_133_value v : eval_hfexpr expr_word_133 (closed_word_133 v) (closed_word_133 v) = Some (Gval (Fuint 9) (word_133 v)).
Proof. unfold word_133, closed_word_133, expr_word_133, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_133.
Lemma node_word_133_value v : eval_hfexpr expr_word_133 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_133 v)).
Proof. change (eval_hfexpr expr_word_133 (closed_word_133 v) (closed_word_133 v) = Some (Gval (Fuint 9) (word_133 v))). apply closed_word_133_value. Qed.
Transparent word_134.
Lemma closed_word_134_value v : eval_hfexpr expr_word_134 (closed_word_134 v) (closed_word_134 v) = Some (Gval (Fuint 1) (word_134 v)).
Proof. unfold word_134, closed_word_134, expr_word_134, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_134.
Lemma node_word_134_value v : eval_hfexpr expr_word_134 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_134 v)).
Proof. change (eval_hfexpr expr_word_134 (closed_word_134 v) (closed_word_134 v) = Some (Gval (Fuint 1) (word_134 v))). apply closed_word_134_value. Qed.
Transparent word_135.
Lemma closed_word_135_value v : eval_hfexpr expr_word_135 (closed_word_135 v) (closed_word_135 v) = Some (Gval (Fuint 1) (word_135 v)).
Proof. unfold word_135, closed_word_135, expr_word_135, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_135.
Lemma node_word_135_value v : eval_hfexpr expr_word_135 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_135 v)).
Proof. change (eval_hfexpr expr_word_135 (closed_word_135 v) (closed_word_135 v) = Some (Gval (Fuint 1) (word_135 v))). apply closed_word_135_value. Qed.
Transparent word_136.
Lemma closed_word_136_value v : eval_hfexpr expr_word_136 (closed_word_136 v) (closed_word_136 v) = Some (Gval (Fuint 2) (word_136 v)).
Proof. unfold word_136, closed_word_136, expr_word_136, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_136.
Lemma node_word_136_value v : eval_hfexpr expr_word_136 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_136 v)).
Proof. change (eval_hfexpr expr_word_136 (closed_word_136 v) (closed_word_136 v) = Some (Gval (Fuint 2) (word_136 v))). apply closed_word_136_value. Qed.
Transparent word_137.
Lemma closed_word_137_value v : eval_hfexpr expr_word_137 (closed_word_137 v) (closed_word_137 v) = Some (Gval (Fuint 1) (word_137 v)).
Proof. unfold word_137, closed_word_137, expr_word_137, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_137.
Lemma node_word_137_value v : eval_hfexpr expr_word_137 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_137 v)).
Proof. change (eval_hfexpr expr_word_137 (closed_word_137 v) (closed_word_137 v) = Some (Gval (Fuint 1) (word_137 v))). apply closed_word_137_value. Qed.
Transparent word_138.
Lemma closed_word_138_value v : eval_hfexpr expr_word_138 (closed_word_138 v) (closed_word_138 v) = Some (Gval (Fuint 2) (word_138 v)).
Proof. unfold word_138, closed_word_138, expr_word_138, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_138.
Lemma node_word_138_value v : eval_hfexpr expr_word_138 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_138 v)).
Proof. change (eval_hfexpr expr_word_138 (closed_word_138 v) (closed_word_138 v) = Some (Gval (Fuint 2) (word_138 v))). apply closed_word_138_value. Qed.
Transparent word_139.
Lemma closed_word_139_value v : eval_hfexpr expr_word_139 (closed_word_139 v) (closed_word_139 v) = Some (Gval (Fuint 1) (word_139 v)).
Proof. unfold word_139, closed_word_139, expr_word_139, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_139.
Lemma node_word_139_value v : eval_hfexpr expr_word_139 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_139 v)).
Proof. change (eval_hfexpr expr_word_139 (closed_word_139 v) (closed_word_139 v) = Some (Gval (Fuint 1) (word_139 v))). apply closed_word_139_value. Qed.
Transparent word_140.
Lemma closed_word_140_value v : eval_hfexpr expr_word_140 (closed_word_140 v) (closed_word_140 v) = Some (Gval (Fuint 2) (word_140 v)).
Proof. unfold word_140, closed_word_140, expr_word_140, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_140.
Lemma node_word_140_value v : eval_hfexpr expr_word_140 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_140 v)).
Proof. change (eval_hfexpr expr_word_140 (closed_word_140 v) (closed_word_140 v) = Some (Gval (Fuint 2) (word_140 v))). apply closed_word_140_value. Qed.
Transparent word_141.
Lemma closed_word_141_value v : eval_hfexpr expr_word_141 (closed_word_141 v) (closed_word_141 v) = Some (Gval (Fuint 1) (word_141 v)).
Proof. unfold word_141, closed_word_141, expr_word_141, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_141.
Lemma node_word_141_value v : eval_hfexpr expr_word_141 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_141 v)).
Proof. change (eval_hfexpr expr_word_141 (closed_word_141 v) (closed_word_141 v) = Some (Gval (Fuint 1) (word_141 v))). apply closed_word_141_value. Qed.
Transparent word_142.
Lemma closed_word_142_value v : eval_hfexpr expr_word_142 (closed_word_142 v) (closed_word_142 v) = Some (Gval (Fuint 11) (word_142 v)).
Proof. unfold word_142, closed_word_142, expr_word_142, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_142.
Lemma node_word_142_value v : eval_hfexpr expr_word_142 (stable_env v) (stable_env v) = Some (Gval (Fuint 11) (word_142 v)).
Proof. change (eval_hfexpr expr_word_142 (closed_word_142 v) (closed_word_142 v) = Some (Gval (Fuint 11) (word_142 v))). apply closed_word_142_value. Qed.
Transparent word_143.
Lemma closed_word_143_value v : eval_hfexpr expr_word_143 (closed_word_143 v) (closed_word_143 v) = Some (Gval (Fuint 2) (word_143 v)).
Proof. unfold word_143, closed_word_143, expr_word_143, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_143.
Lemma node_word_143_value v : eval_hfexpr expr_word_143 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_143 v)).
Proof. change (eval_hfexpr expr_word_143 (closed_word_143 v) (closed_word_143 v) = Some (Gval (Fuint 2) (word_143 v))). apply closed_word_143_value. Qed.
Transparent word_144.
Lemma closed_word_144_value v : eval_hfexpr expr_word_144 (closed_word_144 v) (closed_word_144 v) = Some (Gval (Fuint 13) (word_144 v)).
Proof. unfold word_144, closed_word_144, expr_word_144, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_144.
Lemma node_word_144_value v : eval_hfexpr expr_word_144 (stable_env v) (stable_env v) = Some (Gval (Fuint 13) (word_144 v)).
Proof. change (eval_hfexpr expr_word_144 (closed_word_144 v) (closed_word_144 v) = Some (Gval (Fuint 13) (word_144 v))). apply closed_word_144_value. Qed.
Transparent word_145.
Lemma closed_word_145_value v : eval_hfexpr expr_word_145 (closed_word_145 v) (closed_word_145 v) = Some (Gval (Fuint 1) (word_145 v)).
Proof. unfold word_145, closed_word_145, expr_word_145, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_145.
Lemma node_word_145_value v : eval_hfexpr expr_word_145 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_145 v)).
Proof. change (eval_hfexpr expr_word_145 (closed_word_145 v) (closed_word_145 v) = Some (Gval (Fuint 1) (word_145 v))). apply closed_word_145_value. Qed.
Transparent word_146.
Lemma closed_word_146_value v : eval_hfexpr expr_word_146 (closed_word_146 v) (closed_word_146 v) = Some (Gval (Fuint 1) (word_146 v)).
Proof. unfold word_146, closed_word_146, expr_word_146, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_146.
Lemma node_word_146_value v : eval_hfexpr expr_word_146 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_146 v)).
Proof. change (eval_hfexpr expr_word_146 (closed_word_146 v) (closed_word_146 v) = Some (Gval (Fuint 1) (word_146 v))). apply closed_word_146_value. Qed.
Transparent word_147.
Lemma closed_word_147_value v : eval_hfexpr expr_word_147 (closed_word_147 v) (closed_word_147 v) = Some (Gval (Fuint 1) (word_147 v)).
Proof. unfold word_147, closed_word_147, expr_word_147, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_147.
Lemma node_word_147_value v : eval_hfexpr expr_word_147 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_147 v)).
Proof. change (eval_hfexpr expr_word_147 (closed_word_147 v) (closed_word_147 v) = Some (Gval (Fuint 1) (word_147 v))). apply closed_word_147_value. Qed.
Transparent word_148.
Lemma closed_word_148_value v : eval_hfexpr expr_word_148 (closed_word_148 v) (closed_word_148 v) = Some (Gval (Fuint 1) (word_148 v)).
Proof. unfold word_148, closed_word_148, expr_word_148, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_148.
Lemma node_word_148_value v : eval_hfexpr expr_word_148 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_148 v)).
Proof. change (eval_hfexpr expr_word_148 (closed_word_148 v) (closed_word_148 v) = Some (Gval (Fuint 1) (word_148 v))). apply closed_word_148_value. Qed.
Transparent word_149.
Lemma closed_word_149_value v : eval_hfexpr expr_word_149 (closed_word_149 v) (closed_word_149 v) = Some (Gval (Fuint 1) (word_149 v)).
Proof. unfold word_149, closed_word_149, expr_word_149, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_149.
Lemma node_word_149_value v : eval_hfexpr expr_word_149 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_149 v)).
Proof. change (eval_hfexpr expr_word_149 (closed_word_149 v) (closed_word_149 v) = Some (Gval (Fuint 1) (word_149 v))). apply closed_word_149_value. Qed.
Transparent word_150.
Lemma closed_word_150_value v : eval_hfexpr expr_word_150 (closed_word_150 v) (closed_word_150 v) = Some (Gval (Fuint 1) (word_150 v)).
Proof. unfold word_150, closed_word_150, expr_word_150, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_150.
Lemma node_word_150_value v : eval_hfexpr expr_word_150 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_150 v)).
Proof. change (eval_hfexpr expr_word_150 (closed_word_150 v) (closed_word_150 v) = Some (Gval (Fuint 1) (word_150 v))). apply closed_word_150_value. Qed.
Transparent word_151.
Lemma closed_word_151_value v : eval_hfexpr expr_word_151 (closed_word_151 v) (closed_word_151 v) = Some (Gval (Fuint 1) (word_151 v)).
Proof. unfold word_151, closed_word_151, expr_word_151, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_151.
Lemma node_word_151_value v : eval_hfexpr expr_word_151 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_151 v)).
Proof. change (eval_hfexpr expr_word_151 (closed_word_151 v) (closed_word_151 v) = Some (Gval (Fuint 1) (word_151 v))). apply closed_word_151_value. Qed.
Transparent word_152.
Lemma closed_word_152_value v : eval_hfexpr expr_word_152 (closed_word_152 v) (closed_word_152 v) = Some (Gval (Fuint 1) (word_152 v)).
Proof. unfold word_152, closed_word_152, expr_word_152, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_152.
Lemma node_word_152_value v : eval_hfexpr expr_word_152 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_152 v)).
Proof. change (eval_hfexpr expr_word_152 (closed_word_152 v) (closed_word_152 v) = Some (Gval (Fuint 1) (word_152 v))). apply closed_word_152_value. Qed.
Transparent word_153.
Lemma closed_word_153_value v : eval_hfexpr expr_word_153 (closed_word_153 v) (closed_word_153 v) = Some (Gval (Fuint 1) (word_153 v)).
Proof. unfold word_153, closed_word_153, expr_word_153, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_153.
Lemma node_word_153_value v : eval_hfexpr expr_word_153 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_153 v)).
Proof. change (eval_hfexpr expr_word_153 (closed_word_153 v) (closed_word_153 v) = Some (Gval (Fuint 1) (word_153 v))). apply closed_word_153_value. Qed.
Transparent word_154.
Lemma closed_word_154_value v : eval_hfexpr expr_word_154 (closed_word_154 v) (closed_word_154 v) = Some (Gval (Fuint 1) (word_154 v)).
Proof. unfold word_154, closed_word_154, expr_word_154, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_154.
Lemma node_word_154_value v : eval_hfexpr expr_word_154 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_154 v)).
Proof. change (eval_hfexpr expr_word_154 (closed_word_154 v) (closed_word_154 v) = Some (Gval (Fuint 1) (word_154 v))). apply closed_word_154_value. Qed.
Transparent word_155.
Lemma closed_word_155_value v : eval_hfexpr expr_word_155 (closed_word_155 v) (closed_word_155 v) = Some (Gval (Fuint 1) (word_155 v)).
Proof. unfold word_155, closed_word_155, expr_word_155, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_155.
Lemma node_word_155_value v : eval_hfexpr expr_word_155 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_155 v)).
Proof. change (eval_hfexpr expr_word_155 (closed_word_155 v) (closed_word_155 v) = Some (Gval (Fuint 1) (word_155 v))). apply closed_word_155_value. Qed.
Transparent word_156.
Lemma closed_word_156_value v : eval_hfexpr expr_word_156 (closed_word_156 v) (closed_word_156 v) = Some (Gval (Fuint 1) (word_156 v)).
Proof. unfold word_156, closed_word_156, expr_word_156, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_156.
Lemma node_word_156_value v : eval_hfexpr expr_word_156 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_156 v)).
Proof. change (eval_hfexpr expr_word_156 (closed_word_156 v) (closed_word_156 v) = Some (Gval (Fuint 1) (word_156 v))). apply closed_word_156_value. Qed.
Transparent word_157.
Lemma closed_word_157_value v : eval_hfexpr expr_word_157 (closed_word_157 v) (closed_word_157 v) = Some (Gval (Fuint 1) (word_157 v)).
Proof. unfold word_157, closed_word_157, expr_word_157, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_157.
Lemma node_word_157_value v : eval_hfexpr expr_word_157 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_157 v)).
Proof. change (eval_hfexpr expr_word_157 (closed_word_157 v) (closed_word_157 v) = Some (Gval (Fuint 1) (word_157 v))). apply closed_word_157_value. Qed.
Transparent word_158.
Lemma closed_word_158_value v : eval_hfexpr expr_word_158 (closed_word_158 v) (closed_word_158 v) = Some (Gval (Fuint 3) (word_158 v)).
Proof. unfold word_158, closed_word_158, expr_word_158, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_158.
Lemma node_word_158_value v : eval_hfexpr expr_word_158 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_158 v)).
Proof. change (eval_hfexpr expr_word_158 (closed_word_158 v) (closed_word_158 v) = Some (Gval (Fuint 3) (word_158 v))). apply closed_word_158_value. Qed.
Transparent word_159.
Lemma closed_word_159_value v : eval_hfexpr expr_word_159 (closed_word_159 v) (closed_word_159 v) = Some (Gval (Fuint 1) (word_159 v)).
Proof. unfold word_159, closed_word_159, expr_word_159, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_159.
Lemma node_word_159_value v : eval_hfexpr expr_word_159 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_159 v)).
Proof. change (eval_hfexpr expr_word_159 (closed_word_159 v) (closed_word_159 v) = Some (Gval (Fuint 1) (word_159 v))). apply closed_word_159_value. Qed.
Transparent word_160.
Lemma closed_word_160_value v : eval_hfexpr expr_word_160 (closed_word_160 v) (closed_word_160 v) = Some (Gval (Fuint 9) (word_160 v)).
Proof. unfold word_160, closed_word_160, expr_word_160, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_160.
Lemma node_word_160_value v : eval_hfexpr expr_word_160 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_160 v)).
Proof. change (eval_hfexpr expr_word_160 (closed_word_160 v) (closed_word_160 v) = Some (Gval (Fuint 9) (word_160 v))). apply closed_word_160_value. Qed.
Transparent word_161.
Lemma closed_word_161_value v : eval_hfexpr expr_word_161 (closed_word_161 v) (closed_word_161 v) = Some (Gval (Fuint 1) (word_161 v)).
Proof. unfold word_161, closed_word_161, expr_word_161, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_161.
Lemma node_word_161_value v : eval_hfexpr expr_word_161 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_161 v)).
Proof. change (eval_hfexpr expr_word_161 (closed_word_161 v) (closed_word_161 v) = Some (Gval (Fuint 1) (word_161 v))). apply closed_word_161_value. Qed.
Transparent word_162.
Lemma closed_word_162_value v : eval_hfexpr expr_word_162 (closed_word_162 v) (closed_word_162 v) = Some (Gval (Fuint 9) (word_162 v)).
Proof. unfold word_162, closed_word_162, expr_word_162, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_162.
Lemma node_word_162_value v : eval_hfexpr expr_word_162 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_162 v)).
Proof. change (eval_hfexpr expr_word_162 (closed_word_162 v) (closed_word_162 v) = Some (Gval (Fuint 9) (word_162 v))). apply closed_word_162_value. Qed.
Transparent word_163.
Lemma closed_word_163_value v : eval_hfexpr expr_word_163 (closed_word_163 v) (closed_word_163 v) = Some (Gval (Fuint 1) (word_163 v)).
Proof. unfold word_163, closed_word_163, expr_word_163, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_163.
Lemma node_word_163_value v : eval_hfexpr expr_word_163 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_163 v)).
Proof. change (eval_hfexpr expr_word_163 (closed_word_163 v) (closed_word_163 v) = Some (Gval (Fuint 1) (word_163 v))). apply closed_word_163_value. Qed.
Transparent word_164.
Lemma closed_word_164_value v : eval_hfexpr expr_word_164 (closed_word_164 v) (closed_word_164 v) = Some (Gval (Fuint 9) (word_164 v)).
Proof. unfold word_164, closed_word_164, expr_word_164, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_164.
Lemma node_word_164_value v : eval_hfexpr expr_word_164 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_164 v)).
Proof. change (eval_hfexpr expr_word_164 (closed_word_164 v) (closed_word_164 v) = Some (Gval (Fuint 9) (word_164 v))). apply closed_word_164_value. Qed.
Transparent word_165.
Lemma closed_word_165_value v : eval_hfexpr expr_word_165 (closed_word_165 v) (closed_word_165 v) = Some (Gval (Fuint 1) (word_165 v)).
Proof. unfold word_165, closed_word_165, expr_word_165, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_165.
Lemma node_word_165_value v : eval_hfexpr expr_word_165 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_165 v)).
Proof. change (eval_hfexpr expr_word_165 (closed_word_165 v) (closed_word_165 v) = Some (Gval (Fuint 1) (word_165 v))). apply closed_word_165_value. Qed.
Transparent word_166.
Lemma closed_word_166_value v : eval_hfexpr expr_word_166 (closed_word_166 v) (closed_word_166 v) = Some (Gval (Fuint 9) (word_166 v)).
Proof. unfold word_166, closed_word_166, expr_word_166, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_166.
Lemma node_word_166_value v : eval_hfexpr expr_word_166 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_166 v)).
Proof. change (eval_hfexpr expr_word_166 (closed_word_166 v) (closed_word_166 v) = Some (Gval (Fuint 9) (word_166 v))). apply closed_word_166_value. Qed.
Transparent word_167.
Lemma closed_word_167_value v : eval_hfexpr expr_word_167 (closed_word_167 v) (closed_word_167 v) = Some (Gval (Fuint 1) (word_167 v)).
Proof. unfold word_167, closed_word_167, expr_word_167, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_167.
Lemma node_word_167_value v : eval_hfexpr expr_word_167 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_167 v)).
Proof. change (eval_hfexpr expr_word_167 (closed_word_167 v) (closed_word_167 v) = Some (Gval (Fuint 1) (word_167 v))). apply closed_word_167_value. Qed.
Transparent word_168.
Lemma closed_word_168_value v : eval_hfexpr expr_word_168 (closed_word_168 v) (closed_word_168 v) = Some (Gval (Fuint 9) (word_168 v)).
Proof. unfold word_168, closed_word_168, expr_word_168, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_168.
Lemma node_word_168_value v : eval_hfexpr expr_word_168 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_168 v)).
Proof. change (eval_hfexpr expr_word_168 (closed_word_168 v) (closed_word_168 v) = Some (Gval (Fuint 9) (word_168 v))). apply closed_word_168_value. Qed.
Transparent word_169.
Lemma closed_word_169_value v : eval_hfexpr expr_word_169 (closed_word_169 v) (closed_word_169 v) = Some (Gval (Fuint 1) (word_169 v)).
Proof. unfold word_169, closed_word_169, expr_word_169, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_169.
Lemma node_word_169_value v : eval_hfexpr expr_word_169 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_169 v)).
Proof. change (eval_hfexpr expr_word_169 (closed_word_169 v) (closed_word_169 v) = Some (Gval (Fuint 1) (word_169 v))). apply closed_word_169_value. Qed.
Transparent word_170.
Lemma closed_word_170_value v : eval_hfexpr expr_word_170 (closed_word_170 v) (closed_word_170 v) = Some (Gval (Fuint 9) (word_170 v)).
Proof. unfold word_170, closed_word_170, expr_word_170, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_170.
Lemma node_word_170_value v : eval_hfexpr expr_word_170 (stable_env v) (stable_env v) = Some (Gval (Fuint 9) (word_170 v)).
Proof. change (eval_hfexpr expr_word_170 (closed_word_170 v) (closed_word_170 v) = Some (Gval (Fuint 9) (word_170 v))). apply closed_word_170_value. Qed.
Transparent word_171.
Lemma closed_word_171_value v : eval_hfexpr expr_word_171 (closed_word_171 v) (closed_word_171 v) = Some (Gval (Fuint 1) (word_171 v)).
Proof. unfold word_171, closed_word_171, expr_word_171, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_171.
Lemma node_word_171_value v : eval_hfexpr expr_word_171 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_171 v)).
Proof. change (eval_hfexpr expr_word_171 (closed_word_171 v) (closed_word_171 v) = Some (Gval (Fuint 1) (word_171 v))). apply closed_word_171_value. Qed.
Transparent word_172.
Lemma closed_word_172_value v : eval_hfexpr expr_word_172 (closed_word_172 v) (closed_word_172 v) = Some (Gval (Fuint 1) (word_172 v)).
Proof. unfold word_172, closed_word_172, expr_word_172, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_172.
Lemma node_word_172_value v : eval_hfexpr expr_word_172 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_172 v)).
Proof. change (eval_hfexpr expr_word_172 (closed_word_172 v) (closed_word_172 v) = Some (Gval (Fuint 1) (word_172 v))). apply closed_word_172_value. Qed.
Transparent word_173.
Lemma closed_word_173_value v : eval_hfexpr expr_word_173 (closed_word_173 v) (closed_word_173 v) = Some (Gval (Fuint 2) (word_173 v)).
Proof. unfold word_173, closed_word_173, expr_word_173, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_173.
Lemma node_word_173_value v : eval_hfexpr expr_word_173 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_173 v)).
Proof. change (eval_hfexpr expr_word_173 (closed_word_173 v) (closed_word_173 v) = Some (Gval (Fuint 2) (word_173 v))). apply closed_word_173_value. Qed.
Transparent word_174.
Lemma closed_word_174_value v : eval_hfexpr expr_word_174 (closed_word_174 v) (closed_word_174 v) = Some (Gval (Fuint 1) (word_174 v)).
Proof. unfold word_174, closed_word_174, expr_word_174, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_174.
Lemma node_word_174_value v : eval_hfexpr expr_word_174 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_174 v)).
Proof. change (eval_hfexpr expr_word_174 (closed_word_174 v) (closed_word_174 v) = Some (Gval (Fuint 1) (word_174 v))). apply closed_word_174_value. Qed.
Transparent word_175.
Lemma closed_word_175_value v : eval_hfexpr expr_word_175 (closed_word_175 v) (closed_word_175 v) = Some (Gval (Fuint 2) (word_175 v)).
Proof. unfold word_175, closed_word_175, expr_word_175, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_175.
Lemma node_word_175_value v : eval_hfexpr expr_word_175 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_175 v)).
Proof. change (eval_hfexpr expr_word_175 (closed_word_175 v) (closed_word_175 v) = Some (Gval (Fuint 2) (word_175 v))). apply closed_word_175_value. Qed.
Transparent word_176.
Lemma closed_word_176_value v : eval_hfexpr expr_word_176 (closed_word_176 v) (closed_word_176 v) = Some (Gval (Fuint 1) (word_176 v)).
Proof. unfold word_176, closed_word_176, expr_word_176, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_176.
Lemma node_word_176_value v : eval_hfexpr expr_word_176 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_176 v)).
Proof. change (eval_hfexpr expr_word_176 (closed_word_176 v) (closed_word_176 v) = Some (Gval (Fuint 1) (word_176 v))). apply closed_word_176_value. Qed.
Transparent word_177.
Lemma closed_word_177_value v : eval_hfexpr expr_word_177 (closed_word_177 v) (closed_word_177 v) = Some (Gval (Fuint 2) (word_177 v)).
Proof. unfold word_177, closed_word_177, expr_word_177, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_177.
Lemma node_word_177_value v : eval_hfexpr expr_word_177 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_177 v)).
Proof. change (eval_hfexpr expr_word_177 (closed_word_177 v) (closed_word_177 v) = Some (Gval (Fuint 2) (word_177 v))). apply closed_word_177_value. Qed.
Transparent word_178.
Lemma closed_word_178_value v : eval_hfexpr expr_word_178 (closed_word_178 v) (closed_word_178 v) = Some (Gval (Fuint 1) (word_178 v)).
Proof. unfold word_178, closed_word_178, expr_word_178, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_178.
Lemma node_word_178_value v : eval_hfexpr expr_word_178 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_178 v)).
Proof. change (eval_hfexpr expr_word_178 (closed_word_178 v) (closed_word_178 v) = Some (Gval (Fuint 1) (word_178 v))). apply closed_word_178_value. Qed.
Transparent word_179.
Lemma closed_word_179_value v : eval_hfexpr expr_word_179 (closed_word_179 v) (closed_word_179 v) = Some (Gval (Fuint 10) (word_179 v)).
Proof. unfold word_179, closed_word_179, expr_word_179, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_179.
Lemma node_word_179_value v : eval_hfexpr expr_word_179 (stable_env v) (stable_env v) = Some (Gval (Fuint 10) (word_179 v)).
Proof. change (eval_hfexpr expr_word_179 (closed_word_179 v) (closed_word_179 v) = Some (Gval (Fuint 10) (word_179 v))). apply closed_word_179_value. Qed.
Transparent word_180.
Lemma closed_word_180_value v : eval_hfexpr expr_word_180 (closed_word_180 v) (closed_word_180 v) = Some (Gval (Fuint 12) (word_180 v)).
Proof. unfold word_180, closed_word_180, expr_word_180, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_180.
Lemma node_word_180_value v : eval_hfexpr expr_word_180 (stable_env v) (stable_env v) = Some (Gval (Fuint 12) (word_180 v)).
Proof. change (eval_hfexpr expr_word_180 (closed_word_180 v) (closed_word_180 v) = Some (Gval (Fuint 12) (word_180 v))). apply closed_word_180_value. Qed.
Transparent word_181.
Lemma closed_word_181_value v : eval_hfexpr expr_word_181 (closed_word_181 v) (closed_word_181 v) = Some (Gval (Fuint 1) (word_181 v)).
Proof. unfold word_181, closed_word_181, expr_word_181, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_181.
Lemma node_word_181_value v : eval_hfexpr expr_word_181 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_181 v)).
Proof. change (eval_hfexpr expr_word_181 (closed_word_181 v) (closed_word_181 v) = Some (Gval (Fuint 1) (word_181 v))). apply closed_word_181_value. Qed.
Transparent word_182.
Lemma closed_word_182_value v : eval_hfexpr expr_word_182 (closed_word_182 v) (closed_word_182 v) = Some (Gval (Fuint 1) (word_182 v)).
Proof. unfold word_182, closed_word_182, expr_word_182, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_182.
Lemma node_word_182_value v : eval_hfexpr expr_word_182 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_182 v)).
Proof. change (eval_hfexpr expr_word_182 (closed_word_182 v) (closed_word_182 v) = Some (Gval (Fuint 1) (word_182 v))). apply closed_word_182_value. Qed.
Transparent word_183.
Lemma closed_word_183_value v : eval_hfexpr expr_word_183 (closed_word_183 v) (closed_word_183 v) = Some (Gval (Fuint 1) (word_183 v)).
Proof. unfold word_183, closed_word_183, expr_word_183, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_183.
Lemma node_word_183_value v : eval_hfexpr expr_word_183 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_183 v)).
Proof. change (eval_hfexpr expr_word_183 (closed_word_183 v) (closed_word_183 v) = Some (Gval (Fuint 1) (word_183 v))). apply closed_word_183_value. Qed.
Transparent word_184.
Lemma closed_word_184_value v : eval_hfexpr expr_word_184 (closed_word_184 v) (closed_word_184 v) = Some (Gval (Fuint 1) (word_184 v)).
Proof. unfold word_184, closed_word_184, expr_word_184, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_184.
Lemma node_word_184_value v : eval_hfexpr expr_word_184 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_184 v)).
Proof. change (eval_hfexpr expr_word_184 (closed_word_184 v) (closed_word_184 v) = Some (Gval (Fuint 1) (word_184 v))). apply closed_word_184_value. Qed.
Transparent word_185.
Lemma closed_word_185_value v : eval_hfexpr expr_word_185 (closed_word_185 v) (closed_word_185 v) = Some (Gval (Fuint 1) (word_185 v)).
Proof. unfold word_185, closed_word_185, expr_word_185, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_185.
Lemma node_word_185_value v : eval_hfexpr expr_word_185 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_185 v)).
Proof. change (eval_hfexpr expr_word_185 (closed_word_185 v) (closed_word_185 v) = Some (Gval (Fuint 1) (word_185 v))). apply closed_word_185_value. Qed.
Transparent word_186.
Lemma closed_word_186_value v : eval_hfexpr expr_word_186 (closed_word_186 v) (closed_word_186 v) = Some (Gval (Fuint 1) (word_186 v)).
Proof. unfold word_186, closed_word_186, expr_word_186, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_186.
Lemma node_word_186_value v : eval_hfexpr expr_word_186 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_186 v)).
Proof. change (eval_hfexpr expr_word_186 (closed_word_186 v) (closed_word_186 v) = Some (Gval (Fuint 1) (word_186 v))). apply closed_word_186_value. Qed.
Transparent word_187.
Lemma closed_word_187_value v : eval_hfexpr expr_word_187 (closed_word_187 v) (closed_word_187 v) = Some (Gval (Fuint 1) (word_187 v)).
Proof. unfold word_187, closed_word_187, expr_word_187, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_187.
Lemma node_word_187_value v : eval_hfexpr expr_word_187 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_187 v)).
Proof. change (eval_hfexpr expr_word_187 (closed_word_187 v) (closed_word_187 v) = Some (Gval (Fuint 1) (word_187 v))). apply closed_word_187_value. Qed.
Transparent word_188.
Lemma closed_word_188_value v : eval_hfexpr expr_word_188 (closed_word_188 v) (closed_word_188 v) = Some (Gval (Fuint 1) (word_188 v)).
Proof. unfold word_188, closed_word_188, expr_word_188, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_188.
Lemma node_word_188_value v : eval_hfexpr expr_word_188 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_188 v)).
Proof. change (eval_hfexpr expr_word_188 (closed_word_188 v) (closed_word_188 v) = Some (Gval (Fuint 1) (word_188 v))). apply closed_word_188_value. Qed.
Transparent word_189.
Lemma closed_word_189_value v : eval_hfexpr expr_word_189 (closed_word_189 v) (closed_word_189 v) = Some (Gval (Fuint 1) (word_189 v)).
Proof. unfold word_189, closed_word_189, expr_word_189, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_189.
Lemma node_word_189_value v : eval_hfexpr expr_word_189 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_189 v)).
Proof. change (eval_hfexpr expr_word_189 (closed_word_189 v) (closed_word_189 v) = Some (Gval (Fuint 1) (word_189 v))). apply closed_word_189_value. Qed.
Transparent word_190.
Lemma closed_word_190_value v : eval_hfexpr expr_word_190 (closed_word_190 v) (closed_word_190 v) = Some (Gval (Fuint 1) (word_190 v)).
Proof. unfold word_190, closed_word_190, expr_word_190, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_190.
Lemma node_word_190_value v : eval_hfexpr expr_word_190 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_190 v)).
Proof. change (eval_hfexpr expr_word_190 (closed_word_190 v) (closed_word_190 v) = Some (Gval (Fuint 1) (word_190 v))). apply closed_word_190_value. Qed.
Transparent word_191.
Lemma closed_word_191_value v : eval_hfexpr expr_word_191 (closed_word_191 v) (closed_word_191 v) = Some (Gval (Fuint 1) (word_191 v)).
Proof. unfold word_191, closed_word_191, expr_word_191, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_191.
Lemma node_word_191_value v : eval_hfexpr expr_word_191 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_191 v)).
Proof. change (eval_hfexpr expr_word_191 (closed_word_191 v) (closed_word_191 v) = Some (Gval (Fuint 1) (word_191 v))). apply closed_word_191_value. Qed.
Transparent word_192.
Lemma closed_word_192_value v : eval_hfexpr expr_word_192 (closed_word_192 v) (closed_word_192 v) = Some (Gval (Fuint 1) (word_192 v)).
Proof. unfold word_192, closed_word_192, expr_word_192, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_192.
Lemma node_word_192_value v : eval_hfexpr expr_word_192 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_192 v)).
Proof. change (eval_hfexpr expr_word_192 (closed_word_192 v) (closed_word_192 v) = Some (Gval (Fuint 1) (word_192 v))). apply closed_word_192_value. Qed.
Transparent word_193.
Lemma closed_word_193_value v : eval_hfexpr expr_word_193 (closed_word_193 v) (closed_word_193 v) = Some (Gval (Fuint 1) (word_193 v)).
Proof. unfold word_193, closed_word_193, expr_word_193, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_193.
Lemma node_word_193_value v : eval_hfexpr expr_word_193 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_193 v)).
Proof. change (eval_hfexpr expr_word_193 (closed_word_193 v) (closed_word_193 v) = Some (Gval (Fuint 1) (word_193 v))). apply closed_word_193_value. Qed.
Transparent word_194.
Lemma closed_word_194_value v : eval_hfexpr expr_word_194 (closed_word_194 v) (closed_word_194 v) = Some (Gval (Fuint 2) (word_194 v)).
Proof. unfold word_194, closed_word_194, expr_word_194, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_194.
Lemma node_word_194_value v : eval_hfexpr expr_word_194 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_194 v)).
Proof. change (eval_hfexpr expr_word_194 (closed_word_194 v) (closed_word_194 v) = Some (Gval (Fuint 2) (word_194 v))). apply closed_word_194_value. Qed.
Transparent word_195.
Lemma closed_word_195_value v : eval_hfexpr expr_word_195 (closed_word_195 v) (closed_word_195 v) = Some (Gval (Fuint 1) (word_195 v)).
Proof. unfold word_195, closed_word_195, expr_word_195, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_195.
Lemma node_word_195_value v : eval_hfexpr expr_word_195 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_195 v)).
Proof. change (eval_hfexpr expr_word_195 (closed_word_195 v) (closed_word_195 v) = Some (Gval (Fuint 1) (word_195 v))). apply closed_word_195_value. Qed.
Transparent word_196.
Lemma closed_word_196_value v : eval_hfexpr expr_word_196 (closed_word_196 v) (closed_word_196 v) = Some (Gval (Fuint 2) (word_196 v)).
Proof. unfold word_196, closed_word_196, expr_word_196, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_196.
Lemma node_word_196_value v : eval_hfexpr expr_word_196 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_196 v)).
Proof. change (eval_hfexpr expr_word_196 (closed_word_196 v) (closed_word_196 v) = Some (Gval (Fuint 2) (word_196 v))). apply closed_word_196_value. Qed.
Transparent word_197.
Lemma closed_word_197_value v : eval_hfexpr expr_word_197 (closed_word_197 v) (closed_word_197 v) = Some (Gval (Fuint 1) (word_197 v)).
Proof. unfold word_197, closed_word_197, expr_word_197, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_197.
Lemma node_word_197_value v : eval_hfexpr expr_word_197 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_197 v)).
Proof. change (eval_hfexpr expr_word_197 (closed_word_197 v) (closed_word_197 v) = Some (Gval (Fuint 1) (word_197 v))). apply closed_word_197_value. Qed.
Transparent word_198.
Lemma closed_word_198_value v : eval_hfexpr expr_word_198 (closed_word_198 v) (closed_word_198 v) = Some (Gval (Fuint 2) (word_198 v)).
Proof. unfold word_198, closed_word_198, expr_word_198, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_198.
Lemma node_word_198_value v : eval_hfexpr expr_word_198 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_198 v)).
Proof. change (eval_hfexpr expr_word_198 (closed_word_198 v) (closed_word_198 v) = Some (Gval (Fuint 2) (word_198 v))). apply closed_word_198_value. Qed.
Transparent word_199.
Lemma closed_word_199_value v : eval_hfexpr expr_word_199 (closed_word_199 v) (closed_word_199 v) = Some (Gval (Fuint 1) (word_199 v)).
Proof. unfold word_199, closed_word_199, expr_word_199, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_199.
Lemma node_word_199_value v : eval_hfexpr expr_word_199 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_199 v)).
Proof. change (eval_hfexpr expr_word_199 (closed_word_199 v) (closed_word_199 v) = Some (Gval (Fuint 1) (word_199 v))). apply closed_word_199_value. Qed.
Transparent word_200.
Lemma closed_word_200_value v : eval_hfexpr expr_word_200 (closed_word_200 v) (closed_word_200 v) = Some (Gval (Fuint 1) (word_200 v)).
Proof. unfold word_200, closed_word_200, expr_word_200, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_200.
Lemma node_word_200_value v : eval_hfexpr expr_word_200 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_200 v)).
Proof. change (eval_hfexpr expr_word_200 (closed_word_200 v) (closed_word_200 v) = Some (Gval (Fuint 1) (word_200 v))). apply closed_word_200_value. Qed.
Transparent word_202.
Lemma closed_word_202_value v : eval_hfexpr expr_word_202 (closed_word_202 v) (closed_word_202 v) = Some (Gval (Fuint 1) (word_202 v)).
Proof. unfold word_202, closed_word_202, expr_word_202, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_202.
Lemma node_word_202_value v : eval_hfexpr expr_word_202 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_202 v)).
Proof. change (eval_hfexpr expr_word_202 (closed_word_202 v) (closed_word_202 v) = Some (Gval (Fuint 1) (word_202 v))). apply closed_word_202_value. Qed.
Transparent word_204.
Lemma closed_word_204_value v : eval_hfexpr expr_word_204 (closed_word_204 v) (closed_word_204 v) = Some (Gval (Fuint 1) (word_204 v)).
Proof. unfold word_204, closed_word_204, expr_word_204, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_204.
Lemma node_word_204_value v : eval_hfexpr expr_word_204 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_204 v)).
Proof. change (eval_hfexpr expr_word_204 (closed_word_204 v) (closed_word_204 v) = Some (Gval (Fuint 1) (word_204 v))). apply closed_word_204_value. Qed.
Transparent word_206.
Lemma closed_word_206_value v : eval_hfexpr expr_word_206 (closed_word_206 v) (closed_word_206 v) = Some (Gval (Fuint 1) (word_206 v)).
Proof. unfold word_206, closed_word_206, expr_word_206, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_206.
Lemma node_word_206_value v : eval_hfexpr expr_word_206 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_206 v)).
Proof. change (eval_hfexpr expr_word_206 (closed_word_206 v) (closed_word_206 v) = Some (Gval (Fuint 1) (word_206 v))). apply closed_word_206_value. Qed.
Transparent word_208.
Lemma closed_word_208_value v : eval_hfexpr expr_word_208 (closed_word_208 v) (closed_word_208 v) = Some (Gval (Fuint 1) (word_208 v)).
Proof. unfold word_208, closed_word_208, expr_word_208, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_208.
Lemma node_word_208_value v : eval_hfexpr expr_word_208 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_208 v)).
Proof. change (eval_hfexpr expr_word_208 (closed_word_208 v) (closed_word_208 v) = Some (Gval (Fuint 1) (word_208 v))). apply closed_word_208_value. Qed.
Transparent word_210.
Lemma closed_word_210_value v : eval_hfexpr expr_word_210 (closed_word_210 v) (closed_word_210 v) = Some (Gval (Fuint 1) (word_210 v)).
Proof. unfold word_210, closed_word_210, expr_word_210, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_210.
Lemma node_word_210_value v : eval_hfexpr expr_word_210 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_210 v)).
Proof. change (eval_hfexpr expr_word_210 (closed_word_210 v) (closed_word_210 v) = Some (Gval (Fuint 1) (word_210 v))). apply closed_word_210_value. Qed.
Transparent word_212.
Lemma closed_word_212_value v : eval_hfexpr expr_word_212 (closed_word_212 v) (closed_word_212 v) = Some (Gval (Fuint 1) (word_212 v)).
Proof. unfold word_212, closed_word_212, expr_word_212, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_212.
Lemma node_word_212_value v : eval_hfexpr expr_word_212 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_212 v)).
Proof. change (eval_hfexpr expr_word_212 (closed_word_212 v) (closed_word_212 v) = Some (Gval (Fuint 1) (word_212 v))). apply closed_word_212_value. Qed.
Transparent word_214.
Lemma closed_word_214_value v : eval_hfexpr expr_word_214 (closed_word_214 v) (closed_word_214 v) = Some (Gval (Fuint 1) (word_214 v)).
Proof. unfold word_214, closed_word_214, expr_word_214, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_214.
Lemma node_word_214_value v : eval_hfexpr expr_word_214 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_214 v)).
Proof. change (eval_hfexpr expr_word_214 (closed_word_214 v) (closed_word_214 v) = Some (Gval (Fuint 1) (word_214 v))). apply closed_word_214_value. Qed.
Transparent word_216.
Lemma closed_word_216_value v : eval_hfexpr expr_word_216 (closed_word_216 v) (closed_word_216 v) = Some (Gval (Fuint 1) (word_216 v)).
Proof. unfold word_216, closed_word_216, expr_word_216, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_216.
Lemma node_word_216_value v : eval_hfexpr expr_word_216 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_216 v)).
Proof. change (eval_hfexpr expr_word_216 (closed_word_216 v) (closed_word_216 v) = Some (Gval (Fuint 1) (word_216 v))). apply closed_word_216_value. Qed.
Transparent word_218.
Lemma closed_word_218_value v : eval_hfexpr expr_word_218 (closed_word_218 v) (closed_word_218 v) = Some (Gval (Fuint 1) (word_218 v)).
Proof. unfold word_218, closed_word_218, expr_word_218, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_218.
Lemma node_word_218_value v : eval_hfexpr expr_word_218 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_218 v)).
Proof. change (eval_hfexpr expr_word_218 (closed_word_218 v) (closed_word_218 v) = Some (Gval (Fuint 1) (word_218 v))). apply closed_word_218_value. Qed.
Transparent word_220.
Lemma closed_word_220_value v : eval_hfexpr expr_word_220 (closed_word_220 v) (closed_word_220 v) = Some (Gval (Fuint 1) (word_220 v)).
Proof. unfold word_220, closed_word_220, expr_word_220, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_220.
Lemma node_word_220_value v : eval_hfexpr expr_word_220 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_220 v)).
Proof. change (eval_hfexpr expr_word_220 (closed_word_220 v) (closed_word_220 v) = Some (Gval (Fuint 1) (word_220 v))). apply closed_word_220_value. Qed.
Transparent word_222.
Lemma closed_word_222_value v : eval_hfexpr expr_word_222 (closed_word_222 v) (closed_word_222 v) = Some (Gval (Fuint 1) (word_222 v)).
Proof. unfold word_222, closed_word_222, expr_word_222, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_222.
Lemma node_word_222_value v : eval_hfexpr expr_word_222 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_222 v)).
Proof. change (eval_hfexpr expr_word_222 (closed_word_222 v) (closed_word_222 v) = Some (Gval (Fuint 1) (word_222 v))). apply closed_word_222_value. Qed.
Transparent word_224.
Lemma closed_word_224_value v : eval_hfexpr expr_word_224 (closed_word_224 v) (closed_word_224 v) = Some (Gval (Fuint 1) (word_224 v)).
Proof. unfold word_224, closed_word_224, expr_word_224, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_224.
Lemma node_word_224_value v : eval_hfexpr expr_word_224 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_224 v)).
Proof. change (eval_hfexpr expr_word_224 (closed_word_224 v) (closed_word_224 v) = Some (Gval (Fuint 1) (word_224 v))). apply closed_word_224_value. Qed.
Transparent word_226.
Lemma closed_word_226_value v : eval_hfexpr expr_word_226 (closed_word_226 v) (closed_word_226 v) = Some (Gval (Fuint 1) (word_226 v)).
Proof. unfold word_226, closed_word_226, expr_word_226, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_226.
Lemma node_word_226_value v : eval_hfexpr expr_word_226 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_226 v)).
Proof. change (eval_hfexpr expr_word_226 (closed_word_226 v) (closed_word_226 v) = Some (Gval (Fuint 1) (word_226 v))). apply closed_word_226_value. Qed.
Transparent word_228.
Lemma closed_word_228_value v : eval_hfexpr expr_word_228 (closed_word_228 v) (closed_word_228 v) = Some (Gval (Fuint 1) (word_228 v)).
Proof. unfold word_228, closed_word_228, expr_word_228, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_228.
Lemma node_word_228_value v : eval_hfexpr expr_word_228 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_228 v)).
Proof. change (eval_hfexpr expr_word_228 (closed_word_228 v) (closed_word_228 v) = Some (Gval (Fuint 1) (word_228 v))). apply closed_word_228_value. Qed.
Transparent word_230.
Lemma closed_word_230_value v : eval_hfexpr expr_word_230 (closed_word_230 v) (closed_word_230 v) = Some (Gval (Fuint 1) (word_230 v)).
Proof. unfold word_230, closed_word_230, expr_word_230, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_230.
Lemma node_word_230_value v : eval_hfexpr expr_word_230 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_230 v)).
Proof. change (eval_hfexpr expr_word_230 (closed_word_230 v) (closed_word_230 v) = Some (Gval (Fuint 1) (word_230 v))). apply closed_word_230_value. Qed.
Transparent word_232.
Lemma closed_word_232_value v : eval_hfexpr expr_word_232 (closed_word_232 v) (closed_word_232 v) = Some (Gval (Fuint 1) (word_232 v)).
Proof. unfold word_232, closed_word_232, expr_word_232, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_232.
Lemma node_word_232_value v : eval_hfexpr expr_word_232 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_232 v)).
Proof. change (eval_hfexpr expr_word_232 (closed_word_232 v) (closed_word_232 v) = Some (Gval (Fuint 1) (word_232 v))). apply closed_word_232_value. Qed.
Transparent word_234.
Lemma closed_word_234_value v : eval_hfexpr expr_word_234 (closed_word_234 v) (closed_word_234 v) = Some (Gval (Fuint 1) (word_234 v)).
Proof. unfold word_234, closed_word_234, expr_word_234, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_234.
Lemma node_word_234_value v : eval_hfexpr expr_word_234 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_234 v)).
Proof. change (eval_hfexpr expr_word_234 (closed_word_234 v) (closed_word_234 v) = Some (Gval (Fuint 1) (word_234 v))). apply closed_word_234_value. Qed.
Transparent word_236.
Lemma closed_word_236_value v : eval_hfexpr expr_word_236 (closed_word_236 v) (closed_word_236 v) = Some (Gval (Fuint 1) (word_236 v)).
Proof. unfold word_236, closed_word_236, expr_word_236, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_236.
Lemma node_word_236_value v : eval_hfexpr expr_word_236 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_236 v)).
Proof. change (eval_hfexpr expr_word_236 (closed_word_236 v) (closed_word_236 v) = Some (Gval (Fuint 1) (word_236 v))). apply closed_word_236_value. Qed.
Transparent word_238.
Lemma closed_word_238_value v : eval_hfexpr expr_word_238 (closed_word_238 v) (closed_word_238 v) = Some (Gval (Fuint 1) (word_238 v)).
Proof. unfold word_238, closed_word_238, expr_word_238, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_238.
Lemma node_word_238_value v : eval_hfexpr expr_word_238 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_238 v)).
Proof. change (eval_hfexpr expr_word_238 (closed_word_238 v) (closed_word_238 v) = Some (Gval (Fuint 1) (word_238 v))). apply closed_word_238_value. Qed.
Transparent word_240.
Lemma closed_word_240_value v : eval_hfexpr expr_word_240 (closed_word_240 v) (closed_word_240 v) = Some (Gval (Fuint 1) (word_240 v)).
Proof. unfold word_240, closed_word_240, expr_word_240, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_240.
Lemma node_word_240_value v : eval_hfexpr expr_word_240 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_240 v)).
Proof. change (eval_hfexpr expr_word_240 (closed_word_240 v) (closed_word_240 v) = Some (Gval (Fuint 1) (word_240 v))). apply closed_word_240_value. Qed.
Transparent word_242.
Lemma closed_word_242_value v : eval_hfexpr expr_word_242 (closed_word_242 v) (closed_word_242 v) = Some (Gval (Fuint 1) (word_242 v)).
Proof. unfold word_242, closed_word_242, expr_word_242, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_242.
Lemma node_word_242_value v : eval_hfexpr expr_word_242 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_242 v)).
Proof. change (eval_hfexpr expr_word_242 (closed_word_242 v) (closed_word_242 v) = Some (Gval (Fuint 1) (word_242 v))). apply closed_word_242_value. Qed.
Transparent word_244.
Lemma closed_word_244_value v : eval_hfexpr expr_word_244 (closed_word_244 v) (closed_word_244 v) = Some (Gval (Fuint 1) (word_244 v)).
Proof. unfold word_244, closed_word_244, expr_word_244, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_244.
Lemma node_word_244_value v : eval_hfexpr expr_word_244 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_244 v)).
Proof. change (eval_hfexpr expr_word_244 (closed_word_244 v) (closed_word_244 v) = Some (Gval (Fuint 1) (word_244 v))). apply closed_word_244_value. Qed.
Transparent word_246.
Lemma closed_word_246_value v : eval_hfexpr expr_word_246 (closed_word_246 v) (closed_word_246 v) = Some (Gval (Fuint 1) (word_246 v)).
Proof. unfold word_246, closed_word_246, expr_word_246, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_246.
Lemma node_word_246_value v : eval_hfexpr expr_word_246 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_246 v)).
Proof. change (eval_hfexpr expr_word_246 (closed_word_246 v) (closed_word_246 v) = Some (Gval (Fuint 1) (word_246 v))). apply closed_word_246_value. Qed.
Transparent word_248.
Lemma closed_word_248_value v : eval_hfexpr expr_word_248 (closed_word_248 v) (closed_word_248 v) = Some (Gval (Fuint 1) (word_248 v)).
Proof. unfold word_248, closed_word_248, expr_word_248, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_248.
Lemma node_word_248_value v : eval_hfexpr expr_word_248 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_248 v)).
Proof. change (eval_hfexpr expr_word_248 (closed_word_248 v) (closed_word_248 v) = Some (Gval (Fuint 1) (word_248 v))). apply closed_word_248_value. Qed.
Transparent word_250.
Lemma closed_word_250_value v : eval_hfexpr expr_word_250 (closed_word_250 v) (closed_word_250 v) = Some (Gval (Fuint 1) (word_250 v)).
Proof. unfold word_250, closed_word_250, expr_word_250, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_250.
Lemma node_word_250_value v : eval_hfexpr expr_word_250 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_250 v)).
Proof. change (eval_hfexpr expr_word_250 (closed_word_250 v) (closed_word_250 v) = Some (Gval (Fuint 1) (word_250 v))). apply closed_word_250_value. Qed.
Transparent word_252.
Lemma closed_word_252_value v : eval_hfexpr expr_word_252 (closed_word_252 v) (closed_word_252 v) = Some (Gval (Fuint 1) (word_252 v)).
Proof. unfold word_252, closed_word_252, expr_word_252, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_252.
Lemma node_word_252_value v : eval_hfexpr expr_word_252 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_252 v)).
Proof. change (eval_hfexpr expr_word_252 (closed_word_252 v) (closed_word_252 v) = Some (Gval (Fuint 1) (word_252 v))). apply closed_word_252_value. Qed.
Transparent word_254.
Lemma closed_word_254_value v : eval_hfexpr expr_word_254 (closed_word_254 v) (closed_word_254 v) = Some (Gval (Fuint 1) (word_254 v)).
Proof. unfold word_254, closed_word_254, expr_word_254, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_254.
Lemma node_word_254_value v : eval_hfexpr expr_word_254 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_254 v)).
Proof. change (eval_hfexpr expr_word_254 (closed_word_254 v) (closed_word_254 v) = Some (Gval (Fuint 1) (word_254 v))). apply closed_word_254_value. Qed.
Transparent word_256.
Lemma closed_word_256_value v : eval_hfexpr expr_word_256 (closed_word_256 v) (closed_word_256 v) = Some (Gval (Fuint 1) (word_256 v)).
Proof. unfold word_256, closed_word_256, expr_word_256, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_256.
Lemma node_word_256_value v : eval_hfexpr expr_word_256 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_256 v)).
Proof. change (eval_hfexpr expr_word_256 (closed_word_256 v) (closed_word_256 v) = Some (Gval (Fuint 1) (word_256 v))). apply closed_word_256_value. Qed.
Transparent word_258.
Lemma closed_word_258_value v : eval_hfexpr expr_word_258 (closed_word_258 v) (closed_word_258 v) = Some (Gval (Fuint 1) (word_258 v)).
Proof. unfold word_258, closed_word_258, expr_word_258, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_258.
Lemma node_word_258_value v : eval_hfexpr expr_word_258 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_258 v)).
Proof. change (eval_hfexpr expr_word_258 (closed_word_258 v) (closed_word_258 v) = Some (Gval (Fuint 1) (word_258 v))). apply closed_word_258_value. Qed.
Transparent word_260.
Lemma closed_word_260_value v : eval_hfexpr expr_word_260 (closed_word_260 v) (closed_word_260 v) = Some (Gval (Fuint 1) (word_260 v)).
Proof. unfold word_260, closed_word_260, expr_word_260, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_260.
Lemma node_word_260_value v : eval_hfexpr expr_word_260 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_260 v)).
Proof. change (eval_hfexpr expr_word_260 (closed_word_260 v) (closed_word_260 v) = Some (Gval (Fuint 1) (word_260 v))). apply closed_word_260_value. Qed.
Transparent word_262.
Lemma closed_word_262_value v : eval_hfexpr expr_word_262 (closed_word_262 v) (closed_word_262 v) = Some (Gval (Fuint 1) (word_262 v)).
Proof. unfold word_262, closed_word_262, expr_word_262, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_262.
Lemma node_word_262_value v : eval_hfexpr expr_word_262 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_262 v)).
Proof. change (eval_hfexpr expr_word_262 (closed_word_262 v) (closed_word_262 v) = Some (Gval (Fuint 1) (word_262 v))). apply closed_word_262_value. Qed.
Transparent word_264.
Lemma closed_word_264_value v : eval_hfexpr expr_word_264 (closed_word_264 v) (closed_word_264 v) = Some (Gval (Fuint 1) (word_264 v)).
Proof. unfold word_264, closed_word_264, expr_word_264, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_264.
Lemma node_word_264_value v : eval_hfexpr expr_word_264 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_264 v)).
Proof. change (eval_hfexpr expr_word_264 (closed_word_264 v) (closed_word_264 v) = Some (Gval (Fuint 1) (word_264 v))). apply closed_word_264_value. Qed.
Transparent word_266.
Lemma closed_word_266_value v : eval_hfexpr expr_word_266 (closed_word_266 v) (closed_word_266 v) = Some (Gval (Fuint 1) (word_266 v)).
Proof. unfold word_266, closed_word_266, expr_word_266, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_266.
Lemma node_word_266_value v : eval_hfexpr expr_word_266 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_266 v)).
Proof. change (eval_hfexpr expr_word_266 (closed_word_266 v) (closed_word_266 v) = Some (Gval (Fuint 1) (word_266 v))). apply closed_word_266_value. Qed.
Transparent word_268.
Lemma closed_word_268_value v : eval_hfexpr expr_word_268 (closed_word_268 v) (closed_word_268 v) = Some (Gval (Fuint 1) (word_268 v)).
Proof. unfold word_268, closed_word_268, expr_word_268, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_268.
Lemma node_word_268_value v : eval_hfexpr expr_word_268 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_268 v)).
Proof. change (eval_hfexpr expr_word_268 (closed_word_268 v) (closed_word_268 v) = Some (Gval (Fuint 1) (word_268 v))). apply closed_word_268_value. Qed.
Transparent word_270.
Lemma closed_word_270_value v : eval_hfexpr expr_word_270 (closed_word_270 v) (closed_word_270 v) = Some (Gval (Fuint 1) (word_270 v)).
Proof. unfold word_270, closed_word_270, expr_word_270, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_270.
Lemma node_word_270_value v : eval_hfexpr expr_word_270 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_270 v)).
Proof. change (eval_hfexpr expr_word_270 (closed_word_270 v) (closed_word_270 v) = Some (Gval (Fuint 1) (word_270 v))). apply closed_word_270_value. Qed.
Transparent word_272.
Lemma closed_word_272_value v : eval_hfexpr expr_word_272 (closed_word_272 v) (closed_word_272 v) = Some (Gval (Fuint 1) (word_272 v)).
Proof. unfold word_272, closed_word_272, expr_word_272, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_272.
Lemma node_word_272_value v : eval_hfexpr expr_word_272 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_272 v)).
Proof. change (eval_hfexpr expr_word_272 (closed_word_272 v) (closed_word_272 v) = Some (Gval (Fuint 1) (word_272 v))). apply closed_word_272_value. Qed.
Transparent word_274.
Lemma closed_word_274_value v : eval_hfexpr expr_word_274 (closed_word_274 v) (closed_word_274 v) = Some (Gval (Fuint 1) (word_274 v)).
Proof. unfold word_274, closed_word_274, expr_word_274, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_274.
Lemma node_word_274_value v : eval_hfexpr expr_word_274 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_274 v)).
Proof. change (eval_hfexpr expr_word_274 (closed_word_274 v) (closed_word_274 v) = Some (Gval (Fuint 1) (word_274 v))). apply closed_word_274_value. Qed.
Transparent word_276.
Lemma closed_word_276_value v : eval_hfexpr expr_word_276 (closed_word_276 v) (closed_word_276 v) = Some (Gval (Fuint 1) (word_276 v)).
Proof. unfold word_276, closed_word_276, expr_word_276, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_276.
Lemma node_word_276_value v : eval_hfexpr expr_word_276 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_276 v)).
Proof. change (eval_hfexpr expr_word_276 (closed_word_276 v) (closed_word_276 v) = Some (Gval (Fuint 1) (word_276 v))). apply closed_word_276_value. Qed.
Transparent word_278.
Lemma closed_word_278_value v : eval_hfexpr expr_word_278 (closed_word_278 v) (closed_word_278 v) = Some (Gval (Fuint 1) (word_278 v)).
Proof. unfold word_278, closed_word_278, expr_word_278, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_278.
Lemma node_word_278_value v : eval_hfexpr expr_word_278 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_278 v)).
Proof. change (eval_hfexpr expr_word_278 (closed_word_278 v) (closed_word_278 v) = Some (Gval (Fuint 1) (word_278 v))). apply closed_word_278_value. Qed.
Transparent word_280.
Lemma closed_word_280_value v : eval_hfexpr expr_word_280 (closed_word_280 v) (closed_word_280 v) = Some (Gval (Fuint 1) (word_280 v)).
Proof. unfold word_280, closed_word_280, expr_word_280, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_280.
Lemma node_word_280_value v : eval_hfexpr expr_word_280 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_280 v)).
Proof. change (eval_hfexpr expr_word_280 (closed_word_280 v) (closed_word_280 v) = Some (Gval (Fuint 1) (word_280 v))). apply closed_word_280_value. Qed.
Transparent word_282.
Lemma closed_word_282_value v : eval_hfexpr expr_word_282 (closed_word_282 v) (closed_word_282 v) = Some (Gval (Fuint 1) (word_282 v)).
Proof. unfold word_282, closed_word_282, expr_word_282, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_282.
Lemma node_word_282_value v : eval_hfexpr expr_word_282 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_282 v)).
Proof. change (eval_hfexpr expr_word_282 (closed_word_282 v) (closed_word_282 v) = Some (Gval (Fuint 1) (word_282 v))). apply closed_word_282_value. Qed.
Transparent word_284.
Lemma closed_word_284_value v : eval_hfexpr expr_word_284 (closed_word_284 v) (closed_word_284 v) = Some (Gval (Fuint 1) (word_284 v)).
Proof. unfold word_284, closed_word_284, expr_word_284, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_284.
Lemma node_word_284_value v : eval_hfexpr expr_word_284 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_284 v)).
Proof. change (eval_hfexpr expr_word_284 (closed_word_284 v) (closed_word_284 v) = Some (Gval (Fuint 1) (word_284 v))). apply closed_word_284_value. Qed.
Transparent word_286.
Lemma closed_word_286_value v : eval_hfexpr expr_word_286 (closed_word_286 v) (closed_word_286 v) = Some (Gval (Fuint 1) (word_286 v)).
Proof. unfold word_286, closed_word_286, expr_word_286, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_286.
Lemma node_word_286_value v : eval_hfexpr expr_word_286 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_286 v)).
Proof. change (eval_hfexpr expr_word_286 (closed_word_286 v) (closed_word_286 v) = Some (Gval (Fuint 1) (word_286 v))). apply closed_word_286_value. Qed.
Transparent word_288.
Lemma closed_word_288_value v : eval_hfexpr expr_word_288 (closed_word_288 v) (closed_word_288 v) = Some (Gval (Fuint 1) (word_288 v)).
Proof. unfold word_288, closed_word_288, expr_word_288, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_288.
Lemma node_word_288_value v : eval_hfexpr expr_word_288 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_288 v)).
Proof. change (eval_hfexpr expr_word_288 (closed_word_288 v) (closed_word_288 v) = Some (Gval (Fuint 1) (word_288 v))). apply closed_word_288_value. Qed.
Transparent word_290.
Lemma closed_word_290_value v : eval_hfexpr expr_word_290 (closed_word_290 v) (closed_word_290 v) = Some (Gval (Fuint 1) (word_290 v)).
Proof. unfold word_290, closed_word_290, expr_word_290, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_290.
Lemma node_word_290_value v : eval_hfexpr expr_word_290 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_290 v)).
Proof. change (eval_hfexpr expr_word_290 (closed_word_290 v) (closed_word_290 v) = Some (Gval (Fuint 1) (word_290 v))). apply closed_word_290_value. Qed.
Transparent word_292.
Lemma closed_word_292_value v : eval_hfexpr expr_word_292 (closed_word_292 v) (closed_word_292 v) = Some (Gval (Fuint 1) (word_292 v)).
Proof. unfold word_292, closed_word_292, expr_word_292, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_292.
Lemma node_word_292_value v : eval_hfexpr expr_word_292 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_292 v)).
Proof. change (eval_hfexpr expr_word_292 (closed_word_292 v) (closed_word_292 v) = Some (Gval (Fuint 1) (word_292 v))). apply closed_word_292_value. Qed.
Transparent word_294.
Lemma closed_word_294_value v : eval_hfexpr expr_word_294 (closed_word_294 v) (closed_word_294 v) = Some (Gval (Fuint 1) (word_294 v)).
Proof. unfold word_294, closed_word_294, expr_word_294, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_294.
Lemma node_word_294_value v : eval_hfexpr expr_word_294 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_294 v)).
Proof. change (eval_hfexpr expr_word_294 (closed_word_294 v) (closed_word_294 v) = Some (Gval (Fuint 1) (word_294 v))). apply closed_word_294_value. Qed.
Transparent word_296.
Lemma closed_word_296_value v : eval_hfexpr expr_word_296 (closed_word_296 v) (closed_word_296 v) = Some (Gval (Fuint 1) (word_296 v)).
Proof. unfold word_296, closed_word_296, expr_word_296, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_296.
Lemma node_word_296_value v : eval_hfexpr expr_word_296 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_296 v)).
Proof. change (eval_hfexpr expr_word_296 (closed_word_296 v) (closed_word_296 v) = Some (Gval (Fuint 1) (word_296 v))). apply closed_word_296_value. Qed.
Transparent word_298.
Lemma closed_word_298_value v : eval_hfexpr expr_word_298 (closed_word_298 v) (closed_word_298 v) = Some (Gval (Fuint 1) (word_298 v)).
Proof. unfold word_298, closed_word_298, expr_word_298, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_298.
Lemma node_word_298_value v : eval_hfexpr expr_word_298 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_298 v)).
Proof. change (eval_hfexpr expr_word_298 (closed_word_298 v) (closed_word_298 v) = Some (Gval (Fuint 1) (word_298 v))). apply closed_word_298_value. Qed.
Transparent word_300.
Lemma closed_word_300_value v : eval_hfexpr expr_word_300 (closed_word_300 v) (closed_word_300 v) = Some (Gval (Fuint 1) (word_300 v)).
Proof. unfold word_300, closed_word_300, expr_word_300, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_300.
Lemma node_word_300_value v : eval_hfexpr expr_word_300 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_300 v)).
Proof. change (eval_hfexpr expr_word_300 (closed_word_300 v) (closed_word_300 v) = Some (Gval (Fuint 1) (word_300 v))). apply closed_word_300_value. Qed.
Transparent word_302.
Lemma closed_word_302_value v : eval_hfexpr expr_word_302 (closed_word_302 v) (closed_word_302 v) = Some (Gval (Fuint 1) (word_302 v)).
Proof. unfold word_302, closed_word_302, expr_word_302, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_302.
Lemma node_word_302_value v : eval_hfexpr expr_word_302 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_302 v)).
Proof. change (eval_hfexpr expr_word_302 (closed_word_302 v) (closed_word_302 v) = Some (Gval (Fuint 1) (word_302 v))). apply closed_word_302_value. Qed.
Transparent word_304.
Lemma closed_word_304_value v : eval_hfexpr expr_word_304 (closed_word_304 v) (closed_word_304 v) = Some (Gval (Fuint 1) (word_304 v)).
Proof. unfold word_304, closed_word_304, expr_word_304, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_304.
Lemma node_word_304_value v : eval_hfexpr expr_word_304 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_304 v)).
Proof. change (eval_hfexpr expr_word_304 (closed_word_304 v) (closed_word_304 v) = Some (Gval (Fuint 1) (word_304 v))). apply closed_word_304_value. Qed.
Transparent word_305.
Lemma closed_word_305_value v : eval_hfexpr expr_word_305 (closed_word_305 v) (closed_word_305 v) = Some (Gval (Fuint 1) (word_305 v)).
Proof. unfold word_305, closed_word_305, expr_word_305, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_305.
Lemma node_word_305_value v : eval_hfexpr expr_word_305 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_305 v)).
Proof. change (eval_hfexpr expr_word_305 (closed_word_305 v) (closed_word_305 v) = Some (Gval (Fuint 1) (word_305 v))). apply closed_word_305_value. Qed.
Transparent word_306.
Lemma closed_word_306_value v : eval_hfexpr expr_word_306 (closed_word_306 v) (closed_word_306 v) = Some (Gval (Fuint 1) (word_306 v)).
Proof. unfold word_306, closed_word_306, expr_word_306, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_306.
Lemma node_word_306_value v : eval_hfexpr expr_word_306 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_306 v)).
Proof. change (eval_hfexpr expr_word_306 (closed_word_306 v) (closed_word_306 v) = Some (Gval (Fuint 1) (word_306 v))). apply closed_word_306_value. Qed.
Transparent word_307.
Lemma closed_word_307_value v : eval_hfexpr expr_word_307 (closed_word_307 v) (closed_word_307 v) = Some (Gval (Fuint 1) (word_307 v)).
Proof. unfold word_307, closed_word_307, expr_word_307, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_307.
Lemma node_word_307_value v : eval_hfexpr expr_word_307 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_307 v)).
Proof. change (eval_hfexpr expr_word_307 (closed_word_307 v) (closed_word_307 v) = Some (Gval (Fuint 1) (word_307 v))). apply closed_word_307_value. Qed.
Transparent word_308.
Lemma closed_word_308_value v : eval_hfexpr expr_word_308 (closed_word_308 v) (closed_word_308 v) = Some (Gval (Fuint 1) (word_308 v)).
Proof. unfold word_308, closed_word_308, expr_word_308, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_308.
Lemma node_word_308_value v : eval_hfexpr expr_word_308 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_308 v)).
Proof. change (eval_hfexpr expr_word_308 (closed_word_308 v) (closed_word_308 v) = Some (Gval (Fuint 1) (word_308 v))). apply closed_word_308_value. Qed.
Transparent word_309.
Lemma closed_word_309_value v : eval_hfexpr expr_word_309 (closed_word_309 v) (closed_word_309 v) = Some (Gval (Fuint 1) (word_309 v)).
Proof. unfold word_309, closed_word_309, expr_word_309, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_309.
Lemma node_word_309_value v : eval_hfexpr expr_word_309 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_309 v)).
Proof. change (eval_hfexpr expr_word_309 (closed_word_309 v) (closed_word_309 v) = Some (Gval (Fuint 1) (word_309 v))). apply closed_word_309_value. Qed.
Transparent word_310.
Lemma closed_word_310_value v : eval_hfexpr expr_word_310 (closed_word_310 v) (closed_word_310 v) = Some (Gval (Fuint 1) (word_310 v)).
Proof. unfold word_310, closed_word_310, expr_word_310, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_310.
Lemma node_word_310_value v : eval_hfexpr expr_word_310 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_310 v)).
Proof. change (eval_hfexpr expr_word_310 (closed_word_310 v) (closed_word_310 v) = Some (Gval (Fuint 1) (word_310 v))). apply closed_word_310_value. Qed.
Transparent word_311.
Lemma closed_word_311_value v : eval_hfexpr expr_word_311 (closed_word_311 v) (closed_word_311 v) = Some (Gval (Fuint 1) (word_311 v)).
Proof. unfold word_311, closed_word_311, expr_word_311, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_311.
Lemma node_word_311_value v : eval_hfexpr expr_word_311 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_311 v)).
Proof. change (eval_hfexpr expr_word_311 (closed_word_311 v) (closed_word_311 v) = Some (Gval (Fuint 1) (word_311 v))). apply closed_word_311_value. Qed.
Transparent word_312.
Lemma closed_word_312_value v : eval_hfexpr expr_word_312 (closed_word_312 v) (closed_word_312 v) = Some (Gval (Fuint 1) (word_312 v)).
Proof. unfold word_312, closed_word_312, expr_word_312, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_312.
Lemma node_word_312_value v : eval_hfexpr expr_word_312 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_312 v)).
Proof. change (eval_hfexpr expr_word_312 (closed_word_312 v) (closed_word_312 v) = Some (Gval (Fuint 1) (word_312 v))). apply closed_word_312_value. Qed.
Transparent word_313.
Lemma closed_word_313_value v : eval_hfexpr expr_word_313 (closed_word_313 v) (closed_word_313 v) = Some (Gval (Fuint 1) (word_313 v)).
Proof. unfold word_313, closed_word_313, expr_word_313, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_313.
Lemma node_word_313_value v : eval_hfexpr expr_word_313 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_313 v)).
Proof. change (eval_hfexpr expr_word_313 (closed_word_313 v) (closed_word_313 v) = Some (Gval (Fuint 1) (word_313 v))). apply closed_word_313_value. Qed.
Transparent word_314.
Lemma closed_word_314_value v : eval_hfexpr expr_word_314 (closed_word_314 v) (closed_word_314 v) = Some (Gval (Fuint 1) (word_314 v)).
Proof. unfold word_314, closed_word_314, expr_word_314, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_314.
Lemma node_word_314_value v : eval_hfexpr expr_word_314 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_314 v)).
Proof. change (eval_hfexpr expr_word_314 (closed_word_314 v) (closed_word_314 v) = Some (Gval (Fuint 1) (word_314 v))). apply closed_word_314_value. Qed.
Transparent word_315.
Lemma closed_word_315_value v : eval_hfexpr expr_word_315 (closed_word_315 v) (closed_word_315 v) = Some (Gval (Fuint 1) (word_315 v)).
Proof. unfold word_315, closed_word_315, expr_word_315, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_315.
Lemma node_word_315_value v : eval_hfexpr expr_word_315 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_315 v)).
Proof. change (eval_hfexpr expr_word_315 (closed_word_315 v) (closed_word_315 v) = Some (Gval (Fuint 1) (word_315 v))). apply closed_word_315_value. Qed.
Transparent word_316.
Lemma closed_word_316_value v : eval_hfexpr expr_word_316 (closed_word_316 v) (closed_word_316 v) = Some (Gval (Fuint 1) (word_316 v)).
Proof. unfold word_316, closed_word_316, expr_word_316, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_316.
Lemma node_word_316_value v : eval_hfexpr expr_word_316 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_316 v)).
Proof. change (eval_hfexpr expr_word_316 (closed_word_316 v) (closed_word_316 v) = Some (Gval (Fuint 1) (word_316 v))). apply closed_word_316_value. Qed.
Transparent word_317.
Lemma closed_word_317_value v : eval_hfexpr expr_word_317 (closed_word_317 v) (closed_word_317 v) = Some (Gval (Fuint 1) (word_317 v)).
Proof. unfold word_317, closed_word_317, expr_word_317, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_317.
Lemma node_word_317_value v : eval_hfexpr expr_word_317 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_317 v)).
Proof. change (eval_hfexpr expr_word_317 (closed_word_317 v) (closed_word_317 v) = Some (Gval (Fuint 1) (word_317 v))). apply closed_word_317_value. Qed.
Transparent word_318.
Lemma closed_word_318_value v : eval_hfexpr expr_word_318 (closed_word_318 v) (closed_word_318 v) = Some (Gval (Fuint 1) (word_318 v)).
Proof. unfold word_318, closed_word_318, expr_word_318, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_318.
Lemma node_word_318_value v : eval_hfexpr expr_word_318 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_318 v)).
Proof. change (eval_hfexpr expr_word_318 (closed_word_318 v) (closed_word_318 v) = Some (Gval (Fuint 1) (word_318 v))). apply closed_word_318_value. Qed.
Transparent word_319.
Lemma closed_word_319_value v : eval_hfexpr expr_word_319 (closed_word_319 v) (closed_word_319 v) = Some (Gval (Fuint 1) (word_319 v)).
Proof. unfold word_319, closed_word_319, expr_word_319, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_319.
Lemma node_word_319_value v : eval_hfexpr expr_word_319 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_319 v)).
Proof. change (eval_hfexpr expr_word_319 (closed_word_319 v) (closed_word_319 v) = Some (Gval (Fuint 1) (word_319 v))). apply closed_word_319_value. Qed.
Transparent word_320.
Lemma closed_word_320_value v : eval_hfexpr expr_word_320 (closed_word_320 v) (closed_word_320 v) = Some (Gval (Fuint 1) (word_320 v)).
Proof. unfold word_320, closed_word_320, expr_word_320, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_320.
Lemma node_word_320_value v : eval_hfexpr expr_word_320 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_320 v)).
Proof. change (eval_hfexpr expr_word_320 (closed_word_320 v) (closed_word_320 v) = Some (Gval (Fuint 1) (word_320 v))). apply closed_word_320_value. Qed.
Transparent word_321.
Lemma closed_word_321_value v : eval_hfexpr expr_word_321 (closed_word_321 v) (closed_word_321 v) = Some (Gval (Fuint 1) (word_321 v)).
Proof. unfold word_321, closed_word_321, expr_word_321, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_321.
Lemma node_word_321_value v : eval_hfexpr expr_word_321 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_321 v)).
Proof. change (eval_hfexpr expr_word_321 (closed_word_321 v) (closed_word_321 v) = Some (Gval (Fuint 1) (word_321 v))). apply closed_word_321_value. Qed.
Transparent word_322.
Lemma closed_word_322_value v : eval_hfexpr expr_word_322 (closed_word_322 v) (closed_word_322 v) = Some (Gval (Fuint 1) (word_322 v)).
Proof. unfold word_322, closed_word_322, expr_word_322, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_322.
Lemma node_word_322_value v : eval_hfexpr expr_word_322 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_322 v)).
Proof. change (eval_hfexpr expr_word_322 (closed_word_322 v) (closed_word_322 v) = Some (Gval (Fuint 1) (word_322 v))). apply closed_word_322_value. Qed.
Transparent word_323.
Lemma closed_word_323_value v : eval_hfexpr expr_word_323 (closed_word_323 v) (closed_word_323 v) = Some (Gval (Fuint 1) (word_323 v)).
Proof. unfold word_323, closed_word_323, expr_word_323, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_323.
Lemma node_word_323_value v : eval_hfexpr expr_word_323 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_323 v)).
Proof. change (eval_hfexpr expr_word_323 (closed_word_323 v) (closed_word_323 v) = Some (Gval (Fuint 1) (word_323 v))). apply closed_word_323_value. Qed.
Transparent word_324.
Lemma closed_word_324_value v : eval_hfexpr expr_word_324 (closed_word_324 v) (closed_word_324 v) = Some (Gval (Fuint 1) (word_324 v)).
Proof. unfold word_324, closed_word_324, expr_word_324, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_324.
Lemma node_word_324_value v : eval_hfexpr expr_word_324 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_324 v)).
Proof. change (eval_hfexpr expr_word_324 (closed_word_324 v) (closed_word_324 v) = Some (Gval (Fuint 1) (word_324 v))). apply closed_word_324_value. Qed.
Transparent word_325.
Lemma closed_word_325_value v : eval_hfexpr expr_word_325 (closed_word_325 v) (closed_word_325 v) = Some (Gval (Fuint 1) (word_325 v)).
Proof. unfold word_325, closed_word_325, expr_word_325, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_325.
Lemma node_word_325_value v : eval_hfexpr expr_word_325 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_325 v)).
Proof. change (eval_hfexpr expr_word_325 (closed_word_325 v) (closed_word_325 v) = Some (Gval (Fuint 1) (word_325 v))). apply closed_word_325_value. Qed.
Transparent word_326.
Lemma closed_word_326_value v : eval_hfexpr expr_word_326 (closed_word_326 v) (closed_word_326 v) = Some (Gval (Fuint 1) (word_326 v)).
Proof. unfold word_326, closed_word_326, expr_word_326, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_326.
Lemma node_word_326_value v : eval_hfexpr expr_word_326 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_326 v)).
Proof. change (eval_hfexpr expr_word_326 (closed_word_326 v) (closed_word_326 v) = Some (Gval (Fuint 1) (word_326 v))). apply closed_word_326_value. Qed.
Transparent word_327.
Lemma closed_word_327_value v : eval_hfexpr expr_word_327 (closed_word_327 v) (closed_word_327 v) = Some (Gval (Fuint 1) (word_327 v)).
Proof. unfold word_327, closed_word_327, expr_word_327, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_327.
Lemma node_word_327_value v : eval_hfexpr expr_word_327 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_327 v)).
Proof. change (eval_hfexpr expr_word_327 (closed_word_327 v) (closed_word_327 v) = Some (Gval (Fuint 1) (word_327 v))). apply closed_word_327_value. Qed.
Transparent word_328.
Lemma closed_word_328_value v : eval_hfexpr expr_word_328 (closed_word_328 v) (closed_word_328 v) = Some (Gval (Fuint 1) (word_328 v)).
Proof. unfold word_328, closed_word_328, expr_word_328, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_328.
Lemma node_word_328_value v : eval_hfexpr expr_word_328 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_328 v)).
Proof. change (eval_hfexpr expr_word_328 (closed_word_328 v) (closed_word_328 v) = Some (Gval (Fuint 1) (word_328 v))). apply closed_word_328_value. Qed.
Transparent word_329.
Lemma closed_word_329_value v : eval_hfexpr expr_word_329 (closed_word_329 v) (closed_word_329 v) = Some (Gval (Fuint 1) (word_329 v)).
Proof. unfold word_329, closed_word_329, expr_word_329, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_329.
Lemma node_word_329_value v : eval_hfexpr expr_word_329 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_329 v)).
Proof. change (eval_hfexpr expr_word_329 (closed_word_329 v) (closed_word_329 v) = Some (Gval (Fuint 1) (word_329 v))). apply closed_word_329_value. Qed.
Transparent word_330.
Lemma closed_word_330_value v : eval_hfexpr expr_word_330 (closed_word_330 v) (closed_word_330 v) = Some (Gval (Fuint 1) (word_330 v)).
Proof. unfold word_330, closed_word_330, expr_word_330, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_330.
Lemma node_word_330_value v : eval_hfexpr expr_word_330 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_330 v)).
Proof. change (eval_hfexpr expr_word_330 (closed_word_330 v) (closed_word_330 v) = Some (Gval (Fuint 1) (word_330 v))). apply closed_word_330_value. Qed.
Transparent word_331.
Lemma closed_word_331_value v : eval_hfexpr expr_word_331 (closed_word_331 v) (closed_word_331 v) = Some (Gval (Fuint 1) (word_331 v)).
Proof. unfold word_331, closed_word_331, expr_word_331, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_331.
Lemma node_word_331_value v : eval_hfexpr expr_word_331 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_331 v)).
Proof. change (eval_hfexpr expr_word_331 (closed_word_331 v) (closed_word_331 v) = Some (Gval (Fuint 1) (word_331 v))). apply closed_word_331_value. Qed.
Transparent word_332.
Lemma closed_word_332_value v : eval_hfexpr expr_word_332 (closed_word_332 v) (closed_word_332 v) = Some (Gval (Fuint 1) (word_332 v)).
Proof. unfold word_332, closed_word_332, expr_word_332, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_332.
Lemma node_word_332_value v : eval_hfexpr expr_word_332 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_332 v)).
Proof. change (eval_hfexpr expr_word_332 (closed_word_332 v) (closed_word_332 v) = Some (Gval (Fuint 1) (word_332 v))). apply closed_word_332_value. Qed.
Transparent word_333.
Lemma closed_word_333_value v : eval_hfexpr expr_word_333 (closed_word_333 v) (closed_word_333 v) = Some (Gval (Fuint 1) (word_333 v)).
Proof. unfold word_333, closed_word_333, expr_word_333, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_333.
Lemma node_word_333_value v : eval_hfexpr expr_word_333 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_333 v)).
Proof. change (eval_hfexpr expr_word_333 (closed_word_333 v) (closed_word_333 v) = Some (Gval (Fuint 1) (word_333 v))). apply closed_word_333_value. Qed.
Transparent word_334.
Lemma closed_word_334_value v : eval_hfexpr expr_word_334 (closed_word_334 v) (closed_word_334 v) = Some (Gval (Fuint 1) (word_334 v)).
Proof. unfold word_334, closed_word_334, expr_word_334, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_334.
Lemma node_word_334_value v : eval_hfexpr expr_word_334 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_334 v)).
Proof. change (eval_hfexpr expr_word_334 (closed_word_334 v) (closed_word_334 v) = Some (Gval (Fuint 1) (word_334 v))). apply closed_word_334_value. Qed.
Transparent word_335.
Lemma closed_word_335_value v : eval_hfexpr expr_word_335 (closed_word_335 v) (closed_word_335 v) = Some (Gval (Fuint 1) (word_335 v)).
Proof. unfold word_335, closed_word_335, expr_word_335, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_335.
Lemma node_word_335_value v : eval_hfexpr expr_word_335 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_335 v)).
Proof. change (eval_hfexpr expr_word_335 (closed_word_335 v) (closed_word_335 v) = Some (Gval (Fuint 1) (word_335 v))). apply closed_word_335_value. Qed.
Transparent word_336.
Lemma closed_word_336_value v : eval_hfexpr expr_word_336 (closed_word_336 v) (closed_word_336 v) = Some (Gval (Fuint 1) (word_336 v)).
Proof. unfold word_336, closed_word_336, expr_word_336, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_336.
Lemma node_word_336_value v : eval_hfexpr expr_word_336 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_336 v)).
Proof. change (eval_hfexpr expr_word_336 (closed_word_336 v) (closed_word_336 v) = Some (Gval (Fuint 1) (word_336 v))). apply closed_word_336_value. Qed.
Transparent word_337.
Lemma closed_word_337_value v : eval_hfexpr expr_word_337 (closed_word_337 v) (closed_word_337 v) = Some (Gval (Fuint 1) (word_337 v)).
Proof. unfold word_337, closed_word_337, expr_word_337, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_337.
Lemma node_word_337_value v : eval_hfexpr expr_word_337 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_337 v)).
Proof. change (eval_hfexpr expr_word_337 (closed_word_337 v) (closed_word_337 v) = Some (Gval (Fuint 1) (word_337 v))). apply closed_word_337_value. Qed.
Transparent word_338.
Lemma closed_word_338_value v : eval_hfexpr expr_word_338 (closed_word_338 v) (closed_word_338 v) = Some (Gval (Fuint 1) (word_338 v)).
Proof. unfold word_338, closed_word_338, expr_word_338, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_338.
Lemma node_word_338_value v : eval_hfexpr expr_word_338 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_338 v)).
Proof. change (eval_hfexpr expr_word_338 (closed_word_338 v) (closed_word_338 v) = Some (Gval (Fuint 1) (word_338 v))). apply closed_word_338_value. Qed.
Transparent word_339.
Lemma closed_word_339_value v : eval_hfexpr expr_word_339 (closed_word_339 v) (closed_word_339 v) = Some (Gval (Fuint 1) (word_339 v)).
Proof. unfold word_339, closed_word_339, expr_word_339, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_339.
Lemma node_word_339_value v : eval_hfexpr expr_word_339 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_339 v)).
Proof. change (eval_hfexpr expr_word_339 (closed_word_339 v) (closed_word_339 v) = Some (Gval (Fuint 1) (word_339 v))). apply closed_word_339_value. Qed.
Transparent word_340.
Lemma closed_word_340_value v : eval_hfexpr expr_word_340 (closed_word_340 v) (closed_word_340 v) = Some (Gval (Fuint 1) (word_340 v)).
Proof. unfold word_340, closed_word_340, expr_word_340, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_340.
Lemma node_word_340_value v : eval_hfexpr expr_word_340 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_340 v)).
Proof. change (eval_hfexpr expr_word_340 (closed_word_340 v) (closed_word_340 v) = Some (Gval (Fuint 1) (word_340 v))). apply closed_word_340_value. Qed.
Transparent word_341.
Lemma closed_word_341_value v : eval_hfexpr expr_word_341 (closed_word_341 v) (closed_word_341 v) = Some (Gval (Fuint 1) (word_341 v)).
Proof. unfold word_341, closed_word_341, expr_word_341, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_341.
Lemma node_word_341_value v : eval_hfexpr expr_word_341 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_341 v)).
Proof. change (eval_hfexpr expr_word_341 (closed_word_341 v) (closed_word_341 v) = Some (Gval (Fuint 1) (word_341 v))). apply closed_word_341_value. Qed.
Transparent word_342.
Lemma closed_word_342_value v : eval_hfexpr expr_word_342 (closed_word_342 v) (closed_word_342 v) = Some (Gval (Fuint 1) (word_342 v)).
Proof. unfold word_342, closed_word_342, expr_word_342, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_342.
Lemma node_word_342_value v : eval_hfexpr expr_word_342 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_342 v)).
Proof. change (eval_hfexpr expr_word_342 (closed_word_342 v) (closed_word_342 v) = Some (Gval (Fuint 1) (word_342 v))). apply closed_word_342_value. Qed.
Transparent word_343.
Lemma closed_word_343_value v : eval_hfexpr expr_word_343 (closed_word_343 v) (closed_word_343 v) = Some (Gval (Fuint 1) (word_343 v)).
Proof. unfold word_343, closed_word_343, expr_word_343, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_343.
Lemma node_word_343_value v : eval_hfexpr expr_word_343 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_343 v)).
Proof. change (eval_hfexpr expr_word_343 (closed_word_343 v) (closed_word_343 v) = Some (Gval (Fuint 1) (word_343 v))). apply closed_word_343_value. Qed.
Transparent word_344.
Lemma closed_word_344_value v : eval_hfexpr expr_word_344 (closed_word_344 v) (closed_word_344 v) = Some (Gval (Fuint 1) (word_344 v)).
Proof. unfold word_344, closed_word_344, expr_word_344, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_344.
Lemma node_word_344_value v : eval_hfexpr expr_word_344 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_344 v)).
Proof. change (eval_hfexpr expr_word_344 (closed_word_344 v) (closed_word_344 v) = Some (Gval (Fuint 1) (word_344 v))). apply closed_word_344_value. Qed.
Transparent word_345.
Lemma closed_word_345_value v : eval_hfexpr expr_word_345 (closed_word_345 v) (closed_word_345 v) = Some (Gval (Fuint 1) (word_345 v)).
Proof. unfold word_345, closed_word_345, expr_word_345, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_345.
Lemma node_word_345_value v : eval_hfexpr expr_word_345 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_345 v)).
Proof. change (eval_hfexpr expr_word_345 (closed_word_345 v) (closed_word_345 v) = Some (Gval (Fuint 1) (word_345 v))). apply closed_word_345_value. Qed.
Transparent word_346.
Lemma closed_word_346_value v : eval_hfexpr expr_word_346 (closed_word_346 v) (closed_word_346 v) = Some (Gval (Fuint 1) (word_346 v)).
Proof. unfold word_346, closed_word_346, expr_word_346, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_346.
Lemma node_word_346_value v : eval_hfexpr expr_word_346 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_346 v)).
Proof. change (eval_hfexpr expr_word_346 (closed_word_346 v) (closed_word_346 v) = Some (Gval (Fuint 1) (word_346 v))). apply closed_word_346_value. Qed.
Transparent word_347.
Lemma closed_word_347_value v : eval_hfexpr expr_word_347 (closed_word_347 v) (closed_word_347 v) = Some (Gval (Fuint 1) (word_347 v)).
Proof. unfold word_347, closed_word_347, expr_word_347, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_347.
Lemma node_word_347_value v : eval_hfexpr expr_word_347 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_347 v)).
Proof. change (eval_hfexpr expr_word_347 (closed_word_347 v) (closed_word_347 v) = Some (Gval (Fuint 1) (word_347 v))). apply closed_word_347_value. Qed.
Transparent word_348.
Lemma closed_word_348_value v : eval_hfexpr expr_word_348 (closed_word_348 v) (closed_word_348 v) = Some (Gval (Fuint 1) (word_348 v)).
Proof. unfold word_348, closed_word_348, expr_word_348, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_348.
Lemma node_word_348_value v : eval_hfexpr expr_word_348 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_348 v)).
Proof. change (eval_hfexpr expr_word_348 (closed_word_348 v) (closed_word_348 v) = Some (Gval (Fuint 1) (word_348 v))). apply closed_word_348_value. Qed.
Transparent word_349.
Lemma closed_word_349_value v : eval_hfexpr expr_word_349 (closed_word_349 v) (closed_word_349 v) = Some (Gval (Fuint 1) (word_349 v)).
Proof. unfold word_349, closed_word_349, expr_word_349, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_349.
Lemma node_word_349_value v : eval_hfexpr expr_word_349 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_349 v)).
Proof. change (eval_hfexpr expr_word_349 (closed_word_349 v) (closed_word_349 v) = Some (Gval (Fuint 1) (word_349 v))). apply closed_word_349_value. Qed.
Transparent word_350.
Lemma closed_word_350_value v : eval_hfexpr expr_word_350 (closed_word_350 v) (closed_word_350 v) = Some (Gval (Fuint 1) (word_350 v)).
Proof. unfold word_350, closed_word_350, expr_word_350, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_350.
Lemma node_word_350_value v : eval_hfexpr expr_word_350 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_350 v)).
Proof. change (eval_hfexpr expr_word_350 (closed_word_350 v) (closed_word_350 v) = Some (Gval (Fuint 1) (word_350 v))). apply closed_word_350_value. Qed.
Transparent word_351.
Lemma closed_word_351_value v : eval_hfexpr expr_word_351 (closed_word_351 v) (closed_word_351 v) = Some (Gval (Fuint 1) (word_351 v)).
Proof. unfold word_351, closed_word_351, expr_word_351, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_351.
Lemma node_word_351_value v : eval_hfexpr expr_word_351 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_351 v)).
Proof. change (eval_hfexpr expr_word_351 (closed_word_351 v) (closed_word_351 v) = Some (Gval (Fuint 1) (word_351 v))). apply closed_word_351_value. Qed.
Transparent word_352.
Lemma closed_word_352_value v : eval_hfexpr expr_word_352 (closed_word_352 v) (closed_word_352 v) = Some (Gval (Fuint 1) (word_352 v)).
Proof. unfold word_352, closed_word_352, expr_word_352, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_352.
Lemma node_word_352_value v : eval_hfexpr expr_word_352 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_352 v)).
Proof. change (eval_hfexpr expr_word_352 (closed_word_352 v) (closed_word_352 v) = Some (Gval (Fuint 1) (word_352 v))). apply closed_word_352_value. Qed.
Transparent word_353.
Lemma closed_word_353_value v : eval_hfexpr expr_word_353 (closed_word_353 v) (closed_word_353 v) = Some (Gval (Fuint 1) (word_353 v)).
Proof. unfold word_353, closed_word_353, expr_word_353, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_353.
Lemma node_word_353_value v : eval_hfexpr expr_word_353 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_353 v)).
Proof. change (eval_hfexpr expr_word_353 (closed_word_353 v) (closed_word_353 v) = Some (Gval (Fuint 1) (word_353 v))). apply closed_word_353_value. Qed.
Transparent word_354.
Lemma closed_word_354_value v : eval_hfexpr expr_word_354 (closed_word_354 v) (closed_word_354 v) = Some (Gval (Fuint 1) (word_354 v)).
Proof. unfold word_354, closed_word_354, expr_word_354, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_354.
Lemma node_word_354_value v : eval_hfexpr expr_word_354 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_354 v)).
Proof. change (eval_hfexpr expr_word_354 (closed_word_354 v) (closed_word_354 v) = Some (Gval (Fuint 1) (word_354 v))). apply closed_word_354_value. Qed.
Transparent word_355.
Lemma closed_word_355_value v : eval_hfexpr expr_word_355 (closed_word_355 v) (closed_word_355 v) = Some (Gval (Fuint 1) (word_355 v)).
Proof. unfold word_355, closed_word_355, expr_word_355, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_355.
Lemma node_word_355_value v : eval_hfexpr expr_word_355 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_355 v)).
Proof. change (eval_hfexpr expr_word_355 (closed_word_355 v) (closed_word_355 v) = Some (Gval (Fuint 1) (word_355 v))). apply closed_word_355_value. Qed.
Transparent word_356.
Lemma closed_word_356_value v : eval_hfexpr expr_word_356 (closed_word_356 v) (closed_word_356 v) = Some (Gval (Fuint 1) (word_356 v)).
Proof. unfold word_356, closed_word_356, expr_word_356, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_356.
Lemma node_word_356_value v : eval_hfexpr expr_word_356 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_356 v)).
Proof. change (eval_hfexpr expr_word_356 (closed_word_356 v) (closed_word_356 v) = Some (Gval (Fuint 1) (word_356 v))). apply closed_word_356_value. Qed.
Transparent word_357.
Lemma closed_word_357_value v : eval_hfexpr expr_word_357 (closed_word_357 v) (closed_word_357 v) = Some (Gval (Fuint 1) (word_357 v)).
Proof. unfold word_357, closed_word_357, expr_word_357, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_357.
Lemma node_word_357_value v : eval_hfexpr expr_word_357 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_357 v)).
Proof. change (eval_hfexpr expr_word_357 (closed_word_357 v) (closed_word_357 v) = Some (Gval (Fuint 1) (word_357 v))). apply closed_word_357_value. Qed.
Transparent word_358.
Lemma closed_word_358_value v : eval_hfexpr expr_word_358 (closed_word_358 v) (closed_word_358 v) = Some (Gval (Fuint 1) (word_358 v)).
Proof. unfold word_358, closed_word_358, expr_word_358, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_358.
Lemma node_word_358_value v : eval_hfexpr expr_word_358 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_358 v)).
Proof. change (eval_hfexpr expr_word_358 (closed_word_358 v) (closed_word_358 v) = Some (Gval (Fuint 1) (word_358 v))). apply closed_word_358_value. Qed.
Transparent word_359.
Lemma closed_word_359_value v : eval_hfexpr expr_word_359 (closed_word_359 v) (closed_word_359 v) = Some (Gval (Fuint 1) (word_359 v)).
Proof. unfold word_359, closed_word_359, expr_word_359, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_359.
Lemma node_word_359_value v : eval_hfexpr expr_word_359 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_359 v)).
Proof. change (eval_hfexpr expr_word_359 (closed_word_359 v) (closed_word_359 v) = Some (Gval (Fuint 1) (word_359 v))). apply closed_word_359_value. Qed.
Transparent word_360.
Lemma closed_word_360_value v : eval_hfexpr expr_word_360 (closed_word_360 v) (closed_word_360 v) = Some (Gval (Fuint 1) (word_360 v)).
Proof. unfold word_360, closed_word_360, expr_word_360, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_360.
Lemma node_word_360_value v : eval_hfexpr expr_word_360 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_360 v)).
Proof. change (eval_hfexpr expr_word_360 (closed_word_360 v) (closed_word_360 v) = Some (Gval (Fuint 1) (word_360 v))). apply closed_word_360_value. Qed.
Transparent word_361.
Lemma closed_word_361_value v : eval_hfexpr expr_word_361 (closed_word_361 v) (closed_word_361 v) = Some (Gval (Fuint 1) (word_361 v)).
Proof. unfold word_361, closed_word_361, expr_word_361, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_361.
Lemma node_word_361_value v : eval_hfexpr expr_word_361 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_361 v)).
Proof. change (eval_hfexpr expr_word_361 (closed_word_361 v) (closed_word_361 v) = Some (Gval (Fuint 1) (word_361 v))). apply closed_word_361_value. Qed.
Transparent word_362.
Lemma closed_word_362_value v : eval_hfexpr expr_word_362 (closed_word_362 v) (closed_word_362 v) = Some (Gval (Fuint 1) (word_362 v)).
Proof. unfold word_362, closed_word_362, expr_word_362, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_362.
Lemma node_word_362_value v : eval_hfexpr expr_word_362 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_362 v)).
Proof. change (eval_hfexpr expr_word_362 (closed_word_362 v) (closed_word_362 v) = Some (Gval (Fuint 1) (word_362 v))). apply closed_word_362_value. Qed.
Transparent word_363.
Lemma closed_word_363_value v : eval_hfexpr expr_word_363 (closed_word_363 v) (closed_word_363 v) = Some (Gval (Fuint 1) (word_363 v)).
Proof. unfold word_363, closed_word_363, expr_word_363, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_363.
Lemma node_word_363_value v : eval_hfexpr expr_word_363 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_363 v)).
Proof. change (eval_hfexpr expr_word_363 (closed_word_363 v) (closed_word_363 v) = Some (Gval (Fuint 1) (word_363 v))). apply closed_word_363_value. Qed.
Transparent word_364.
Lemma closed_word_364_value v : eval_hfexpr expr_word_364 (closed_word_364 v) (closed_word_364 v) = Some (Gval (Fuint 1) (word_364 v)).
Proof. unfold word_364, closed_word_364, expr_word_364, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_364.
Lemma node_word_364_value v : eval_hfexpr expr_word_364 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_364 v)).
Proof. change (eval_hfexpr expr_word_364 (closed_word_364 v) (closed_word_364 v) = Some (Gval (Fuint 1) (word_364 v))). apply closed_word_364_value. Qed.
Transparent word_365.
Lemma closed_word_365_value v : eval_hfexpr expr_word_365 (closed_word_365 v) (closed_word_365 v) = Some (Gval (Fuint 1) (word_365 v)).
Proof. unfold word_365, closed_word_365, expr_word_365, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_365.
Lemma node_word_365_value v : eval_hfexpr expr_word_365 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_365 v)).
Proof. change (eval_hfexpr expr_word_365 (closed_word_365 v) (closed_word_365 v) = Some (Gval (Fuint 1) (word_365 v))). apply closed_word_365_value. Qed.
Transparent word_366.
Lemma closed_word_366_value v : eval_hfexpr expr_word_366 (closed_word_366 v) (closed_word_366 v) = Some (Gval (Fuint 1) (word_366 v)).
Proof. unfold word_366, closed_word_366, expr_word_366, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_366.
Lemma node_word_366_value v : eval_hfexpr expr_word_366 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_366 v)).
Proof. change (eval_hfexpr expr_word_366 (closed_word_366 v) (closed_word_366 v) = Some (Gval (Fuint 1) (word_366 v))). apply closed_word_366_value. Qed.
Transparent word_367.
Lemma closed_word_367_value v : eval_hfexpr expr_word_367 (closed_word_367 v) (closed_word_367 v) = Some (Gval (Fuint 1) (word_367 v)).
Proof. unfold word_367, closed_word_367, expr_word_367, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_367.
Lemma node_word_367_value v : eval_hfexpr expr_word_367 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_367 v)).
Proof. change (eval_hfexpr expr_word_367 (closed_word_367 v) (closed_word_367 v) = Some (Gval (Fuint 1) (word_367 v))). apply closed_word_367_value. Qed.
Transparent word_368.
Lemma closed_word_368_value v : eval_hfexpr expr_word_368 (closed_word_368 v) (closed_word_368 v) = Some (Gval (Fuint 1) (word_368 v)).
Proof. unfold word_368, closed_word_368, expr_word_368, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_368.
Lemma node_word_368_value v : eval_hfexpr expr_word_368 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_368 v)).
Proof. change (eval_hfexpr expr_word_368 (closed_word_368 v) (closed_word_368 v) = Some (Gval (Fuint 1) (word_368 v))). apply closed_word_368_value. Qed.
Transparent word_369.
Lemma closed_word_369_value v : eval_hfexpr expr_word_369 (closed_word_369 v) (closed_word_369 v) = Some (Gval (Fuint 1) (word_369 v)).
Proof. unfold word_369, closed_word_369, expr_word_369, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_369.
Lemma node_word_369_value v : eval_hfexpr expr_word_369 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_369 v)).
Proof. change (eval_hfexpr expr_word_369 (closed_word_369 v) (closed_word_369 v) = Some (Gval (Fuint 1) (word_369 v))). apply closed_word_369_value. Qed.
Transparent word_370.
Lemma closed_word_370_value v : eval_hfexpr expr_word_370 (closed_word_370 v) (closed_word_370 v) = Some (Gval (Fuint 1) (word_370 v)).
Proof. unfold word_370, closed_word_370, expr_word_370, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_370.
Lemma node_word_370_value v : eval_hfexpr expr_word_370 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_370 v)).
Proof. change (eval_hfexpr expr_word_370 (closed_word_370 v) (closed_word_370 v) = Some (Gval (Fuint 1) (word_370 v))). apply closed_word_370_value. Qed.
Transparent word_371.
Lemma closed_word_371_value v : eval_hfexpr expr_word_371 (closed_word_371 v) (closed_word_371 v) = Some (Gval (Fuint 1) (word_371 v)).
Proof. unfold word_371, closed_word_371, expr_word_371, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_371.
Lemma node_word_371_value v : eval_hfexpr expr_word_371 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_371 v)).
Proof. change (eval_hfexpr expr_word_371 (closed_word_371 v) (closed_word_371 v) = Some (Gval (Fuint 1) (word_371 v))). apply closed_word_371_value. Qed.
Transparent word_372.
Lemma closed_word_372_value v : eval_hfexpr expr_word_372 (closed_word_372 v) (closed_word_372 v) = Some (Gval (Fuint 1) (word_372 v)).
Proof. unfold word_372, closed_word_372, expr_word_372, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_372.
Lemma node_word_372_value v : eval_hfexpr expr_word_372 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_372 v)).
Proof. change (eval_hfexpr expr_word_372 (closed_word_372 v) (closed_word_372 v) = Some (Gval (Fuint 1) (word_372 v))). apply closed_word_372_value. Qed.
Transparent word_373.
Lemma closed_word_373_value v : eval_hfexpr expr_word_373 (closed_word_373 v) (closed_word_373 v) = Some (Gval (Fuint 2) (word_373 v)).
Proof. unfold word_373, closed_word_373, expr_word_373, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_373.
Lemma node_word_373_value v : eval_hfexpr expr_word_373 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_373 v)).
Proof. change (eval_hfexpr expr_word_373 (closed_word_373 v) (closed_word_373 v) = Some (Gval (Fuint 2) (word_373 v))). apply closed_word_373_value. Qed.
Transparent word_374.
Lemma closed_word_374_value v : eval_hfexpr expr_word_374 (closed_word_374 v) (closed_word_374 v) = Some (Gval (Fuint 2) (word_374 v)).
Proof. unfold word_374, closed_word_374, expr_word_374, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_374.
Lemma node_word_374_value v : eval_hfexpr expr_word_374 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_374 v)).
Proof. change (eval_hfexpr expr_word_374 (closed_word_374 v) (closed_word_374 v) = Some (Gval (Fuint 2) (word_374 v))). apply closed_word_374_value. Qed.
Transparent word_375.
Lemma closed_word_375_value v : eval_hfexpr expr_word_375 (closed_word_375 v) (closed_word_375 v) = Some (Gval (Fuint 4) (word_375 v)).
Proof. unfold word_375, closed_word_375, expr_word_375, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_375.
Lemma node_word_375_value v : eval_hfexpr expr_word_375 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_375 v)).
Proof. change (eval_hfexpr expr_word_375 (closed_word_375 v) (closed_word_375 v) = Some (Gval (Fuint 4) (word_375 v))). apply closed_word_375_value. Qed.
Transparent word_376.
Lemma closed_word_376_value v : eval_hfexpr expr_word_376 (closed_word_376 v) (closed_word_376 v) = Some (Gval (Fuint 2) (word_376 v)).
Proof. unfold word_376, closed_word_376, expr_word_376, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_376.
Lemma node_word_376_value v : eval_hfexpr expr_word_376 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_376 v)).
Proof. change (eval_hfexpr expr_word_376 (closed_word_376 v) (closed_word_376 v) = Some (Gval (Fuint 2) (word_376 v))). apply closed_word_376_value. Qed.
Transparent word_377.
Lemma closed_word_377_value v : eval_hfexpr expr_word_377 (closed_word_377 v) (closed_word_377 v) = Some (Gval (Fuint 2) (word_377 v)).
Proof. unfold word_377, closed_word_377, expr_word_377, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_377.
Lemma node_word_377_value v : eval_hfexpr expr_word_377 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_377 v)).
Proof. change (eval_hfexpr expr_word_377 (closed_word_377 v) (closed_word_377 v) = Some (Gval (Fuint 2) (word_377 v))). apply closed_word_377_value. Qed.
Transparent word_378.
Lemma closed_word_378_value v : eval_hfexpr expr_word_378 (closed_word_378 v) (closed_word_378 v) = Some (Gval (Fuint 4) (word_378 v)).
Proof. unfold word_378, closed_word_378, expr_word_378, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_378.
Lemma node_word_378_value v : eval_hfexpr expr_word_378 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_378 v)).
Proof. change (eval_hfexpr expr_word_378 (closed_word_378 v) (closed_word_378 v) = Some (Gval (Fuint 4) (word_378 v))). apply closed_word_378_value. Qed.
Transparent word_379.
Lemma closed_word_379_value v : eval_hfexpr expr_word_379 (closed_word_379 v) (closed_word_379 v) = Some (Gval (Fuint 8) (word_379 v)).
Proof. unfold word_379, closed_word_379, expr_word_379, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_379.
Lemma node_word_379_value v : eval_hfexpr expr_word_379 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_379 v)).
Proof. change (eval_hfexpr expr_word_379 (closed_word_379 v) (closed_word_379 v) = Some (Gval (Fuint 8) (word_379 v))). apply closed_word_379_value. Qed.
Transparent word_380.
Lemma closed_word_380_value v : eval_hfexpr expr_word_380 (closed_word_380 v) (closed_word_380 v) = Some (Gval (Fuint 2) (word_380 v)).
Proof. unfold word_380, closed_word_380, expr_word_380, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_380.
Lemma node_word_380_value v : eval_hfexpr expr_word_380 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_380 v)).
Proof. change (eval_hfexpr expr_word_380 (closed_word_380 v) (closed_word_380 v) = Some (Gval (Fuint 2) (word_380 v))). apply closed_word_380_value. Qed.
Transparent word_381.
Lemma closed_word_381_value v : eval_hfexpr expr_word_381 (closed_word_381 v) (closed_word_381 v) = Some (Gval (Fuint 2) (word_381 v)).
Proof. unfold word_381, closed_word_381, expr_word_381, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_381.
Lemma node_word_381_value v : eval_hfexpr expr_word_381 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_381 v)).
Proof. change (eval_hfexpr expr_word_381 (closed_word_381 v) (closed_word_381 v) = Some (Gval (Fuint 2) (word_381 v))). apply closed_word_381_value. Qed.
Transparent word_382.
Lemma closed_word_382_value v : eval_hfexpr expr_word_382 (closed_word_382 v) (closed_word_382 v) = Some (Gval (Fuint 4) (word_382 v)).
Proof. unfold word_382, closed_word_382, expr_word_382, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_382.
Lemma node_word_382_value v : eval_hfexpr expr_word_382 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_382 v)).
Proof. change (eval_hfexpr expr_word_382 (closed_word_382 v) (closed_word_382 v) = Some (Gval (Fuint 4) (word_382 v))). apply closed_word_382_value. Qed.
Transparent word_383.
Lemma closed_word_383_value v : eval_hfexpr expr_word_383 (closed_word_383 v) (closed_word_383 v) = Some (Gval (Fuint 2) (word_383 v)).
Proof. unfold word_383, closed_word_383, expr_word_383, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_383.
Lemma node_word_383_value v : eval_hfexpr expr_word_383 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_383 v)).
Proof. change (eval_hfexpr expr_word_383 (closed_word_383 v) (closed_word_383 v) = Some (Gval (Fuint 2) (word_383 v))). apply closed_word_383_value. Qed.
Transparent word_384.
Lemma closed_word_384_value v : eval_hfexpr expr_word_384 (closed_word_384 v) (closed_word_384 v) = Some (Gval (Fuint 2) (word_384 v)).
Proof. unfold word_384, closed_word_384, expr_word_384, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_384.
Lemma node_word_384_value v : eval_hfexpr expr_word_384 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_384 v)).
Proof. change (eval_hfexpr expr_word_384 (closed_word_384 v) (closed_word_384 v) = Some (Gval (Fuint 2) (word_384 v))). apply closed_word_384_value. Qed.
Transparent word_385.
Lemma closed_word_385_value v : eval_hfexpr expr_word_385 (closed_word_385 v) (closed_word_385 v) = Some (Gval (Fuint 4) (word_385 v)).
Proof. unfold word_385, closed_word_385, expr_word_385, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_385.
Lemma node_word_385_value v : eval_hfexpr expr_word_385 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_385 v)).
Proof. change (eval_hfexpr expr_word_385 (closed_word_385 v) (closed_word_385 v) = Some (Gval (Fuint 4) (word_385 v))). apply closed_word_385_value. Qed.
Transparent word_386.
Lemma closed_word_386_value v : eval_hfexpr expr_word_386 (closed_word_386 v) (closed_word_386 v) = Some (Gval (Fuint 8) (word_386 v)).
Proof. unfold word_386, closed_word_386, expr_word_386, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_386.
Lemma node_word_386_value v : eval_hfexpr expr_word_386 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_386 v)).
Proof. change (eval_hfexpr expr_word_386 (closed_word_386 v) (closed_word_386 v) = Some (Gval (Fuint 8) (word_386 v))). apply closed_word_386_value. Qed.
Transparent word_387.
Lemma closed_word_387_value v : eval_hfexpr expr_word_387 (closed_word_387 v) (closed_word_387 v) = Some (Gval (Fuint 16) (word_387 v)).
Proof. unfold word_387, closed_word_387, expr_word_387, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_387.
Lemma node_word_387_value v : eval_hfexpr expr_word_387 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_387 v)).
Proof. change (eval_hfexpr expr_word_387 (closed_word_387 v) (closed_word_387 v) = Some (Gval (Fuint 16) (word_387 v))). apply closed_word_387_value. Qed.
Transparent word_388.
Lemma closed_word_388_value v : eval_hfexpr expr_word_388 (closed_word_388 v) (closed_word_388 v) = Some (Gval (Fuint 2) (word_388 v)).
Proof. unfold word_388, closed_word_388, expr_word_388, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_388.
Lemma node_word_388_value v : eval_hfexpr expr_word_388 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_388 v)).
Proof. change (eval_hfexpr expr_word_388 (closed_word_388 v) (closed_word_388 v) = Some (Gval (Fuint 2) (word_388 v))). apply closed_word_388_value. Qed.
Transparent word_389.
Lemma closed_word_389_value v : eval_hfexpr expr_word_389 (closed_word_389 v) (closed_word_389 v) = Some (Gval (Fuint 3) (word_389 v)).
Proof. unfold word_389, closed_word_389, expr_word_389, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_389.
Lemma node_word_389_value v : eval_hfexpr expr_word_389 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_389 v)).
Proof. change (eval_hfexpr expr_word_389 (closed_word_389 v) (closed_word_389 v) = Some (Gval (Fuint 3) (word_389 v))). apply closed_word_389_value. Qed.
Transparent word_390.
Lemma closed_word_390_value v : eval_hfexpr expr_word_390 (closed_word_390 v) (closed_word_390 v) = Some (Gval (Fuint 2) (word_390 v)).
Proof. unfold word_390, closed_word_390, expr_word_390, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_390.
Lemma node_word_390_value v : eval_hfexpr expr_word_390 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_390 v)).
Proof. change (eval_hfexpr expr_word_390 (closed_word_390 v) (closed_word_390 v) = Some (Gval (Fuint 2) (word_390 v))). apply closed_word_390_value. Qed.
Transparent word_391.
Lemma closed_word_391_value v : eval_hfexpr expr_word_391 (closed_word_391 v) (closed_word_391 v) = Some (Gval (Fuint 2) (word_391 v)).
Proof. unfold word_391, closed_word_391, expr_word_391, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_391.
Lemma node_word_391_value v : eval_hfexpr expr_word_391 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_391 v)).
Proof. change (eval_hfexpr expr_word_391 (closed_word_391 v) (closed_word_391 v) = Some (Gval (Fuint 2) (word_391 v))). apply closed_word_391_value. Qed.
Transparent word_392.
Lemma closed_word_392_value v : eval_hfexpr expr_word_392 (closed_word_392 v) (closed_word_392 v) = Some (Gval (Fuint 4) (word_392 v)).
Proof. unfold word_392, closed_word_392, expr_word_392, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_392.
Lemma node_word_392_value v : eval_hfexpr expr_word_392 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_392 v)).
Proof. change (eval_hfexpr expr_word_392 (closed_word_392 v) (closed_word_392 v) = Some (Gval (Fuint 4) (word_392 v))). apply closed_word_392_value. Qed.
Transparent word_393.
Lemma closed_word_393_value v : eval_hfexpr expr_word_393 (closed_word_393 v) (closed_word_393 v) = Some (Gval (Fuint 7) (word_393 v)).
Proof. unfold word_393, closed_word_393, expr_word_393, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_393.
Lemma node_word_393_value v : eval_hfexpr expr_word_393 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_393 v)).
Proof. change (eval_hfexpr expr_word_393 (closed_word_393 v) (closed_word_393 v) = Some (Gval (Fuint 7) (word_393 v))). apply closed_word_393_value. Qed.
Transparent word_394.
Lemma closed_word_394_value v : eval_hfexpr expr_word_394 (closed_word_394 v) (closed_word_394 v) = Some (Gval (Fuint 2) (word_394 v)).
Proof. unfold word_394, closed_word_394, expr_word_394, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_394.
Lemma node_word_394_value v : eval_hfexpr expr_word_394 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_394 v)).
Proof. change (eval_hfexpr expr_word_394 (closed_word_394 v) (closed_word_394 v) = Some (Gval (Fuint 2) (word_394 v))). apply closed_word_394_value. Qed.
Transparent word_395.
Lemma closed_word_395_value v : eval_hfexpr expr_word_395 (closed_word_395 v) (closed_word_395 v) = Some (Gval (Fuint 3) (word_395 v)).
Proof. unfold word_395, closed_word_395, expr_word_395, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_395.
Lemma node_word_395_value v : eval_hfexpr expr_word_395 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_395 v)).
Proof. change (eval_hfexpr expr_word_395 (closed_word_395 v) (closed_word_395 v) = Some (Gval (Fuint 3) (word_395 v))). apply closed_word_395_value. Qed.
Transparent word_396.
Lemma closed_word_396_value v : eval_hfexpr expr_word_396 (closed_word_396 v) (closed_word_396 v) = Some (Gval (Fuint 2) (word_396 v)).
Proof. unfold word_396, closed_word_396, expr_word_396, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_396.
Lemma node_word_396_value v : eval_hfexpr expr_word_396 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_396 v)).
Proof. change (eval_hfexpr expr_word_396 (closed_word_396 v) (closed_word_396 v) = Some (Gval (Fuint 2) (word_396 v))). apply closed_word_396_value. Qed.
Transparent word_397.
Lemma closed_word_397_value v : eval_hfexpr expr_word_397 (closed_word_397 v) (closed_word_397 v) = Some (Gval (Fuint 2) (word_397 v)).
Proof. unfold word_397, closed_word_397, expr_word_397, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_397.
Lemma node_word_397_value v : eval_hfexpr expr_word_397 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_397 v)).
Proof. change (eval_hfexpr expr_word_397 (closed_word_397 v) (closed_word_397 v) = Some (Gval (Fuint 2) (word_397 v))). apply closed_word_397_value. Qed.
Transparent word_398.
Lemma closed_word_398_value v : eval_hfexpr expr_word_398 (closed_word_398 v) (closed_word_398 v) = Some (Gval (Fuint 4) (word_398 v)).
Proof. unfold word_398, closed_word_398, expr_word_398, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_398.
Lemma node_word_398_value v : eval_hfexpr expr_word_398 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_398 v)).
Proof. change (eval_hfexpr expr_word_398 (closed_word_398 v) (closed_word_398 v) = Some (Gval (Fuint 4) (word_398 v))). apply closed_word_398_value. Qed.
Transparent word_399.
Lemma closed_word_399_value v : eval_hfexpr expr_word_399 (closed_word_399 v) (closed_word_399 v) = Some (Gval (Fuint 7) (word_399 v)).
Proof. unfold word_399, closed_word_399, expr_word_399, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_399.
Lemma node_word_399_value v : eval_hfexpr expr_word_399 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_399 v)).
Proof. change (eval_hfexpr expr_word_399 (closed_word_399 v) (closed_word_399 v) = Some (Gval (Fuint 7) (word_399 v))). apply closed_word_399_value. Qed.
Transparent word_400.
Lemma closed_word_400_value v : eval_hfexpr expr_word_400 (closed_word_400 v) (closed_word_400 v) = Some (Gval (Fuint 14) (word_400 v)).
Proof. unfold word_400, closed_word_400, expr_word_400, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_400.
Lemma node_word_400_value v : eval_hfexpr expr_word_400 (stable_env v) (stable_env v) = Some (Gval (Fuint 14) (word_400 v)).
Proof. change (eval_hfexpr expr_word_400 (closed_word_400 v) (closed_word_400 v) = Some (Gval (Fuint 14) (word_400 v))). apply closed_word_400_value. Qed.
Transparent word_401.
Lemma closed_word_401_value v : eval_hfexpr expr_word_401 (closed_word_401 v) (closed_word_401 v) = Some (Gval (Fuint 16) (word_401 v)).
Proof. unfold word_401, closed_word_401, expr_word_401, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_401.
Lemma node_word_401_value v : eval_hfexpr expr_word_401 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_401 v)).
Proof. change (eval_hfexpr expr_word_401 (closed_word_401 v) (closed_word_401 v) = Some (Gval (Fuint 16) (word_401 v))). apply closed_word_401_value. Qed.
Transparent word_402.
Lemma closed_word_402_value v : eval_hfexpr expr_word_402 (closed_word_402 v) (closed_word_402 v) = Some (Gval (Fuint 17) (word_402 v)).
Proof. unfold word_402, closed_word_402, expr_word_402, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_402.
Lemma node_word_402_value v : eval_hfexpr expr_word_402 (stable_env v) (stable_env v) = Some (Gval (Fuint 17) (word_402 v)).
Proof. change (eval_hfexpr expr_word_402 (closed_word_402 v) (closed_word_402 v) = Some (Gval (Fuint 17) (word_402 v))). apply closed_word_402_value. Qed.
Transparent word_403.
Lemma closed_word_403_value v : eval_hfexpr expr_word_403 (closed_word_403 v) (closed_word_403 v) = Some (Gval (Fuint 16) (word_403 v)).
Proof. unfold word_403, closed_word_403, expr_word_403, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_403.
Lemma node_word_403_value v : eval_hfexpr expr_word_403 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_403 v)).
Proof. change (eval_hfexpr expr_word_403 (closed_word_403 v) (closed_word_403 v) = Some (Gval (Fuint 16) (word_403 v))). apply closed_word_403_value. Qed.
Transparent word_404.
Lemma closed_word_404_value v : eval_hfexpr expr_word_404 (closed_word_404 v) (closed_word_404 v) = Some (Gval (Fsint 8) (word_404 v)).
Proof. unfold word_404, closed_word_404, expr_word_404, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_404.
Lemma node_word_404_value v : eval_hfexpr expr_word_404 (stable_env v) (stable_env v) = Some (Gval (Fsint 8) (word_404 v)).
Proof. change (eval_hfexpr expr_word_404 (closed_word_404 v) (closed_word_404 v) = Some (Gval (Fsint 8) (word_404 v))). apply closed_word_404_value. Qed.
Transparent word_405.
Lemma closed_word_405_value v : eval_hfexpr expr_word_405 (closed_word_405 v) (closed_word_405 v) = Some (Gval (Fsint 8) (word_405 v)).
Proof. unfold word_405, closed_word_405, expr_word_405, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_405.
Lemma node_word_405_value v : eval_hfexpr expr_word_405 (stable_env v) (stable_env v) = Some (Gval (Fsint 8) (word_405 v)).
Proof. change (eval_hfexpr expr_word_405 (closed_word_405 v) (closed_word_405 v) = Some (Gval (Fsint 8) (word_405 v))). apply closed_word_405_value. Qed.
Transparent word_406.
Lemma closed_word_406_value v : eval_hfexpr expr_word_406 (closed_word_406 v) (closed_word_406 v) = Some (Gval (Fsint 16) (word_406 v)).
Proof. unfold word_406, closed_word_406, expr_word_406, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_406.
Lemma node_word_406_value v : eval_hfexpr expr_word_406 (stable_env v) (stable_env v) = Some (Gval (Fsint 16) (word_406 v)).
Proof. change (eval_hfexpr expr_word_406 (closed_word_406 v) (closed_word_406 v) = Some (Gval (Fsint 16) (word_406 v))). apply closed_word_406_value. Qed.
Transparent word_407.
Lemma closed_word_407_value v : eval_hfexpr expr_word_407 (closed_word_407 v) (closed_word_407 v) = Some (Gval (Fuint 16) (word_407 v)).
Proof. unfold word_407, closed_word_407, expr_word_407, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_407.
Lemma node_word_407_value v : eval_hfexpr expr_word_407 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_407 v)).
Proof. change (eval_hfexpr expr_word_407 (closed_word_407 v) (closed_word_407 v) = Some (Gval (Fuint 16) (word_407 v))). apply closed_word_407_value. Qed.
Transparent word_409.
Lemma closed_word_409_value v : eval_hfexpr expr_word_409 (closed_word_409 v) (closed_word_409 v) = Some (Gval (Fuint 16) (word_409 v)).
Proof. unfold word_409, closed_word_409, expr_word_409, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_409.
Lemma node_word_409_value v : eval_hfexpr expr_word_409 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_409 v)).
Proof. change (eval_hfexpr expr_word_409 (closed_word_409 v) (closed_word_409 v) = Some (Gval (Fuint 16) (word_409 v))). apply closed_word_409_value. Qed.
Transparent word_411.
Lemma closed_word_411_value v : eval_hfexpr expr_word_411 (closed_word_411 v) (closed_word_411 v) = Some (Gval (Fuint 1) (word_411 v)).
Proof. unfold word_411, closed_word_411, expr_word_411, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_411.
Lemma node_word_411_value v : eval_hfexpr expr_word_411 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_411 v)).
Proof. change (eval_hfexpr expr_word_411 (closed_word_411 v) (closed_word_411 v) = Some (Gval (Fuint 1) (word_411 v))). apply closed_word_411_value. Qed.
Transparent word_6.
Lemma closed_word_6_value v : eval_hfexpr expr_word_6 (closed_word_6 v) (closed_word_6 v) = Some (Gval (Fuint 16) (word_6 v)).
Proof. unfold word_6, closed_word_6, expr_word_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_6.
Lemma node_word_6_value v : eval_hfexpr expr_word_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_6 v)).
Proof. change (eval_hfexpr expr_word_6 (closed_word_6 v) (closed_word_6 v) = Some (Gval (Fuint 16) (word_6 v))). apply closed_word_6_value. Qed.
Transparent word_412.
Lemma closed_word_412_value v : eval_hfexpr expr_word_412 (closed_word_412 v) (closed_word_412 v) = Some (Gval (Fuint 1) (word_412 v)).
Proof. unfold word_412, closed_word_412, expr_word_412, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_412.
Lemma node_word_412_value v : eval_hfexpr expr_word_412 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_412 v)).
Proof. change (eval_hfexpr expr_word_412 (closed_word_412 v) (closed_word_412 v) = Some (Gval (Fuint 1) (word_412 v))). apply closed_word_412_value. Qed.
Transparent word_413.
Lemma closed_word_413_value v : eval_hfexpr expr_word_413 (closed_word_413 v) (closed_word_413 v) = Some (Gval (Fuint 1) (word_413 v)).
Proof. unfold word_413, closed_word_413, expr_word_413, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_413.
Lemma node_word_413_value v : eval_hfexpr expr_word_413 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_413 v)).
Proof. change (eval_hfexpr expr_word_413 (closed_word_413 v) (closed_word_413 v) = Some (Gval (Fuint 1) (word_413 v))). apply closed_word_413_value. Qed.
Transparent word_414.
Lemma closed_word_414_value v : eval_hfexpr expr_word_414 (closed_word_414 v) (closed_word_414 v) = Some (Gval (Fuint 1) (word_414 v)).
Proof. unfold word_414, closed_word_414, expr_word_414, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_414.
Lemma node_word_414_value v : eval_hfexpr expr_word_414 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_414 v)).
Proof. change (eval_hfexpr expr_word_414 (closed_word_414 v) (closed_word_414 v) = Some (Gval (Fuint 1) (word_414 v))). apply closed_word_414_value. Qed.
Transparent word_415.
Lemma closed_word_415_value v : eval_hfexpr expr_word_415 (closed_word_415 v) (closed_word_415 v) = Some (Gval (Fuint 1) (word_415 v)).
Proof. unfold word_415, closed_word_415, expr_word_415, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_415.
Lemma node_word_415_value v : eval_hfexpr expr_word_415 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_415 v)).
Proof. change (eval_hfexpr expr_word_415 (closed_word_415 v) (closed_word_415 v) = Some (Gval (Fuint 1) (word_415 v))). apply closed_word_415_value. Qed.
Transparent word_417.
Lemma closed_word_417_value v : eval_hfexpr expr_word_417 (closed_word_417 v) (closed_word_417 v) = Some (Gval (Fuint 1) (word_417 v)).
Proof. unfold word_417, closed_word_417, expr_word_417, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_417.
Lemma node_word_417_value v : eval_hfexpr expr_word_417 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_417 v)).
Proof. change (eval_hfexpr expr_word_417 (closed_word_417 v) (closed_word_417 v) = Some (Gval (Fuint 1) (word_417 v))). apply closed_word_417_value. Qed.
Transparent word_418.
Lemma closed_word_418_value v : eval_hfexpr expr_word_418 (closed_word_418 v) (closed_word_418 v) = Some (Gval (Fuint 1) (word_418 v)).
Proof. unfold word_418, closed_word_418, expr_word_418, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_418.
Lemma node_word_418_value v : eval_hfexpr expr_word_418 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_418 v)).
Proof. change (eval_hfexpr expr_word_418 (closed_word_418 v) (closed_word_418 v) = Some (Gval (Fuint 1) (word_418 v))). apply closed_word_418_value. Qed.
Transparent word_420.
Lemma closed_word_420_value v : eval_hfexpr expr_word_420 (closed_word_420 v) (closed_word_420 v) = Some (Gval (Fuint 1) (word_420 v)).
Proof. unfold word_420, closed_word_420, expr_word_420, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_420.
Lemma node_word_420_value v : eval_hfexpr expr_word_420 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_420 v)).
Proof. change (eval_hfexpr expr_word_420 (closed_word_420 v) (closed_word_420 v) = Some (Gval (Fuint 1) (word_420 v))). apply closed_word_420_value. Qed.
Transparent word_421.
Lemma closed_word_421_value v : eval_hfexpr expr_word_421 (closed_word_421 v) (closed_word_421 v) = Some (Gval (Fuint 1) (word_421 v)).
Proof. unfold word_421, closed_word_421, expr_word_421, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_421.
Lemma node_word_421_value v : eval_hfexpr expr_word_421 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_421 v)).
Proof. change (eval_hfexpr expr_word_421 (closed_word_421 v) (closed_word_421 v) = Some (Gval (Fuint 1) (word_421 v))). apply closed_word_421_value. Qed.
Transparent word_422.
Lemma closed_word_422_value v : eval_hfexpr expr_word_422 (closed_word_422 v) (closed_word_422 v) = Some (Gval (Fuint 1) (word_422 v)).
Proof. unfold word_422, closed_word_422, expr_word_422, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_422.
Lemma node_word_422_value v : eval_hfexpr expr_word_422 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_422 v)).
Proof. change (eval_hfexpr expr_word_422 (closed_word_422 v) (closed_word_422 v) = Some (Gval (Fuint 1) (word_422 v))). apply closed_word_422_value. Qed.
Transparent word_423.
Lemma closed_word_423_value v : eval_hfexpr expr_word_423 (closed_word_423 v) (closed_word_423 v) = Some (Gval (Fuint 1) (word_423 v)).
Proof. unfold word_423, closed_word_423, expr_word_423, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_423.
Lemma node_word_423_value v : eval_hfexpr expr_word_423 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_423 v)).
Proof. change (eval_hfexpr expr_word_423 (closed_word_423 v) (closed_word_423 v) = Some (Gval (Fuint 1) (word_423 v))). apply closed_word_423_value. Qed.
Transparent port_7_0.
Lemma closed_port_7_0_value v : eval_hfexpr expr_port_7_0 (closed_port_7_0 v) (closed_port_7_0 v) = Some (Gval Fclock (port_7_0 v)).
Proof. unfold port_7_0, closed_port_7_0, expr_port_7_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_7_0.
Lemma node_port_7_0_value v : eval_hfexpr expr_port_7_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_7_0 v)).
Proof. change (eval_hfexpr expr_port_7_0 (closed_port_7_0 v) (closed_port_7_0 v) = Some (Gval Fclock (port_7_0 v))). apply closed_port_7_0_value. Qed.
Transparent port_7_1.
Lemma closed_port_7_1_value v : eval_hfexpr expr_port_7_1 (closed_port_7_1 v) (closed_port_7_1 v) = Some (Gval (Fuint 1) (port_7_1 v)).
Proof. unfold port_7_1, closed_port_7_1, expr_port_7_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_7_1.
Lemma node_port_7_1_value v : eval_hfexpr expr_port_7_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_7_1 v)).
Proof. change (eval_hfexpr expr_port_7_1 (closed_port_7_1 v) (closed_port_7_1 v) = Some (Gval (Fuint 1) (port_7_1 v))). apply closed_port_7_1_value. Qed.
Transparent port_7_2.
Lemma closed_port_7_2_value v : eval_hfexpr expr_port_7_2 (closed_port_7_2 v) (closed_port_7_2 v) = Some (Gval (Fuint 1) (port_7_2 v)).
Proof. unfold port_7_2, closed_port_7_2, expr_port_7_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_7_2.
Lemma node_port_7_2_value v : eval_hfexpr expr_port_7_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_7_2 v)).
Proof. change (eval_hfexpr expr_port_7_2 (closed_port_7_2 v) (closed_port_7_2 v) = Some (Gval (Fuint 1) (port_7_2 v))). apply closed_port_7_2_value. Qed.
Transparent port_7_3.
Lemma closed_port_7_3_value v : eval_hfexpr expr_port_7_3 (closed_port_7_3 v) (closed_port_7_3 v) = Some (Gval (Fuint 1) (port_7_3 v)).
Proof. unfold port_7_3, closed_port_7_3, expr_port_7_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_7_3.
Lemma node_port_7_3_value v : eval_hfexpr expr_port_7_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_7_3 v)).
Proof. change (eval_hfexpr expr_port_7_3 (closed_port_7_3 v) (closed_port_7_3 v) = Some (Gval (Fuint 1) (port_7_3 v))). apply closed_port_7_3_value. Qed.
Transparent port_8_0.
Lemma closed_port_8_0_value v : eval_hfexpr expr_port_8_0 (closed_port_8_0 v) (closed_port_8_0 v) = Some (Gval Fclock (port_8_0 v)).
Proof. unfold port_8_0, closed_port_8_0, expr_port_8_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_8_0.
Lemma node_port_8_0_value v : eval_hfexpr expr_port_8_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_8_0 v)).
Proof. change (eval_hfexpr expr_port_8_0 (closed_port_8_0 v) (closed_port_8_0 v) = Some (Gval Fclock (port_8_0 v))). apply closed_port_8_0_value. Qed.
Transparent port_8_1.
Lemma closed_port_8_1_value v : eval_hfexpr expr_port_8_1 (closed_port_8_1 v) (closed_port_8_1 v) = Some (Gval (Fuint 1) (port_8_1 v)).
Proof. unfold port_8_1, closed_port_8_1, expr_port_8_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_8_1.
Lemma node_port_8_1_value v : eval_hfexpr expr_port_8_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_8_1 v)).
Proof. change (eval_hfexpr expr_port_8_1 (closed_port_8_1 v) (closed_port_8_1 v) = Some (Gval (Fuint 1) (port_8_1 v))). apply closed_port_8_1_value. Qed.
Transparent port_8_2.
Lemma closed_port_8_2_value v : eval_hfexpr expr_port_8_2 (closed_port_8_2 v) (closed_port_8_2 v) = Some (Gval (Fuint 1) (port_8_2 v)).
Proof. unfold port_8_2, closed_port_8_2, expr_port_8_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_8_2.
Lemma node_port_8_2_value v : eval_hfexpr expr_port_8_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_8_2 v)).
Proof. change (eval_hfexpr expr_port_8_2 (closed_port_8_2 v) (closed_port_8_2 v) = Some (Gval (Fuint 1) (port_8_2 v))). apply closed_port_8_2_value. Qed.
Transparent port_8_3.
Lemma closed_port_8_3_value v : eval_hfexpr expr_port_8_3 (closed_port_8_3 v) (closed_port_8_3 v) = Some (Gval (Fuint 1) (port_8_3 v)).
Proof. unfold port_8_3, closed_port_8_3, expr_port_8_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_8_3.
Lemma node_port_8_3_value v : eval_hfexpr expr_port_8_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_8_3 v)).
Proof. change (eval_hfexpr expr_port_8_3 (closed_port_8_3 v) (closed_port_8_3 v) = Some (Gval (Fuint 1) (port_8_3 v))). apply closed_port_8_3_value. Qed.
Transparent port_9_0.
Lemma closed_port_9_0_value v : eval_hfexpr expr_port_9_0 (closed_port_9_0 v) (closed_port_9_0 v) = Some (Gval Fclock (port_9_0 v)).
Proof. unfold port_9_0, closed_port_9_0, expr_port_9_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_9_0.
Lemma node_port_9_0_value v : eval_hfexpr expr_port_9_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_9_0 v)).
Proof. change (eval_hfexpr expr_port_9_0 (closed_port_9_0 v) (closed_port_9_0 v) = Some (Gval Fclock (port_9_0 v))). apply closed_port_9_0_value. Qed.
Transparent port_9_1.
Lemma closed_port_9_1_value v : eval_hfexpr expr_port_9_1 (closed_port_9_1 v) (closed_port_9_1 v) = Some (Gval (Fuint 1) (port_9_1 v)).
Proof. unfold port_9_1, closed_port_9_1, expr_port_9_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_9_1.
Lemma node_port_9_1_value v : eval_hfexpr expr_port_9_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_9_1 v)).
Proof. change (eval_hfexpr expr_port_9_1 (closed_port_9_1 v) (closed_port_9_1 v) = Some (Gval (Fuint 1) (port_9_1 v))). apply closed_port_9_1_value. Qed.
Transparent port_9_2.
Lemma closed_port_9_2_value v : eval_hfexpr expr_port_9_2 (closed_port_9_2 v) (closed_port_9_2 v) = Some (Gval (Fuint 1) (port_9_2 v)).
Proof. unfold port_9_2, closed_port_9_2, expr_port_9_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_9_2.
Lemma node_port_9_2_value v : eval_hfexpr expr_port_9_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_9_2 v)).
Proof. change (eval_hfexpr expr_port_9_2 (closed_port_9_2 v) (closed_port_9_2 v) = Some (Gval (Fuint 1) (port_9_2 v))). apply closed_port_9_2_value. Qed.
Transparent port_9_3.
Lemma closed_port_9_3_value v : eval_hfexpr expr_port_9_3 (closed_port_9_3 v) (closed_port_9_3 v) = Some (Gval (Fuint 1) (port_9_3 v)).
Proof. unfold port_9_3, closed_port_9_3, expr_port_9_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_9_3.
Lemma node_port_9_3_value v : eval_hfexpr expr_port_9_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_9_3 v)).
Proof. change (eval_hfexpr expr_port_9_3 (closed_port_9_3 v) (closed_port_9_3 v) = Some (Gval (Fuint 1) (port_9_3 v))). apply closed_port_9_3_value. Qed.
Transparent port_9_4.
Lemma closed_port_9_4_value v : eval_hfexpr expr_port_9_4 (closed_port_9_4 v) (closed_port_9_4 v) = Some (Gval (Fuint 1) (port_9_4 v)).
Proof. unfold port_9_4, closed_port_9_4, expr_port_9_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_9_4.
Lemma node_port_9_4_value v : eval_hfexpr expr_port_9_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_9_4 v)).
Proof. change (eval_hfexpr expr_port_9_4 (closed_port_9_4 v) (closed_port_9_4 v) = Some (Gval (Fuint 1) (port_9_4 v))). apply closed_port_9_4_value. Qed.
Transparent port_10_0.
Lemma closed_port_10_0_value v : eval_hfexpr expr_port_10_0 (closed_port_10_0 v) (closed_port_10_0 v) = Some (Gval Fclock (port_10_0 v)).
Proof. unfold port_10_0, closed_port_10_0, expr_port_10_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_10_0.
Lemma node_port_10_0_value v : eval_hfexpr expr_port_10_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_10_0 v)).
Proof. change (eval_hfexpr expr_port_10_0 (closed_port_10_0 v) (closed_port_10_0 v) = Some (Gval Fclock (port_10_0 v))). apply closed_port_10_0_value. Qed.
Transparent port_10_1.
Lemma closed_port_10_1_value v : eval_hfexpr expr_port_10_1 (closed_port_10_1 v) (closed_port_10_1 v) = Some (Gval (Fuint 1) (port_10_1 v)).
Proof. unfold port_10_1, closed_port_10_1, expr_port_10_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_10_1.
Lemma node_port_10_1_value v : eval_hfexpr expr_port_10_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_10_1 v)).
Proof. change (eval_hfexpr expr_port_10_1 (closed_port_10_1 v) (closed_port_10_1 v) = Some (Gval (Fuint 1) (port_10_1 v))). apply closed_port_10_1_value. Qed.
Transparent port_10_2.
Lemma closed_port_10_2_value v : eval_hfexpr expr_port_10_2 (closed_port_10_2 v) (closed_port_10_2 v) = Some (Gval (Fuint 1) (port_10_2 v)).
Proof. unfold port_10_2, closed_port_10_2, expr_port_10_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_10_2.
Lemma node_port_10_2_value v : eval_hfexpr expr_port_10_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_10_2 v)).
Proof. change (eval_hfexpr expr_port_10_2 (closed_port_10_2 v) (closed_port_10_2 v) = Some (Gval (Fuint 1) (port_10_2 v))). apply closed_port_10_2_value. Qed.
Transparent port_10_3.
Lemma closed_port_10_3_value v : eval_hfexpr expr_port_10_3 (closed_port_10_3 v) (closed_port_10_3 v) = Some (Gval (Fuint 1) (port_10_3 v)).
Proof. unfold port_10_3, closed_port_10_3, expr_port_10_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_10_3.
Lemma node_port_10_3_value v : eval_hfexpr expr_port_10_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_10_3 v)).
Proof. change (eval_hfexpr expr_port_10_3 (closed_port_10_3 v) (closed_port_10_3 v) = Some (Gval (Fuint 1) (port_10_3 v))). apply closed_port_10_3_value. Qed.
Transparent port_10_4.
Lemma closed_port_10_4_value v : eval_hfexpr expr_port_10_4 (closed_port_10_4 v) (closed_port_10_4 v) = Some (Gval (Fuint 1) (port_10_4 v)).
Proof. unfold port_10_4, closed_port_10_4, expr_port_10_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_10_4.
Lemma node_port_10_4_value v : eval_hfexpr expr_port_10_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_10_4 v)).
Proof. change (eval_hfexpr expr_port_10_4 (closed_port_10_4 v) (closed_port_10_4 v) = Some (Gval (Fuint 1) (port_10_4 v))). apply closed_port_10_4_value. Qed.
Transparent port_11_0.
Lemma closed_port_11_0_value v : eval_hfexpr expr_port_11_0 (closed_port_11_0 v) (closed_port_11_0 v) = Some (Gval Fclock (port_11_0 v)).
Proof. unfold port_11_0, closed_port_11_0, expr_port_11_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_11_0.
Lemma node_port_11_0_value v : eval_hfexpr expr_port_11_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_11_0 v)).
Proof. change (eval_hfexpr expr_port_11_0 (closed_port_11_0 v) (closed_port_11_0 v) = Some (Gval Fclock (port_11_0 v))). apply closed_port_11_0_value. Qed.
Transparent port_11_1.
Lemma closed_port_11_1_value v : eval_hfexpr expr_port_11_1 (closed_port_11_1 v) (closed_port_11_1 v) = Some (Gval (Fuint 1) (port_11_1 v)).
Proof. unfold port_11_1, closed_port_11_1, expr_port_11_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_11_1.
Lemma node_port_11_1_value v : eval_hfexpr expr_port_11_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_11_1 v)).
Proof. change (eval_hfexpr expr_port_11_1 (closed_port_11_1 v) (closed_port_11_1 v) = Some (Gval (Fuint 1) (port_11_1 v))). apply closed_port_11_1_value. Qed.
Transparent port_11_2.
Lemma closed_port_11_2_value v : eval_hfexpr expr_port_11_2 (closed_port_11_2 v) (closed_port_11_2 v) = Some (Gval (Fuint 1) (port_11_2 v)).
Proof. unfold port_11_2, closed_port_11_2, expr_port_11_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_11_2.
Lemma node_port_11_2_value v : eval_hfexpr expr_port_11_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_11_2 v)).
Proof. change (eval_hfexpr expr_port_11_2 (closed_port_11_2 v) (closed_port_11_2 v) = Some (Gval (Fuint 1) (port_11_2 v))). apply closed_port_11_2_value. Qed.
Transparent port_11_3.
Lemma closed_port_11_3_value v : eval_hfexpr expr_port_11_3 (closed_port_11_3 v) (closed_port_11_3 v) = Some (Gval (Fuint 1) (port_11_3 v)).
Proof. unfold port_11_3, closed_port_11_3, expr_port_11_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_11_3.
Lemma node_port_11_3_value v : eval_hfexpr expr_port_11_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_11_3 v)).
Proof. change (eval_hfexpr expr_port_11_3 (closed_port_11_3 v) (closed_port_11_3 v) = Some (Gval (Fuint 1) (port_11_3 v))). apply closed_port_11_3_value. Qed.
Transparent port_11_4.
Lemma closed_port_11_4_value v : eval_hfexpr expr_port_11_4 (closed_port_11_4 v) (closed_port_11_4 v) = Some (Gval (Fuint 1) (port_11_4 v)).
Proof. unfold port_11_4, closed_port_11_4, expr_port_11_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_11_4.
Lemma node_port_11_4_value v : eval_hfexpr expr_port_11_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_11_4 v)).
Proof. change (eval_hfexpr expr_port_11_4 (closed_port_11_4 v) (closed_port_11_4 v) = Some (Gval (Fuint 1) (port_11_4 v))). apply closed_port_11_4_value. Qed.
Transparent port_11_5.
Lemma closed_port_11_5_value v : eval_hfexpr expr_port_11_5 (closed_port_11_5 v) (closed_port_11_5 v) = Some (Gval (Fuint 1) (port_11_5 v)).
Proof. unfold port_11_5, closed_port_11_5, expr_port_11_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_11_5.
Lemma node_port_11_5_value v : eval_hfexpr expr_port_11_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_11_5 v)).
Proof. change (eval_hfexpr expr_port_11_5 (closed_port_11_5 v) (closed_port_11_5 v) = Some (Gval (Fuint 1) (port_11_5 v))). apply closed_port_11_5_value. Qed.
Transparent port_11_6.
Lemma closed_port_11_6_value v : eval_hfexpr expr_port_11_6 (closed_port_11_6 v) (closed_port_11_6 v) = Some (Gval (Fuint 1) (port_11_6 v)).
Proof. unfold port_11_6, closed_port_11_6, expr_port_11_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_11_6.
Lemma node_port_11_6_value v : eval_hfexpr expr_port_11_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_11_6 v)).
Proof. change (eval_hfexpr expr_port_11_6 (closed_port_11_6 v) (closed_port_11_6 v) = Some (Gval (Fuint 1) (port_11_6 v))). apply closed_port_11_6_value. Qed.
Transparent port_12_0.
Lemma closed_port_12_0_value v : eval_hfexpr expr_port_12_0 (closed_port_12_0 v) (closed_port_12_0 v) = Some (Gval Fclock (port_12_0 v)).
Proof. unfold port_12_0, closed_port_12_0, expr_port_12_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_12_0.
Lemma node_port_12_0_value v : eval_hfexpr expr_port_12_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_12_0 v)).
Proof. change (eval_hfexpr expr_port_12_0 (closed_port_12_0 v) (closed_port_12_0 v) = Some (Gval Fclock (port_12_0 v))). apply closed_port_12_0_value. Qed.
Transparent port_12_1.
Lemma closed_port_12_1_value v : eval_hfexpr expr_port_12_1 (closed_port_12_1 v) (closed_port_12_1 v) = Some (Gval (Fuint 1) (port_12_1 v)).
Proof. unfold port_12_1, closed_port_12_1, expr_port_12_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_12_1.
Lemma node_port_12_1_value v : eval_hfexpr expr_port_12_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_12_1 v)).
Proof. change (eval_hfexpr expr_port_12_1 (closed_port_12_1 v) (closed_port_12_1 v) = Some (Gval (Fuint 1) (port_12_1 v))). apply closed_port_12_1_value. Qed.
Transparent port_12_2.
Lemma closed_port_12_2_value v : eval_hfexpr expr_port_12_2 (closed_port_12_2 v) (closed_port_12_2 v) = Some (Gval (Fuint 1) (port_12_2 v)).
Proof. unfold port_12_2, closed_port_12_2, expr_port_12_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_12_2.
Lemma node_port_12_2_value v : eval_hfexpr expr_port_12_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_12_2 v)).
Proof. change (eval_hfexpr expr_port_12_2 (closed_port_12_2 v) (closed_port_12_2 v) = Some (Gval (Fuint 1) (port_12_2 v))). apply closed_port_12_2_value. Qed.
Transparent port_12_3.
Lemma closed_port_12_3_value v : eval_hfexpr expr_port_12_3 (closed_port_12_3 v) (closed_port_12_3 v) = Some (Gval (Fuint 1) (port_12_3 v)).
Proof. unfold port_12_3, closed_port_12_3, expr_port_12_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_12_3.
Lemma node_port_12_3_value v : eval_hfexpr expr_port_12_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_12_3 v)).
Proof. change (eval_hfexpr expr_port_12_3 (closed_port_12_3 v) (closed_port_12_3 v) = Some (Gval (Fuint 1) (port_12_3 v))). apply closed_port_12_3_value. Qed.
Transparent port_12_4.
Lemma closed_port_12_4_value v : eval_hfexpr expr_port_12_4 (closed_port_12_4 v) (closed_port_12_4 v) = Some (Gval (Fuint 1) (port_12_4 v)).
Proof. unfold port_12_4, closed_port_12_4, expr_port_12_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_12_4.
Lemma node_port_12_4_value v : eval_hfexpr expr_port_12_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_12_4 v)).
Proof. change (eval_hfexpr expr_port_12_4 (closed_port_12_4 v) (closed_port_12_4 v) = Some (Gval (Fuint 1) (port_12_4 v))). apply closed_port_12_4_value. Qed.
Transparent port_12_5.
Lemma closed_port_12_5_value v : eval_hfexpr expr_port_12_5 (closed_port_12_5 v) (closed_port_12_5 v) = Some (Gval (Fuint 1) (port_12_5 v)).
Proof. unfold port_12_5, closed_port_12_5, expr_port_12_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_12_5.
Lemma node_port_12_5_value v : eval_hfexpr expr_port_12_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_12_5 v)).
Proof. change (eval_hfexpr expr_port_12_5 (closed_port_12_5 v) (closed_port_12_5 v) = Some (Gval (Fuint 1) (port_12_5 v))). apply closed_port_12_5_value. Qed.
Transparent port_12_6.
Lemma closed_port_12_6_value v : eval_hfexpr expr_port_12_6 (closed_port_12_6 v) (closed_port_12_6 v) = Some (Gval (Fuint 1) (port_12_6 v)).
Proof. unfold port_12_6, closed_port_12_6, expr_port_12_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_12_6.
Lemma node_port_12_6_value v : eval_hfexpr expr_port_12_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_12_6 v)).
Proof. change (eval_hfexpr expr_port_12_6 (closed_port_12_6 v) (closed_port_12_6 v) = Some (Gval (Fuint 1) (port_12_6 v))). apply closed_port_12_6_value. Qed.
Transparent port_13_0.
Lemma closed_port_13_0_value v : eval_hfexpr expr_port_13_0 (closed_port_13_0 v) (closed_port_13_0 v) = Some (Gval Fclock (port_13_0 v)).
Proof. unfold port_13_0, closed_port_13_0, expr_port_13_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_13_0.
Lemma node_port_13_0_value v : eval_hfexpr expr_port_13_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_13_0 v)).
Proof. change (eval_hfexpr expr_port_13_0 (closed_port_13_0 v) (closed_port_13_0 v) = Some (Gval Fclock (port_13_0 v))). apply closed_port_13_0_value. Qed.
Transparent port_13_1.
Lemma closed_port_13_1_value v : eval_hfexpr expr_port_13_1 (closed_port_13_1 v) (closed_port_13_1 v) = Some (Gval (Fuint 1) (port_13_1 v)).
Proof. unfold port_13_1, closed_port_13_1, expr_port_13_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_13_1.
Lemma node_port_13_1_value v : eval_hfexpr expr_port_13_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_13_1 v)).
Proof. change (eval_hfexpr expr_port_13_1 (closed_port_13_1 v) (closed_port_13_1 v) = Some (Gval (Fuint 1) (port_13_1 v))). apply closed_port_13_1_value. Qed.
Transparent port_13_2.
Lemma closed_port_13_2_value v : eval_hfexpr expr_port_13_2 (closed_port_13_2 v) (closed_port_13_2 v) = Some (Gval (Fuint 1) (port_13_2 v)).
Proof. unfold port_13_2, closed_port_13_2, expr_port_13_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_13_2.
Lemma node_port_13_2_value v : eval_hfexpr expr_port_13_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_13_2 v)).
Proof. change (eval_hfexpr expr_port_13_2 (closed_port_13_2 v) (closed_port_13_2 v) = Some (Gval (Fuint 1) (port_13_2 v))). apply closed_port_13_2_value. Qed.
Transparent port_13_3.
Lemma closed_port_13_3_value v : eval_hfexpr expr_port_13_3 (closed_port_13_3 v) (closed_port_13_3 v) = Some (Gval (Fuint 1) (port_13_3 v)).
Proof. unfold port_13_3, closed_port_13_3, expr_port_13_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_13_3.
Lemma node_port_13_3_value v : eval_hfexpr expr_port_13_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_13_3 v)).
Proof. change (eval_hfexpr expr_port_13_3 (closed_port_13_3 v) (closed_port_13_3 v) = Some (Gval (Fuint 1) (port_13_3 v))). apply closed_port_13_3_value. Qed.
Transparent port_13_4.
Lemma closed_port_13_4_value v : eval_hfexpr expr_port_13_4 (closed_port_13_4 v) (closed_port_13_4 v) = Some (Gval (Fuint 1) (port_13_4 v)).
Proof. unfold port_13_4, closed_port_13_4, expr_port_13_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_13_4.
Lemma node_port_13_4_value v : eval_hfexpr expr_port_13_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_13_4 v)).
Proof. change (eval_hfexpr expr_port_13_4 (closed_port_13_4 v) (closed_port_13_4 v) = Some (Gval (Fuint 1) (port_13_4 v))). apply closed_port_13_4_value. Qed.
Transparent port_13_5.
Lemma closed_port_13_5_value v : eval_hfexpr expr_port_13_5 (closed_port_13_5 v) (closed_port_13_5 v) = Some (Gval (Fuint 1) (port_13_5 v)).
Proof. unfold port_13_5, closed_port_13_5, expr_port_13_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_13_5.
Lemma node_port_13_5_value v : eval_hfexpr expr_port_13_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_13_5 v)).
Proof. change (eval_hfexpr expr_port_13_5 (closed_port_13_5 v) (closed_port_13_5 v) = Some (Gval (Fuint 1) (port_13_5 v))). apply closed_port_13_5_value. Qed.
Transparent port_13_6.
Lemma closed_port_13_6_value v : eval_hfexpr expr_port_13_6 (closed_port_13_6 v) (closed_port_13_6 v) = Some (Gval (Fuint 1) (port_13_6 v)).
Proof. unfold port_13_6, closed_port_13_6, expr_port_13_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_13_6.
Lemma node_port_13_6_value v : eval_hfexpr expr_port_13_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_13_6 v)).
Proof. change (eval_hfexpr expr_port_13_6 (closed_port_13_6 v) (closed_port_13_6 v) = Some (Gval (Fuint 1) (port_13_6 v))). apply closed_port_13_6_value. Qed.
Transparent port_14_0.
Lemma closed_port_14_0_value v : eval_hfexpr expr_port_14_0 (closed_port_14_0 v) (closed_port_14_0 v) = Some (Gval Fclock (port_14_0 v)).
Proof. unfold port_14_0, closed_port_14_0, expr_port_14_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_14_0.
Lemma node_port_14_0_value v : eval_hfexpr expr_port_14_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_14_0 v)).
Proof. change (eval_hfexpr expr_port_14_0 (closed_port_14_0 v) (closed_port_14_0 v) = Some (Gval Fclock (port_14_0 v))). apply closed_port_14_0_value. Qed.
Transparent port_14_1.
Lemma closed_port_14_1_value v : eval_hfexpr expr_port_14_1 (closed_port_14_1 v) (closed_port_14_1 v) = Some (Gval (Fuint 1) (port_14_1 v)).
Proof. unfold port_14_1, closed_port_14_1, expr_port_14_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_14_1.
Lemma node_port_14_1_value v : eval_hfexpr expr_port_14_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_14_1 v)).
Proof. change (eval_hfexpr expr_port_14_1 (closed_port_14_1 v) (closed_port_14_1 v) = Some (Gval (Fuint 1) (port_14_1 v))). apply closed_port_14_1_value. Qed.
Transparent port_14_2.
Lemma closed_port_14_2_value v : eval_hfexpr expr_port_14_2 (closed_port_14_2 v) (closed_port_14_2 v) = Some (Gval (Fuint 1) (port_14_2 v)).
Proof. unfold port_14_2, closed_port_14_2, expr_port_14_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_14_2.
Lemma node_port_14_2_value v : eval_hfexpr expr_port_14_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_14_2 v)).
Proof. change (eval_hfexpr expr_port_14_2 (closed_port_14_2 v) (closed_port_14_2 v) = Some (Gval (Fuint 1) (port_14_2 v))). apply closed_port_14_2_value. Qed.
Transparent port_14_3.
Lemma closed_port_14_3_value v : eval_hfexpr expr_port_14_3 (closed_port_14_3 v) (closed_port_14_3 v) = Some (Gval (Fuint 1) (port_14_3 v)).
Proof. unfold port_14_3, closed_port_14_3, expr_port_14_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_14_3.
Lemma node_port_14_3_value v : eval_hfexpr expr_port_14_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_14_3 v)).
Proof. change (eval_hfexpr expr_port_14_3 (closed_port_14_3 v) (closed_port_14_3 v) = Some (Gval (Fuint 1) (port_14_3 v))). apply closed_port_14_3_value. Qed.
Transparent port_14_4.
Lemma closed_port_14_4_value v : eval_hfexpr expr_port_14_4 (closed_port_14_4 v) (closed_port_14_4 v) = Some (Gval (Fuint 1) (port_14_4 v)).
Proof. unfold port_14_4, closed_port_14_4, expr_port_14_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_14_4.
Lemma node_port_14_4_value v : eval_hfexpr expr_port_14_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_14_4 v)).
Proof. change (eval_hfexpr expr_port_14_4 (closed_port_14_4 v) (closed_port_14_4 v) = Some (Gval (Fuint 1) (port_14_4 v))). apply closed_port_14_4_value. Qed.
Transparent port_14_5.
Lemma closed_port_14_5_value v : eval_hfexpr expr_port_14_5 (closed_port_14_5 v) (closed_port_14_5 v) = Some (Gval (Fuint 1) (port_14_5 v)).
Proof. unfold port_14_5, closed_port_14_5, expr_port_14_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_14_5.
Lemma node_port_14_5_value v : eval_hfexpr expr_port_14_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_14_5 v)).
Proof. change (eval_hfexpr expr_port_14_5 (closed_port_14_5 v) (closed_port_14_5 v) = Some (Gval (Fuint 1) (port_14_5 v))). apply closed_port_14_5_value. Qed.
Transparent port_14_6.
Lemma closed_port_14_6_value v : eval_hfexpr expr_port_14_6 (closed_port_14_6 v) (closed_port_14_6 v) = Some (Gval (Fuint 1) (port_14_6 v)).
Proof. unfold port_14_6, closed_port_14_6, expr_port_14_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_14_6.
Lemma node_port_14_6_value v : eval_hfexpr expr_port_14_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_14_6 v)).
Proof. change (eval_hfexpr expr_port_14_6 (closed_port_14_6 v) (closed_port_14_6 v) = Some (Gval (Fuint 1) (port_14_6 v))). apply closed_port_14_6_value. Qed.
Transparent port_15_0.
Lemma closed_port_15_0_value v : eval_hfexpr expr_port_15_0 (closed_port_15_0 v) (closed_port_15_0 v) = Some (Gval Fclock (port_15_0 v)).
Proof. unfold port_15_0, closed_port_15_0, expr_port_15_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_15_0.
Lemma node_port_15_0_value v : eval_hfexpr expr_port_15_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_15_0 v)).
Proof. change (eval_hfexpr expr_port_15_0 (closed_port_15_0 v) (closed_port_15_0 v) = Some (Gval Fclock (port_15_0 v))). apply closed_port_15_0_value. Qed.
Transparent port_15_1.
Lemma closed_port_15_1_value v : eval_hfexpr expr_port_15_1 (closed_port_15_1 v) (closed_port_15_1 v) = Some (Gval (Fuint 1) (port_15_1 v)).
Proof. unfold port_15_1, closed_port_15_1, expr_port_15_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_15_1.
Lemma node_port_15_1_value v : eval_hfexpr expr_port_15_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_15_1 v)).
Proof. change (eval_hfexpr expr_port_15_1 (closed_port_15_1 v) (closed_port_15_1 v) = Some (Gval (Fuint 1) (port_15_1 v))). apply closed_port_15_1_value. Qed.
Transparent port_15_2.
Lemma closed_port_15_2_value v : eval_hfexpr expr_port_15_2 (closed_port_15_2 v) (closed_port_15_2 v) = Some (Gval (Fuint 1) (port_15_2 v)).
Proof. unfold port_15_2, closed_port_15_2, expr_port_15_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_15_2.
Lemma node_port_15_2_value v : eval_hfexpr expr_port_15_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_15_2 v)).
Proof. change (eval_hfexpr expr_port_15_2 (closed_port_15_2 v) (closed_port_15_2 v) = Some (Gval (Fuint 1) (port_15_2 v))). apply closed_port_15_2_value. Qed.
Transparent port_15_3.
Lemma closed_port_15_3_value v : eval_hfexpr expr_port_15_3 (closed_port_15_3 v) (closed_port_15_3 v) = Some (Gval (Fuint 1) (port_15_3 v)).
Proof. unfold port_15_3, closed_port_15_3, expr_port_15_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_15_3.
Lemma node_port_15_3_value v : eval_hfexpr expr_port_15_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_15_3 v)).
Proof. change (eval_hfexpr expr_port_15_3 (closed_port_15_3 v) (closed_port_15_3 v) = Some (Gval (Fuint 1) (port_15_3 v))). apply closed_port_15_3_value. Qed.
Transparent port_15_4.
Lemma closed_port_15_4_value v : eval_hfexpr expr_port_15_4 (closed_port_15_4 v) (closed_port_15_4 v) = Some (Gval (Fuint 1) (port_15_4 v)).
Proof. unfold port_15_4, closed_port_15_4, expr_port_15_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_15_4.
Lemma node_port_15_4_value v : eval_hfexpr expr_port_15_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_15_4 v)).
Proof. change (eval_hfexpr expr_port_15_4 (closed_port_15_4 v) (closed_port_15_4 v) = Some (Gval (Fuint 1) (port_15_4 v))). apply closed_port_15_4_value. Qed.
Transparent port_15_5.
Lemma closed_port_15_5_value v : eval_hfexpr expr_port_15_5 (closed_port_15_5 v) (closed_port_15_5 v) = Some (Gval (Fuint 1) (port_15_5 v)).
Proof. unfold port_15_5, closed_port_15_5, expr_port_15_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_15_5.
Lemma node_port_15_5_value v : eval_hfexpr expr_port_15_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_15_5 v)).
Proof. change (eval_hfexpr expr_port_15_5 (closed_port_15_5 v) (closed_port_15_5 v) = Some (Gval (Fuint 1) (port_15_5 v))). apply closed_port_15_5_value. Qed.
Transparent port_15_6.
Lemma closed_port_15_6_value v : eval_hfexpr expr_port_15_6 (closed_port_15_6 v) (closed_port_15_6 v) = Some (Gval (Fuint 1) (port_15_6 v)).
Proof. unfold port_15_6, closed_port_15_6, expr_port_15_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_15_6.
Lemma node_port_15_6_value v : eval_hfexpr expr_port_15_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_15_6 v)).
Proof. change (eval_hfexpr expr_port_15_6 (closed_port_15_6 v) (closed_port_15_6 v) = Some (Gval (Fuint 1) (port_15_6 v))). apply closed_port_15_6_value. Qed.
Transparent port_16_0.
Lemma closed_port_16_0_value v : eval_hfexpr expr_port_16_0 (closed_port_16_0 v) (closed_port_16_0 v) = Some (Gval Fclock (port_16_0 v)).
Proof. unfold port_16_0, closed_port_16_0, expr_port_16_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_16_0.
Lemma node_port_16_0_value v : eval_hfexpr expr_port_16_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_16_0 v)).
Proof. change (eval_hfexpr expr_port_16_0 (closed_port_16_0 v) (closed_port_16_0 v) = Some (Gval Fclock (port_16_0 v))). apply closed_port_16_0_value. Qed.
Transparent port_16_1.
Lemma closed_port_16_1_value v : eval_hfexpr expr_port_16_1 (closed_port_16_1 v) (closed_port_16_1 v) = Some (Gval (Fuint 1) (port_16_1 v)).
Proof. unfold port_16_1, closed_port_16_1, expr_port_16_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_16_1.
Lemma node_port_16_1_value v : eval_hfexpr expr_port_16_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_16_1 v)).
Proof. change (eval_hfexpr expr_port_16_1 (closed_port_16_1 v) (closed_port_16_1 v) = Some (Gval (Fuint 1) (port_16_1 v))). apply closed_port_16_1_value. Qed.
Transparent port_16_2.
Lemma closed_port_16_2_value v : eval_hfexpr expr_port_16_2 (closed_port_16_2 v) (closed_port_16_2 v) = Some (Gval (Fuint 1) (port_16_2 v)).
Proof. unfold port_16_2, closed_port_16_2, expr_port_16_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_16_2.
Lemma node_port_16_2_value v : eval_hfexpr expr_port_16_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_16_2 v)).
Proof. change (eval_hfexpr expr_port_16_2 (closed_port_16_2 v) (closed_port_16_2 v) = Some (Gval (Fuint 1) (port_16_2 v))). apply closed_port_16_2_value. Qed.
Transparent port_16_3.
Lemma closed_port_16_3_value v : eval_hfexpr expr_port_16_3 (closed_port_16_3 v) (closed_port_16_3 v) = Some (Gval (Fuint 1) (port_16_3 v)).
Proof. unfold port_16_3, closed_port_16_3, expr_port_16_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_16_3.
Lemma node_port_16_3_value v : eval_hfexpr expr_port_16_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_16_3 v)).
Proof. change (eval_hfexpr expr_port_16_3 (closed_port_16_3 v) (closed_port_16_3 v) = Some (Gval (Fuint 1) (port_16_3 v))). apply closed_port_16_3_value. Qed.
Transparent port_16_4.
Lemma closed_port_16_4_value v : eval_hfexpr expr_port_16_4 (closed_port_16_4 v) (closed_port_16_4 v) = Some (Gval (Fuint 1) (port_16_4 v)).
Proof. unfold port_16_4, closed_port_16_4, expr_port_16_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_16_4.
Lemma node_port_16_4_value v : eval_hfexpr expr_port_16_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_16_4 v)).
Proof. change (eval_hfexpr expr_port_16_4 (closed_port_16_4 v) (closed_port_16_4 v) = Some (Gval (Fuint 1) (port_16_4 v))). apply closed_port_16_4_value. Qed.
Transparent port_16_5.
Lemma closed_port_16_5_value v : eval_hfexpr expr_port_16_5 (closed_port_16_5 v) (closed_port_16_5 v) = Some (Gval (Fuint 1) (port_16_5 v)).
Proof. unfold port_16_5, closed_port_16_5, expr_port_16_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_16_5.
Lemma node_port_16_5_value v : eval_hfexpr expr_port_16_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_16_5 v)).
Proof. change (eval_hfexpr expr_port_16_5 (closed_port_16_5 v) (closed_port_16_5 v) = Some (Gval (Fuint 1) (port_16_5 v))). apply closed_port_16_5_value. Qed.
Transparent port_16_6.
Lemma closed_port_16_6_value v : eval_hfexpr expr_port_16_6 (closed_port_16_6 v) (closed_port_16_6 v) = Some (Gval (Fuint 1) (port_16_6 v)).
Proof. unfold port_16_6, closed_port_16_6, expr_port_16_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_16_6.
Lemma node_port_16_6_value v : eval_hfexpr expr_port_16_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_16_6 v)).
Proof. change (eval_hfexpr expr_port_16_6 (closed_port_16_6 v) (closed_port_16_6 v) = Some (Gval (Fuint 1) (port_16_6 v))). apply closed_port_16_6_value. Qed.
Transparent port_17_0.
Lemma closed_port_17_0_value v : eval_hfexpr expr_port_17_0 (closed_port_17_0 v) (closed_port_17_0 v) = Some (Gval Fclock (port_17_0 v)).
Proof. unfold port_17_0, closed_port_17_0, expr_port_17_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_17_0.
Lemma node_port_17_0_value v : eval_hfexpr expr_port_17_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_17_0 v)).
Proof. change (eval_hfexpr expr_port_17_0 (closed_port_17_0 v) (closed_port_17_0 v) = Some (Gval Fclock (port_17_0 v))). apply closed_port_17_0_value. Qed.
Transparent port_17_1.
Lemma closed_port_17_1_value v : eval_hfexpr expr_port_17_1 (closed_port_17_1 v) (closed_port_17_1 v) = Some (Gval (Fuint 1) (port_17_1 v)).
Proof. unfold port_17_1, closed_port_17_1, expr_port_17_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_17_1.
Lemma node_port_17_1_value v : eval_hfexpr expr_port_17_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_17_1 v)).
Proof. change (eval_hfexpr expr_port_17_1 (closed_port_17_1 v) (closed_port_17_1 v) = Some (Gval (Fuint 1) (port_17_1 v))). apply closed_port_17_1_value. Qed.
Transparent port_17_2.
Lemma closed_port_17_2_value v : eval_hfexpr expr_port_17_2 (closed_port_17_2 v) (closed_port_17_2 v) = Some (Gval (Fuint 1) (port_17_2 v)).
Proof. unfold port_17_2, closed_port_17_2, expr_port_17_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_17_2.
Lemma node_port_17_2_value v : eval_hfexpr expr_port_17_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_17_2 v)).
Proof. change (eval_hfexpr expr_port_17_2 (closed_port_17_2 v) (closed_port_17_2 v) = Some (Gval (Fuint 1) (port_17_2 v))). apply closed_port_17_2_value. Qed.
Transparent port_17_3.
Lemma closed_port_17_3_value v : eval_hfexpr expr_port_17_3 (closed_port_17_3 v) (closed_port_17_3 v) = Some (Gval (Fuint 1) (port_17_3 v)).
Proof. unfold port_17_3, closed_port_17_3, expr_port_17_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_17_3.
Lemma node_port_17_3_value v : eval_hfexpr expr_port_17_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_17_3 v)).
Proof. change (eval_hfexpr expr_port_17_3 (closed_port_17_3 v) (closed_port_17_3 v) = Some (Gval (Fuint 1) (port_17_3 v))). apply closed_port_17_3_value. Qed.
Transparent port_17_4.
Lemma closed_port_17_4_value v : eval_hfexpr expr_port_17_4 (closed_port_17_4 v) (closed_port_17_4 v) = Some (Gval (Fuint 1) (port_17_4 v)).
Proof. unfold port_17_4, closed_port_17_4, expr_port_17_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_17_4.
Lemma node_port_17_4_value v : eval_hfexpr expr_port_17_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_17_4 v)).
Proof. change (eval_hfexpr expr_port_17_4 (closed_port_17_4 v) (closed_port_17_4 v) = Some (Gval (Fuint 1) (port_17_4 v))). apply closed_port_17_4_value. Qed.
Transparent port_17_5.
Lemma closed_port_17_5_value v : eval_hfexpr expr_port_17_5 (closed_port_17_5 v) (closed_port_17_5 v) = Some (Gval (Fuint 1) (port_17_5 v)).
Proof. unfold port_17_5, closed_port_17_5, expr_port_17_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_17_5.
Lemma node_port_17_5_value v : eval_hfexpr expr_port_17_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_17_5 v)).
Proof. change (eval_hfexpr expr_port_17_5 (closed_port_17_5 v) (closed_port_17_5 v) = Some (Gval (Fuint 1) (port_17_5 v))). apply closed_port_17_5_value. Qed.
Transparent port_17_6.
Lemma closed_port_17_6_value v : eval_hfexpr expr_port_17_6 (closed_port_17_6 v) (closed_port_17_6 v) = Some (Gval (Fuint 1) (port_17_6 v)).
Proof. unfold port_17_6, closed_port_17_6, expr_port_17_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_17_6.
Lemma node_port_17_6_value v : eval_hfexpr expr_port_17_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_17_6 v)).
Proof. change (eval_hfexpr expr_port_17_6 (closed_port_17_6 v) (closed_port_17_6 v) = Some (Gval (Fuint 1) (port_17_6 v))). apply closed_port_17_6_value. Qed.
Transparent port_18_0.
Lemma closed_port_18_0_value v : eval_hfexpr expr_port_18_0 (closed_port_18_0 v) (closed_port_18_0 v) = Some (Gval Fclock (port_18_0 v)).
Proof. unfold port_18_0, closed_port_18_0, expr_port_18_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_18_0.
Lemma node_port_18_0_value v : eval_hfexpr expr_port_18_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_18_0 v)).
Proof. change (eval_hfexpr expr_port_18_0 (closed_port_18_0 v) (closed_port_18_0 v) = Some (Gval Fclock (port_18_0 v))). apply closed_port_18_0_value. Qed.
Transparent port_18_1.
Lemma closed_port_18_1_value v : eval_hfexpr expr_port_18_1 (closed_port_18_1 v) (closed_port_18_1 v) = Some (Gval (Fuint 1) (port_18_1 v)).
Proof. unfold port_18_1, closed_port_18_1, expr_port_18_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_18_1.
Lemma node_port_18_1_value v : eval_hfexpr expr_port_18_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_18_1 v)).
Proof. change (eval_hfexpr expr_port_18_1 (closed_port_18_1 v) (closed_port_18_1 v) = Some (Gval (Fuint 1) (port_18_1 v))). apply closed_port_18_1_value. Qed.
Transparent port_18_2.
Lemma closed_port_18_2_value v : eval_hfexpr expr_port_18_2 (closed_port_18_2 v) (closed_port_18_2 v) = Some (Gval (Fuint 1) (port_18_2 v)).
Proof. unfold port_18_2, closed_port_18_2, expr_port_18_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_18_2.
Lemma node_port_18_2_value v : eval_hfexpr expr_port_18_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_18_2 v)).
Proof. change (eval_hfexpr expr_port_18_2 (closed_port_18_2 v) (closed_port_18_2 v) = Some (Gval (Fuint 1) (port_18_2 v))). apply closed_port_18_2_value. Qed.
Transparent port_18_3.
Lemma closed_port_18_3_value v : eval_hfexpr expr_port_18_3 (closed_port_18_3 v) (closed_port_18_3 v) = Some (Gval (Fuint 1) (port_18_3 v)).
Proof. unfold port_18_3, closed_port_18_3, expr_port_18_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_18_3.
Lemma node_port_18_3_value v : eval_hfexpr expr_port_18_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_18_3 v)).
Proof. change (eval_hfexpr expr_port_18_3 (closed_port_18_3 v) (closed_port_18_3 v) = Some (Gval (Fuint 1) (port_18_3 v))). apply closed_port_18_3_value. Qed.
Transparent port_18_4.
Lemma closed_port_18_4_value v : eval_hfexpr expr_port_18_4 (closed_port_18_4 v) (closed_port_18_4 v) = Some (Gval (Fuint 1) (port_18_4 v)).
Proof. unfold port_18_4, closed_port_18_4, expr_port_18_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_18_4.
Lemma node_port_18_4_value v : eval_hfexpr expr_port_18_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_18_4 v)).
Proof. change (eval_hfexpr expr_port_18_4 (closed_port_18_4 v) (closed_port_18_4 v) = Some (Gval (Fuint 1) (port_18_4 v))). apply closed_port_18_4_value. Qed.
Transparent port_18_5.
Lemma closed_port_18_5_value v : eval_hfexpr expr_port_18_5 (closed_port_18_5 v) (closed_port_18_5 v) = Some (Gval (Fuint 1) (port_18_5 v)).
Proof. unfold port_18_5, closed_port_18_5, expr_port_18_5, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_18_5.
Lemma node_port_18_5_value v : eval_hfexpr expr_port_18_5 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_18_5 v)).
Proof. change (eval_hfexpr expr_port_18_5 (closed_port_18_5 v) (closed_port_18_5 v) = Some (Gval (Fuint 1) (port_18_5 v))). apply closed_port_18_5_value. Qed.
Transparent port_18_6.
Lemma closed_port_18_6_value v : eval_hfexpr expr_port_18_6 (closed_port_18_6 v) (closed_port_18_6 v) = Some (Gval (Fuint 1) (port_18_6 v)).
Proof. unfold port_18_6, closed_port_18_6, expr_port_18_6, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_18_6.
Lemma node_port_18_6_value v : eval_hfexpr expr_port_18_6 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_18_6 v)).
Proof. change (eval_hfexpr expr_port_18_6 (closed_port_18_6 v) (closed_port_18_6 v) = Some (Gval (Fuint 1) (port_18_6 v))). apply closed_port_18_6_value. Qed.
Transparent port_19_0.
Lemma closed_port_19_0_value v : eval_hfexpr expr_port_19_0 (closed_port_19_0 v) (closed_port_19_0 v) = Some (Gval Fclock (port_19_0 v)).
Proof. unfold port_19_0, closed_port_19_0, expr_port_19_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_19_0.
Lemma node_port_19_0_value v : eval_hfexpr expr_port_19_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_19_0 v)).
Proof. change (eval_hfexpr expr_port_19_0 (closed_port_19_0 v) (closed_port_19_0 v) = Some (Gval Fclock (port_19_0 v))). apply closed_port_19_0_value. Qed.
Transparent port_19_1.
Lemma closed_port_19_1_value v : eval_hfexpr expr_port_19_1 (closed_port_19_1 v) (closed_port_19_1 v) = Some (Gval (Fuint 1) (port_19_1 v)).
Proof. unfold port_19_1, closed_port_19_1, expr_port_19_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_19_1.
Lemma node_port_19_1_value v : eval_hfexpr expr_port_19_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_19_1 v)).
Proof. change (eval_hfexpr expr_port_19_1 (closed_port_19_1 v) (closed_port_19_1 v) = Some (Gval (Fuint 1) (port_19_1 v))). apply closed_port_19_1_value. Qed.
Transparent port_19_2.
Lemma closed_port_19_2_value v : eval_hfexpr expr_port_19_2 (closed_port_19_2 v) (closed_port_19_2 v) = Some (Gval (Fuint 1) (port_19_2 v)).
Proof. unfold port_19_2, closed_port_19_2, expr_port_19_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_19_2.
Lemma node_port_19_2_value v : eval_hfexpr expr_port_19_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_19_2 v)).
Proof. change (eval_hfexpr expr_port_19_2 (closed_port_19_2 v) (closed_port_19_2 v) = Some (Gval (Fuint 1) (port_19_2 v))). apply closed_port_19_2_value. Qed.
Transparent port_19_3.
Lemma closed_port_19_3_value v : eval_hfexpr expr_port_19_3 (closed_port_19_3 v) (closed_port_19_3 v) = Some (Gval (Fuint 1) (port_19_3 v)).
Proof. unfold port_19_3, closed_port_19_3, expr_port_19_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_19_3.
Lemma node_port_19_3_value v : eval_hfexpr expr_port_19_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_19_3 v)).
Proof. change (eval_hfexpr expr_port_19_3 (closed_port_19_3 v) (closed_port_19_3 v) = Some (Gval (Fuint 1) (port_19_3 v))). apply closed_port_19_3_value. Qed.
Transparent port_19_4.
Lemma closed_port_19_4_value v : eval_hfexpr expr_port_19_4 (closed_port_19_4 v) (closed_port_19_4 v) = Some (Gval (Fuint 1) (port_19_4 v)).
Proof. unfold port_19_4, closed_port_19_4, expr_port_19_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_19_4.
Lemma node_port_19_4_value v : eval_hfexpr expr_port_19_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_19_4 v)).
Proof. change (eval_hfexpr expr_port_19_4 (closed_port_19_4 v) (closed_port_19_4 v) = Some (Gval (Fuint 1) (port_19_4 v))). apply closed_port_19_4_value. Qed.
Transparent port_20_0.
Lemma closed_port_20_0_value v : eval_hfexpr expr_port_20_0 (closed_port_20_0 v) (closed_port_20_0 v) = Some (Gval Fclock (port_20_0 v)).
Proof. unfold port_20_0, closed_port_20_0, expr_port_20_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_20_0.
Lemma node_port_20_0_value v : eval_hfexpr expr_port_20_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_20_0 v)).
Proof. change (eval_hfexpr expr_port_20_0 (closed_port_20_0 v) (closed_port_20_0 v) = Some (Gval Fclock (port_20_0 v))). apply closed_port_20_0_value. Qed.
Transparent port_20_1.
Lemma closed_port_20_1_value v : eval_hfexpr expr_port_20_1 (closed_port_20_1 v) (closed_port_20_1 v) = Some (Gval (Fuint 1) (port_20_1 v)).
Proof. unfold port_20_1, closed_port_20_1, expr_port_20_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_20_1.
Lemma node_port_20_1_value v : eval_hfexpr expr_port_20_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_20_1 v)).
Proof. change (eval_hfexpr expr_port_20_1 (closed_port_20_1 v) (closed_port_20_1 v) = Some (Gval (Fuint 1) (port_20_1 v))). apply closed_port_20_1_value. Qed.
Transparent port_20_2.
Lemma closed_port_20_2_value v : eval_hfexpr expr_port_20_2 (closed_port_20_2 v) (closed_port_20_2 v) = Some (Gval (Fuint 1) (port_20_2 v)).
Proof. unfold port_20_2, closed_port_20_2, expr_port_20_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_20_2.
Lemma node_port_20_2_value v : eval_hfexpr expr_port_20_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_20_2 v)).
Proof. change (eval_hfexpr expr_port_20_2 (closed_port_20_2 v) (closed_port_20_2 v) = Some (Gval (Fuint 1) (port_20_2 v))). apply closed_port_20_2_value. Qed.
Transparent port_20_3.
Lemma closed_port_20_3_value v : eval_hfexpr expr_port_20_3 (closed_port_20_3 v) (closed_port_20_3 v) = Some (Gval (Fuint 1) (port_20_3 v)).
Proof. unfold port_20_3, closed_port_20_3, expr_port_20_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_20_3.
Lemma node_port_20_3_value v : eval_hfexpr expr_port_20_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_20_3 v)).
Proof. change (eval_hfexpr expr_port_20_3 (closed_port_20_3 v) (closed_port_20_3 v) = Some (Gval (Fuint 1) (port_20_3 v))). apply closed_port_20_3_value. Qed.
Transparent port_21_0.
Lemma closed_port_21_0_value v : eval_hfexpr expr_port_21_0 (closed_port_21_0 v) (closed_port_21_0 v) = Some (Gval Fclock (port_21_0 v)).
Proof. unfold port_21_0, closed_port_21_0, expr_port_21_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_21_0.
Lemma node_port_21_0_value v : eval_hfexpr expr_port_21_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_21_0 v)).
Proof. change (eval_hfexpr expr_port_21_0 (closed_port_21_0 v) (closed_port_21_0 v) = Some (Gval Fclock (port_21_0 v))). apply closed_port_21_0_value. Qed.
Transparent port_21_1.
Lemma closed_port_21_1_value v : eval_hfexpr expr_port_21_1 (closed_port_21_1 v) (closed_port_21_1 v) = Some (Gval (Fuint 1) (port_21_1 v)).
Proof. unfold port_21_1, closed_port_21_1, expr_port_21_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_21_1.
Lemma node_port_21_1_value v : eval_hfexpr expr_port_21_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_21_1 v)).
Proof. change (eval_hfexpr expr_port_21_1 (closed_port_21_1 v) (closed_port_21_1 v) = Some (Gval (Fuint 1) (port_21_1 v))). apply closed_port_21_1_value. Qed.
Transparent port_21_2.
Lemma closed_port_21_2_value v : eval_hfexpr expr_port_21_2 (closed_port_21_2 v) (closed_port_21_2 v) = Some (Gval (Fuint 1) (port_21_2 v)).
Proof. unfold port_21_2, closed_port_21_2, expr_port_21_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_21_2.
Lemma node_port_21_2_value v : eval_hfexpr expr_port_21_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_21_2 v)).
Proof. change (eval_hfexpr expr_port_21_2 (closed_port_21_2 v) (closed_port_21_2 v) = Some (Gval (Fuint 1) (port_21_2 v))). apply closed_port_21_2_value. Qed.
Transparent port_21_3.
Lemma closed_port_21_3_value v : eval_hfexpr expr_port_21_3 (closed_port_21_3 v) (closed_port_21_3 v) = Some (Gval (Fuint 1) (port_21_3 v)).
Proof. unfold port_21_3, closed_port_21_3, expr_port_21_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_21_3.
Lemma node_port_21_3_value v : eval_hfexpr expr_port_21_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_21_3 v)).
Proof. change (eval_hfexpr expr_port_21_3 (closed_port_21_3 v) (closed_port_21_3 v) = Some (Gval (Fuint 1) (port_21_3 v))). apply closed_port_21_3_value. Qed.
Transparent port_22_0.
Lemma closed_port_22_0_value v : eval_hfexpr expr_port_22_0 (closed_port_22_0 v) (closed_port_22_0 v) = Some (Gval Fclock (port_22_0 v)).
Proof. unfold port_22_0, closed_port_22_0, expr_port_22_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_22_0.
Lemma node_port_22_0_value v : eval_hfexpr expr_port_22_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_22_0 v)).
Proof. change (eval_hfexpr expr_port_22_0 (closed_port_22_0 v) (closed_port_22_0 v) = Some (Gval Fclock (port_22_0 v))). apply closed_port_22_0_value. Qed.
Transparent port_22_1.
Lemma closed_port_22_1_value v : eval_hfexpr expr_port_22_1 (closed_port_22_1 v) (closed_port_22_1 v) = Some (Gval (Fuint 1) (port_22_1 v)).
Proof. unfold port_22_1, closed_port_22_1, expr_port_22_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_22_1.
Lemma node_port_22_1_value v : eval_hfexpr expr_port_22_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_22_1 v)).
Proof. change (eval_hfexpr expr_port_22_1 (closed_port_22_1 v) (closed_port_22_1 v) = Some (Gval (Fuint 1) (port_22_1 v))). apply closed_port_22_1_value. Qed.
Transparent port_22_2.
Lemma closed_port_22_2_value v : eval_hfexpr expr_port_22_2 (closed_port_22_2 v) (closed_port_22_2 v) = Some (Gval (Fuint 1) (port_22_2 v)).
Proof. unfold port_22_2, closed_port_22_2, expr_port_22_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_22_2.
Lemma node_port_22_2_value v : eval_hfexpr expr_port_22_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_22_2 v)).
Proof. change (eval_hfexpr expr_port_22_2 (closed_port_22_2 v) (closed_port_22_2 v) = Some (Gval (Fuint 1) (port_22_2 v))). apply closed_port_22_2_value. Qed.
Transparent port_22_3.
Lemma closed_port_22_3_value v : eval_hfexpr expr_port_22_3 (closed_port_22_3 v) (closed_port_22_3 v) = Some (Gval (Fuint 1) (port_22_3 v)).
Proof. unfold port_22_3, closed_port_22_3, expr_port_22_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_22_3.
Lemma node_port_22_3_value v : eval_hfexpr expr_port_22_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_22_3 v)).
Proof. change (eval_hfexpr expr_port_22_3 (closed_port_22_3 v) (closed_port_22_3 v) = Some (Gval (Fuint 1) (port_22_3 v))). apply closed_port_22_3_value. Qed.
Transparent port_23_0.
Lemma closed_port_23_0_value v : eval_hfexpr expr_port_23_0 (closed_port_23_0 v) (closed_port_23_0 v) = Some (Gval Fclock (port_23_0 v)).
Proof. unfold port_23_0, closed_port_23_0, expr_port_23_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_23_0.
Lemma node_port_23_0_value v : eval_hfexpr expr_port_23_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_23_0 v)).
Proof. change (eval_hfexpr expr_port_23_0 (closed_port_23_0 v) (closed_port_23_0 v) = Some (Gval Fclock (port_23_0 v))). apply closed_port_23_0_value. Qed.
Transparent port_23_1.
Lemma closed_port_23_1_value v : eval_hfexpr expr_port_23_1 (closed_port_23_1 v) (closed_port_23_1 v) = Some (Gval (Fuint 1) (port_23_1 v)).
Proof. unfold port_23_1, closed_port_23_1, expr_port_23_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_23_1.
Lemma node_port_23_1_value v : eval_hfexpr expr_port_23_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_23_1 v)).
Proof. change (eval_hfexpr expr_port_23_1 (closed_port_23_1 v) (closed_port_23_1 v) = Some (Gval (Fuint 1) (port_23_1 v))). apply closed_port_23_1_value. Qed.
Transparent port_23_2.
Lemma closed_port_23_2_value v : eval_hfexpr expr_port_23_2 (closed_port_23_2 v) (closed_port_23_2 v) = Some (Gval (Fuint 1) (port_23_2 v)).
Proof. unfold port_23_2, closed_port_23_2, expr_port_23_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_23_2.
Lemma node_port_23_2_value v : eval_hfexpr expr_port_23_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_23_2 v)).
Proof. change (eval_hfexpr expr_port_23_2 (closed_port_23_2 v) (closed_port_23_2 v) = Some (Gval (Fuint 1) (port_23_2 v))). apply closed_port_23_2_value. Qed.
Transparent port_23_3.
Lemma closed_port_23_3_value v : eval_hfexpr expr_port_23_3 (closed_port_23_3 v) (closed_port_23_3 v) = Some (Gval (Fuint 1) (port_23_3 v)).
Proof. unfold port_23_3, closed_port_23_3, expr_port_23_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_23_3.
Lemma node_port_23_3_value v : eval_hfexpr expr_port_23_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_23_3 v)).
Proof. change (eval_hfexpr expr_port_23_3 (closed_port_23_3 v) (closed_port_23_3 v) = Some (Gval (Fuint 1) (port_23_3 v))). apply closed_port_23_3_value. Qed.
Transparent port_24_0.
Lemma closed_port_24_0_value v : eval_hfexpr expr_port_24_0 (closed_port_24_0 v) (closed_port_24_0 v) = Some (Gval Fclock (port_24_0 v)).
Proof. unfold port_24_0, closed_port_24_0, expr_port_24_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_24_0.
Lemma node_port_24_0_value v : eval_hfexpr expr_port_24_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_24_0 v)).
Proof. change (eval_hfexpr expr_port_24_0 (closed_port_24_0 v) (closed_port_24_0 v) = Some (Gval Fclock (port_24_0 v))). apply closed_port_24_0_value. Qed.
Transparent port_24_1.
Lemma closed_port_24_1_value v : eval_hfexpr expr_port_24_1 (closed_port_24_1 v) (closed_port_24_1 v) = Some (Gval (Fuint 1) (port_24_1 v)).
Proof. unfold port_24_1, closed_port_24_1, expr_port_24_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_24_1.
Lemma node_port_24_1_value v : eval_hfexpr expr_port_24_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_24_1 v)).
Proof. change (eval_hfexpr expr_port_24_1 (closed_port_24_1 v) (closed_port_24_1 v) = Some (Gval (Fuint 1) (port_24_1 v))). apply closed_port_24_1_value. Qed.
Transparent port_24_2.
Lemma closed_port_24_2_value v : eval_hfexpr expr_port_24_2 (closed_port_24_2 v) (closed_port_24_2 v) = Some (Gval (Fuint 1) (port_24_2 v)).
Proof. unfold port_24_2, closed_port_24_2, expr_port_24_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_24_2.
Lemma node_port_24_2_value v : eval_hfexpr expr_port_24_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_24_2 v)).
Proof. change (eval_hfexpr expr_port_24_2 (closed_port_24_2 v) (closed_port_24_2 v) = Some (Gval (Fuint 1) (port_24_2 v))). apply closed_port_24_2_value. Qed.
Transparent port_24_3.
Lemma closed_port_24_3_value v : eval_hfexpr expr_port_24_3 (closed_port_24_3 v) (closed_port_24_3 v) = Some (Gval (Fuint 1) (port_24_3 v)).
Proof. unfold port_24_3, closed_port_24_3, expr_port_24_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_24_3.
Lemma node_port_24_3_value v : eval_hfexpr expr_port_24_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_24_3 v)).
Proof. change (eval_hfexpr expr_port_24_3 (closed_port_24_3 v) (closed_port_24_3 v) = Some (Gval (Fuint 1) (port_24_3 v))). apply closed_port_24_3_value. Qed.
Transparent port_25_0.
Lemma closed_port_25_0_value v : eval_hfexpr expr_port_25_0 (closed_port_25_0 v) (closed_port_25_0 v) = Some (Gval Fclock (port_25_0 v)).
Proof. unfold port_25_0, closed_port_25_0, expr_port_25_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_25_0.
Lemma node_port_25_0_value v : eval_hfexpr expr_port_25_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_25_0 v)).
Proof. change (eval_hfexpr expr_port_25_0 (closed_port_25_0 v) (closed_port_25_0 v) = Some (Gval Fclock (port_25_0 v))). apply closed_port_25_0_value. Qed.
Transparent port_25_1.
Lemma closed_port_25_1_value v : eval_hfexpr expr_port_25_1 (closed_port_25_1 v) (closed_port_25_1 v) = Some (Gval (Fuint 1) (port_25_1 v)).
Proof. unfold port_25_1, closed_port_25_1, expr_port_25_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_25_1.
Lemma node_port_25_1_value v : eval_hfexpr expr_port_25_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_25_1 v)).
Proof. change (eval_hfexpr expr_port_25_1 (closed_port_25_1 v) (closed_port_25_1 v) = Some (Gval (Fuint 1) (port_25_1 v))). apply closed_port_25_1_value. Qed.
Transparent port_25_2.
Lemma closed_port_25_2_value v : eval_hfexpr expr_port_25_2 (closed_port_25_2 v) (closed_port_25_2 v) = Some (Gval (Fuint 1) (port_25_2 v)).
Proof. unfold port_25_2, closed_port_25_2, expr_port_25_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_25_2.
Lemma node_port_25_2_value v : eval_hfexpr expr_port_25_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_25_2 v)).
Proof. change (eval_hfexpr expr_port_25_2 (closed_port_25_2 v) (closed_port_25_2 v) = Some (Gval (Fuint 1) (port_25_2 v))). apply closed_port_25_2_value. Qed.
Transparent port_25_3.
Lemma closed_port_25_3_value v : eval_hfexpr expr_port_25_3 (closed_port_25_3 v) (closed_port_25_3 v) = Some (Gval (Fuint 1) (port_25_3 v)).
Proof. unfold port_25_3, closed_port_25_3, expr_port_25_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_25_3.
Lemma node_port_25_3_value v : eval_hfexpr expr_port_25_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_25_3 v)).
Proof. change (eval_hfexpr expr_port_25_3 (closed_port_25_3 v) (closed_port_25_3 v) = Some (Gval (Fuint 1) (port_25_3 v))). apply closed_port_25_3_value. Qed.
Transparent port_26_0.
Lemma closed_port_26_0_value v : eval_hfexpr expr_port_26_0 (closed_port_26_0 v) (closed_port_26_0 v) = Some (Gval Fclock (port_26_0 v)).
Proof. unfold port_26_0, closed_port_26_0, expr_port_26_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_26_0.
Lemma node_port_26_0_value v : eval_hfexpr expr_port_26_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_26_0 v)).
Proof. change (eval_hfexpr expr_port_26_0 (closed_port_26_0 v) (closed_port_26_0 v) = Some (Gval Fclock (port_26_0 v))). apply closed_port_26_0_value. Qed.
Transparent port_26_1.
Lemma closed_port_26_1_value v : eval_hfexpr expr_port_26_1 (closed_port_26_1 v) (closed_port_26_1 v) = Some (Gval (Fuint 1) (port_26_1 v)).
Proof. unfold port_26_1, closed_port_26_1, expr_port_26_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_26_1.
Lemma node_port_26_1_value v : eval_hfexpr expr_port_26_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_26_1 v)).
Proof. change (eval_hfexpr expr_port_26_1 (closed_port_26_1 v) (closed_port_26_1 v) = Some (Gval (Fuint 1) (port_26_1 v))). apply closed_port_26_1_value. Qed.
Transparent port_26_2.
Lemma closed_port_26_2_value v : eval_hfexpr expr_port_26_2 (closed_port_26_2 v) (closed_port_26_2 v) = Some (Gval (Fuint 1) (port_26_2 v)).
Proof. unfold port_26_2, closed_port_26_2, expr_port_26_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_26_2.
Lemma node_port_26_2_value v : eval_hfexpr expr_port_26_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_26_2 v)).
Proof. change (eval_hfexpr expr_port_26_2 (closed_port_26_2 v) (closed_port_26_2 v) = Some (Gval (Fuint 1) (port_26_2 v))). apply closed_port_26_2_value. Qed.
Transparent port_26_3.
Lemma closed_port_26_3_value v : eval_hfexpr expr_port_26_3 (closed_port_26_3 v) (closed_port_26_3 v) = Some (Gval (Fuint 1) (port_26_3 v)).
Proof. unfold port_26_3, closed_port_26_3, expr_port_26_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_26_3.
Lemma node_port_26_3_value v : eval_hfexpr expr_port_26_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_26_3 v)).
Proof. change (eval_hfexpr expr_port_26_3 (closed_port_26_3 v) (closed_port_26_3 v) = Some (Gval (Fuint 1) (port_26_3 v))). apply closed_port_26_3_value. Qed.
Transparent port_27_0.
Lemma closed_port_27_0_value v : eval_hfexpr expr_port_27_0 (closed_port_27_0 v) (closed_port_27_0 v) = Some (Gval Fclock (port_27_0 v)).
Proof. unfold port_27_0, closed_port_27_0, expr_port_27_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_27_0.
Lemma node_port_27_0_value v : eval_hfexpr expr_port_27_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_27_0 v)).
Proof. change (eval_hfexpr expr_port_27_0 (closed_port_27_0 v) (closed_port_27_0 v) = Some (Gval Fclock (port_27_0 v))). apply closed_port_27_0_value. Qed.
Transparent port_27_1.
Lemma closed_port_27_1_value v : eval_hfexpr expr_port_27_1 (closed_port_27_1 v) (closed_port_27_1 v) = Some (Gval (Fuint 1) (port_27_1 v)).
Proof. unfold port_27_1, closed_port_27_1, expr_port_27_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_27_1.
Lemma node_port_27_1_value v : eval_hfexpr expr_port_27_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_27_1 v)).
Proof. change (eval_hfexpr expr_port_27_1 (closed_port_27_1 v) (closed_port_27_1 v) = Some (Gval (Fuint 1) (port_27_1 v))). apply closed_port_27_1_value. Qed.
Transparent port_27_2.
Lemma closed_port_27_2_value v : eval_hfexpr expr_port_27_2 (closed_port_27_2 v) (closed_port_27_2 v) = Some (Gval (Fuint 1) (port_27_2 v)).
Proof. unfold port_27_2, closed_port_27_2, expr_port_27_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_27_2.
Lemma node_port_27_2_value v : eval_hfexpr expr_port_27_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_27_2 v)).
Proof. change (eval_hfexpr expr_port_27_2 (closed_port_27_2 v) (closed_port_27_2 v) = Some (Gval (Fuint 1) (port_27_2 v))). apply closed_port_27_2_value. Qed.
Transparent port_27_3.
Lemma closed_port_27_3_value v : eval_hfexpr expr_port_27_3 (closed_port_27_3 v) (closed_port_27_3 v) = Some (Gval (Fuint 1) (port_27_3 v)).
Proof. unfold port_27_3, closed_port_27_3, expr_port_27_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_27_3.
Lemma node_port_27_3_value v : eval_hfexpr expr_port_27_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_27_3 v)).
Proof. change (eval_hfexpr expr_port_27_3 (closed_port_27_3 v) (closed_port_27_3 v) = Some (Gval (Fuint 1) (port_27_3 v))). apply closed_port_27_3_value. Qed.
Transparent port_27_4.
Lemma closed_port_27_4_value v : eval_hfexpr expr_port_27_4 (closed_port_27_4 v) (closed_port_27_4 v) = Some (Gval (Fuint 1) (port_27_4 v)).
Proof. unfold port_27_4, closed_port_27_4, expr_port_27_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_27_4.
Lemma node_port_27_4_value v : eval_hfexpr expr_port_27_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_27_4 v)).
Proof. change (eval_hfexpr expr_port_27_4 (closed_port_27_4 v) (closed_port_27_4 v) = Some (Gval (Fuint 1) (port_27_4 v))). apply closed_port_27_4_value. Qed.
Transparent port_28_0.
Lemma closed_port_28_0_value v : eval_hfexpr expr_port_28_0 (closed_port_28_0 v) (closed_port_28_0 v) = Some (Gval Fclock (port_28_0 v)).
Proof. unfold port_28_0, closed_port_28_0, expr_port_28_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_28_0.
Lemma node_port_28_0_value v : eval_hfexpr expr_port_28_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_28_0 v)).
Proof. change (eval_hfexpr expr_port_28_0 (closed_port_28_0 v) (closed_port_28_0 v) = Some (Gval Fclock (port_28_0 v))). apply closed_port_28_0_value. Qed.
Transparent port_28_1.
Lemma closed_port_28_1_value v : eval_hfexpr expr_port_28_1 (closed_port_28_1 v) (closed_port_28_1 v) = Some (Gval (Fuint 1) (port_28_1 v)).
Proof. unfold port_28_1, closed_port_28_1, expr_port_28_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_28_1.
Lemma node_port_28_1_value v : eval_hfexpr expr_port_28_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_28_1 v)).
Proof. change (eval_hfexpr expr_port_28_1 (closed_port_28_1 v) (closed_port_28_1 v) = Some (Gval (Fuint 1) (port_28_1 v))). apply closed_port_28_1_value. Qed.
Transparent port_28_2.
Lemma closed_port_28_2_value v : eval_hfexpr expr_port_28_2 (closed_port_28_2 v) (closed_port_28_2 v) = Some (Gval (Fuint 1) (port_28_2 v)).
Proof. unfold port_28_2, closed_port_28_2, expr_port_28_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_28_2.
Lemma node_port_28_2_value v : eval_hfexpr expr_port_28_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_28_2 v)).
Proof. change (eval_hfexpr expr_port_28_2 (closed_port_28_2 v) (closed_port_28_2 v) = Some (Gval (Fuint 1) (port_28_2 v))). apply closed_port_28_2_value. Qed.
Transparent port_28_3.
Lemma closed_port_28_3_value v : eval_hfexpr expr_port_28_3 (closed_port_28_3 v) (closed_port_28_3 v) = Some (Gval (Fuint 1) (port_28_3 v)).
Proof. unfold port_28_3, closed_port_28_3, expr_port_28_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_28_3.
Lemma node_port_28_3_value v : eval_hfexpr expr_port_28_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_28_3 v)).
Proof. change (eval_hfexpr expr_port_28_3 (closed_port_28_3 v) (closed_port_28_3 v) = Some (Gval (Fuint 1) (port_28_3 v))). apply closed_port_28_3_value. Qed.
Transparent port_28_4.
Lemma closed_port_28_4_value v : eval_hfexpr expr_port_28_4 (closed_port_28_4 v) (closed_port_28_4 v) = Some (Gval (Fuint 1) (port_28_4 v)).
Proof. unfold port_28_4, closed_port_28_4, expr_port_28_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_28_4.
Lemma node_port_28_4_value v : eval_hfexpr expr_port_28_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_28_4 v)).
Proof. change (eval_hfexpr expr_port_28_4 (closed_port_28_4 v) (closed_port_28_4 v) = Some (Gval (Fuint 1) (port_28_4 v))). apply closed_port_28_4_value. Qed.
Transparent port_29_0.
Lemma closed_port_29_0_value v : eval_hfexpr expr_port_29_0 (closed_port_29_0 v) (closed_port_29_0 v) = Some (Gval Fclock (port_29_0 v)).
Proof. unfold port_29_0, closed_port_29_0, expr_port_29_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_29_0.
Lemma node_port_29_0_value v : eval_hfexpr expr_port_29_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_29_0 v)).
Proof. change (eval_hfexpr expr_port_29_0 (closed_port_29_0 v) (closed_port_29_0 v) = Some (Gval Fclock (port_29_0 v))). apply closed_port_29_0_value. Qed.
Transparent port_29_1.
Lemma closed_port_29_1_value v : eval_hfexpr expr_port_29_1 (closed_port_29_1 v) (closed_port_29_1 v) = Some (Gval (Fuint 1) (port_29_1 v)).
Proof. unfold port_29_1, closed_port_29_1, expr_port_29_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_29_1.
Lemma node_port_29_1_value v : eval_hfexpr expr_port_29_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_29_1 v)).
Proof. change (eval_hfexpr expr_port_29_1 (closed_port_29_1 v) (closed_port_29_1 v) = Some (Gval (Fuint 1) (port_29_1 v))). apply closed_port_29_1_value. Qed.
Transparent port_29_2.
Lemma closed_port_29_2_value v : eval_hfexpr expr_port_29_2 (closed_port_29_2 v) (closed_port_29_2 v) = Some (Gval (Fuint 1) (port_29_2 v)).
Proof. unfold port_29_2, closed_port_29_2, expr_port_29_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_29_2.
Lemma node_port_29_2_value v : eval_hfexpr expr_port_29_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_29_2 v)).
Proof. change (eval_hfexpr expr_port_29_2 (closed_port_29_2 v) (closed_port_29_2 v) = Some (Gval (Fuint 1) (port_29_2 v))). apply closed_port_29_2_value. Qed.
Transparent port_29_3.
Lemma closed_port_29_3_value v : eval_hfexpr expr_port_29_3 (closed_port_29_3 v) (closed_port_29_3 v) = Some (Gval (Fuint 1) (port_29_3 v)).
Proof. unfold port_29_3, closed_port_29_3, expr_port_29_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_29_3.
Lemma node_port_29_3_value v : eval_hfexpr expr_port_29_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_29_3 v)).
Proof. change (eval_hfexpr expr_port_29_3 (closed_port_29_3 v) (closed_port_29_3 v) = Some (Gval (Fuint 1) (port_29_3 v))). apply closed_port_29_3_value. Qed.
Transparent port_30_0.
Lemma closed_port_30_0_value v : eval_hfexpr expr_port_30_0 (closed_port_30_0 v) (closed_port_30_0 v) = Some (Gval Fclock (port_30_0 v)).
Proof. unfold port_30_0, closed_port_30_0, expr_port_30_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_30_0.
Lemma node_port_30_0_value v : eval_hfexpr expr_port_30_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_30_0 v)).
Proof. change (eval_hfexpr expr_port_30_0 (closed_port_30_0 v) (closed_port_30_0 v) = Some (Gval Fclock (port_30_0 v))). apply closed_port_30_0_value. Qed.
Transparent port_30_1.
Lemma closed_port_30_1_value v : eval_hfexpr expr_port_30_1 (closed_port_30_1 v) (closed_port_30_1 v) = Some (Gval (Fuint 1) (port_30_1 v)).
Proof. unfold port_30_1, closed_port_30_1, expr_port_30_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_30_1.
Lemma node_port_30_1_value v : eval_hfexpr expr_port_30_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_30_1 v)).
Proof. change (eval_hfexpr expr_port_30_1 (closed_port_30_1 v) (closed_port_30_1 v) = Some (Gval (Fuint 1) (port_30_1 v))). apply closed_port_30_1_value. Qed.
Transparent port_30_2.
Lemma closed_port_30_2_value v : eval_hfexpr expr_port_30_2 (closed_port_30_2 v) (closed_port_30_2 v) = Some (Gval (Fuint 1) (port_30_2 v)).
Proof. unfold port_30_2, closed_port_30_2, expr_port_30_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_30_2.
Lemma node_port_30_2_value v : eval_hfexpr expr_port_30_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_30_2 v)).
Proof. change (eval_hfexpr expr_port_30_2 (closed_port_30_2 v) (closed_port_30_2 v) = Some (Gval (Fuint 1) (port_30_2 v))). apply closed_port_30_2_value. Qed.
Transparent port_30_3.
Lemma closed_port_30_3_value v : eval_hfexpr expr_port_30_3 (closed_port_30_3 v) (closed_port_30_3 v) = Some (Gval (Fuint 1) (port_30_3 v)).
Proof. unfold port_30_3, closed_port_30_3, expr_port_30_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_30_3.
Lemma node_port_30_3_value v : eval_hfexpr expr_port_30_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_30_3 v)).
Proof. change (eval_hfexpr expr_port_30_3 (closed_port_30_3 v) (closed_port_30_3 v) = Some (Gval (Fuint 1) (port_30_3 v))). apply closed_port_30_3_value. Qed.
Transparent port_31_0.
Lemma closed_port_31_0_value v : eval_hfexpr expr_port_31_0 (closed_port_31_0 v) (closed_port_31_0 v) = Some (Gval Fclock (port_31_0 v)).
Proof. unfold port_31_0, closed_port_31_0, expr_port_31_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_31_0.
Lemma node_port_31_0_value v : eval_hfexpr expr_port_31_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_31_0 v)).
Proof. change (eval_hfexpr expr_port_31_0 (closed_port_31_0 v) (closed_port_31_0 v) = Some (Gval Fclock (port_31_0 v))). apply closed_port_31_0_value. Qed.
Transparent port_31_1.
Lemma closed_port_31_1_value v : eval_hfexpr expr_port_31_1 (closed_port_31_1 v) (closed_port_31_1 v) = Some (Gval (Fuint 1) (port_31_1 v)).
Proof. unfold port_31_1, closed_port_31_1, expr_port_31_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_31_1.
Lemma node_port_31_1_value v : eval_hfexpr expr_port_31_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_31_1 v)).
Proof. change (eval_hfexpr expr_port_31_1 (closed_port_31_1 v) (closed_port_31_1 v) = Some (Gval (Fuint 1) (port_31_1 v))). apply closed_port_31_1_value. Qed.
Transparent port_31_2.
Lemma closed_port_31_2_value v : eval_hfexpr expr_port_31_2 (closed_port_31_2 v) (closed_port_31_2 v) = Some (Gval (Fuint 1) (port_31_2 v)).
Proof. unfold port_31_2, closed_port_31_2, expr_port_31_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_31_2.
Lemma node_port_31_2_value v : eval_hfexpr expr_port_31_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_31_2 v)).
Proof. change (eval_hfexpr expr_port_31_2 (closed_port_31_2 v) (closed_port_31_2 v) = Some (Gval (Fuint 1) (port_31_2 v))). apply closed_port_31_2_value. Qed.
Transparent port_31_3.
Lemma closed_port_31_3_value v : eval_hfexpr expr_port_31_3 (closed_port_31_3 v) (closed_port_31_3 v) = Some (Gval (Fuint 1) (port_31_3 v)).
Proof. unfold port_31_3, closed_port_31_3, expr_port_31_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_31_3.
Lemma node_port_31_3_value v : eval_hfexpr expr_port_31_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_31_3 v)).
Proof. change (eval_hfexpr expr_port_31_3 (closed_port_31_3 v) (closed_port_31_3 v) = Some (Gval (Fuint 1) (port_31_3 v))). apply closed_port_31_3_value. Qed.
Transparent port_32_0.
Lemma closed_port_32_0_value v : eval_hfexpr expr_port_32_0 (closed_port_32_0 v) (closed_port_32_0 v) = Some (Gval Fclock (port_32_0 v)).
Proof. unfold port_32_0, closed_port_32_0, expr_port_32_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_32_0.
Lemma node_port_32_0_value v : eval_hfexpr expr_port_32_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_32_0 v)).
Proof. change (eval_hfexpr expr_port_32_0 (closed_port_32_0 v) (closed_port_32_0 v) = Some (Gval Fclock (port_32_0 v))). apply closed_port_32_0_value. Qed.
Transparent port_32_1.
Lemma closed_port_32_1_value v : eval_hfexpr expr_port_32_1 (closed_port_32_1 v) (closed_port_32_1 v) = Some (Gval (Fuint 1) (port_32_1 v)).
Proof. unfold port_32_1, closed_port_32_1, expr_port_32_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_32_1.
Lemma node_port_32_1_value v : eval_hfexpr expr_port_32_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_32_1 v)).
Proof. change (eval_hfexpr expr_port_32_1 (closed_port_32_1 v) (closed_port_32_1 v) = Some (Gval (Fuint 1) (port_32_1 v))). apply closed_port_32_1_value. Qed.
Transparent port_32_2.
Lemma closed_port_32_2_value v : eval_hfexpr expr_port_32_2 (closed_port_32_2 v) (closed_port_32_2 v) = Some (Gval (Fuint 1) (port_32_2 v)).
Proof. unfold port_32_2, closed_port_32_2, expr_port_32_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_32_2.
Lemma node_port_32_2_value v : eval_hfexpr expr_port_32_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_32_2 v)).
Proof. change (eval_hfexpr expr_port_32_2 (closed_port_32_2 v) (closed_port_32_2 v) = Some (Gval (Fuint 1) (port_32_2 v))). apply closed_port_32_2_value. Qed.
Transparent port_32_3.
Lemma closed_port_32_3_value v : eval_hfexpr expr_port_32_3 (closed_port_32_3 v) (closed_port_32_3 v) = Some (Gval (Fuint 1) (port_32_3 v)).
Proof. unfold port_32_3, closed_port_32_3, expr_port_32_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_32_3.
Lemma node_port_32_3_value v : eval_hfexpr expr_port_32_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_32_3 v)).
Proof. change (eval_hfexpr expr_port_32_3 (closed_port_32_3 v) (closed_port_32_3 v) = Some (Gval (Fuint 1) (port_32_3 v))). apply closed_port_32_3_value. Qed.
Transparent port_33_0.
Lemma closed_port_33_0_value v : eval_hfexpr expr_port_33_0 (closed_port_33_0 v) (closed_port_33_0 v) = Some (Gval Fclock (port_33_0 v)).
Proof. unfold port_33_0, closed_port_33_0, expr_port_33_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_33_0.
Lemma node_port_33_0_value v : eval_hfexpr expr_port_33_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_33_0 v)).
Proof. change (eval_hfexpr expr_port_33_0 (closed_port_33_0 v) (closed_port_33_0 v) = Some (Gval Fclock (port_33_0 v))). apply closed_port_33_0_value. Qed.
Transparent port_33_1.
Lemma closed_port_33_1_value v : eval_hfexpr expr_port_33_1 (closed_port_33_1 v) (closed_port_33_1 v) = Some (Gval (Fuint 1) (port_33_1 v)).
Proof. unfold port_33_1, closed_port_33_1, expr_port_33_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_33_1.
Lemma node_port_33_1_value v : eval_hfexpr expr_port_33_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_33_1 v)).
Proof. change (eval_hfexpr expr_port_33_1 (closed_port_33_1 v) (closed_port_33_1 v) = Some (Gval (Fuint 1) (port_33_1 v))). apply closed_port_33_1_value. Qed.
Transparent port_33_2.
Lemma closed_port_33_2_value v : eval_hfexpr expr_port_33_2 (closed_port_33_2 v) (closed_port_33_2 v) = Some (Gval (Fuint 1) (port_33_2 v)).
Proof. unfold port_33_2, closed_port_33_2, expr_port_33_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_33_2.
Lemma node_port_33_2_value v : eval_hfexpr expr_port_33_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_33_2 v)).
Proof. change (eval_hfexpr expr_port_33_2 (closed_port_33_2 v) (closed_port_33_2 v) = Some (Gval (Fuint 1) (port_33_2 v))). apply closed_port_33_2_value. Qed.
Transparent port_33_3.
Lemma closed_port_33_3_value v : eval_hfexpr expr_port_33_3 (closed_port_33_3 v) (closed_port_33_3 v) = Some (Gval (Fuint 1) (port_33_3 v)).
Proof. unfold port_33_3, closed_port_33_3, expr_port_33_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_33_3.
Lemma node_port_33_3_value v : eval_hfexpr expr_port_33_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_33_3 v)).
Proof. change (eval_hfexpr expr_port_33_3 (closed_port_33_3 v) (closed_port_33_3 v) = Some (Gval (Fuint 1) (port_33_3 v))). apply closed_port_33_3_value. Qed.
Transparent port_33_4.
Lemma closed_port_33_4_value v : eval_hfexpr expr_port_33_4 (closed_port_33_4 v) (closed_port_33_4 v) = Some (Gval (Fuint 1) (port_33_4 v)).
Proof. unfold port_33_4, closed_port_33_4, expr_port_33_4, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_33_4.
Lemma node_port_33_4_value v : eval_hfexpr expr_port_33_4 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_33_4 v)).
Proof. change (eval_hfexpr expr_port_33_4 (closed_port_33_4 v) (closed_port_33_4 v) = Some (Gval (Fuint 1) (port_33_4 v))). apply closed_port_33_4_value. Qed.
Transparent port_34_0.
Lemma closed_port_34_0_value v : eval_hfexpr expr_port_34_0 (closed_port_34_0 v) (closed_port_34_0 v) = Some (Gval Fclock (port_34_0 v)).
Proof. unfold port_34_0, closed_port_34_0, expr_port_34_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_34_0.
Lemma node_port_34_0_value v : eval_hfexpr expr_port_34_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_34_0 v)).
Proof. change (eval_hfexpr expr_port_34_0 (closed_port_34_0 v) (closed_port_34_0 v) = Some (Gval Fclock (port_34_0 v))). apply closed_port_34_0_value. Qed.
Transparent port_34_1.
Lemma closed_port_34_1_value v : eval_hfexpr expr_port_34_1 (closed_port_34_1 v) (closed_port_34_1 v) = Some (Gval (Fuint 1) (port_34_1 v)).
Proof. unfold port_34_1, closed_port_34_1, expr_port_34_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_34_1.
Lemma node_port_34_1_value v : eval_hfexpr expr_port_34_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_34_1 v)).
Proof. change (eval_hfexpr expr_port_34_1 (closed_port_34_1 v) (closed_port_34_1 v) = Some (Gval (Fuint 1) (port_34_1 v))). apply closed_port_34_1_value. Qed.
Transparent port_34_2.
Lemma closed_port_34_2_value v : eval_hfexpr expr_port_34_2 (closed_port_34_2 v) (closed_port_34_2 v) = Some (Gval (Fuint 1) (port_34_2 v)).
Proof. unfold port_34_2, closed_port_34_2, expr_port_34_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_34_2.
Lemma node_port_34_2_value v : eval_hfexpr expr_port_34_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_34_2 v)).
Proof. change (eval_hfexpr expr_port_34_2 (closed_port_34_2 v) (closed_port_34_2 v) = Some (Gval (Fuint 1) (port_34_2 v))). apply closed_port_34_2_value. Qed.
Transparent port_34_3.
Lemma closed_port_34_3_value v : eval_hfexpr expr_port_34_3 (closed_port_34_3 v) (closed_port_34_3 v) = Some (Gval (Fuint 1) (port_34_3 v)).
Proof. unfold port_34_3, closed_port_34_3, expr_port_34_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_34_3.
Lemma node_port_34_3_value v : eval_hfexpr expr_port_34_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_34_3 v)).
Proof. change (eval_hfexpr expr_port_34_3 (closed_port_34_3 v) (closed_port_34_3 v) = Some (Gval (Fuint 1) (port_34_3 v))). apply closed_port_34_3_value. Qed.
Transparent port_35_0.
Lemma closed_port_35_0_value v : eval_hfexpr expr_port_35_0 (closed_port_35_0 v) (closed_port_35_0 v) = Some (Gval Fclock (port_35_0 v)).
Proof. unfold port_35_0, closed_port_35_0, expr_port_35_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_35_0.
Lemma node_port_35_0_value v : eval_hfexpr expr_port_35_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_35_0 v)).
Proof. change (eval_hfexpr expr_port_35_0 (closed_port_35_0 v) (closed_port_35_0 v) = Some (Gval Fclock (port_35_0 v))). apply closed_port_35_0_value. Qed.
Transparent port_35_1.
Lemma closed_port_35_1_value v : eval_hfexpr expr_port_35_1 (closed_port_35_1 v) (closed_port_35_1 v) = Some (Gval (Fuint 1) (port_35_1 v)).
Proof. unfold port_35_1, closed_port_35_1, expr_port_35_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_35_1.
Lemma node_port_35_1_value v : eval_hfexpr expr_port_35_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_35_1 v)).
Proof. change (eval_hfexpr expr_port_35_1 (closed_port_35_1 v) (closed_port_35_1 v) = Some (Gval (Fuint 1) (port_35_1 v))). apply closed_port_35_1_value. Qed.
Transparent port_35_2.
Lemma closed_port_35_2_value v : eval_hfexpr expr_port_35_2 (closed_port_35_2 v) (closed_port_35_2 v) = Some (Gval (Fuint 1) (port_35_2 v)).
Proof. unfold port_35_2, closed_port_35_2, expr_port_35_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_35_2.
Lemma node_port_35_2_value v : eval_hfexpr expr_port_35_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_35_2 v)).
Proof. change (eval_hfexpr expr_port_35_2 (closed_port_35_2 v) (closed_port_35_2 v) = Some (Gval (Fuint 1) (port_35_2 v))). apply closed_port_35_2_value. Qed.
Transparent port_35_3.
Lemma closed_port_35_3_value v : eval_hfexpr expr_port_35_3 (closed_port_35_3 v) (closed_port_35_3 v) = Some (Gval (Fuint 1) (port_35_3 v)).
Proof. unfold port_35_3, closed_port_35_3, expr_port_35_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_35_3.
Lemma node_port_35_3_value v : eval_hfexpr expr_port_35_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_35_3 v)).
Proof. change (eval_hfexpr expr_port_35_3 (closed_port_35_3 v) (closed_port_35_3 v) = Some (Gval (Fuint 1) (port_35_3 v))). apply closed_port_35_3_value. Qed.
Transparent port_36_0.
Lemma closed_port_36_0_value v : eval_hfexpr expr_port_36_0 (closed_port_36_0 v) (closed_port_36_0 v) = Some (Gval Fclock (port_36_0 v)).
Proof. unfold port_36_0, closed_port_36_0, expr_port_36_0, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_36_0.
Lemma node_port_36_0_value v : eval_hfexpr expr_port_36_0 (stable_env v) (stable_env v) = Some (Gval Fclock (port_36_0 v)).
Proof. change (eval_hfexpr expr_port_36_0 (closed_port_36_0 v) (closed_port_36_0 v) = Some (Gval Fclock (port_36_0 v))). apply closed_port_36_0_value. Qed.
Transparent port_36_1.
Lemma closed_port_36_1_value v : eval_hfexpr expr_port_36_1 (closed_port_36_1 v) (closed_port_36_1 v) = Some (Gval (Fuint 1) (port_36_1 v)).
Proof. unfold port_36_1, closed_port_36_1, expr_port_36_1, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_36_1.
Lemma node_port_36_1_value v : eval_hfexpr expr_port_36_1 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_36_1 v)).
Proof. change (eval_hfexpr expr_port_36_1 (closed_port_36_1 v) (closed_port_36_1 v) = Some (Gval (Fuint 1) (port_36_1 v))). apply closed_port_36_1_value. Qed.
Transparent port_36_2.
Lemma closed_port_36_2_value v : eval_hfexpr expr_port_36_2 (closed_port_36_2 v) (closed_port_36_2 v) = Some (Gval (Fuint 1) (port_36_2 v)).
Proof. unfold port_36_2, closed_port_36_2, expr_port_36_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_36_2.
Lemma node_port_36_2_value v : eval_hfexpr expr_port_36_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_36_2 v)).
Proof. change (eval_hfexpr expr_port_36_2 (closed_port_36_2 v) (closed_port_36_2 v) = Some (Gval (Fuint 1) (port_36_2 v))). apply closed_port_36_2_value. Qed.
Transparent port_36_3.
Lemma closed_port_36_3_value v : eval_hfexpr expr_port_36_3 (closed_port_36_3 v) (closed_port_36_3 v) = Some (Gval (Fuint 1) (port_36_3 v)).
Proof. unfold port_36_3, closed_port_36_3, expr_port_36_3, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque port_36_3.
Lemma node_port_36_3_value v : eval_hfexpr expr_port_36_3 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (port_36_3 v)).
Proof. change (eval_hfexpr expr_port_36_3 (closed_port_36_3 v) (closed_port_36_3 v) = Some (Gval (Fuint 1) (port_36_3 v))). apply closed_port_36_3_value. Qed.

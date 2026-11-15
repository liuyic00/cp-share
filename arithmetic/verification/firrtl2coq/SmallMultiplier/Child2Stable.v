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
Definition word_6 (v : leaf_values) := v 0 6.
Definition port_10_5 (v : leaf_values) := v 10 5.
Definition port_10_6 (v : leaf_values) := v 10 6.
Definition port_11_5 (v : leaf_values) := v 11 5.
Definition port_11_6 (v : leaf_values) := v 11 6.
Definition expr_word_12 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 2))).
Definition closed_word_12 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 1) (word_2 v)) (VM.empty hvalue)).
Definition word_12 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_12 (closed_word_12 v) (closed_word_12 v)).
Definition expr_word_13 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 3))).
Definition closed_word_13 (v : leaf_values) : VM.t hvalue := (VM.add 3 (Gval (Fuint 1) (word_3 v)) (VM.empty hvalue)).
Definition word_13 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_13 (closed_word_13 v) (closed_word_13 v)).
Definition expr_word_14 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 4))).
Definition closed_word_14 (v : leaf_values) : VM.t hvalue := (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)).
Definition word_14 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_14 (closed_word_14 v) (closed_word_14 v)).
Definition expr_word_15 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 5))).
Definition closed_word_15 (v : leaf_values) : VM.t hvalue := (VM.add 5 (Gval (Fuint 1) (word_5 v)) (VM.empty hvalue)).
Definition word_15 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_15 (closed_word_15 v) (closed_word_15 v)).
Definition expr_word_16 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 6))).
Definition closed_word_16 (v : leaf_values) : VM.t hvalue := (VM.add 6 (Gval (Fuint 1) (word_6 v)) (VM.empty hvalue)).
Definition word_16 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_16 (closed_word_16 v) (closed_word_16 v)).
Definition expr_word_17 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 12)) (@Eref VarOrder.T (@Eid VarOrder.T 13))).
Definition closed_word_17 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 4) (word_13 v)) (VM.add 12 (Gval (Fuint 4) (word_12 v)) (VM.empty hvalue))).
Definition word_17 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_17 (closed_word_17 v) (closed_word_17 v)).
Definition expr_word_18 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 17))).
Definition closed_word_18 (v : leaf_values) : VM.t hvalue := (VM.add 17 (Gval (Fuint 5) (word_17 v)) (VM.empty hvalue)).
Definition word_18 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_18 (closed_word_18 v) (closed_word_18 v)).
Definition expr_word_19 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Eref VarOrder.T (@Eid VarOrder.T 14))).
Definition closed_word_19 (v : leaf_values) : VM.t hvalue := (VM.add 18 (Gval (Fuint 4) (word_18 v)) (VM.add 14 (Gval (Fuint 4) (word_14 v)) (VM.empty hvalue))).
Definition word_19 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_19 (closed_word_19 v) (closed_word_19 v)).
Definition expr_word_20 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 19))).
Definition closed_word_20 (v : leaf_values) : VM.t hvalue := (VM.add 19 (Gval (Fuint 5) (word_19 v)) (VM.empty hvalue)).
Definition word_20 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_20 (closed_word_20 v) (closed_word_20 v)).
Definition expr_word_21 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 20)) (@Eref VarOrder.T (@Eid VarOrder.T 15))).
Definition closed_word_21 (v : leaf_values) : VM.t hvalue := (VM.add 20 (Gval (Fuint 4) (word_20 v)) (VM.add 15 (Gval (Fuint 4) (word_15 v)) (VM.empty hvalue))).
Definition word_21 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_21 (closed_word_21 v) (closed_word_21 v)).
Definition expr_word_22 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 21))).
Definition closed_word_22 (v : leaf_values) : VM.t hvalue := (VM.add 21 (Gval (Fuint 5) (word_21 v)) (VM.empty hvalue)).
Definition word_22 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_22 (closed_word_22 v) (closed_word_22 v)).
Definition expr_word_23 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 22)) (@Eref VarOrder.T (@Eid VarOrder.T 16))).
Definition closed_word_23 (v : leaf_values) : VM.t hvalue := (VM.add 22 (Gval (Fuint 4) (word_22 v)) (VM.add 16 (Gval (Fuint 4) (word_16 v)) (VM.empty hvalue))).
Definition word_23 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_23 (closed_word_23 v) (closed_word_23 v)).
Definition expr_word_24 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 23))).
Definition closed_word_24 (v : leaf_values) : VM.t hvalue := (VM.add 23 (Gval (Fuint 5) (word_23 v)) (VM.empty hvalue)).
Definition word_24 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_24 (closed_word_24 v) (closed_word_24 v)).
Definition expr_word_41 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 5)).
Definition closed_word_41 (v : leaf_values) : VM.t hvalue := (VM.add 11 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_11_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_41 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_41 (closed_word_41 v) (closed_word_41 v)).
Definition expr_word_7 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 41)).
Definition closed_word_7 (v : leaf_values) : VM.t hvalue := (VM.add 41 (Gval (Fuint 1) (word_41 v)) (VM.empty hvalue)).
Definition word_7 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_7 (closed_word_7 v) (closed_word_7 v)).
Definition expr_word_25 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 7))).
Definition closed_word_25 (v : leaf_values) : VM.t hvalue := (VM.add 7 (Gval (Fuint 1) (word_7 v)) (VM.empty hvalue)).
Definition word_25 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_25 (closed_word_25 v) (closed_word_25 v)).
Definition expr_word_42 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 6)).
Definition closed_word_42 (v : leaf_values) : VM.t hvalue := (VM.add 10 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_10_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_42 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_42 (closed_word_42 v) (closed_word_42 v)).
Definition expr_word_8 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 42)).
Definition closed_word_8 (v : leaf_values) : VM.t hvalue := (VM.add 42 (Gval (Fuint 1) (word_42 v)) (VM.empty hvalue)).
Definition word_8 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_8 (closed_word_8 v) (closed_word_8 v)).
Definition expr_word_26 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 8))).
Definition closed_word_26 (v : leaf_values) : VM.t hvalue := (VM.add 8 (Gval (Fuint 1) (word_8 v)) (VM.empty hvalue)).
Definition word_26 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_26 (closed_word_26 v) (closed_word_26 v)).
Definition expr_word_27 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 26))).
Definition closed_word_27 (v : leaf_values) : VM.t hvalue := (VM.add 26 (Gval (Fuint 4) (word_26 v)) (VM.empty hvalue)).
Definition word_27 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_27 (closed_word_27 v) (closed_word_27 v)).
Definition expr_word_43 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 11) 6)).
Definition closed_word_43 (v : leaf_values) : VM.t hvalue := (VM.add 11 (Bval (Bflips 6 Nflip (Gval (Fuint 1) (port_11_6 v)) Bnil)) (VM.empty hvalue)).
Definition word_43 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_43 (closed_word_43 v) (closed_word_43 v)).
Definition expr_word_9 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 43)).
Definition closed_word_9 (v : leaf_values) : VM.t hvalue := (VM.add 43 (Gval (Fuint 1) (word_43 v)) (VM.empty hvalue)).
Definition word_9 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_9 (closed_word_9 v) (closed_word_9 v)).
Definition expr_word_28 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Upad 4) (@Eref VarOrder.T (@Eid VarOrder.T 9))).
Definition closed_word_28 (v : leaf_values) : VM.t hvalue := (VM.add 9 (Gval (Fuint 1) (word_9 v)) (VM.empty hvalue)).
Definition word_28 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_28 (closed_word_28 v) (closed_word_28 v)).
Definition expr_word_29 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 28))).
Definition closed_word_29 (v : leaf_values) : VM.t hvalue := (VM.add 28 (Gval (Fuint 4) (word_28 v)) (VM.empty hvalue)).
Definition word_29 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_29 (closed_word_29 v) (closed_word_29 v)).
Definition expr_word_30 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 25)) (@Eref VarOrder.T (@Eid VarOrder.T 27))).
Definition closed_word_30 (v : leaf_values) : VM.t hvalue := (VM.add 27 (Gval (Fuint 5) (word_27 v)) (VM.add 25 (Gval (Fuint 4) (word_25 v)) (VM.empty hvalue))).
Definition word_30 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_30 (closed_word_30 v) (closed_word_30 v)).
Definition expr_word_31 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 30))).
Definition closed_word_31 (v : leaf_values) : VM.t hvalue := (VM.add 30 (Gval (Fuint 6) (word_30 v)) (VM.empty hvalue)).
Definition word_31 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_31 (closed_word_31 v) (closed_word_31 v)).
Definition expr_word_32 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 31)) (@Eref VarOrder.T (@Eid VarOrder.T 29))).
Definition closed_word_32 (v : leaf_values) : VM.t hvalue := (VM.add 31 (Gval (Fuint 5) (word_31 v)) (VM.add 29 (Gval (Fuint 5) (word_29 v)) (VM.empty hvalue))).
Definition word_32 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_32 (closed_word_32 v) (closed_word_32 v)).
Definition expr_word_33 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 32))).
Definition closed_word_33 (v : leaf_values) : VM.t hvalue := (VM.add 32 (Gval (Fuint 6) (word_32 v)) (VM.empty hvalue)).
Definition word_33 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_33 (closed_word_33 v) (closed_word_33 v)).
Definition expr_word_34 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 24)) (@Eref VarOrder.T (@Eid VarOrder.T 33))).
Definition closed_word_34 (v : leaf_values) : VM.t hvalue := (VM.add 33 (Gval (Fuint 5) (word_33 v)) (VM.add 24 (Gval (Fuint 4) (word_24 v)) (VM.empty hvalue))).
Definition word_34 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_34 (closed_word_34 v) (closed_word_34 v)).
Definition expr_word_35 : @hfexpr VarOrder.T := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_word_35 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_35 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_35 (closed_word_35 v) (closed_word_35 v)).
Definition expr_word_36 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 35)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_36 (v : leaf_values) : VM.t hvalue := (VM.add 35 (Gval (Fuint 1) (word_35 v)) (VM.empty hvalue)).
Definition word_36 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_36 (closed_word_36 v) (closed_word_36 v)).
Definition expr_word_37 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 34)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_word_37 (v : leaf_values) : VM.t hvalue := (VM.add 34 (Gval (Fuint 1) (word_34 v)) (VM.empty hvalue)).
Definition word_37 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_37 (closed_word_37 v) (closed_word_37 v)).
Definition expr_word_38 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 10) 5)).
Definition closed_word_38 (v : leaf_values) : VM.t hvalue := (VM.add 10 (Bval (Bflips 5 Nflip (Gval (Fuint 1) (port_10_5 v)) Bnil)) (VM.empty hvalue)).
Definition word_38 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_38 (closed_word_38 v) (closed_word_38 v)).
Definition expr_word_39 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 5)).
Definition closed_word_39 (v : leaf_values) : VM.t hvalue := (VM.add 5 (Gval (Fuint 1) (word_5 v)) (VM.empty hvalue)).
Definition word_39 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_39 (closed_word_39 v) (closed_word_39 v)).
Definition expr_word_40 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 6)).
Definition closed_word_40 (v : leaf_values) : VM.t hvalue := (VM.add 6 (Gval (Fuint 1) (word_6 v)) (VM.empty hvalue)).
Definition word_40 (v : leaf_values) := word_of_eval (eval_hfexpr expr_word_40 (closed_word_40 v) (closed_word_40 v)).
Definition expr_port_10_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_10_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_10_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_0 (closed_port_10_0 v) (closed_port_10_0 v)).
Definition expr_port_10_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_10_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_10_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_1 (closed_port_10_1 v) (closed_port_10_1 v)).
Definition expr_port_10_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 2)).
Definition closed_port_10_2 (v : leaf_values) : VM.t hvalue := (VM.add 2 (Gval (Fuint 1) (word_2 v)) (VM.empty hvalue)).
Definition port_10_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_2 (closed_port_10_2 v) (closed_port_10_2 v)).
Definition expr_port_10_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 3)).
Definition closed_port_10_3 (v : leaf_values) : VM.t hvalue := (VM.add 3 (Gval (Fuint 1) (word_3 v)) (VM.empty hvalue)).
Definition port_10_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_3 (closed_port_10_3 v) (closed_port_10_3 v)).
Definition expr_port_10_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 4)).
Definition closed_port_10_4 (v : leaf_values) : VM.t hvalue := (VM.add 4 (Gval (Fuint 1) (word_4 v)) (VM.empty hvalue)).
Definition port_10_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_10_4 (closed_port_10_4 v) (closed_port_10_4 v)).
Definition expr_port_11_0 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 0)).
Definition closed_port_11_0 (v : leaf_values) : VM.t hvalue := (VM.add 0 (Gval Fclock (word_0 v)) (VM.empty hvalue)).
Definition port_11_0 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_0 (closed_port_11_0 v) (closed_port_11_0 v)).
Definition expr_port_11_1 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition closed_port_11_1 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition port_11_1 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_1 (closed_port_11_1 v) (closed_port_11_1 v)).
Definition expr_port_11_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 38)).
Definition closed_port_11_2 (v : leaf_values) : VM.t hvalue := (VM.add 38 (Gval (Fuint 1) (word_38 v)) (VM.empty hvalue)).
Definition port_11_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_2 (closed_port_11_2 v) (closed_port_11_2 v)).
Definition expr_port_11_3 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 39)).
Definition closed_port_11_3 (v : leaf_values) : VM.t hvalue := (VM.add 39 (Gval (Fuint 1) (word_39 v)) (VM.empty hvalue)).
Definition port_11_3 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_3 (closed_port_11_3 v) (closed_port_11_3 v)).
Definition expr_port_11_4 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 40)).
Definition closed_port_11_4 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 1) (word_40 v)) (VM.empty hvalue)).
Definition port_11_4 (v : leaf_values) := word_of_eval (eval_hfexpr expr_port_11_4 (closed_port_11_4 v) (closed_port_11_4 v)).
Opaque word_0 word_1 word_2 word_3 word_4 word_5 word_6 word_7 word_8 word_9 word_12 word_13 word_14 word_15 word_16 word_17 word_18 word_19 word_20 word_21 word_22 word_23 word_24 word_25 word_26 word_27 word_28 word_29 word_30 word_31 word_32 word_33 word_34 word_35 word_36 word_37 word_38 word_39 word_40 word_41 word_42 word_43 port_10_0 port_10_1 port_10_2 port_10_3 port_10_4 port_10_5 port_10_6 port_11_0 port_11_1 port_11_2 port_11_3 port_11_4 port_11_5 port_11_6.
Definition stable_shape (values : N -> hvalue) : VM.t hvalue := Eval vm_compute in
 (VM.add 43 (values 43) (VM.add 42 (values 42) (VM.add 41 (values 41) (VM.add 40 (values 40) (VM.add 39 (values 39) (VM.add 38 (values 38) (VM.add 37 (values 37) (VM.add 36 (values 36) (VM.add 35 (values 35) (VM.add 34 (values 34) (VM.add 33 (values 33) (VM.add 32 (values 32) (VM.add 31 (values 31) (VM.add 30 (values 30) (VM.add 29 (values 29) (VM.add 28 (values 28) (VM.add 27 (values 27) (VM.add 26 (values 26) (VM.add 25 (values 25) (VM.add 24 (values 24) (VM.add 23 (values 23) (VM.add 22 (values 22) (VM.add 21 (values 21) (VM.add 20 (values 20) (VM.add 19 (values 19) (VM.add 18 (values 18) (VM.add 17 (values 17) (VM.add 16 (values 16) (VM.add 15 (values 15) (VM.add 14 (values 14) (VM.add 13 (values 13) (VM.add 12 (values 12) (VM.add 11 (values 11) (VM.add 10 (values 10) (VM.add 9 (values 9) (VM.add 8 (values 8) (VM.add 7 (values 7) (VM.add 6 (values 6) (VM.add 5 (values 5) (VM.add 4 (values 4) (VM.add 3 (values 3) (VM.add 2 (values 2) (VM.add 1 (values 1) (VM.add 0 (values 0) (VM.empty hvalue))))))))))))))))))))))))))))))))))))))))))))).
Definition stable_values (v : leaf_values) (id : N) : hvalue := match id with
| 0 => (Gval Fclock (word_0 v))
| 1 => (Gval (Fuint 1) (word_1 v))
| 2 => (Gval (Fuint 1) (word_2 v))
| 3 => (Gval (Fuint 1) (word_3 v))
| 4 => (Gval (Fuint 1) (word_4 v))
| 5 => (Gval (Fuint 1) (word_5 v))
| 6 => (Gval (Fuint 1) (word_6 v))
| 7 => (Gval (Fuint 1) (word_7 v))
| 8 => (Gval (Fuint 1) (word_8 v))
| 9 => (Gval (Fuint 1) (word_9 v))
| 10 => (Bval (Bflips 0 Flipped (Gval Fclock (port_10_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_10_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_10_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_10_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_10_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_10_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_10_6 v)) Bnil))))))))
| 11 => (Bval (Bflips 0 Flipped (Gval Fclock (port_11_0 v)) (Bflips 1 Flipped (Gval (Fuint 1) (port_11_1 v)) (Bflips 2 Flipped (Gval (Fuint 1) (port_11_2 v)) (Bflips 3 Flipped (Gval (Fuint 1) (port_11_3 v)) (Bflips 4 Flipped (Gval (Fuint 1) (port_11_4 v)) (Bflips 5 Nflip (Gval (Fuint 1) (port_11_5 v)) (Bflips 6 Nflip (Gval (Fuint 1) (port_11_6 v)) Bnil))))))))
| 12 => (Gval (Fuint 4) (word_12 v))
| 13 => (Gval (Fuint 4) (word_13 v))
| 14 => (Gval (Fuint 4) (word_14 v))
| 15 => (Gval (Fuint 4) (word_15 v))
| 16 => (Gval (Fuint 4) (word_16 v))
| 17 => (Gval (Fuint 5) (word_17 v))
| 18 => (Gval (Fuint 4) (word_18 v))
| 19 => (Gval (Fuint 5) (word_19 v))
| 20 => (Gval (Fuint 4) (word_20 v))
| 21 => (Gval (Fuint 5) (word_21 v))
| 22 => (Gval (Fuint 4) (word_22 v))
| 23 => (Gval (Fuint 5) (word_23 v))
| 24 => (Gval (Fuint 4) (word_24 v))
| 25 => (Gval (Fuint 4) (word_25 v))
| 26 => (Gval (Fuint 4) (word_26 v))
| 27 => (Gval (Fuint 5) (word_27 v))
| 28 => (Gval (Fuint 4) (word_28 v))
| 29 => (Gval (Fuint 5) (word_29 v))
| 30 => (Gval (Fuint 6) (word_30 v))
| 31 => (Gval (Fuint 5) (word_31 v))
| 32 => (Gval (Fuint 6) (word_32 v))
| 33 => (Gval (Fuint 5) (word_33 v))
| 34 => (Gval (Fuint 1) (word_34 v))
| 35 => (Gval (Fuint 1) (word_35 v))
| 36 => (Gval (Fuint 1) (word_36 v))
| 37 => (Gval (Fuint 1) (word_37 v))
| 38 => (Gval (Fuint 1) (word_38 v))
| 39 => (Gval (Fuint 1) (word_39 v))
| 40 => (Gval (Fuint 1) (word_40 v))
| 41 => (Gval (Fuint 1) (word_41 v))
| 42 => (Gval (Fuint 1) (word_42 v))
| 43 => (Gval (Fuint 1) (word_43 v))
| _ => Needtobedefined (Gtyp (Fuint 0)) end.
Definition stable_env v := stable_shape (stable_values v).
Transparent word_12.
Lemma closed_word_12_value v : eval_hfexpr expr_word_12 (closed_word_12 v) (closed_word_12 v) = Some (Gval (Fuint 4) (word_12 v)).
Proof. unfold word_12, closed_word_12, expr_word_12, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_12.
Lemma node_word_12_value v : eval_hfexpr expr_word_12 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_12 v)).
Proof. change (eval_hfexpr expr_word_12 (closed_word_12 v) (closed_word_12 v) = Some (Gval (Fuint 4) (word_12 v))). apply closed_word_12_value. Qed.
Transparent word_13.
Lemma closed_word_13_value v : eval_hfexpr expr_word_13 (closed_word_13 v) (closed_word_13 v) = Some (Gval (Fuint 4) (word_13 v)).
Proof. unfold word_13, closed_word_13, expr_word_13, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_13.
Lemma node_word_13_value v : eval_hfexpr expr_word_13 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_13 v)).
Proof. change (eval_hfexpr expr_word_13 (closed_word_13 v) (closed_word_13 v) = Some (Gval (Fuint 4) (word_13 v))). apply closed_word_13_value. Qed.
Transparent word_14.
Lemma closed_word_14_value v : eval_hfexpr expr_word_14 (closed_word_14 v) (closed_word_14 v) = Some (Gval (Fuint 4) (word_14 v)).
Proof. unfold word_14, closed_word_14, expr_word_14, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_14.
Lemma node_word_14_value v : eval_hfexpr expr_word_14 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_14 v)).
Proof. change (eval_hfexpr expr_word_14 (closed_word_14 v) (closed_word_14 v) = Some (Gval (Fuint 4) (word_14 v))). apply closed_word_14_value. Qed.
Transparent word_15.
Lemma closed_word_15_value v : eval_hfexpr expr_word_15 (closed_word_15 v) (closed_word_15 v) = Some (Gval (Fuint 4) (word_15 v)).
Proof. unfold word_15, closed_word_15, expr_word_15, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_15.
Lemma node_word_15_value v : eval_hfexpr expr_word_15 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_15 v)).
Proof. change (eval_hfexpr expr_word_15 (closed_word_15 v) (closed_word_15 v) = Some (Gval (Fuint 4) (word_15 v))). apply closed_word_15_value. Qed.
Transparent word_16.
Lemma closed_word_16_value v : eval_hfexpr expr_word_16 (closed_word_16 v) (closed_word_16 v) = Some (Gval (Fuint 4) (word_16 v)).
Proof. unfold word_16, closed_word_16, expr_word_16, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_16.
Lemma node_word_16_value v : eval_hfexpr expr_word_16 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_16 v)).
Proof. change (eval_hfexpr expr_word_16 (closed_word_16 v) (closed_word_16 v) = Some (Gval (Fuint 4) (word_16 v))). apply closed_word_16_value. Qed.
Transparent word_17.
Lemma closed_word_17_value v : eval_hfexpr expr_word_17 (closed_word_17 v) (closed_word_17 v) = Some (Gval (Fuint 5) (word_17 v)).
Proof. unfold word_17, closed_word_17, expr_word_17, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_17.
Lemma node_word_17_value v : eval_hfexpr expr_word_17 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_17 v)).
Proof. change (eval_hfexpr expr_word_17 (closed_word_17 v) (closed_word_17 v) = Some (Gval (Fuint 5) (word_17 v))). apply closed_word_17_value. Qed.
Transparent word_18.
Lemma closed_word_18_value v : eval_hfexpr expr_word_18 (closed_word_18 v) (closed_word_18 v) = Some (Gval (Fuint 4) (word_18 v)).
Proof. unfold word_18, closed_word_18, expr_word_18, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_18.
Lemma node_word_18_value v : eval_hfexpr expr_word_18 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_18 v)).
Proof. change (eval_hfexpr expr_word_18 (closed_word_18 v) (closed_word_18 v) = Some (Gval (Fuint 4) (word_18 v))). apply closed_word_18_value. Qed.
Transparent word_19.
Lemma closed_word_19_value v : eval_hfexpr expr_word_19 (closed_word_19 v) (closed_word_19 v) = Some (Gval (Fuint 5) (word_19 v)).
Proof. unfold word_19, closed_word_19, expr_word_19, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_19.
Lemma node_word_19_value v : eval_hfexpr expr_word_19 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_19 v)).
Proof. change (eval_hfexpr expr_word_19 (closed_word_19 v) (closed_word_19 v) = Some (Gval (Fuint 5) (word_19 v))). apply closed_word_19_value. Qed.
Transparent word_20.
Lemma closed_word_20_value v : eval_hfexpr expr_word_20 (closed_word_20 v) (closed_word_20 v) = Some (Gval (Fuint 4) (word_20 v)).
Proof. unfold word_20, closed_word_20, expr_word_20, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_20.
Lemma node_word_20_value v : eval_hfexpr expr_word_20 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_20 v)).
Proof. change (eval_hfexpr expr_word_20 (closed_word_20 v) (closed_word_20 v) = Some (Gval (Fuint 4) (word_20 v))). apply closed_word_20_value. Qed.
Transparent word_21.
Lemma closed_word_21_value v : eval_hfexpr expr_word_21 (closed_word_21 v) (closed_word_21 v) = Some (Gval (Fuint 5) (word_21 v)).
Proof. unfold word_21, closed_word_21, expr_word_21, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_21.
Lemma node_word_21_value v : eval_hfexpr expr_word_21 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_21 v)).
Proof. change (eval_hfexpr expr_word_21 (closed_word_21 v) (closed_word_21 v) = Some (Gval (Fuint 5) (word_21 v))). apply closed_word_21_value. Qed.
Transparent word_22.
Lemma closed_word_22_value v : eval_hfexpr expr_word_22 (closed_word_22 v) (closed_word_22 v) = Some (Gval (Fuint 4) (word_22 v)).
Proof. unfold word_22, closed_word_22, expr_word_22, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_22.
Lemma node_word_22_value v : eval_hfexpr expr_word_22 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_22 v)).
Proof. change (eval_hfexpr expr_word_22 (closed_word_22 v) (closed_word_22 v) = Some (Gval (Fuint 4) (word_22 v))). apply closed_word_22_value. Qed.
Transparent word_23.
Lemma closed_word_23_value v : eval_hfexpr expr_word_23 (closed_word_23 v) (closed_word_23 v) = Some (Gval (Fuint 5) (word_23 v)).
Proof. unfold word_23, closed_word_23, expr_word_23, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_23.
Lemma node_word_23_value v : eval_hfexpr expr_word_23 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_23 v)).
Proof. change (eval_hfexpr expr_word_23 (closed_word_23 v) (closed_word_23 v) = Some (Gval (Fuint 5) (word_23 v))). apply closed_word_23_value. Qed.
Transparent word_24.
Lemma closed_word_24_value v : eval_hfexpr expr_word_24 (closed_word_24 v) (closed_word_24 v) = Some (Gval (Fuint 4) (word_24 v)).
Proof. unfold word_24, closed_word_24, expr_word_24, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_24.
Lemma node_word_24_value v : eval_hfexpr expr_word_24 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_24 v)).
Proof. change (eval_hfexpr expr_word_24 (closed_word_24 v) (closed_word_24 v) = Some (Gval (Fuint 4) (word_24 v))). apply closed_word_24_value. Qed.
Transparent word_41.
Lemma closed_word_41_value v : eval_hfexpr expr_word_41 (closed_word_41 v) (closed_word_41 v) = Some (Gval (Fuint 1) (word_41 v)).
Proof. unfold word_41, closed_word_41, expr_word_41, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_41.
Lemma node_word_41_value v : eval_hfexpr expr_word_41 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_41 v)).
Proof. change (eval_hfexpr expr_word_41 (closed_word_41 v) (closed_word_41 v) = Some (Gval (Fuint 1) (word_41 v))). apply closed_word_41_value. Qed.
Transparent word_7.
Lemma closed_word_7_value v : eval_hfexpr expr_word_7 (closed_word_7 v) (closed_word_7 v) = Some (Gval (Fuint 1) (word_7 v)).
Proof. unfold word_7, closed_word_7, expr_word_7, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_7.
Lemma node_word_7_value v : eval_hfexpr expr_word_7 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_7 v)).
Proof. change (eval_hfexpr expr_word_7 (closed_word_7 v) (closed_word_7 v) = Some (Gval (Fuint 1) (word_7 v))). apply closed_word_7_value. Qed.
Transparent word_25.
Lemma closed_word_25_value v : eval_hfexpr expr_word_25 (closed_word_25 v) (closed_word_25 v) = Some (Gval (Fuint 4) (word_25 v)).
Proof. unfold word_25, closed_word_25, expr_word_25, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_25.
Lemma node_word_25_value v : eval_hfexpr expr_word_25 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_25 v)).
Proof. change (eval_hfexpr expr_word_25 (closed_word_25 v) (closed_word_25 v) = Some (Gval (Fuint 4) (word_25 v))). apply closed_word_25_value. Qed.
Transparent word_42.
Lemma closed_word_42_value v : eval_hfexpr expr_word_42 (closed_word_42 v) (closed_word_42 v) = Some (Gval (Fuint 1) (word_42 v)).
Proof. unfold word_42, closed_word_42, expr_word_42, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_42.
Lemma node_word_42_value v : eval_hfexpr expr_word_42 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_42 v)).
Proof. change (eval_hfexpr expr_word_42 (closed_word_42 v) (closed_word_42 v) = Some (Gval (Fuint 1) (word_42 v))). apply closed_word_42_value. Qed.
Transparent word_8.
Lemma closed_word_8_value v : eval_hfexpr expr_word_8 (closed_word_8 v) (closed_word_8 v) = Some (Gval (Fuint 1) (word_8 v)).
Proof. unfold word_8, closed_word_8, expr_word_8, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_8.
Lemma node_word_8_value v : eval_hfexpr expr_word_8 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_8 v)).
Proof. change (eval_hfexpr expr_word_8 (closed_word_8 v) (closed_word_8 v) = Some (Gval (Fuint 1) (word_8 v))). apply closed_word_8_value. Qed.
Transparent word_26.
Lemma closed_word_26_value v : eval_hfexpr expr_word_26 (closed_word_26 v) (closed_word_26 v) = Some (Gval (Fuint 4) (word_26 v)).
Proof. unfold word_26, closed_word_26, expr_word_26, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_26.
Lemma node_word_26_value v : eval_hfexpr expr_word_26 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_26 v)).
Proof. change (eval_hfexpr expr_word_26 (closed_word_26 v) (closed_word_26 v) = Some (Gval (Fuint 4) (word_26 v))). apply closed_word_26_value. Qed.
Transparent word_27.
Lemma closed_word_27_value v : eval_hfexpr expr_word_27 (closed_word_27 v) (closed_word_27 v) = Some (Gval (Fuint 5) (word_27 v)).
Proof. unfold word_27, closed_word_27, expr_word_27, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_27.
Lemma node_word_27_value v : eval_hfexpr expr_word_27 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_27 v)).
Proof. change (eval_hfexpr expr_word_27 (closed_word_27 v) (closed_word_27 v) = Some (Gval (Fuint 5) (word_27 v))). apply closed_word_27_value. Qed.
Transparent word_43.
Lemma closed_word_43_value v : eval_hfexpr expr_word_43 (closed_word_43 v) (closed_word_43 v) = Some (Gval (Fuint 1) (word_43 v)).
Proof. unfold word_43, closed_word_43, expr_word_43, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_43.
Lemma node_word_43_value v : eval_hfexpr expr_word_43 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_43 v)).
Proof. change (eval_hfexpr expr_word_43 (closed_word_43 v) (closed_word_43 v) = Some (Gval (Fuint 1) (word_43 v))). apply closed_word_43_value. Qed.
Transparent word_9.
Lemma closed_word_9_value v : eval_hfexpr expr_word_9 (closed_word_9 v) (closed_word_9 v) = Some (Gval (Fuint 1) (word_9 v)).
Proof. unfold word_9, closed_word_9, expr_word_9, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_9.
Lemma node_word_9_value v : eval_hfexpr expr_word_9 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_9 v)).
Proof. change (eval_hfexpr expr_word_9 (closed_word_9 v) (closed_word_9 v) = Some (Gval (Fuint 1) (word_9 v))). apply closed_word_9_value. Qed.
Transparent word_28.
Lemma closed_word_28_value v : eval_hfexpr expr_word_28 (closed_word_28 v) (closed_word_28 v) = Some (Gval (Fuint 4) (word_28 v)).
Proof. unfold word_28, closed_word_28, expr_word_28, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_28.
Lemma node_word_28_value v : eval_hfexpr expr_word_28 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_28 v)).
Proof. change (eval_hfexpr expr_word_28 (closed_word_28 v) (closed_word_28 v) = Some (Gval (Fuint 4) (word_28 v))). apply closed_word_28_value. Qed.
Transparent word_29.
Lemma closed_word_29_value v : eval_hfexpr expr_word_29 (closed_word_29 v) (closed_word_29 v) = Some (Gval (Fuint 5) (word_29 v)).
Proof. unfold word_29, closed_word_29, expr_word_29, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_29.
Lemma node_word_29_value v : eval_hfexpr expr_word_29 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_29 v)).
Proof. change (eval_hfexpr expr_word_29 (closed_word_29 v) (closed_word_29 v) = Some (Gval (Fuint 5) (word_29 v))). apply closed_word_29_value. Qed.
Transparent word_30.
Lemma closed_word_30_value v : eval_hfexpr expr_word_30 (closed_word_30 v) (closed_word_30 v) = Some (Gval (Fuint 6) (word_30 v)).
Proof. unfold word_30, closed_word_30, expr_word_30, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_30.
Lemma node_word_30_value v : eval_hfexpr expr_word_30 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_30 v)).
Proof. change (eval_hfexpr expr_word_30 (closed_word_30 v) (closed_word_30 v) = Some (Gval (Fuint 6) (word_30 v))). apply closed_word_30_value. Qed.
Transparent word_31.
Lemma closed_word_31_value v : eval_hfexpr expr_word_31 (closed_word_31 v) (closed_word_31 v) = Some (Gval (Fuint 5) (word_31 v)).
Proof. unfold word_31, closed_word_31, expr_word_31, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_31.
Lemma node_word_31_value v : eval_hfexpr expr_word_31 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_31 v)).
Proof. change (eval_hfexpr expr_word_31 (closed_word_31 v) (closed_word_31 v) = Some (Gval (Fuint 5) (word_31 v))). apply closed_word_31_value. Qed.
Transparent word_32.
Lemma closed_word_32_value v : eval_hfexpr expr_word_32 (closed_word_32 v) (closed_word_32 v) = Some (Gval (Fuint 6) (word_32 v)).
Proof. unfold word_32, closed_word_32, expr_word_32, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_32.
Lemma node_word_32_value v : eval_hfexpr expr_word_32 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_32 v)).
Proof. change (eval_hfexpr expr_word_32 (closed_word_32 v) (closed_word_32 v) = Some (Gval (Fuint 6) (word_32 v))). apply closed_word_32_value. Qed.
Transparent word_33.
Lemma closed_word_33_value v : eval_hfexpr expr_word_33 (closed_word_33 v) (closed_word_33 v) = Some (Gval (Fuint 5) (word_33 v)).
Proof. unfold word_33, closed_word_33, expr_word_33, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_33.
Lemma node_word_33_value v : eval_hfexpr expr_word_33 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_33 v)).
Proof. change (eval_hfexpr expr_word_33 (closed_word_33 v) (closed_word_33 v) = Some (Gval (Fuint 5) (word_33 v))). apply closed_word_33_value. Qed.
Transparent word_34.
Lemma closed_word_34_value v : eval_hfexpr expr_word_34 (closed_word_34 v) (closed_word_34 v) = Some (Gval (Fuint 1) (word_34 v)).
Proof. unfold word_34, closed_word_34, expr_word_34, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_34.
Lemma node_word_34_value v : eval_hfexpr expr_word_34 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_34 v)).
Proof. change (eval_hfexpr expr_word_34 (closed_word_34 v) (closed_word_34 v) = Some (Gval (Fuint 1) (word_34 v))). apply closed_word_34_value. Qed.
Transparent word_35.
Lemma closed_word_35_value v : eval_hfexpr expr_word_35 (closed_word_35 v) (closed_word_35 v) = Some (Gval (Fuint 1) (word_35 v)).
Proof. unfold word_35, closed_word_35, expr_word_35, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_35.
Lemma node_word_35_value v : eval_hfexpr expr_word_35 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_35 v)).
Proof. change (eval_hfexpr expr_word_35 (closed_word_35 v) (closed_word_35 v) = Some (Gval (Fuint 1) (word_35 v))). apply closed_word_35_value. Qed.
Transparent word_36.
Lemma closed_word_36_value v : eval_hfexpr expr_word_36 (closed_word_36 v) (closed_word_36 v) = Some (Gval (Fuint 1) (word_36 v)).
Proof. unfold word_36, closed_word_36, expr_word_36, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_36.
Lemma node_word_36_value v : eval_hfexpr expr_word_36 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_36 v)).
Proof. change (eval_hfexpr expr_word_36 (closed_word_36 v) (closed_word_36 v) = Some (Gval (Fuint 1) (word_36 v))). apply closed_word_36_value. Qed.
Transparent word_37.
Lemma closed_word_37_value v : eval_hfexpr expr_word_37 (closed_word_37 v) (closed_word_37 v) = Some (Gval (Fuint 1) (word_37 v)).
Proof. unfold word_37, closed_word_37, expr_word_37, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_37.
Lemma node_word_37_value v : eval_hfexpr expr_word_37 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_37 v)).
Proof. change (eval_hfexpr expr_word_37 (closed_word_37 v) (closed_word_37 v) = Some (Gval (Fuint 1) (word_37 v))). apply closed_word_37_value. Qed.
Transparent word_38.
Lemma closed_word_38_value v : eval_hfexpr expr_word_38 (closed_word_38 v) (closed_word_38 v) = Some (Gval (Fuint 1) (word_38 v)).
Proof. unfold word_38, closed_word_38, expr_word_38, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_38.
Lemma node_word_38_value v : eval_hfexpr expr_word_38 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_38 v)).
Proof. change (eval_hfexpr expr_word_38 (closed_word_38 v) (closed_word_38 v) = Some (Gval (Fuint 1) (word_38 v))). apply closed_word_38_value. Qed.
Transparent word_39.
Lemma closed_word_39_value v : eval_hfexpr expr_word_39 (closed_word_39 v) (closed_word_39 v) = Some (Gval (Fuint 1) (word_39 v)).
Proof. unfold word_39, closed_word_39, expr_word_39, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_39.
Lemma node_word_39_value v : eval_hfexpr expr_word_39 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_39 v)).
Proof. change (eval_hfexpr expr_word_39 (closed_word_39 v) (closed_word_39 v) = Some (Gval (Fuint 1) (word_39 v))). apply closed_word_39_value. Qed.
Transparent word_40.
Lemma closed_word_40_value v : eval_hfexpr expr_word_40 (closed_word_40 v) (closed_word_40 v) = Some (Gval (Fuint 1) (word_40 v)).
Proof. unfold word_40, closed_word_40, expr_word_40, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type convert_to_bundle_value]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type convert_to_bundle_value]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val type_of_bundle_val make_ftype_explicit extend_hvalue_as_type convert_to_bundle_value]; reflexivity. Qed.
Opaque word_40.
Lemma node_word_40_value v : eval_hfexpr expr_word_40 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_40 v)).
Proof. change (eval_hfexpr expr_word_40 (closed_word_40 v) (closed_word_40 v) = Some (Gval (Fuint 1) (word_40 v))). apply closed_word_40_value. Qed.
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

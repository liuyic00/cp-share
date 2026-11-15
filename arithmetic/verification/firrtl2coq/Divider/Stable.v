(* Generated from the original deep-embedded AST.  No proof assumptions. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
  HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From Divider Require Import Model.
Local Open Scope N_scope.
Lemma refine_ground known t b : refine_boolean_result known (Some (Gval t b)) = Some (Gval t b).
Proof. destruct known; reflexivity. Qed.
Fixpoint find_driver (id : N) (stmts : @hfstmt_seq VarOrder.T) : option (@hfexpr VarOrder.T) :=
 match stmts with
 | Qnil => None
 | Qcons (Snode n e) tail => if id == n then Some e else find_driver id tail
 | Qcons (Sfcnct (Eid n) e) tail => if id == n then Some e else find_driver id tail
 | Qcons _ tail => find_driver id tail
 end.
Definition leaf_values := N -> bits.
Definition word_of_eval (v : option hvalue) : bits :=
 match v with Some (Gval _ b) => b | _ => [::] end.

Definition word_0 (v : leaf_values) := v 0.
Definition word_1 (v : leaf_values) := v 1.
Definition word_3 (v : leaf_values) := v 3.
Definition word_4 (v : leaf_values) := v 4.
Definition word_5 (v : leaf_values) := v 5.
Definition word_6 (v : leaf_values) := v 6.
Definition word_7 (v : leaf_values) := v 7.
Definition word_10 (v : leaf_values) := v 10.
Definition word_11 (v : leaf_values) := v 11.
Definition word_12 (v : leaf_values) := v 12.
Definition word_13 (v : leaf_values) := v 13.
Definition word_18 (v : leaf_values) := v 18.
Definition word_20 (v : leaf_values) := v 20.
Definition word_33 (v : leaf_values) := v 33.
Definition word_38 (v : leaf_values) := v 38.
Definition word_40 (v : leaf_values) := v 40.
Definition word_43 (v : leaf_values) := v 43.
Definition word_45 (v : leaf_values) := v 45.
Definition word_46 (v : leaf_values) := v 46.
Definition word_47 (v : leaf_values) := v 47.
Definition word_51 (v : leaf_values) := v 51.
Definition word_445 (v : leaf_values) := v 445.
Definition word_446 (v : leaf_values) := v 446.
Definition word_447 (v : leaf_values) := v 447.
Definition word_475 (v : leaf_values) := v 475.
Definition word_476 (v : leaf_values) := v 476.
Definition expr_14 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::false; false; false])).
Definition closed_14 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_14 (v : leaf_values) := word_of_eval (eval_hfexpr expr_14 (closed_14 v) (closed_14 v)).
Definition expr_420 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::false; false; false])).
Definition closed_420 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_420 (v : leaf_values) := word_of_eval (eval_hfexpr expr_420 (closed_420 v) (closed_420 v)).
Definition expr_2 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 420)).
Definition closed_2 (v : leaf_values) : VM.t hvalue := (VM.add 420 (Gval (Fuint 1) (word_420 v)) (VM.empty hvalue)).
Definition word_2 (v : leaf_values) := word_of_eval (eval_hfexpr expr_2 (closed_2 v) (closed_2 v)).
Definition expr_15 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 2)) (@Eref VarOrder.T (@Eid VarOrder.T 3))).
Definition closed_15 (v : leaf_values) : VM.t hvalue := (VM.add 3 (Gval (Fuint 1) (word_3 v)) (VM.add 2 (Gval (Fuint 1) (word_2 v)) (VM.empty hvalue))).
Definition word_15 (v : leaf_values) := word_of_eval (eval_hfexpr expr_15 (closed_15 v) (closed_15 v)).
Definition expr_16 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 14)) (@Eref VarOrder.T (@Eid VarOrder.T 15))).
Definition closed_16 (v : leaf_values) : VM.t hvalue := (VM.add 15 (Gval (Fuint 1) (word_15 v)) (VM.add 14 (Gval (Fuint 1) (word_14 v)) (VM.empty hvalue))).
Definition word_16 (v : leaf_values) := word_of_eval (eval_hfexpr expr_16 (closed_16 v) (closed_16 v)).
Definition expr_17 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 5)) (@Econst VarOrder.T (Fuint 64) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition closed_17 (v : leaf_values) : VM.t hvalue := (VM.add 5 (Gval (Fuint 64) (word_5 v)) (VM.empty hvalue)).
Definition word_17 (v : leaf_values) := word_of_eval (eval_hfexpr expr_17 (closed_17 v) (closed_17 v)).
Definition expr_19 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 17)) (@Eref VarOrder.T (@Eid VarOrder.T 18))).
Definition closed_19 (v : leaf_values) : VM.t hvalue := (VM.add 18 (Gval (Fuint 1) (word_18 v)) (VM.add 17 (Gval (Fuint 1) (word_17 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)))).
Definition word_19 (v : leaf_values) := word_of_eval (eval_hfexpr expr_19 (closed_19 v) (closed_19 v)).
Definition expr_21 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 128 64) (@Eref VarOrder.T (@Eid VarOrder.T 20))).
Definition closed_21 (v : leaf_values) : VM.t hvalue := (VM.add 20 (Gval (Fuint 129) (word_20 v)) (VM.empty hvalue)).
Definition word_21 (v : leaf_values) := word_of_eval (eval_hfexpr expr_21 (closed_21 v) (closed_21 v)).
Definition expr_22 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 63 0) (@Eref VarOrder.T (@Eid VarOrder.T 20))).
Definition closed_22 (v : leaf_values) : VM.t hvalue := (VM.add 20 (Gval (Fuint 129) (word_20 v)) (VM.empty hvalue)).
Definition word_22 (v : leaf_values) := word_of_eval (eval_hfexpr expr_22 (closed_22 v) (closed_22 v)).
Definition expr_23 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 63 63) (@Eref VarOrder.T (@Eid VarOrder.T 4))).
Definition closed_23 (v : leaf_values) : VM.t hvalue := (VM.add 4 (Gval (Fuint 64) (word_4 v)) (VM.empty hvalue)).
Definition word_23 (v : leaf_values) := word_of_eval (eval_hfexpr expr_23 (closed_23 v) (closed_23 v)).
Definition expr_24 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 23)) (@Eref VarOrder.T (@Eid VarOrder.T 10))).
Definition closed_24 (v : leaf_values) : VM.t hvalue := (VM.add 23 (Gval (Fuint 1) (word_23 v)) (VM.add 10 (Gval (Fuint 1) (word_10 v)) (VM.empty hvalue))).
Definition word_24 (v : leaf_values) := word_of_eval (eval_hfexpr expr_24 (closed_24 v) (closed_24 v)).
Definition expr_25 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 4))).
Definition closed_25 (v : leaf_values) : VM.t hvalue := (VM.add 4 (Gval (Fuint 64) (word_4 v)) (VM.empty hvalue)).
Definition word_25 (v : leaf_values) := word_of_eval (eval_hfexpr expr_25 (closed_25 v) (closed_25 v)).
Definition expr_26 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 25))).
Definition closed_26 (v : leaf_values) : VM.t hvalue := (VM.add 25 (Gval (Fuint 65) (word_25 v)) (VM.empty hvalue)).
Definition word_26 (v : leaf_values) := word_of_eval (eval_hfexpr expr_26 (closed_26 v) (closed_26 v)).
Definition expr_27 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 24)) (@Eref VarOrder.T (@Eid VarOrder.T 26)) (@Eref VarOrder.T (@Eid VarOrder.T 4))).
Definition closed_27 (v : leaf_values) : VM.t hvalue := (VM.add 26 (Gval (Fuint 64) (word_26 v)) (VM.add 24 (Gval (Fuint 1) (word_24 v)) (VM.add 4 (Gval (Fuint 64) (word_4 v)) (VM.empty hvalue)))).
Definition word_27 (v : leaf_values) := word_of_eval (eval_hfexpr expr_27 (closed_27 v) (closed_27 v)).
Definition expr_28 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 63 63) (@Eref VarOrder.T (@Eid VarOrder.T 5))).
Definition closed_28 (v : leaf_values) : VM.t hvalue := (VM.add 5 (Gval (Fuint 64) (word_5 v)) (VM.empty hvalue)).
Definition word_28 (v : leaf_values) := word_of_eval (eval_hfexpr expr_28 (closed_28 v) (closed_28 v)).
Definition expr_29 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 28)) (@Eref VarOrder.T (@Eid VarOrder.T 10))).
Definition closed_29 (v : leaf_values) : VM.t hvalue := (VM.add 28 (Gval (Fuint 1) (word_28 v)) (VM.add 10 (Gval (Fuint 1) (word_10 v)) (VM.empty hvalue))).
Definition word_29 (v : leaf_values) := word_of_eval (eval_hfexpr expr_29 (closed_29 v) (closed_29 v)).
Definition expr_30 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 5))).
Definition closed_30 (v : leaf_values) : VM.t hvalue := (VM.add 5 (Gval (Fuint 64) (word_5 v)) (VM.empty hvalue)).
Definition word_30 (v : leaf_values) := word_of_eval (eval_hfexpr expr_30 (closed_30 v) (closed_30 v)).
Definition expr_31 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 30))).
Definition closed_31 (v : leaf_values) : VM.t hvalue := (VM.add 30 (Gval (Fuint 65) (word_30 v)) (VM.empty hvalue)).
Definition word_31 (v : leaf_values) := word_of_eval (eval_hfexpr expr_31 (closed_31 v) (closed_31 v)).
Definition expr_32 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 29)) (@Eref VarOrder.T (@Eid VarOrder.T 31)) (@Eref VarOrder.T (@Eid VarOrder.T 5))).
Definition closed_32 (v : leaf_values) : VM.t hvalue := (VM.add 31 (Gval (Fuint 64) (word_31 v)) (VM.add 29 (Gval (Fuint 1) (word_29 v)) (VM.add 5 (Gval (Fuint 64) (word_5 v)) (VM.empty hvalue)))).
Definition word_32 (v : leaf_values) := word_of_eval (eval_hfexpr expr_32 (closed_32 v) (closed_32 v)).
Definition expr_34 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 24)) (@Eref VarOrder.T (@Eid VarOrder.T 33))).
Definition closed_34 (v : leaf_values) : VM.t hvalue := (VM.add 33 (Gval (Fuint 1) (word_33 v)) (VM.add 24 (Gval (Fuint 1) (word_24 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)))).
Definition word_34 (v : leaf_values) := word_of_eval (eval_hfexpr expr_34 (closed_34 v) (closed_34 v)).
Definition expr_35 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 24)) (@Eref VarOrder.T (@Eid VarOrder.T 29))).
Definition closed_35 (v : leaf_values) : VM.t hvalue := (VM.add 29 (Gval (Fuint 1) (word_29 v)) (VM.add 24 (Gval (Fuint 1) (word_24 v)) (VM.empty hvalue))).
Definition word_35 (v : leaf_values) := word_of_eval (eval_hfexpr expr_35 (closed_35 v) (closed_35 v)).
Definition expr_36 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 17)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_36 (v : leaf_values) : VM.t hvalue := (VM.add 17 (Gval (Fuint 1) (word_17 v)) (VM.empty hvalue)).
Definition word_36 (v : leaf_values) := word_of_eval (eval_hfexpr expr_36 (closed_36 v) (closed_36 v)).
Definition expr_37 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 35)) (@Eref VarOrder.T (@Eid VarOrder.T 36))).
Definition closed_37 (v : leaf_values) : VM.t hvalue := (VM.add 36 (Gval (Fuint 1) (word_36 v)) (VM.add 35 (Gval (Fuint 1) (word_35 v)) (VM.empty hvalue))).
Definition word_37 (v : leaf_values) := word_of_eval (eval_hfexpr expr_37 (closed_37 v) (closed_37 v)).
Definition expr_39 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 37)) (@Eref VarOrder.T (@Eid VarOrder.T 38))).
Definition closed_39 (v : leaf_values) : VM.t hvalue := (VM.add 38 (Gval (Fuint 1) (word_38 v)) (VM.add 37 (Gval (Fuint 1) (word_37 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)))).
Definition word_39 (v : leaf_values) := word_of_eval (eval_hfexpr expr_39 (closed_39 v) (closed_39 v)).
Definition expr_41 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 32)) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_41 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.add 32 (Gval (Fuint 64) (word_32 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)))).
Definition word_41 (v : leaf_values) := word_of_eval (eval_hfexpr expr_41 (closed_41 v) (closed_41 v)).
Definition expr_42 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 27)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_42 (v : leaf_values) : VM.t hvalue := (VM.add 27 (Gval (Fuint 64) (word_27 v)) (VM.empty hvalue)).
Definition word_42 (v : leaf_values) := word_of_eval (eval_hfexpr expr_42 (closed_42 v) (closed_42 v)).
Definition expr_44 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Eref VarOrder.T (@Eid VarOrder.T 43))).
Definition closed_44 (v : leaf_values) : VM.t hvalue := (VM.add 43 (Gval (Fuint 65) (word_43 v)) (VM.add 42 (Gval (Fuint 65) (word_42 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)))).
Definition word_44 (v : leaf_values) := word_of_eval (eval_hfexpr expr_44 (closed_44 v) (closed_44 v)).
Definition expr_48 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 12)) (@Eref VarOrder.T (@Eid VarOrder.T 47))).
Definition closed_48 (v : leaf_values) : VM.t hvalue := (VM.add 47 (Gval (Fuint 1) (word_47 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.add 12 (Gval (Fuint 1) (word_12 v)) (VM.empty hvalue)))).
Definition word_48 (v : leaf_values) := word_of_eval (eval_hfexpr expr_48 (closed_48 v) (closed_48 v)).
Definition expr_49 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 11)) (@Eref VarOrder.T (@Eid VarOrder.T 46))).
Definition closed_49 (v : leaf_values) : VM.t hvalue := (VM.add 46 (Gval (Fuint 1) (word_46 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.add 11 (Gval (Fuint 1) (word_11 v)) (VM.empty hvalue)))).
Definition word_49 (v : leaf_values) := word_of_eval (eval_hfexpr expr_49 (closed_49 v) (closed_49 v)).
Definition expr_50 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 10)) (@Eref VarOrder.T (@Eid VarOrder.T 45))).
Definition closed_50 (v : leaf_values) : VM.t hvalue := (VM.add 45 (Gval (Fuint 1) (word_45 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.add 10 (Gval (Fuint 1) (word_10 v)) (VM.empty hvalue)))).
Definition word_50 (v : leaf_values) := word_of_eval (eval_hfexpr expr_50 (closed_50 v) (closed_50 v)).
Definition expr_52 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::true; false; false])).
Definition closed_52 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_52 (v : leaf_values) := word_of_eval (eval_hfexpr expr_52 (closed_52 v) (closed_52 v)).
Definition expr_53 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 63 32) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_53 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.empty hvalue)).
Definition word_53 (v : leaf_values) := word_of_eval (eval_hfexpr expr_53 (closed_53 v) (closed_53 v)).
Definition expr_54 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_54 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.empty hvalue)).
Definition word_54 (v : leaf_values) := word_of_eval (eval_hfexpr expr_54 (closed_54 v) (closed_54 v)).
Definition expr_55 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 53))).
Definition closed_55 (v : leaf_values) : VM.t hvalue := (VM.add 53 (Gval (Fuint 32) (word_53 v)) (VM.empty hvalue)).
Definition word_55 (v : leaf_values) := word_of_eval (eval_hfexpr expr_55 (closed_55 v) (closed_55 v)).
Definition expr_56 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 16) (@Eref VarOrder.T (@Eid VarOrder.T 53))).
Definition closed_56 (v : leaf_values) : VM.t hvalue := (VM.add 53 (Gval (Fuint 32) (word_53 v)) (VM.empty hvalue)).
Definition word_56 (v : leaf_values) := word_of_eval (eval_hfexpr expr_56 (closed_56 v) (closed_56 v)).
Definition expr_57 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 53))).
Definition closed_57 (v : leaf_values) : VM.t hvalue := (VM.add 53 (Gval (Fuint 32) (word_53 v)) (VM.empty hvalue)).
Definition word_57 (v : leaf_values) := word_of_eval (eval_hfexpr expr_57 (closed_57 v) (closed_57 v)).
Definition expr_58 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 56))).
Definition closed_58 (v : leaf_values) : VM.t hvalue := (VM.add 56 (Gval (Fuint 16) (word_56 v)) (VM.empty hvalue)).
Definition word_58 (v : leaf_values) := word_of_eval (eval_hfexpr expr_58 (closed_58 v) (closed_58 v)).
Definition expr_59 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 56))).
Definition closed_59 (v : leaf_values) : VM.t hvalue := (VM.add 56 (Gval (Fuint 16) (word_56 v)) (VM.empty hvalue)).
Definition word_59 (v : leaf_values) := word_of_eval (eval_hfexpr expr_59 (closed_59 v) (closed_59 v)).
Definition expr_60 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 56))).
Definition closed_60 (v : leaf_values) : VM.t hvalue := (VM.add 56 (Gval (Fuint 16) (word_56 v)) (VM.empty hvalue)).
Definition word_60 (v : leaf_values) := word_of_eval (eval_hfexpr expr_60 (closed_60 v) (closed_60 v)).
Definition expr_61 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 59))).
Definition closed_61 (v : leaf_values) : VM.t hvalue := (VM.add 59 (Gval (Fuint 8) (word_59 v)) (VM.empty hvalue)).
Definition word_61 (v : leaf_values) := word_of_eval (eval_hfexpr expr_61 (closed_61 v) (closed_61 v)).
Definition expr_62 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 59))).
Definition closed_62 (v : leaf_values) : VM.t hvalue := (VM.add 59 (Gval (Fuint 8) (word_59 v)) (VM.empty hvalue)).
Definition word_62 (v : leaf_values) := word_of_eval (eval_hfexpr expr_62 (closed_62 v) (closed_62 v)).
Definition expr_63 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 59))).
Definition closed_63 (v : leaf_values) : VM.t hvalue := (VM.add 59 (Gval (Fuint 8) (word_59 v)) (VM.empty hvalue)).
Definition word_63 (v : leaf_values) := word_of_eval (eval_hfexpr expr_63 (closed_63 v) (closed_63 v)).
Definition expr_64 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 62))).
Definition closed_64 (v : leaf_values) : VM.t hvalue := (VM.add 62 (Gval (Fuint 4) (word_62 v)) (VM.empty hvalue)).
Definition word_64 (v : leaf_values) := word_of_eval (eval_hfexpr expr_64 (closed_64 v) (closed_64 v)).
Definition expr_65 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 62))).
Definition closed_65 (v : leaf_values) : VM.t hvalue := (VM.add 62 (Gval (Fuint 4) (word_62 v)) (VM.empty hvalue)).
Definition word_65 (v : leaf_values) := word_of_eval (eval_hfexpr expr_65 (closed_65 v) (closed_65 v)).
Definition expr_66 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 62))).
Definition closed_66 (v : leaf_values) : VM.t hvalue := (VM.add 62 (Gval (Fuint 4) (word_62 v)) (VM.empty hvalue)).
Definition word_66 (v : leaf_values) := word_of_eval (eval_hfexpr expr_66 (closed_66 v) (closed_66 v)).
Definition expr_67 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 62))).
Definition closed_67 (v : leaf_values) : VM.t hvalue := (VM.add 62 (Gval (Fuint 4) (word_62 v)) (VM.empty hvalue)).
Definition word_67 (v : leaf_values) := word_of_eval (eval_hfexpr expr_67 (closed_67 v) (closed_67 v)).
Definition expr_68 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 66)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 67))).
Definition closed_68 (v : leaf_values) : VM.t hvalue := (VM.add 67 (Gval (Fuint 1) (word_67 v)) (VM.add 66 (Gval (Fuint 1) (word_66 v)) (VM.empty hvalue))).
Definition word_68 (v : leaf_values) := word_of_eval (eval_hfexpr expr_68 (closed_68 v) (closed_68 v)).
Definition expr_69 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 68))).
Definition closed_69 (v : leaf_values) : VM.t hvalue := (VM.add 68 (Gval (Fuint 2) (word_68 v)) (VM.add 65 (Gval (Fuint 1) (word_65 v)) (VM.empty hvalue))).
Definition word_69 (v : leaf_values) := word_of_eval (eval_hfexpr expr_69 (closed_69 v) (closed_69 v)).
Definition expr_70 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 63))).
Definition closed_70 (v : leaf_values) : VM.t hvalue := (VM.add 63 (Gval (Fuint 4) (word_63 v)) (VM.empty hvalue)).
Definition word_70 (v : leaf_values) := word_of_eval (eval_hfexpr expr_70 (closed_70 v) (closed_70 v)).
Definition expr_71 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 63))).
Definition closed_71 (v : leaf_values) : VM.t hvalue := (VM.add 63 (Gval (Fuint 4) (word_63 v)) (VM.empty hvalue)).
Definition word_71 (v : leaf_values) := word_of_eval (eval_hfexpr expr_71 (closed_71 v) (closed_71 v)).
Definition expr_72 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 63))).
Definition closed_72 (v : leaf_values) : VM.t hvalue := (VM.add 63 (Gval (Fuint 4) (word_63 v)) (VM.empty hvalue)).
Definition word_72 (v : leaf_values) := word_of_eval (eval_hfexpr expr_72 (closed_72 v) (closed_72 v)).
Definition expr_73 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 71)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 72))).
Definition closed_73 (v : leaf_values) : VM.t hvalue := (VM.add 72 (Gval (Fuint 1) (word_72 v)) (VM.add 71 (Gval (Fuint 1) (word_71 v)) (VM.empty hvalue))).
Definition word_73 (v : leaf_values) := word_of_eval (eval_hfexpr expr_73 (closed_73 v) (closed_73 v)).
Definition expr_74 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 70)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 73))).
Definition closed_74 (v : leaf_values) : VM.t hvalue := (VM.add 73 (Gval (Fuint 2) (word_73 v)) (VM.add 70 (Gval (Fuint 1) (word_70 v)) (VM.empty hvalue))).
Definition word_74 (v : leaf_values) := word_of_eval (eval_hfexpr expr_74 (closed_74 v) (closed_74 v)).
Definition expr_75 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 64)) (@Eref VarOrder.T (@Eid VarOrder.T 69)) (@Eref VarOrder.T (@Eid VarOrder.T 74))).
Definition closed_75 (v : leaf_values) : VM.t hvalue := (VM.add 74 (Gval (Fuint 2) (word_74 v)) (VM.add 69 (Gval (Fuint 2) (word_69 v)) (VM.add 64 (Gval (Fuint 1) (word_64 v)) (VM.empty hvalue)))).
Definition word_75 (v : leaf_values) := word_of_eval (eval_hfexpr expr_75 (closed_75 v) (closed_75 v)).
Definition expr_76 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 64)) (@Eref VarOrder.T (@Eid VarOrder.T 75))).
Definition closed_76 (v : leaf_values) : VM.t hvalue := (VM.add 75 (Gval (Fuint 2) (word_75 v)) (VM.add 64 (Gval (Fuint 1) (word_64 v)) (VM.empty hvalue))).
Definition word_76 (v : leaf_values) := word_of_eval (eval_hfexpr expr_76 (closed_76 v) (closed_76 v)).
Definition expr_77 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 60))).
Definition closed_77 (v : leaf_values) : VM.t hvalue := (VM.add 60 (Gval (Fuint 8) (word_60 v)) (VM.empty hvalue)).
Definition word_77 (v : leaf_values) := word_of_eval (eval_hfexpr expr_77 (closed_77 v) (closed_77 v)).
Definition expr_78 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 60))).
Definition closed_78 (v : leaf_values) : VM.t hvalue := (VM.add 60 (Gval (Fuint 8) (word_60 v)) (VM.empty hvalue)).
Definition word_78 (v : leaf_values) := word_of_eval (eval_hfexpr expr_78 (closed_78 v) (closed_78 v)).
Definition expr_79 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 77))).
Definition closed_79 (v : leaf_values) : VM.t hvalue := (VM.add 77 (Gval (Fuint 4) (word_77 v)) (VM.empty hvalue)).
Definition word_79 (v : leaf_values) := word_of_eval (eval_hfexpr expr_79 (closed_79 v) (closed_79 v)).
Definition expr_80 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 77))).
Definition closed_80 (v : leaf_values) : VM.t hvalue := (VM.add 77 (Gval (Fuint 4) (word_77 v)) (VM.empty hvalue)).
Definition word_80 (v : leaf_values) := word_of_eval (eval_hfexpr expr_80 (closed_80 v) (closed_80 v)).
Definition expr_81 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 77))).
Definition closed_81 (v : leaf_values) : VM.t hvalue := (VM.add 77 (Gval (Fuint 4) (word_77 v)) (VM.empty hvalue)).
Definition word_81 (v : leaf_values) := word_of_eval (eval_hfexpr expr_81 (closed_81 v) (closed_81 v)).
Definition expr_82 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 77))).
Definition closed_82 (v : leaf_values) : VM.t hvalue := (VM.add 77 (Gval (Fuint 4) (word_77 v)) (VM.empty hvalue)).
Definition word_82 (v : leaf_values) := word_of_eval (eval_hfexpr expr_82 (closed_82 v) (closed_82 v)).
Definition expr_83 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 81)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 82))).
Definition closed_83 (v : leaf_values) : VM.t hvalue := (VM.add 82 (Gval (Fuint 1) (word_82 v)) (VM.add 81 (Gval (Fuint 1) (word_81 v)) (VM.empty hvalue))).
Definition word_83 (v : leaf_values) := word_of_eval (eval_hfexpr expr_83 (closed_83 v) (closed_83 v)).
Definition expr_84 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 80)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 83))).
Definition closed_84 (v : leaf_values) : VM.t hvalue := (VM.add 83 (Gval (Fuint 2) (word_83 v)) (VM.add 80 (Gval (Fuint 1) (word_80 v)) (VM.empty hvalue))).
Definition word_84 (v : leaf_values) := word_of_eval (eval_hfexpr expr_84 (closed_84 v) (closed_84 v)).
Definition expr_85 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 78))).
Definition closed_85 (v : leaf_values) : VM.t hvalue := (VM.add 78 (Gval (Fuint 4) (word_78 v)) (VM.empty hvalue)).
Definition word_85 (v : leaf_values) := word_of_eval (eval_hfexpr expr_85 (closed_85 v) (closed_85 v)).
Definition expr_86 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 78))).
Definition closed_86 (v : leaf_values) : VM.t hvalue := (VM.add 78 (Gval (Fuint 4) (word_78 v)) (VM.empty hvalue)).
Definition word_86 (v : leaf_values) := word_of_eval (eval_hfexpr expr_86 (closed_86 v) (closed_86 v)).
Definition expr_87 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 78))).
Definition closed_87 (v : leaf_values) : VM.t hvalue := (VM.add 78 (Gval (Fuint 4) (word_78 v)) (VM.empty hvalue)).
Definition word_87 (v : leaf_values) := word_of_eval (eval_hfexpr expr_87 (closed_87 v) (closed_87 v)).
Definition expr_88 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 86)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 87))).
Definition closed_88 (v : leaf_values) : VM.t hvalue := (VM.add 87 (Gval (Fuint 1) (word_87 v)) (VM.add 86 (Gval (Fuint 1) (word_86 v)) (VM.empty hvalue))).
Definition word_88 (v : leaf_values) := word_of_eval (eval_hfexpr expr_88 (closed_88 v) (closed_88 v)).
Definition expr_89 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 85)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 88))).
Definition closed_89 (v : leaf_values) : VM.t hvalue := (VM.add 88 (Gval (Fuint 2) (word_88 v)) (VM.add 85 (Gval (Fuint 1) (word_85 v)) (VM.empty hvalue))).
Definition word_89 (v : leaf_values) := word_of_eval (eval_hfexpr expr_89 (closed_89 v) (closed_89 v)).
Definition expr_90 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 79)) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Eref VarOrder.T (@Eid VarOrder.T 89))).
Definition closed_90 (v : leaf_values) : VM.t hvalue := (VM.add 89 (Gval (Fuint 2) (word_89 v)) (VM.add 84 (Gval (Fuint 2) (word_84 v)) (VM.add 79 (Gval (Fuint 1) (word_79 v)) (VM.empty hvalue)))).
Definition word_90 (v : leaf_values) := word_of_eval (eval_hfexpr expr_90 (closed_90 v) (closed_90 v)).
Definition expr_91 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 79)) (@Eref VarOrder.T (@Eid VarOrder.T 90))).
Definition closed_91 (v : leaf_values) : VM.t hvalue := (VM.add 90 (Gval (Fuint 2) (word_90 v)) (VM.add 79 (Gval (Fuint 1) (word_79 v)) (VM.empty hvalue))).
Definition word_91 (v : leaf_values) := word_of_eval (eval_hfexpr expr_91 (closed_91 v) (closed_91 v)).
Definition expr_92 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 61)) (@Eref VarOrder.T (@Eid VarOrder.T 76)) (@Eref VarOrder.T (@Eid VarOrder.T 91))).
Definition closed_92 (v : leaf_values) : VM.t hvalue := (VM.add 91 (Gval (Fuint 3) (word_91 v)) (VM.add 76 (Gval (Fuint 3) (word_76 v)) (VM.add 61 (Gval (Fuint 1) (word_61 v)) (VM.empty hvalue)))).
Definition word_92 (v : leaf_values) := word_of_eval (eval_hfexpr expr_92 (closed_92 v) (closed_92 v)).
Definition expr_93 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 61)) (@Eref VarOrder.T (@Eid VarOrder.T 92))).
Definition closed_93 (v : leaf_values) : VM.t hvalue := (VM.add 92 (Gval (Fuint 3) (word_92 v)) (VM.add 61 (Gval (Fuint 1) (word_61 v)) (VM.empty hvalue))).
Definition word_93 (v : leaf_values) := word_of_eval (eval_hfexpr expr_93 (closed_93 v) (closed_93 v)).
Definition expr_94 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 57))).
Definition closed_94 (v : leaf_values) : VM.t hvalue := (VM.add 57 (Gval (Fuint 16) (word_57 v)) (VM.empty hvalue)).
Definition word_94 (v : leaf_values) := word_of_eval (eval_hfexpr expr_94 (closed_94 v) (closed_94 v)).
Definition expr_95 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 57))).
Definition closed_95 (v : leaf_values) : VM.t hvalue := (VM.add 57 (Gval (Fuint 16) (word_57 v)) (VM.empty hvalue)).
Definition word_95 (v : leaf_values) := word_of_eval (eval_hfexpr expr_95 (closed_95 v) (closed_95 v)).
Definition expr_96 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 94))).
Definition closed_96 (v : leaf_values) : VM.t hvalue := (VM.add 94 (Gval (Fuint 8) (word_94 v)) (VM.empty hvalue)).
Definition word_96 (v : leaf_values) := word_of_eval (eval_hfexpr expr_96 (closed_96 v) (closed_96 v)).
Definition expr_97 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 94))).
Definition closed_97 (v : leaf_values) : VM.t hvalue := (VM.add 94 (Gval (Fuint 8) (word_94 v)) (VM.empty hvalue)).
Definition word_97 (v : leaf_values) := word_of_eval (eval_hfexpr expr_97 (closed_97 v) (closed_97 v)).
Definition expr_98 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 94))).
Definition closed_98 (v : leaf_values) : VM.t hvalue := (VM.add 94 (Gval (Fuint 8) (word_94 v)) (VM.empty hvalue)).
Definition word_98 (v : leaf_values) := word_of_eval (eval_hfexpr expr_98 (closed_98 v) (closed_98 v)).
Definition expr_99 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 97))).
Definition closed_99 (v : leaf_values) : VM.t hvalue := (VM.add 97 (Gval (Fuint 4) (word_97 v)) (VM.empty hvalue)).
Definition word_99 (v : leaf_values) := word_of_eval (eval_hfexpr expr_99 (closed_99 v) (closed_99 v)).
Definition expr_100 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 97))).
Definition closed_100 (v : leaf_values) : VM.t hvalue := (VM.add 97 (Gval (Fuint 4) (word_97 v)) (VM.empty hvalue)).
Definition word_100 (v : leaf_values) := word_of_eval (eval_hfexpr expr_100 (closed_100 v) (closed_100 v)).
Definition expr_101 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 97))).
Definition closed_101 (v : leaf_values) : VM.t hvalue := (VM.add 97 (Gval (Fuint 4) (word_97 v)) (VM.empty hvalue)).
Definition word_101 (v : leaf_values) := word_of_eval (eval_hfexpr expr_101 (closed_101 v) (closed_101 v)).
Definition expr_102 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 97))).
Definition closed_102 (v : leaf_values) : VM.t hvalue := (VM.add 97 (Gval (Fuint 4) (word_97 v)) (VM.empty hvalue)).
Definition word_102 (v : leaf_values) := word_of_eval (eval_hfexpr expr_102 (closed_102 v) (closed_102 v)).
Definition expr_103 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 101)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 102))).
Definition closed_103 (v : leaf_values) : VM.t hvalue := (VM.add 102 (Gval (Fuint 1) (word_102 v)) (VM.add 101 (Gval (Fuint 1) (word_101 v)) (VM.empty hvalue))).
Definition word_103 (v : leaf_values) := word_of_eval (eval_hfexpr expr_103 (closed_103 v) (closed_103 v)).
Definition expr_104 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 100)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 103))).
Definition closed_104 (v : leaf_values) : VM.t hvalue := (VM.add 103 (Gval (Fuint 2) (word_103 v)) (VM.add 100 (Gval (Fuint 1) (word_100 v)) (VM.empty hvalue))).
Definition word_104 (v : leaf_values) := word_of_eval (eval_hfexpr expr_104 (closed_104 v) (closed_104 v)).
Definition expr_105 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 98))).
Definition closed_105 (v : leaf_values) : VM.t hvalue := (VM.add 98 (Gval (Fuint 4) (word_98 v)) (VM.empty hvalue)).
Definition word_105 (v : leaf_values) := word_of_eval (eval_hfexpr expr_105 (closed_105 v) (closed_105 v)).
Definition expr_106 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 98))).
Definition closed_106 (v : leaf_values) : VM.t hvalue := (VM.add 98 (Gval (Fuint 4) (word_98 v)) (VM.empty hvalue)).
Definition word_106 (v : leaf_values) := word_of_eval (eval_hfexpr expr_106 (closed_106 v) (closed_106 v)).
Definition expr_107 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 98))).
Definition closed_107 (v : leaf_values) : VM.t hvalue := (VM.add 98 (Gval (Fuint 4) (word_98 v)) (VM.empty hvalue)).
Definition word_107 (v : leaf_values) := word_of_eval (eval_hfexpr expr_107 (closed_107 v) (closed_107 v)).
Definition expr_108 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 106)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 107))).
Definition closed_108 (v : leaf_values) : VM.t hvalue := (VM.add 107 (Gval (Fuint 1) (word_107 v)) (VM.add 106 (Gval (Fuint 1) (word_106 v)) (VM.empty hvalue))).
Definition word_108 (v : leaf_values) := word_of_eval (eval_hfexpr expr_108 (closed_108 v) (closed_108 v)).
Definition expr_109 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 105)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 108))).
Definition closed_109 (v : leaf_values) : VM.t hvalue := (VM.add 108 (Gval (Fuint 2) (word_108 v)) (VM.add 105 (Gval (Fuint 1) (word_105 v)) (VM.empty hvalue))).
Definition word_109 (v : leaf_values) := word_of_eval (eval_hfexpr expr_109 (closed_109 v) (closed_109 v)).
Definition expr_110 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 99)) (@Eref VarOrder.T (@Eid VarOrder.T 104)) (@Eref VarOrder.T (@Eid VarOrder.T 109))).
Definition closed_110 (v : leaf_values) : VM.t hvalue := (VM.add 109 (Gval (Fuint 2) (word_109 v)) (VM.add 104 (Gval (Fuint 2) (word_104 v)) (VM.add 99 (Gval (Fuint 1) (word_99 v)) (VM.empty hvalue)))).
Definition word_110 (v : leaf_values) := word_of_eval (eval_hfexpr expr_110 (closed_110 v) (closed_110 v)).
Definition expr_111 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 99)) (@Eref VarOrder.T (@Eid VarOrder.T 110))).
Definition closed_111 (v : leaf_values) : VM.t hvalue := (VM.add 110 (Gval (Fuint 2) (word_110 v)) (VM.add 99 (Gval (Fuint 1) (word_99 v)) (VM.empty hvalue))).
Definition word_111 (v : leaf_values) := word_of_eval (eval_hfexpr expr_111 (closed_111 v) (closed_111 v)).
Definition expr_112 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 95))).
Definition closed_112 (v : leaf_values) : VM.t hvalue := (VM.add 95 (Gval (Fuint 8) (word_95 v)) (VM.empty hvalue)).
Definition word_112 (v : leaf_values) := word_of_eval (eval_hfexpr expr_112 (closed_112 v) (closed_112 v)).
Definition expr_113 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 95))).
Definition closed_113 (v : leaf_values) : VM.t hvalue := (VM.add 95 (Gval (Fuint 8) (word_95 v)) (VM.empty hvalue)).
Definition word_113 (v : leaf_values) := word_of_eval (eval_hfexpr expr_113 (closed_113 v) (closed_113 v)).
Definition expr_114 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 112))).
Definition closed_114 (v : leaf_values) : VM.t hvalue := (VM.add 112 (Gval (Fuint 4) (word_112 v)) (VM.empty hvalue)).
Definition word_114 (v : leaf_values) := word_of_eval (eval_hfexpr expr_114 (closed_114 v) (closed_114 v)).
Definition expr_115 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 112))).
Definition closed_115 (v : leaf_values) : VM.t hvalue := (VM.add 112 (Gval (Fuint 4) (word_112 v)) (VM.empty hvalue)).
Definition word_115 (v : leaf_values) := word_of_eval (eval_hfexpr expr_115 (closed_115 v) (closed_115 v)).
Definition expr_116 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 112))).
Definition closed_116 (v : leaf_values) : VM.t hvalue := (VM.add 112 (Gval (Fuint 4) (word_112 v)) (VM.empty hvalue)).
Definition word_116 (v : leaf_values) := word_of_eval (eval_hfexpr expr_116 (closed_116 v) (closed_116 v)).
Definition expr_117 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 112))).
Definition closed_117 (v : leaf_values) : VM.t hvalue := (VM.add 112 (Gval (Fuint 4) (word_112 v)) (VM.empty hvalue)).
Definition word_117 (v : leaf_values) := word_of_eval (eval_hfexpr expr_117 (closed_117 v) (closed_117 v)).
Definition expr_118 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 117))).
Definition closed_118 (v : leaf_values) : VM.t hvalue := (VM.add 117 (Gval (Fuint 1) (word_117 v)) (VM.add 116 (Gval (Fuint 1) (word_116 v)) (VM.empty hvalue))).
Definition word_118 (v : leaf_values) := word_of_eval (eval_hfexpr expr_118 (closed_118 v) (closed_118 v)).
Definition expr_119 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 115)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Definition closed_119 (v : leaf_values) : VM.t hvalue := (VM.add 118 (Gval (Fuint 2) (word_118 v)) (VM.add 115 (Gval (Fuint 1) (word_115 v)) (VM.empty hvalue))).
Definition word_119 (v : leaf_values) := word_of_eval (eval_hfexpr expr_119 (closed_119 v) (closed_119 v)).
Definition expr_120 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 113))).
Definition closed_120 (v : leaf_values) : VM.t hvalue := (VM.add 113 (Gval (Fuint 4) (word_113 v)) (VM.empty hvalue)).
Definition word_120 (v : leaf_values) := word_of_eval (eval_hfexpr expr_120 (closed_120 v) (closed_120 v)).
Definition expr_121 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 113))).
Definition closed_121 (v : leaf_values) : VM.t hvalue := (VM.add 113 (Gval (Fuint 4) (word_113 v)) (VM.empty hvalue)).
Definition word_121 (v : leaf_values) := word_of_eval (eval_hfexpr expr_121 (closed_121 v) (closed_121 v)).
Definition expr_122 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 113))).
Definition closed_122 (v : leaf_values) : VM.t hvalue := (VM.add 113 (Gval (Fuint 4) (word_113 v)) (VM.empty hvalue)).
Definition word_122 (v : leaf_values) := word_of_eval (eval_hfexpr expr_122 (closed_122 v) (closed_122 v)).
Definition expr_123 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 121)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Definition closed_123 (v : leaf_values) : VM.t hvalue := (VM.add 122 (Gval (Fuint 1) (word_122 v)) (VM.add 121 (Gval (Fuint 1) (word_121 v)) (VM.empty hvalue))).
Definition word_123 (v : leaf_values) := word_of_eval (eval_hfexpr expr_123 (closed_123 v) (closed_123 v)).
Definition expr_124 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 120)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 123))).
Definition closed_124 (v : leaf_values) : VM.t hvalue := (VM.add 123 (Gval (Fuint 2) (word_123 v)) (VM.add 120 (Gval (Fuint 1) (word_120 v)) (VM.empty hvalue))).
Definition word_124 (v : leaf_values) := word_of_eval (eval_hfexpr expr_124 (closed_124 v) (closed_124 v)).
Definition expr_125 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 114)) (@Eref VarOrder.T (@Eid VarOrder.T 119)) (@Eref VarOrder.T (@Eid VarOrder.T 124))).
Definition closed_125 (v : leaf_values) : VM.t hvalue := (VM.add 124 (Gval (Fuint 2) (word_124 v)) (VM.add 119 (Gval (Fuint 2) (word_119 v)) (VM.add 114 (Gval (Fuint 1) (word_114 v)) (VM.empty hvalue)))).
Definition word_125 (v : leaf_values) := word_of_eval (eval_hfexpr expr_125 (closed_125 v) (closed_125 v)).
Definition expr_126 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 114)) (@Eref VarOrder.T (@Eid VarOrder.T 125))).
Definition closed_126 (v : leaf_values) : VM.t hvalue := (VM.add 125 (Gval (Fuint 2) (word_125 v)) (VM.add 114 (Gval (Fuint 1) (word_114 v)) (VM.empty hvalue))).
Definition word_126 (v : leaf_values) := word_of_eval (eval_hfexpr expr_126 (closed_126 v) (closed_126 v)).
Definition expr_127 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 96)) (@Eref VarOrder.T (@Eid VarOrder.T 111)) (@Eref VarOrder.T (@Eid VarOrder.T 126))).
Definition closed_127 (v : leaf_values) : VM.t hvalue := (VM.add 126 (Gval (Fuint 3) (word_126 v)) (VM.add 111 (Gval (Fuint 3) (word_111 v)) (VM.add 96 (Gval (Fuint 1) (word_96 v)) (VM.empty hvalue)))).
Definition word_127 (v : leaf_values) := word_of_eval (eval_hfexpr expr_127 (closed_127 v) (closed_127 v)).
Definition expr_128 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 96)) (@Eref VarOrder.T (@Eid VarOrder.T 127))).
Definition closed_128 (v : leaf_values) : VM.t hvalue := (VM.add 127 (Gval (Fuint 3) (word_127 v)) (VM.add 96 (Gval (Fuint 1) (word_96 v)) (VM.empty hvalue))).
Definition word_128 (v : leaf_values) := word_of_eval (eval_hfexpr expr_128 (closed_128 v) (closed_128 v)).
Definition expr_129 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 58)) (@Eref VarOrder.T (@Eid VarOrder.T 93)) (@Eref VarOrder.T (@Eid VarOrder.T 128))).
Definition closed_129 (v : leaf_values) : VM.t hvalue := (VM.add 128 (Gval (Fuint 4) (word_128 v)) (VM.add 93 (Gval (Fuint 4) (word_93 v)) (VM.add 58 (Gval (Fuint 1) (word_58 v)) (VM.empty hvalue)))).
Definition word_129 (v : leaf_values) := word_of_eval (eval_hfexpr expr_129 (closed_129 v) (closed_129 v)).
Definition expr_130 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 58)) (@Eref VarOrder.T (@Eid VarOrder.T 129))).
Definition closed_130 (v : leaf_values) : VM.t hvalue := (VM.add 129 (Gval (Fuint 4) (word_129 v)) (VM.add 58 (Gval (Fuint 1) (word_58 v)) (VM.empty hvalue))).
Definition word_130 (v : leaf_values) := word_of_eval (eval_hfexpr expr_130 (closed_130 v) (closed_130 v)).
Definition expr_131 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 16) (@Eref VarOrder.T (@Eid VarOrder.T 54))).
Definition closed_131 (v : leaf_values) : VM.t hvalue := (VM.add 54 (Gval (Fuint 32) (word_54 v)) (VM.empty hvalue)).
Definition word_131 (v : leaf_values) := word_of_eval (eval_hfexpr expr_131 (closed_131 v) (closed_131 v)).
Definition expr_132 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 54))).
Definition closed_132 (v : leaf_values) : VM.t hvalue := (VM.add 54 (Gval (Fuint 32) (word_54 v)) (VM.empty hvalue)).
Definition word_132 (v : leaf_values) := word_of_eval (eval_hfexpr expr_132 (closed_132 v) (closed_132 v)).
Definition expr_133 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 131))).
Definition closed_133 (v : leaf_values) : VM.t hvalue := (VM.add 131 (Gval (Fuint 16) (word_131 v)) (VM.empty hvalue)).
Definition word_133 (v : leaf_values) := word_of_eval (eval_hfexpr expr_133 (closed_133 v) (closed_133 v)).
Definition expr_134 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 131))).
Definition closed_134 (v : leaf_values) : VM.t hvalue := (VM.add 131 (Gval (Fuint 16) (word_131 v)) (VM.empty hvalue)).
Definition word_134 (v : leaf_values) := word_of_eval (eval_hfexpr expr_134 (closed_134 v) (closed_134 v)).
Definition expr_135 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 131))).
Definition closed_135 (v : leaf_values) : VM.t hvalue := (VM.add 131 (Gval (Fuint 16) (word_131 v)) (VM.empty hvalue)).
Definition word_135 (v : leaf_values) := word_of_eval (eval_hfexpr expr_135 (closed_135 v) (closed_135 v)).
Definition expr_136 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 134))).
Definition closed_136 (v : leaf_values) : VM.t hvalue := (VM.add 134 (Gval (Fuint 8) (word_134 v)) (VM.empty hvalue)).
Definition word_136 (v : leaf_values) := word_of_eval (eval_hfexpr expr_136 (closed_136 v) (closed_136 v)).
Definition expr_137 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 134))).
Definition closed_137 (v : leaf_values) : VM.t hvalue := (VM.add 134 (Gval (Fuint 8) (word_134 v)) (VM.empty hvalue)).
Definition word_137 (v : leaf_values) := word_of_eval (eval_hfexpr expr_137 (closed_137 v) (closed_137 v)).
Definition expr_138 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 134))).
Definition closed_138 (v : leaf_values) : VM.t hvalue := (VM.add 134 (Gval (Fuint 8) (word_134 v)) (VM.empty hvalue)).
Definition word_138 (v : leaf_values) := word_of_eval (eval_hfexpr expr_138 (closed_138 v) (closed_138 v)).
Definition expr_139 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 137))).
Definition closed_139 (v : leaf_values) : VM.t hvalue := (VM.add 137 (Gval (Fuint 4) (word_137 v)) (VM.empty hvalue)).
Definition word_139 (v : leaf_values) := word_of_eval (eval_hfexpr expr_139 (closed_139 v) (closed_139 v)).
Definition expr_140 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 137))).
Definition closed_140 (v : leaf_values) : VM.t hvalue := (VM.add 137 (Gval (Fuint 4) (word_137 v)) (VM.empty hvalue)).
Definition word_140 (v : leaf_values) := word_of_eval (eval_hfexpr expr_140 (closed_140 v) (closed_140 v)).
Definition expr_141 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 137))).
Definition closed_141 (v : leaf_values) : VM.t hvalue := (VM.add 137 (Gval (Fuint 4) (word_137 v)) (VM.empty hvalue)).
Definition word_141 (v : leaf_values) := word_of_eval (eval_hfexpr expr_141 (closed_141 v) (closed_141 v)).
Definition expr_142 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 137))).
Definition closed_142 (v : leaf_values) : VM.t hvalue := (VM.add 137 (Gval (Fuint 4) (word_137 v)) (VM.empty hvalue)).
Definition word_142 (v : leaf_values) := word_of_eval (eval_hfexpr expr_142 (closed_142 v) (closed_142 v)).
Definition expr_143 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 141)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 142))).
Definition closed_143 (v : leaf_values) : VM.t hvalue := (VM.add 142 (Gval (Fuint 1) (word_142 v)) (VM.add 141 (Gval (Fuint 1) (word_141 v)) (VM.empty hvalue))).
Definition word_143 (v : leaf_values) := word_of_eval (eval_hfexpr expr_143 (closed_143 v) (closed_143 v)).
Definition expr_144 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 143))).
Definition closed_144 (v : leaf_values) : VM.t hvalue := (VM.add 143 (Gval (Fuint 2) (word_143 v)) (VM.add 140 (Gval (Fuint 1) (word_140 v)) (VM.empty hvalue))).
Definition word_144 (v : leaf_values) := word_of_eval (eval_hfexpr expr_144 (closed_144 v) (closed_144 v)).
Definition expr_145 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 138))).
Definition closed_145 (v : leaf_values) : VM.t hvalue := (VM.add 138 (Gval (Fuint 4) (word_138 v)) (VM.empty hvalue)).
Definition word_145 (v : leaf_values) := word_of_eval (eval_hfexpr expr_145 (closed_145 v) (closed_145 v)).
Definition expr_146 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 138))).
Definition closed_146 (v : leaf_values) : VM.t hvalue := (VM.add 138 (Gval (Fuint 4) (word_138 v)) (VM.empty hvalue)).
Definition word_146 (v : leaf_values) := word_of_eval (eval_hfexpr expr_146 (closed_146 v) (closed_146 v)).
Definition expr_147 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 138))).
Definition closed_147 (v : leaf_values) : VM.t hvalue := (VM.add 138 (Gval (Fuint 4) (word_138 v)) (VM.empty hvalue)).
Definition word_147 (v : leaf_values) := word_of_eval (eval_hfexpr expr_147 (closed_147 v) (closed_147 v)).
Definition expr_148 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 146)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 147))).
Definition closed_148 (v : leaf_values) : VM.t hvalue := (VM.add 147 (Gval (Fuint 1) (word_147 v)) (VM.add 146 (Gval (Fuint 1) (word_146 v)) (VM.empty hvalue))).
Definition word_148 (v : leaf_values) := word_of_eval (eval_hfexpr expr_148 (closed_148 v) (closed_148 v)).
Definition expr_149 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 145)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 148))).
Definition closed_149 (v : leaf_values) : VM.t hvalue := (VM.add 148 (Gval (Fuint 2) (word_148 v)) (VM.add 145 (Gval (Fuint 1) (word_145 v)) (VM.empty hvalue))).
Definition word_149 (v : leaf_values) := word_of_eval (eval_hfexpr expr_149 (closed_149 v) (closed_149 v)).
Definition expr_150 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 139)) (@Eref VarOrder.T (@Eid VarOrder.T 144)) (@Eref VarOrder.T (@Eid VarOrder.T 149))).
Definition closed_150 (v : leaf_values) : VM.t hvalue := (VM.add 149 (Gval (Fuint 2) (word_149 v)) (VM.add 144 (Gval (Fuint 2) (word_144 v)) (VM.add 139 (Gval (Fuint 1) (word_139 v)) (VM.empty hvalue)))).
Definition word_150 (v : leaf_values) := word_of_eval (eval_hfexpr expr_150 (closed_150 v) (closed_150 v)).
Definition expr_151 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 139)) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Definition closed_151 (v : leaf_values) : VM.t hvalue := (VM.add 150 (Gval (Fuint 2) (word_150 v)) (VM.add 139 (Gval (Fuint 1) (word_139 v)) (VM.empty hvalue))).
Definition word_151 (v : leaf_values) := word_of_eval (eval_hfexpr expr_151 (closed_151 v) (closed_151 v)).
Definition expr_152 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 135))).
Definition closed_152 (v : leaf_values) : VM.t hvalue := (VM.add 135 (Gval (Fuint 8) (word_135 v)) (VM.empty hvalue)).
Definition word_152 (v : leaf_values) := word_of_eval (eval_hfexpr expr_152 (closed_152 v) (closed_152 v)).
Definition expr_153 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 135))).
Definition closed_153 (v : leaf_values) : VM.t hvalue := (VM.add 135 (Gval (Fuint 8) (word_135 v)) (VM.empty hvalue)).
Definition word_153 (v : leaf_values) := word_of_eval (eval_hfexpr expr_153 (closed_153 v) (closed_153 v)).
Definition expr_154 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Definition closed_154 (v : leaf_values) : VM.t hvalue := (VM.add 152 (Gval (Fuint 4) (word_152 v)) (VM.empty hvalue)).
Definition word_154 (v : leaf_values) := word_of_eval (eval_hfexpr expr_154 (closed_154 v) (closed_154 v)).
Definition expr_155 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Definition closed_155 (v : leaf_values) : VM.t hvalue := (VM.add 152 (Gval (Fuint 4) (word_152 v)) (VM.empty hvalue)).
Definition word_155 (v : leaf_values) := word_of_eval (eval_hfexpr expr_155 (closed_155 v) (closed_155 v)).
Definition expr_156 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Definition closed_156 (v : leaf_values) : VM.t hvalue := (VM.add 152 (Gval (Fuint 4) (word_152 v)) (VM.empty hvalue)).
Definition word_156 (v : leaf_values) := word_of_eval (eval_hfexpr expr_156 (closed_156 v) (closed_156 v)).
Definition expr_157 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Definition closed_157 (v : leaf_values) : VM.t hvalue := (VM.add 152 (Gval (Fuint 4) (word_152 v)) (VM.empty hvalue)).
Definition word_157 (v : leaf_values) := word_of_eval (eval_hfexpr expr_157 (closed_157 v) (closed_157 v)).
Definition expr_158 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 156)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 157))).
Definition closed_158 (v : leaf_values) : VM.t hvalue := (VM.add 157 (Gval (Fuint 1) (word_157 v)) (VM.add 156 (Gval (Fuint 1) (word_156 v)) (VM.empty hvalue))).
Definition word_158 (v : leaf_values) := word_of_eval (eval_hfexpr expr_158 (closed_158 v) (closed_158 v)).
Definition expr_159 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 155)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 158))).
Definition closed_159 (v : leaf_values) : VM.t hvalue := (VM.add 158 (Gval (Fuint 2) (word_158 v)) (VM.add 155 (Gval (Fuint 1) (word_155 v)) (VM.empty hvalue))).
Definition word_159 (v : leaf_values) := word_of_eval (eval_hfexpr expr_159 (closed_159 v) (closed_159 v)).
Definition expr_160 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 153))).
Definition closed_160 (v : leaf_values) : VM.t hvalue := (VM.add 153 (Gval (Fuint 4) (word_153 v)) (VM.empty hvalue)).
Definition word_160 (v : leaf_values) := word_of_eval (eval_hfexpr expr_160 (closed_160 v) (closed_160 v)).
Definition expr_161 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 153))).
Definition closed_161 (v : leaf_values) : VM.t hvalue := (VM.add 153 (Gval (Fuint 4) (word_153 v)) (VM.empty hvalue)).
Definition word_161 (v : leaf_values) := word_of_eval (eval_hfexpr expr_161 (closed_161 v) (closed_161 v)).
Definition expr_162 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 153))).
Definition closed_162 (v : leaf_values) : VM.t hvalue := (VM.add 153 (Gval (Fuint 4) (word_153 v)) (VM.empty hvalue)).
Definition word_162 (v : leaf_values) := word_of_eval (eval_hfexpr expr_162 (closed_162 v) (closed_162 v)).
Definition expr_163 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 161)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 162))).
Definition closed_163 (v : leaf_values) : VM.t hvalue := (VM.add 162 (Gval (Fuint 1) (word_162 v)) (VM.add 161 (Gval (Fuint 1) (word_161 v)) (VM.empty hvalue))).
Definition word_163 (v : leaf_values) := word_of_eval (eval_hfexpr expr_163 (closed_163 v) (closed_163 v)).
Definition expr_164 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 160)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 163))).
Definition closed_164 (v : leaf_values) : VM.t hvalue := (VM.add 163 (Gval (Fuint 2) (word_163 v)) (VM.add 160 (Gval (Fuint 1) (word_160 v)) (VM.empty hvalue))).
Definition word_164 (v : leaf_values) := word_of_eval (eval_hfexpr expr_164 (closed_164 v) (closed_164 v)).
Definition expr_165 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 154)) (@Eref VarOrder.T (@Eid VarOrder.T 159)) (@Eref VarOrder.T (@Eid VarOrder.T 164))).
Definition closed_165 (v : leaf_values) : VM.t hvalue := (VM.add 164 (Gval (Fuint 2) (word_164 v)) (VM.add 159 (Gval (Fuint 2) (word_159 v)) (VM.add 154 (Gval (Fuint 1) (word_154 v)) (VM.empty hvalue)))).
Definition word_165 (v : leaf_values) := word_of_eval (eval_hfexpr expr_165 (closed_165 v) (closed_165 v)).
Definition expr_166 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 154)) (@Eref VarOrder.T (@Eid VarOrder.T 165))).
Definition closed_166 (v : leaf_values) : VM.t hvalue := (VM.add 165 (Gval (Fuint 2) (word_165 v)) (VM.add 154 (Gval (Fuint 1) (word_154 v)) (VM.empty hvalue))).
Definition word_166 (v : leaf_values) := word_of_eval (eval_hfexpr expr_166 (closed_166 v) (closed_166 v)).
Definition expr_167 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 136)) (@Eref VarOrder.T (@Eid VarOrder.T 151)) (@Eref VarOrder.T (@Eid VarOrder.T 166))).
Definition closed_167 (v : leaf_values) : VM.t hvalue := (VM.add 166 (Gval (Fuint 3) (word_166 v)) (VM.add 151 (Gval (Fuint 3) (word_151 v)) (VM.add 136 (Gval (Fuint 1) (word_136 v)) (VM.empty hvalue)))).
Definition word_167 (v : leaf_values) := word_of_eval (eval_hfexpr expr_167 (closed_167 v) (closed_167 v)).
Definition expr_168 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 136)) (@Eref VarOrder.T (@Eid VarOrder.T 167))).
Definition closed_168 (v : leaf_values) : VM.t hvalue := (VM.add 167 (Gval (Fuint 3) (word_167 v)) (VM.add 136 (Gval (Fuint 1) (word_136 v)) (VM.empty hvalue))).
Definition word_168 (v : leaf_values) := word_of_eval (eval_hfexpr expr_168 (closed_168 v) (closed_168 v)).
Definition expr_169 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 132))).
Definition closed_169 (v : leaf_values) : VM.t hvalue := (VM.add 132 (Gval (Fuint 16) (word_132 v)) (VM.empty hvalue)).
Definition word_169 (v : leaf_values) := word_of_eval (eval_hfexpr expr_169 (closed_169 v) (closed_169 v)).
Definition expr_170 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 132))).
Definition closed_170 (v : leaf_values) : VM.t hvalue := (VM.add 132 (Gval (Fuint 16) (word_132 v)) (VM.empty hvalue)).
Definition word_170 (v : leaf_values) := word_of_eval (eval_hfexpr expr_170 (closed_170 v) (closed_170 v)).
Definition expr_171 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 169))).
Definition closed_171 (v : leaf_values) : VM.t hvalue := (VM.add 169 (Gval (Fuint 8) (word_169 v)) (VM.empty hvalue)).
Definition word_171 (v : leaf_values) := word_of_eval (eval_hfexpr expr_171 (closed_171 v) (closed_171 v)).
Definition expr_172 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 169))).
Definition closed_172 (v : leaf_values) : VM.t hvalue := (VM.add 169 (Gval (Fuint 8) (word_169 v)) (VM.empty hvalue)).
Definition word_172 (v : leaf_values) := word_of_eval (eval_hfexpr expr_172 (closed_172 v) (closed_172 v)).
Definition expr_173 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 169))).
Definition closed_173 (v : leaf_values) : VM.t hvalue := (VM.add 169 (Gval (Fuint 8) (word_169 v)) (VM.empty hvalue)).
Definition word_173 (v : leaf_values) := word_of_eval (eval_hfexpr expr_173 (closed_173 v) (closed_173 v)).
Definition expr_174 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 172))).
Definition closed_174 (v : leaf_values) : VM.t hvalue := (VM.add 172 (Gval (Fuint 4) (word_172 v)) (VM.empty hvalue)).
Definition word_174 (v : leaf_values) := word_of_eval (eval_hfexpr expr_174 (closed_174 v) (closed_174 v)).
Definition expr_175 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 172))).
Definition closed_175 (v : leaf_values) : VM.t hvalue := (VM.add 172 (Gval (Fuint 4) (word_172 v)) (VM.empty hvalue)).
Definition word_175 (v : leaf_values) := word_of_eval (eval_hfexpr expr_175 (closed_175 v) (closed_175 v)).
Definition expr_176 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 172))).
Definition closed_176 (v : leaf_values) : VM.t hvalue := (VM.add 172 (Gval (Fuint 4) (word_172 v)) (VM.empty hvalue)).
Definition word_176 (v : leaf_values) := word_of_eval (eval_hfexpr expr_176 (closed_176 v) (closed_176 v)).
Definition expr_177 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 172))).
Definition closed_177 (v : leaf_values) : VM.t hvalue := (VM.add 172 (Gval (Fuint 4) (word_172 v)) (VM.empty hvalue)).
Definition word_177 (v : leaf_values) := word_of_eval (eval_hfexpr expr_177 (closed_177 v) (closed_177 v)).
Definition expr_178 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 176)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 177))).
Definition closed_178 (v : leaf_values) : VM.t hvalue := (VM.add 177 (Gval (Fuint 1) (word_177 v)) (VM.add 176 (Gval (Fuint 1) (word_176 v)) (VM.empty hvalue))).
Definition word_178 (v : leaf_values) := word_of_eval (eval_hfexpr expr_178 (closed_178 v) (closed_178 v)).
Definition expr_179 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 175)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 178))).
Definition closed_179 (v : leaf_values) : VM.t hvalue := (VM.add 178 (Gval (Fuint 2) (word_178 v)) (VM.add 175 (Gval (Fuint 1) (word_175 v)) (VM.empty hvalue))).
Definition word_179 (v : leaf_values) := word_of_eval (eval_hfexpr expr_179 (closed_179 v) (closed_179 v)).
Definition expr_180 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 173))).
Definition closed_180 (v : leaf_values) : VM.t hvalue := (VM.add 173 (Gval (Fuint 4) (word_173 v)) (VM.empty hvalue)).
Definition word_180 (v : leaf_values) := word_of_eval (eval_hfexpr expr_180 (closed_180 v) (closed_180 v)).
Definition expr_181 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 173))).
Definition closed_181 (v : leaf_values) : VM.t hvalue := (VM.add 173 (Gval (Fuint 4) (word_173 v)) (VM.empty hvalue)).
Definition word_181 (v : leaf_values) := word_of_eval (eval_hfexpr expr_181 (closed_181 v) (closed_181 v)).
Definition expr_182 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 173))).
Definition closed_182 (v : leaf_values) : VM.t hvalue := (VM.add 173 (Gval (Fuint 4) (word_173 v)) (VM.empty hvalue)).
Definition word_182 (v : leaf_values) := word_of_eval (eval_hfexpr expr_182 (closed_182 v) (closed_182 v)).
Definition expr_183 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 181)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 182))).
Definition closed_183 (v : leaf_values) : VM.t hvalue := (VM.add 182 (Gval (Fuint 1) (word_182 v)) (VM.add 181 (Gval (Fuint 1) (word_181 v)) (VM.empty hvalue))).
Definition word_183 (v : leaf_values) := word_of_eval (eval_hfexpr expr_183 (closed_183 v) (closed_183 v)).
Definition expr_184 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 180)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 183))).
Definition closed_184 (v : leaf_values) : VM.t hvalue := (VM.add 183 (Gval (Fuint 2) (word_183 v)) (VM.add 180 (Gval (Fuint 1) (word_180 v)) (VM.empty hvalue))).
Definition word_184 (v : leaf_values) := word_of_eval (eval_hfexpr expr_184 (closed_184 v) (closed_184 v)).
Definition expr_185 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 174)) (@Eref VarOrder.T (@Eid VarOrder.T 179)) (@Eref VarOrder.T (@Eid VarOrder.T 184))).
Definition closed_185 (v : leaf_values) : VM.t hvalue := (VM.add 184 (Gval (Fuint 2) (word_184 v)) (VM.add 179 (Gval (Fuint 2) (word_179 v)) (VM.add 174 (Gval (Fuint 1) (word_174 v)) (VM.empty hvalue)))).
Definition word_185 (v : leaf_values) := word_of_eval (eval_hfexpr expr_185 (closed_185 v) (closed_185 v)).
Definition expr_186 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 174)) (@Eref VarOrder.T (@Eid VarOrder.T 185))).
Definition closed_186 (v : leaf_values) : VM.t hvalue := (VM.add 185 (Gval (Fuint 2) (word_185 v)) (VM.add 174 (Gval (Fuint 1) (word_174 v)) (VM.empty hvalue))).
Definition word_186 (v : leaf_values) := word_of_eval (eval_hfexpr expr_186 (closed_186 v) (closed_186 v)).
Definition expr_187 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 170))).
Definition closed_187 (v : leaf_values) : VM.t hvalue := (VM.add 170 (Gval (Fuint 8) (word_170 v)) (VM.empty hvalue)).
Definition word_187 (v : leaf_values) := word_of_eval (eval_hfexpr expr_187 (closed_187 v) (closed_187 v)).
Definition expr_188 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 170))).
Definition closed_188 (v : leaf_values) : VM.t hvalue := (VM.add 170 (Gval (Fuint 8) (word_170 v)) (VM.empty hvalue)).
Definition word_188 (v : leaf_values) := word_of_eval (eval_hfexpr expr_188 (closed_188 v) (closed_188 v)).
Definition expr_189 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 187))).
Definition closed_189 (v : leaf_values) : VM.t hvalue := (VM.add 187 (Gval (Fuint 4) (word_187 v)) (VM.empty hvalue)).
Definition word_189 (v : leaf_values) := word_of_eval (eval_hfexpr expr_189 (closed_189 v) (closed_189 v)).
Definition expr_190 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 187))).
Definition closed_190 (v : leaf_values) : VM.t hvalue := (VM.add 187 (Gval (Fuint 4) (word_187 v)) (VM.empty hvalue)).
Definition word_190 (v : leaf_values) := word_of_eval (eval_hfexpr expr_190 (closed_190 v) (closed_190 v)).
Definition expr_191 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 187))).
Definition closed_191 (v : leaf_values) : VM.t hvalue := (VM.add 187 (Gval (Fuint 4) (word_187 v)) (VM.empty hvalue)).
Definition word_191 (v : leaf_values) := word_of_eval (eval_hfexpr expr_191 (closed_191 v) (closed_191 v)).
Definition expr_192 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 187))).
Definition closed_192 (v : leaf_values) : VM.t hvalue := (VM.add 187 (Gval (Fuint 4) (word_187 v)) (VM.empty hvalue)).
Definition word_192 (v : leaf_values) := word_of_eval (eval_hfexpr expr_192 (closed_192 v) (closed_192 v)).
Definition expr_193 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 192))).
Definition closed_193 (v : leaf_values) : VM.t hvalue := (VM.add 192 (Gval (Fuint 1) (word_192 v)) (VM.add 191 (Gval (Fuint 1) (word_191 v)) (VM.empty hvalue))).
Definition word_193 (v : leaf_values) := word_of_eval (eval_hfexpr expr_193 (closed_193 v) (closed_193 v)).
Definition expr_194 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 193))).
Definition closed_194 (v : leaf_values) : VM.t hvalue := (VM.add 193 (Gval (Fuint 2) (word_193 v)) (VM.add 190 (Gval (Fuint 1) (word_190 v)) (VM.empty hvalue))).
Definition word_194 (v : leaf_values) := word_of_eval (eval_hfexpr expr_194 (closed_194 v) (closed_194 v)).
Definition expr_195 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 188))).
Definition closed_195 (v : leaf_values) : VM.t hvalue := (VM.add 188 (Gval (Fuint 4) (word_188 v)) (VM.empty hvalue)).
Definition word_195 (v : leaf_values) := word_of_eval (eval_hfexpr expr_195 (closed_195 v) (closed_195 v)).
Definition expr_196 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 188))).
Definition closed_196 (v : leaf_values) : VM.t hvalue := (VM.add 188 (Gval (Fuint 4) (word_188 v)) (VM.empty hvalue)).
Definition word_196 (v : leaf_values) := word_of_eval (eval_hfexpr expr_196 (closed_196 v) (closed_196 v)).
Definition expr_197 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 188))).
Definition closed_197 (v : leaf_values) : VM.t hvalue := (VM.add 188 (Gval (Fuint 4) (word_188 v)) (VM.empty hvalue)).
Definition word_197 (v : leaf_values) := word_of_eval (eval_hfexpr expr_197 (closed_197 v) (closed_197 v)).
Definition expr_198 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 196)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 197))).
Definition closed_198 (v : leaf_values) : VM.t hvalue := (VM.add 197 (Gval (Fuint 1) (word_197 v)) (VM.add 196 (Gval (Fuint 1) (word_196 v)) (VM.empty hvalue))).
Definition word_198 (v : leaf_values) := word_of_eval (eval_hfexpr expr_198 (closed_198 v) (closed_198 v)).
Definition expr_199 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 195)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 198))).
Definition closed_199 (v : leaf_values) : VM.t hvalue := (VM.add 198 (Gval (Fuint 2) (word_198 v)) (VM.add 195 (Gval (Fuint 1) (word_195 v)) (VM.empty hvalue))).
Definition word_199 (v : leaf_values) := word_of_eval (eval_hfexpr expr_199 (closed_199 v) (closed_199 v)).
Definition expr_200 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 199))).
Definition closed_200 (v : leaf_values) : VM.t hvalue := (VM.add 199 (Gval (Fuint 2) (word_199 v)) (VM.add 194 (Gval (Fuint 2) (word_194 v)) (VM.add 189 (Gval (Fuint 1) (word_189 v)) (VM.empty hvalue)))).
Definition word_200 (v : leaf_values) := word_of_eval (eval_hfexpr expr_200 (closed_200 v) (closed_200 v)).
Definition expr_201 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 200))).
Definition closed_201 (v : leaf_values) : VM.t hvalue := (VM.add 200 (Gval (Fuint 2) (word_200 v)) (VM.add 189 (Gval (Fuint 1) (word_189 v)) (VM.empty hvalue))).
Definition word_201 (v : leaf_values) := word_of_eval (eval_hfexpr expr_201 (closed_201 v) (closed_201 v)).
Definition expr_202 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 171)) (@Eref VarOrder.T (@Eid VarOrder.T 186)) (@Eref VarOrder.T (@Eid VarOrder.T 201))).
Definition closed_202 (v : leaf_values) : VM.t hvalue := (VM.add 201 (Gval (Fuint 3) (word_201 v)) (VM.add 186 (Gval (Fuint 3) (word_186 v)) (VM.add 171 (Gval (Fuint 1) (word_171 v)) (VM.empty hvalue)))).
Definition word_202 (v : leaf_values) := word_of_eval (eval_hfexpr expr_202 (closed_202 v) (closed_202 v)).
Definition expr_203 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 171)) (@Eref VarOrder.T (@Eid VarOrder.T 202))).
Definition closed_203 (v : leaf_values) : VM.t hvalue := (VM.add 202 (Gval (Fuint 3) (word_202 v)) (VM.add 171 (Gval (Fuint 1) (word_171 v)) (VM.empty hvalue))).
Definition word_203 (v : leaf_values) := word_of_eval (eval_hfexpr expr_203 (closed_203 v) (closed_203 v)).
Definition expr_204 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 133)) (@Eref VarOrder.T (@Eid VarOrder.T 168)) (@Eref VarOrder.T (@Eid VarOrder.T 203))).
Definition closed_204 (v : leaf_values) : VM.t hvalue := (VM.add 203 (Gval (Fuint 4) (word_203 v)) (VM.add 168 (Gval (Fuint 4) (word_168 v)) (VM.add 133 (Gval (Fuint 1) (word_133 v)) (VM.empty hvalue)))).
Definition word_204 (v : leaf_values) := word_of_eval (eval_hfexpr expr_204 (closed_204 v) (closed_204 v)).
Definition expr_205 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 133)) (@Eref VarOrder.T (@Eid VarOrder.T 204))).
Definition closed_205 (v : leaf_values) : VM.t hvalue := (VM.add 204 (Gval (Fuint 4) (word_204 v)) (VM.add 133 (Gval (Fuint 1) (word_133 v)) (VM.empty hvalue))).
Definition word_205 (v : leaf_values) := word_of_eval (eval_hfexpr expr_205 (closed_205 v) (closed_205 v)).
Definition expr_206 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 55)) (@Eref VarOrder.T (@Eid VarOrder.T 130)) (@Eref VarOrder.T (@Eid VarOrder.T 205))).
Definition closed_206 (v : leaf_values) : VM.t hvalue := (VM.add 205 (Gval (Fuint 5) (word_205 v)) (VM.add 130 (Gval (Fuint 5) (word_130 v)) (VM.add 55 (Gval (Fuint 1) (word_55 v)) (VM.empty hvalue)))).
Definition word_206 (v : leaf_values) := word_of_eval (eval_hfexpr expr_206 (closed_206 v) (closed_206 v)).
Definition expr_207 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 55)) (@Eref VarOrder.T (@Eid VarOrder.T 206))).
Definition closed_207 (v : leaf_values) : VM.t hvalue := (VM.add 206 (Gval (Fuint 5) (word_206 v)) (VM.add 55 (Gval (Fuint 1) (word_55 v)) (VM.empty hvalue))).
Definition word_207 (v : leaf_values) := word_of_eval (eval_hfexpr expr_207 (closed_207 v) (closed_207 v)).
Definition expr_208 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Econst VarOrder.T (Fuint 7) [::false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 207))).
Definition closed_208 (v : leaf_values) : VM.t hvalue := (VM.add 207 (Gval (Fuint 6) (word_207 v)) (VM.empty hvalue)).
Definition word_208 (v : leaf_values) := word_of_eval (eval_hfexpr expr_208 (closed_208 v) (closed_208 v)).
Definition expr_209 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 208))).
Definition closed_209 (v : leaf_values) : VM.t hvalue := (VM.add 208 (Gval (Fuint 8) (word_208 v)) (VM.empty hvalue)).
Definition word_209 (v : leaf_values) := word_of_eval (eval_hfexpr expr_209 (closed_209 v) (closed_209 v)).
Definition expr_210 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 64 64) (@Eref VarOrder.T (@Eid VarOrder.T 43))).
Definition closed_210 (v : leaf_values) : VM.t hvalue := (VM.add 43 (Gval (Fuint 65) (word_43 v)) (VM.empty hvalue)).
Definition word_210 (v : leaf_values) := word_of_eval (eval_hfexpr expr_210 (closed_210 v) (closed_210 v)).
Definition expr_211 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 63 0) (@Eref VarOrder.T (@Eid VarOrder.T 43))).
Definition closed_211 (v : leaf_values) : VM.t hvalue := (VM.add 43 (Gval (Fuint 65) (word_43 v)) (VM.empty hvalue)).
Definition word_211 (v : leaf_values) := word_of_eval (eval_hfexpr expr_211 (closed_211 v) (closed_211 v)).
Definition expr_212 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 210))).
Definition closed_212 (v : leaf_values) : VM.t hvalue := (VM.add 210 (Gval (Fuint 1) (word_210 v)) (VM.empty hvalue)).
Definition word_212 (v : leaf_values) := word_of_eval (eval_hfexpr expr_212 (closed_212 v) (closed_212 v)).
Definition expr_213 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 63 32) (@Eref VarOrder.T (@Eid VarOrder.T 211))).
Definition closed_213 (v : leaf_values) : VM.t hvalue := (VM.add 211 (Gval (Fuint 64) (word_211 v)) (VM.empty hvalue)).
Definition word_213 (v : leaf_values) := word_of_eval (eval_hfexpr expr_213 (closed_213 v) (closed_213 v)).
Definition expr_214 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 211))).
Definition closed_214 (v : leaf_values) : VM.t hvalue := (VM.add 211 (Gval (Fuint 64) (word_211 v)) (VM.empty hvalue)).
Definition word_214 (v : leaf_values) := word_of_eval (eval_hfexpr expr_214 (closed_214 v) (closed_214 v)).
Definition expr_215 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 213))).
Definition closed_215 (v : leaf_values) : VM.t hvalue := (VM.add 213 (Gval (Fuint 32) (word_213 v)) (VM.empty hvalue)).
Definition word_215 (v : leaf_values) := word_of_eval (eval_hfexpr expr_215 (closed_215 v) (closed_215 v)).
Definition expr_216 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 16) (@Eref VarOrder.T (@Eid VarOrder.T 213))).
Definition closed_216 (v : leaf_values) : VM.t hvalue := (VM.add 213 (Gval (Fuint 32) (word_213 v)) (VM.empty hvalue)).
Definition word_216 (v : leaf_values) := word_of_eval (eval_hfexpr expr_216 (closed_216 v) (closed_216 v)).
Definition expr_217 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 213))).
Definition closed_217 (v : leaf_values) : VM.t hvalue := (VM.add 213 (Gval (Fuint 32) (word_213 v)) (VM.empty hvalue)).
Definition word_217 (v : leaf_values) := word_of_eval (eval_hfexpr expr_217 (closed_217 v) (closed_217 v)).
Definition expr_218 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 216))).
Definition closed_218 (v : leaf_values) : VM.t hvalue := (VM.add 216 (Gval (Fuint 16) (word_216 v)) (VM.empty hvalue)).
Definition word_218 (v : leaf_values) := word_of_eval (eval_hfexpr expr_218 (closed_218 v) (closed_218 v)).
Definition expr_219 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 216))).
Definition closed_219 (v : leaf_values) : VM.t hvalue := (VM.add 216 (Gval (Fuint 16) (word_216 v)) (VM.empty hvalue)).
Definition word_219 (v : leaf_values) := word_of_eval (eval_hfexpr expr_219 (closed_219 v) (closed_219 v)).
Definition expr_220 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 216))).
Definition closed_220 (v : leaf_values) : VM.t hvalue := (VM.add 216 (Gval (Fuint 16) (word_216 v)) (VM.empty hvalue)).
Definition word_220 (v : leaf_values) := word_of_eval (eval_hfexpr expr_220 (closed_220 v) (closed_220 v)).
Definition expr_221 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 219))).
Definition closed_221 (v : leaf_values) : VM.t hvalue := (VM.add 219 (Gval (Fuint 8) (word_219 v)) (VM.empty hvalue)).
Definition word_221 (v : leaf_values) := word_of_eval (eval_hfexpr expr_221 (closed_221 v) (closed_221 v)).
Definition expr_222 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 219))).
Definition closed_222 (v : leaf_values) : VM.t hvalue := (VM.add 219 (Gval (Fuint 8) (word_219 v)) (VM.empty hvalue)).
Definition word_222 (v : leaf_values) := word_of_eval (eval_hfexpr expr_222 (closed_222 v) (closed_222 v)).
Definition expr_223 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 219))).
Definition closed_223 (v : leaf_values) : VM.t hvalue := (VM.add 219 (Gval (Fuint 8) (word_219 v)) (VM.empty hvalue)).
Definition word_223 (v : leaf_values) := word_of_eval (eval_hfexpr expr_223 (closed_223 v) (closed_223 v)).
Definition expr_224 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 222))).
Definition closed_224 (v : leaf_values) : VM.t hvalue := (VM.add 222 (Gval (Fuint 4) (word_222 v)) (VM.empty hvalue)).
Definition word_224 (v : leaf_values) := word_of_eval (eval_hfexpr expr_224 (closed_224 v) (closed_224 v)).
Definition expr_225 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 222))).
Definition closed_225 (v : leaf_values) : VM.t hvalue := (VM.add 222 (Gval (Fuint 4) (word_222 v)) (VM.empty hvalue)).
Definition word_225 (v : leaf_values) := word_of_eval (eval_hfexpr expr_225 (closed_225 v) (closed_225 v)).
Definition expr_226 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 222))).
Definition closed_226 (v : leaf_values) : VM.t hvalue := (VM.add 222 (Gval (Fuint 4) (word_222 v)) (VM.empty hvalue)).
Definition word_226 (v : leaf_values) := word_of_eval (eval_hfexpr expr_226 (closed_226 v) (closed_226 v)).
Definition expr_227 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 222))).
Definition closed_227 (v : leaf_values) : VM.t hvalue := (VM.add 222 (Gval (Fuint 4) (word_222 v)) (VM.empty hvalue)).
Definition word_227 (v : leaf_values) := word_of_eval (eval_hfexpr expr_227 (closed_227 v) (closed_227 v)).
Definition expr_228 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 226)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 227))).
Definition closed_228 (v : leaf_values) : VM.t hvalue := (VM.add 227 (Gval (Fuint 1) (word_227 v)) (VM.add 226 (Gval (Fuint 1) (word_226 v)) (VM.empty hvalue))).
Definition word_228 (v : leaf_values) := word_of_eval (eval_hfexpr expr_228 (closed_228 v) (closed_228 v)).
Definition expr_229 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 225)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 228))).
Definition closed_229 (v : leaf_values) : VM.t hvalue := (VM.add 228 (Gval (Fuint 2) (word_228 v)) (VM.add 225 (Gval (Fuint 1) (word_225 v)) (VM.empty hvalue))).
Definition word_229 (v : leaf_values) := word_of_eval (eval_hfexpr expr_229 (closed_229 v) (closed_229 v)).
Definition expr_230 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 223))).
Definition closed_230 (v : leaf_values) : VM.t hvalue := (VM.add 223 (Gval (Fuint 4) (word_223 v)) (VM.empty hvalue)).
Definition word_230 (v : leaf_values) := word_of_eval (eval_hfexpr expr_230 (closed_230 v) (closed_230 v)).
Definition expr_231 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 223))).
Definition closed_231 (v : leaf_values) : VM.t hvalue := (VM.add 223 (Gval (Fuint 4) (word_223 v)) (VM.empty hvalue)).
Definition word_231 (v : leaf_values) := word_of_eval (eval_hfexpr expr_231 (closed_231 v) (closed_231 v)).
Definition expr_232 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 223))).
Definition closed_232 (v : leaf_values) : VM.t hvalue := (VM.add 223 (Gval (Fuint 4) (word_223 v)) (VM.empty hvalue)).
Definition word_232 (v : leaf_values) := word_of_eval (eval_hfexpr expr_232 (closed_232 v) (closed_232 v)).
Definition expr_233 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 231)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 232))).
Definition closed_233 (v : leaf_values) : VM.t hvalue := (VM.add 232 (Gval (Fuint 1) (word_232 v)) (VM.add 231 (Gval (Fuint 1) (word_231 v)) (VM.empty hvalue))).
Definition word_233 (v : leaf_values) := word_of_eval (eval_hfexpr expr_233 (closed_233 v) (closed_233 v)).
Definition expr_234 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 230)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 233))).
Definition closed_234 (v : leaf_values) : VM.t hvalue := (VM.add 233 (Gval (Fuint 2) (word_233 v)) (VM.add 230 (Gval (Fuint 1) (word_230 v)) (VM.empty hvalue))).
Definition word_234 (v : leaf_values) := word_of_eval (eval_hfexpr expr_234 (closed_234 v) (closed_234 v)).
Definition expr_235 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 224)) (@Eref VarOrder.T (@Eid VarOrder.T 229)) (@Eref VarOrder.T (@Eid VarOrder.T 234))).
Definition closed_235 (v : leaf_values) : VM.t hvalue := (VM.add 234 (Gval (Fuint 2) (word_234 v)) (VM.add 229 (Gval (Fuint 2) (word_229 v)) (VM.add 224 (Gval (Fuint 1) (word_224 v)) (VM.empty hvalue)))).
Definition word_235 (v : leaf_values) := word_of_eval (eval_hfexpr expr_235 (closed_235 v) (closed_235 v)).
Definition expr_236 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 224)) (@Eref VarOrder.T (@Eid VarOrder.T 235))).
Definition closed_236 (v : leaf_values) : VM.t hvalue := (VM.add 235 (Gval (Fuint 2) (word_235 v)) (VM.add 224 (Gval (Fuint 1) (word_224 v)) (VM.empty hvalue))).
Definition word_236 (v : leaf_values) := word_of_eval (eval_hfexpr expr_236 (closed_236 v) (closed_236 v)).
Definition expr_237 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 220))).
Definition closed_237 (v : leaf_values) : VM.t hvalue := (VM.add 220 (Gval (Fuint 8) (word_220 v)) (VM.empty hvalue)).
Definition word_237 (v : leaf_values) := word_of_eval (eval_hfexpr expr_237 (closed_237 v) (closed_237 v)).
Definition expr_238 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 220))).
Definition closed_238 (v : leaf_values) : VM.t hvalue := (VM.add 220 (Gval (Fuint 8) (word_220 v)) (VM.empty hvalue)).
Definition word_238 (v : leaf_values) := word_of_eval (eval_hfexpr expr_238 (closed_238 v) (closed_238 v)).
Definition expr_239 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 237))).
Definition closed_239 (v : leaf_values) : VM.t hvalue := (VM.add 237 (Gval (Fuint 4) (word_237 v)) (VM.empty hvalue)).
Definition word_239 (v : leaf_values) := word_of_eval (eval_hfexpr expr_239 (closed_239 v) (closed_239 v)).
Definition expr_240 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 237))).
Definition closed_240 (v : leaf_values) : VM.t hvalue := (VM.add 237 (Gval (Fuint 4) (word_237 v)) (VM.empty hvalue)).
Definition word_240 (v : leaf_values) := word_of_eval (eval_hfexpr expr_240 (closed_240 v) (closed_240 v)).
Definition expr_241 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 237))).
Definition closed_241 (v : leaf_values) : VM.t hvalue := (VM.add 237 (Gval (Fuint 4) (word_237 v)) (VM.empty hvalue)).
Definition word_241 (v : leaf_values) := word_of_eval (eval_hfexpr expr_241 (closed_241 v) (closed_241 v)).
Definition expr_242 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 237))).
Definition closed_242 (v : leaf_values) : VM.t hvalue := (VM.add 237 (Gval (Fuint 4) (word_237 v)) (VM.empty hvalue)).
Definition word_242 (v : leaf_values) := word_of_eval (eval_hfexpr expr_242 (closed_242 v) (closed_242 v)).
Definition expr_243 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 241)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 242))).
Definition closed_243 (v : leaf_values) : VM.t hvalue := (VM.add 242 (Gval (Fuint 1) (word_242 v)) (VM.add 241 (Gval (Fuint 1) (word_241 v)) (VM.empty hvalue))).
Definition word_243 (v : leaf_values) := word_of_eval (eval_hfexpr expr_243 (closed_243 v) (closed_243 v)).
Definition expr_244 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 240)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 243))).
Definition closed_244 (v : leaf_values) : VM.t hvalue := (VM.add 243 (Gval (Fuint 2) (word_243 v)) (VM.add 240 (Gval (Fuint 1) (word_240 v)) (VM.empty hvalue))).
Definition word_244 (v : leaf_values) := word_of_eval (eval_hfexpr expr_244 (closed_244 v) (closed_244 v)).
Definition expr_245 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 238))).
Definition closed_245 (v : leaf_values) : VM.t hvalue := (VM.add 238 (Gval (Fuint 4) (word_238 v)) (VM.empty hvalue)).
Definition word_245 (v : leaf_values) := word_of_eval (eval_hfexpr expr_245 (closed_245 v) (closed_245 v)).
Definition expr_246 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 238))).
Definition closed_246 (v : leaf_values) : VM.t hvalue := (VM.add 238 (Gval (Fuint 4) (word_238 v)) (VM.empty hvalue)).
Definition word_246 (v : leaf_values) := word_of_eval (eval_hfexpr expr_246 (closed_246 v) (closed_246 v)).
Definition expr_247 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 238))).
Definition closed_247 (v : leaf_values) : VM.t hvalue := (VM.add 238 (Gval (Fuint 4) (word_238 v)) (VM.empty hvalue)).
Definition word_247 (v : leaf_values) := word_of_eval (eval_hfexpr expr_247 (closed_247 v) (closed_247 v)).
Definition expr_248 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 246)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 247))).
Definition closed_248 (v : leaf_values) : VM.t hvalue := (VM.add 247 (Gval (Fuint 1) (word_247 v)) (VM.add 246 (Gval (Fuint 1) (word_246 v)) (VM.empty hvalue))).
Definition word_248 (v : leaf_values) := word_of_eval (eval_hfexpr expr_248 (closed_248 v) (closed_248 v)).
Definition expr_249 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 245)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 248))).
Definition closed_249 (v : leaf_values) : VM.t hvalue := (VM.add 248 (Gval (Fuint 2) (word_248 v)) (VM.add 245 (Gval (Fuint 1) (word_245 v)) (VM.empty hvalue))).
Definition word_249 (v : leaf_values) := word_of_eval (eval_hfexpr expr_249 (closed_249 v) (closed_249 v)).
Definition expr_250 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 239)) (@Eref VarOrder.T (@Eid VarOrder.T 244)) (@Eref VarOrder.T (@Eid VarOrder.T 249))).
Definition closed_250 (v : leaf_values) : VM.t hvalue := (VM.add 249 (Gval (Fuint 2) (word_249 v)) (VM.add 244 (Gval (Fuint 2) (word_244 v)) (VM.add 239 (Gval (Fuint 1) (word_239 v)) (VM.empty hvalue)))).
Definition word_250 (v : leaf_values) := word_of_eval (eval_hfexpr expr_250 (closed_250 v) (closed_250 v)).
Definition expr_251 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 239)) (@Eref VarOrder.T (@Eid VarOrder.T 250))).
Definition closed_251 (v : leaf_values) : VM.t hvalue := (VM.add 250 (Gval (Fuint 2) (word_250 v)) (VM.add 239 (Gval (Fuint 1) (word_239 v)) (VM.empty hvalue))).
Definition word_251 (v : leaf_values) := word_of_eval (eval_hfexpr expr_251 (closed_251 v) (closed_251 v)).
Definition expr_252 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 221)) (@Eref VarOrder.T (@Eid VarOrder.T 236)) (@Eref VarOrder.T (@Eid VarOrder.T 251))).
Definition closed_252 (v : leaf_values) : VM.t hvalue := (VM.add 251 (Gval (Fuint 3) (word_251 v)) (VM.add 236 (Gval (Fuint 3) (word_236 v)) (VM.add 221 (Gval (Fuint 1) (word_221 v)) (VM.empty hvalue)))).
Definition word_252 (v : leaf_values) := word_of_eval (eval_hfexpr expr_252 (closed_252 v) (closed_252 v)).
Definition expr_253 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 221)) (@Eref VarOrder.T (@Eid VarOrder.T 252))).
Definition closed_253 (v : leaf_values) : VM.t hvalue := (VM.add 252 (Gval (Fuint 3) (word_252 v)) (VM.add 221 (Gval (Fuint 1) (word_221 v)) (VM.empty hvalue))).
Definition word_253 (v : leaf_values) := word_of_eval (eval_hfexpr expr_253 (closed_253 v) (closed_253 v)).
Definition expr_254 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 217))).
Definition closed_254 (v : leaf_values) : VM.t hvalue := (VM.add 217 (Gval (Fuint 16) (word_217 v)) (VM.empty hvalue)).
Definition word_254 (v : leaf_values) := word_of_eval (eval_hfexpr expr_254 (closed_254 v) (closed_254 v)).
Definition expr_255 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 217))).
Definition closed_255 (v : leaf_values) : VM.t hvalue := (VM.add 217 (Gval (Fuint 16) (word_217 v)) (VM.empty hvalue)).
Definition word_255 (v : leaf_values) := word_of_eval (eval_hfexpr expr_255 (closed_255 v) (closed_255 v)).
Definition expr_256 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 254))).
Definition closed_256 (v : leaf_values) : VM.t hvalue := (VM.add 254 (Gval (Fuint 8) (word_254 v)) (VM.empty hvalue)).
Definition word_256 (v : leaf_values) := word_of_eval (eval_hfexpr expr_256 (closed_256 v) (closed_256 v)).
Definition expr_257 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 254))).
Definition closed_257 (v : leaf_values) : VM.t hvalue := (VM.add 254 (Gval (Fuint 8) (word_254 v)) (VM.empty hvalue)).
Definition word_257 (v : leaf_values) := word_of_eval (eval_hfexpr expr_257 (closed_257 v) (closed_257 v)).
Definition expr_258 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 254))).
Definition closed_258 (v : leaf_values) : VM.t hvalue := (VM.add 254 (Gval (Fuint 8) (word_254 v)) (VM.empty hvalue)).
Definition word_258 (v : leaf_values) := word_of_eval (eval_hfexpr expr_258 (closed_258 v) (closed_258 v)).
Definition expr_259 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 257))).
Definition closed_259 (v : leaf_values) : VM.t hvalue := (VM.add 257 (Gval (Fuint 4) (word_257 v)) (VM.empty hvalue)).
Definition word_259 (v : leaf_values) := word_of_eval (eval_hfexpr expr_259 (closed_259 v) (closed_259 v)).
Definition expr_260 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 257))).
Definition closed_260 (v : leaf_values) : VM.t hvalue := (VM.add 257 (Gval (Fuint 4) (word_257 v)) (VM.empty hvalue)).
Definition word_260 (v : leaf_values) := word_of_eval (eval_hfexpr expr_260 (closed_260 v) (closed_260 v)).
Definition expr_261 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 257))).
Definition closed_261 (v : leaf_values) : VM.t hvalue := (VM.add 257 (Gval (Fuint 4) (word_257 v)) (VM.empty hvalue)).
Definition word_261 (v : leaf_values) := word_of_eval (eval_hfexpr expr_261 (closed_261 v) (closed_261 v)).
Definition expr_262 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 257))).
Definition closed_262 (v : leaf_values) : VM.t hvalue := (VM.add 257 (Gval (Fuint 4) (word_257 v)) (VM.empty hvalue)).
Definition word_262 (v : leaf_values) := word_of_eval (eval_hfexpr expr_262 (closed_262 v) (closed_262 v)).
Definition expr_263 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 261)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 262))).
Definition closed_263 (v : leaf_values) : VM.t hvalue := (VM.add 262 (Gval (Fuint 1) (word_262 v)) (VM.add 261 (Gval (Fuint 1) (word_261 v)) (VM.empty hvalue))).
Definition word_263 (v : leaf_values) := word_of_eval (eval_hfexpr expr_263 (closed_263 v) (closed_263 v)).
Definition expr_264 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 260)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 263))).
Definition closed_264 (v : leaf_values) : VM.t hvalue := (VM.add 263 (Gval (Fuint 2) (word_263 v)) (VM.add 260 (Gval (Fuint 1) (word_260 v)) (VM.empty hvalue))).
Definition word_264 (v : leaf_values) := word_of_eval (eval_hfexpr expr_264 (closed_264 v) (closed_264 v)).
Definition expr_265 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 258))).
Definition closed_265 (v : leaf_values) : VM.t hvalue := (VM.add 258 (Gval (Fuint 4) (word_258 v)) (VM.empty hvalue)).
Definition word_265 (v : leaf_values) := word_of_eval (eval_hfexpr expr_265 (closed_265 v) (closed_265 v)).
Definition expr_266 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 258))).
Definition closed_266 (v : leaf_values) : VM.t hvalue := (VM.add 258 (Gval (Fuint 4) (word_258 v)) (VM.empty hvalue)).
Definition word_266 (v : leaf_values) := word_of_eval (eval_hfexpr expr_266 (closed_266 v) (closed_266 v)).
Definition expr_267 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 258))).
Definition closed_267 (v : leaf_values) : VM.t hvalue := (VM.add 258 (Gval (Fuint 4) (word_258 v)) (VM.empty hvalue)).
Definition word_267 (v : leaf_values) := word_of_eval (eval_hfexpr expr_267 (closed_267 v) (closed_267 v)).
Definition expr_268 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 266)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 267))).
Definition closed_268 (v : leaf_values) : VM.t hvalue := (VM.add 267 (Gval (Fuint 1) (word_267 v)) (VM.add 266 (Gval (Fuint 1) (word_266 v)) (VM.empty hvalue))).
Definition word_268 (v : leaf_values) := word_of_eval (eval_hfexpr expr_268 (closed_268 v) (closed_268 v)).
Definition expr_269 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 265)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 268))).
Definition closed_269 (v : leaf_values) : VM.t hvalue := (VM.add 268 (Gval (Fuint 2) (word_268 v)) (VM.add 265 (Gval (Fuint 1) (word_265 v)) (VM.empty hvalue))).
Definition word_269 (v : leaf_values) := word_of_eval (eval_hfexpr expr_269 (closed_269 v) (closed_269 v)).
Definition expr_270 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 259)) (@Eref VarOrder.T (@Eid VarOrder.T 264)) (@Eref VarOrder.T (@Eid VarOrder.T 269))).
Definition closed_270 (v : leaf_values) : VM.t hvalue := (VM.add 269 (Gval (Fuint 2) (word_269 v)) (VM.add 264 (Gval (Fuint 2) (word_264 v)) (VM.add 259 (Gval (Fuint 1) (word_259 v)) (VM.empty hvalue)))).
Definition word_270 (v : leaf_values) := word_of_eval (eval_hfexpr expr_270 (closed_270 v) (closed_270 v)).
Definition expr_271 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 259)) (@Eref VarOrder.T (@Eid VarOrder.T 270))).
Definition closed_271 (v : leaf_values) : VM.t hvalue := (VM.add 270 (Gval (Fuint 2) (word_270 v)) (VM.add 259 (Gval (Fuint 1) (word_259 v)) (VM.empty hvalue))).
Definition word_271 (v : leaf_values) := word_of_eval (eval_hfexpr expr_271 (closed_271 v) (closed_271 v)).
Definition expr_272 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 255))).
Definition closed_272 (v : leaf_values) : VM.t hvalue := (VM.add 255 (Gval (Fuint 8) (word_255 v)) (VM.empty hvalue)).
Definition word_272 (v : leaf_values) := word_of_eval (eval_hfexpr expr_272 (closed_272 v) (closed_272 v)).
Definition expr_273 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 255))).
Definition closed_273 (v : leaf_values) : VM.t hvalue := (VM.add 255 (Gval (Fuint 8) (word_255 v)) (VM.empty hvalue)).
Definition word_273 (v : leaf_values) := word_of_eval (eval_hfexpr expr_273 (closed_273 v) (closed_273 v)).
Definition expr_274 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 272))).
Definition closed_274 (v : leaf_values) : VM.t hvalue := (VM.add 272 (Gval (Fuint 4) (word_272 v)) (VM.empty hvalue)).
Definition word_274 (v : leaf_values) := word_of_eval (eval_hfexpr expr_274 (closed_274 v) (closed_274 v)).
Definition expr_275 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 272))).
Definition closed_275 (v : leaf_values) : VM.t hvalue := (VM.add 272 (Gval (Fuint 4) (word_272 v)) (VM.empty hvalue)).
Definition word_275 (v : leaf_values) := word_of_eval (eval_hfexpr expr_275 (closed_275 v) (closed_275 v)).
Definition expr_276 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 272))).
Definition closed_276 (v : leaf_values) : VM.t hvalue := (VM.add 272 (Gval (Fuint 4) (word_272 v)) (VM.empty hvalue)).
Definition word_276 (v : leaf_values) := word_of_eval (eval_hfexpr expr_276 (closed_276 v) (closed_276 v)).
Definition expr_277 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 272))).
Definition closed_277 (v : leaf_values) : VM.t hvalue := (VM.add 272 (Gval (Fuint 4) (word_272 v)) (VM.empty hvalue)).
Definition word_277 (v : leaf_values) := word_of_eval (eval_hfexpr expr_277 (closed_277 v) (closed_277 v)).
Definition expr_278 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 276)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 277))).
Definition closed_278 (v : leaf_values) : VM.t hvalue := (VM.add 277 (Gval (Fuint 1) (word_277 v)) (VM.add 276 (Gval (Fuint 1) (word_276 v)) (VM.empty hvalue))).
Definition word_278 (v : leaf_values) := word_of_eval (eval_hfexpr expr_278 (closed_278 v) (closed_278 v)).
Definition expr_279 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 275)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 278))).
Definition closed_279 (v : leaf_values) : VM.t hvalue := (VM.add 278 (Gval (Fuint 2) (word_278 v)) (VM.add 275 (Gval (Fuint 1) (word_275 v)) (VM.empty hvalue))).
Definition word_279 (v : leaf_values) := word_of_eval (eval_hfexpr expr_279 (closed_279 v) (closed_279 v)).
Definition expr_280 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 273))).
Definition closed_280 (v : leaf_values) : VM.t hvalue := (VM.add 273 (Gval (Fuint 4) (word_273 v)) (VM.empty hvalue)).
Definition word_280 (v : leaf_values) := word_of_eval (eval_hfexpr expr_280 (closed_280 v) (closed_280 v)).
Definition expr_281 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 273))).
Definition closed_281 (v : leaf_values) : VM.t hvalue := (VM.add 273 (Gval (Fuint 4) (word_273 v)) (VM.empty hvalue)).
Definition word_281 (v : leaf_values) := word_of_eval (eval_hfexpr expr_281 (closed_281 v) (closed_281 v)).
Definition expr_282 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 273))).
Definition closed_282 (v : leaf_values) : VM.t hvalue := (VM.add 273 (Gval (Fuint 4) (word_273 v)) (VM.empty hvalue)).
Definition word_282 (v : leaf_values) := word_of_eval (eval_hfexpr expr_282 (closed_282 v) (closed_282 v)).
Definition expr_283 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 281)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 282))).
Definition closed_283 (v : leaf_values) : VM.t hvalue := (VM.add 282 (Gval (Fuint 1) (word_282 v)) (VM.add 281 (Gval (Fuint 1) (word_281 v)) (VM.empty hvalue))).
Definition word_283 (v : leaf_values) := word_of_eval (eval_hfexpr expr_283 (closed_283 v) (closed_283 v)).
Definition expr_284 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 280)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 283))).
Definition closed_284 (v : leaf_values) : VM.t hvalue := (VM.add 283 (Gval (Fuint 2) (word_283 v)) (VM.add 280 (Gval (Fuint 1) (word_280 v)) (VM.empty hvalue))).
Definition word_284 (v : leaf_values) := word_of_eval (eval_hfexpr expr_284 (closed_284 v) (closed_284 v)).
Definition expr_285 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 274)) (@Eref VarOrder.T (@Eid VarOrder.T 279)) (@Eref VarOrder.T (@Eid VarOrder.T 284))).
Definition closed_285 (v : leaf_values) : VM.t hvalue := (VM.add 284 (Gval (Fuint 2) (word_284 v)) (VM.add 279 (Gval (Fuint 2) (word_279 v)) (VM.add 274 (Gval (Fuint 1) (word_274 v)) (VM.empty hvalue)))).
Definition word_285 (v : leaf_values) := word_of_eval (eval_hfexpr expr_285 (closed_285 v) (closed_285 v)).
Definition expr_286 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 274)) (@Eref VarOrder.T (@Eid VarOrder.T 285))).
Definition closed_286 (v : leaf_values) : VM.t hvalue := (VM.add 285 (Gval (Fuint 2) (word_285 v)) (VM.add 274 (Gval (Fuint 1) (word_274 v)) (VM.empty hvalue))).
Definition word_286 (v : leaf_values) := word_of_eval (eval_hfexpr expr_286 (closed_286 v) (closed_286 v)).
Definition expr_287 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 256)) (@Eref VarOrder.T (@Eid VarOrder.T 271)) (@Eref VarOrder.T (@Eid VarOrder.T 286))).
Definition closed_287 (v : leaf_values) : VM.t hvalue := (VM.add 286 (Gval (Fuint 3) (word_286 v)) (VM.add 271 (Gval (Fuint 3) (word_271 v)) (VM.add 256 (Gval (Fuint 1) (word_256 v)) (VM.empty hvalue)))).
Definition word_287 (v : leaf_values) := word_of_eval (eval_hfexpr expr_287 (closed_287 v) (closed_287 v)).
Definition expr_288 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 256)) (@Eref VarOrder.T (@Eid VarOrder.T 287))).
Definition closed_288 (v : leaf_values) : VM.t hvalue := (VM.add 287 (Gval (Fuint 3) (word_287 v)) (VM.add 256 (Gval (Fuint 1) (word_256 v)) (VM.empty hvalue))).
Definition word_288 (v : leaf_values) := word_of_eval (eval_hfexpr expr_288 (closed_288 v) (closed_288 v)).
Definition expr_289 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 218)) (@Eref VarOrder.T (@Eid VarOrder.T 253)) (@Eref VarOrder.T (@Eid VarOrder.T 288))).
Definition closed_289 (v : leaf_values) : VM.t hvalue := (VM.add 288 (Gval (Fuint 4) (word_288 v)) (VM.add 253 (Gval (Fuint 4) (word_253 v)) (VM.add 218 (Gval (Fuint 1) (word_218 v)) (VM.empty hvalue)))).
Definition word_289 (v : leaf_values) := word_of_eval (eval_hfexpr expr_289 (closed_289 v) (closed_289 v)).
Definition expr_290 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 218)) (@Eref VarOrder.T (@Eid VarOrder.T 289))).
Definition closed_290 (v : leaf_values) : VM.t hvalue := (VM.add 289 (Gval (Fuint 4) (word_289 v)) (VM.add 218 (Gval (Fuint 1) (word_218 v)) (VM.empty hvalue))).
Definition word_290 (v : leaf_values) := word_of_eval (eval_hfexpr expr_290 (closed_290 v) (closed_290 v)).
Definition expr_291 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 16) (@Eref VarOrder.T (@Eid VarOrder.T 214))).
Definition closed_291 (v : leaf_values) : VM.t hvalue := (VM.add 214 (Gval (Fuint 32) (word_214 v)) (VM.empty hvalue)).
Definition word_291 (v : leaf_values) := word_of_eval (eval_hfexpr expr_291 (closed_291 v) (closed_291 v)).
Definition expr_292 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 214))).
Definition closed_292 (v : leaf_values) : VM.t hvalue := (VM.add 214 (Gval (Fuint 32) (word_214 v)) (VM.empty hvalue)).
Definition word_292 (v : leaf_values) := word_of_eval (eval_hfexpr expr_292 (closed_292 v) (closed_292 v)).
Definition expr_293 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 291))).
Definition closed_293 (v : leaf_values) : VM.t hvalue := (VM.add 291 (Gval (Fuint 16) (word_291 v)) (VM.empty hvalue)).
Definition word_293 (v : leaf_values) := word_of_eval (eval_hfexpr expr_293 (closed_293 v) (closed_293 v)).
Definition expr_294 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 291))).
Definition closed_294 (v : leaf_values) : VM.t hvalue := (VM.add 291 (Gval (Fuint 16) (word_291 v)) (VM.empty hvalue)).
Definition word_294 (v : leaf_values) := word_of_eval (eval_hfexpr expr_294 (closed_294 v) (closed_294 v)).
Definition expr_295 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 291))).
Definition closed_295 (v : leaf_values) : VM.t hvalue := (VM.add 291 (Gval (Fuint 16) (word_291 v)) (VM.empty hvalue)).
Definition word_295 (v : leaf_values) := word_of_eval (eval_hfexpr expr_295 (closed_295 v) (closed_295 v)).
Definition expr_296 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 294))).
Definition closed_296 (v : leaf_values) : VM.t hvalue := (VM.add 294 (Gval (Fuint 8) (word_294 v)) (VM.empty hvalue)).
Definition word_296 (v : leaf_values) := word_of_eval (eval_hfexpr expr_296 (closed_296 v) (closed_296 v)).
Definition expr_297 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 294))).
Definition closed_297 (v : leaf_values) : VM.t hvalue := (VM.add 294 (Gval (Fuint 8) (word_294 v)) (VM.empty hvalue)).
Definition word_297 (v : leaf_values) := word_of_eval (eval_hfexpr expr_297 (closed_297 v) (closed_297 v)).
Definition expr_298 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 294))).
Definition closed_298 (v : leaf_values) : VM.t hvalue := (VM.add 294 (Gval (Fuint 8) (word_294 v)) (VM.empty hvalue)).
Definition word_298 (v : leaf_values) := word_of_eval (eval_hfexpr expr_298 (closed_298 v) (closed_298 v)).
Definition expr_299 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 297))).
Definition closed_299 (v : leaf_values) : VM.t hvalue := (VM.add 297 (Gval (Fuint 4) (word_297 v)) (VM.empty hvalue)).
Definition word_299 (v : leaf_values) := word_of_eval (eval_hfexpr expr_299 (closed_299 v) (closed_299 v)).
Definition expr_300 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 297))).
Definition closed_300 (v : leaf_values) : VM.t hvalue := (VM.add 297 (Gval (Fuint 4) (word_297 v)) (VM.empty hvalue)).
Definition word_300 (v : leaf_values) := word_of_eval (eval_hfexpr expr_300 (closed_300 v) (closed_300 v)).
Definition expr_301 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 297))).
Definition closed_301 (v : leaf_values) : VM.t hvalue := (VM.add 297 (Gval (Fuint 4) (word_297 v)) (VM.empty hvalue)).
Definition word_301 (v : leaf_values) := word_of_eval (eval_hfexpr expr_301 (closed_301 v) (closed_301 v)).
Definition expr_302 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 297))).
Definition closed_302 (v : leaf_values) : VM.t hvalue := (VM.add 297 (Gval (Fuint 4) (word_297 v)) (VM.empty hvalue)).
Definition word_302 (v : leaf_values) := word_of_eval (eval_hfexpr expr_302 (closed_302 v) (closed_302 v)).
Definition expr_303 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 301)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 302))).
Definition closed_303 (v : leaf_values) : VM.t hvalue := (VM.add 302 (Gval (Fuint 1) (word_302 v)) (VM.add 301 (Gval (Fuint 1) (word_301 v)) (VM.empty hvalue))).
Definition word_303 (v : leaf_values) := word_of_eval (eval_hfexpr expr_303 (closed_303 v) (closed_303 v)).
Definition expr_304 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 303))).
Definition closed_304 (v : leaf_values) : VM.t hvalue := (VM.add 303 (Gval (Fuint 2) (word_303 v)) (VM.add 300 (Gval (Fuint 1) (word_300 v)) (VM.empty hvalue))).
Definition word_304 (v : leaf_values) := word_of_eval (eval_hfexpr expr_304 (closed_304 v) (closed_304 v)).
Definition expr_305 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 298))).
Definition closed_305 (v : leaf_values) : VM.t hvalue := (VM.add 298 (Gval (Fuint 4) (word_298 v)) (VM.empty hvalue)).
Definition word_305 (v : leaf_values) := word_of_eval (eval_hfexpr expr_305 (closed_305 v) (closed_305 v)).
Definition expr_306 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 298))).
Definition closed_306 (v : leaf_values) : VM.t hvalue := (VM.add 298 (Gval (Fuint 4) (word_298 v)) (VM.empty hvalue)).
Definition word_306 (v : leaf_values) := word_of_eval (eval_hfexpr expr_306 (closed_306 v) (closed_306 v)).
Definition expr_307 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 298))).
Definition closed_307 (v : leaf_values) : VM.t hvalue := (VM.add 298 (Gval (Fuint 4) (word_298 v)) (VM.empty hvalue)).
Definition word_307 (v : leaf_values) := word_of_eval (eval_hfexpr expr_307 (closed_307 v) (closed_307 v)).
Definition expr_308 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 306)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 307))).
Definition closed_308 (v : leaf_values) : VM.t hvalue := (VM.add 307 (Gval (Fuint 1) (word_307 v)) (VM.add 306 (Gval (Fuint 1) (word_306 v)) (VM.empty hvalue))).
Definition word_308 (v : leaf_values) := word_of_eval (eval_hfexpr expr_308 (closed_308 v) (closed_308 v)).
Definition expr_309 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 305)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 308))).
Definition closed_309 (v : leaf_values) : VM.t hvalue := (VM.add 308 (Gval (Fuint 2) (word_308 v)) (VM.add 305 (Gval (Fuint 1) (word_305 v)) (VM.empty hvalue))).
Definition word_309 (v : leaf_values) := word_of_eval (eval_hfexpr expr_309 (closed_309 v) (closed_309 v)).
Definition expr_310 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 299)) (@Eref VarOrder.T (@Eid VarOrder.T 304)) (@Eref VarOrder.T (@Eid VarOrder.T 309))).
Definition closed_310 (v : leaf_values) : VM.t hvalue := (VM.add 309 (Gval (Fuint 2) (word_309 v)) (VM.add 304 (Gval (Fuint 2) (word_304 v)) (VM.add 299 (Gval (Fuint 1) (word_299 v)) (VM.empty hvalue)))).
Definition word_310 (v : leaf_values) := word_of_eval (eval_hfexpr expr_310 (closed_310 v) (closed_310 v)).
Definition expr_311 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 299)) (@Eref VarOrder.T (@Eid VarOrder.T 310))).
Definition closed_311 (v : leaf_values) : VM.t hvalue := (VM.add 310 (Gval (Fuint 2) (word_310 v)) (VM.add 299 (Gval (Fuint 1) (word_299 v)) (VM.empty hvalue))).
Definition word_311 (v : leaf_values) := word_of_eval (eval_hfexpr expr_311 (closed_311 v) (closed_311 v)).
Definition expr_312 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 295))).
Definition closed_312 (v : leaf_values) : VM.t hvalue := (VM.add 295 (Gval (Fuint 8) (word_295 v)) (VM.empty hvalue)).
Definition word_312 (v : leaf_values) := word_of_eval (eval_hfexpr expr_312 (closed_312 v) (closed_312 v)).
Definition expr_313 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 295))).
Definition closed_313 (v : leaf_values) : VM.t hvalue := (VM.add 295 (Gval (Fuint 8) (word_295 v)) (VM.empty hvalue)).
Definition word_313 (v : leaf_values) := word_of_eval (eval_hfexpr expr_313 (closed_313 v) (closed_313 v)).
Definition expr_314 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 312))).
Definition closed_314 (v : leaf_values) : VM.t hvalue := (VM.add 312 (Gval (Fuint 4) (word_312 v)) (VM.empty hvalue)).
Definition word_314 (v : leaf_values) := word_of_eval (eval_hfexpr expr_314 (closed_314 v) (closed_314 v)).
Definition expr_315 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 312))).
Definition closed_315 (v : leaf_values) : VM.t hvalue := (VM.add 312 (Gval (Fuint 4) (word_312 v)) (VM.empty hvalue)).
Definition word_315 (v : leaf_values) := word_of_eval (eval_hfexpr expr_315 (closed_315 v) (closed_315 v)).
Definition expr_316 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 312))).
Definition closed_316 (v : leaf_values) : VM.t hvalue := (VM.add 312 (Gval (Fuint 4) (word_312 v)) (VM.empty hvalue)).
Definition word_316 (v : leaf_values) := word_of_eval (eval_hfexpr expr_316 (closed_316 v) (closed_316 v)).
Definition expr_317 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 312))).
Definition closed_317 (v : leaf_values) : VM.t hvalue := (VM.add 312 (Gval (Fuint 4) (word_312 v)) (VM.empty hvalue)).
Definition word_317 (v : leaf_values) := word_of_eval (eval_hfexpr expr_317 (closed_317 v) (closed_317 v)).
Definition expr_318 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 316)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 317))).
Definition closed_318 (v : leaf_values) : VM.t hvalue := (VM.add 317 (Gval (Fuint 1) (word_317 v)) (VM.add 316 (Gval (Fuint 1) (word_316 v)) (VM.empty hvalue))).
Definition word_318 (v : leaf_values) := word_of_eval (eval_hfexpr expr_318 (closed_318 v) (closed_318 v)).
Definition expr_319 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 315)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 318))).
Definition closed_319 (v : leaf_values) : VM.t hvalue := (VM.add 318 (Gval (Fuint 2) (word_318 v)) (VM.add 315 (Gval (Fuint 1) (word_315 v)) (VM.empty hvalue))).
Definition word_319 (v : leaf_values) := word_of_eval (eval_hfexpr expr_319 (closed_319 v) (closed_319 v)).
Definition expr_320 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 313))).
Definition closed_320 (v : leaf_values) : VM.t hvalue := (VM.add 313 (Gval (Fuint 4) (word_313 v)) (VM.empty hvalue)).
Definition word_320 (v : leaf_values) := word_of_eval (eval_hfexpr expr_320 (closed_320 v) (closed_320 v)).
Definition expr_321 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 313))).
Definition closed_321 (v : leaf_values) : VM.t hvalue := (VM.add 313 (Gval (Fuint 4) (word_313 v)) (VM.empty hvalue)).
Definition word_321 (v : leaf_values) := word_of_eval (eval_hfexpr expr_321 (closed_321 v) (closed_321 v)).
Definition expr_322 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 313))).
Definition closed_322 (v : leaf_values) : VM.t hvalue := (VM.add 313 (Gval (Fuint 4) (word_313 v)) (VM.empty hvalue)).
Definition word_322 (v : leaf_values) := word_of_eval (eval_hfexpr expr_322 (closed_322 v) (closed_322 v)).
Definition expr_323 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 321)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 322))).
Definition closed_323 (v : leaf_values) : VM.t hvalue := (VM.add 322 (Gval (Fuint 1) (word_322 v)) (VM.add 321 (Gval (Fuint 1) (word_321 v)) (VM.empty hvalue))).
Definition word_323 (v : leaf_values) := word_of_eval (eval_hfexpr expr_323 (closed_323 v) (closed_323 v)).
Definition expr_324 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 320)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 323))).
Definition closed_324 (v : leaf_values) : VM.t hvalue := (VM.add 323 (Gval (Fuint 2) (word_323 v)) (VM.add 320 (Gval (Fuint 1) (word_320 v)) (VM.empty hvalue))).
Definition word_324 (v : leaf_values) := word_of_eval (eval_hfexpr expr_324 (closed_324 v) (closed_324 v)).
Definition expr_325 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 314)) (@Eref VarOrder.T (@Eid VarOrder.T 319)) (@Eref VarOrder.T (@Eid VarOrder.T 324))).
Definition closed_325 (v : leaf_values) : VM.t hvalue := (VM.add 324 (Gval (Fuint 2) (word_324 v)) (VM.add 319 (Gval (Fuint 2) (word_319 v)) (VM.add 314 (Gval (Fuint 1) (word_314 v)) (VM.empty hvalue)))).
Definition word_325 (v : leaf_values) := word_of_eval (eval_hfexpr expr_325 (closed_325 v) (closed_325 v)).
Definition expr_326 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 314)) (@Eref VarOrder.T (@Eid VarOrder.T 325))).
Definition closed_326 (v : leaf_values) : VM.t hvalue := (VM.add 325 (Gval (Fuint 2) (word_325 v)) (VM.add 314 (Gval (Fuint 1) (word_314 v)) (VM.empty hvalue))).
Definition word_326 (v : leaf_values) := word_of_eval (eval_hfexpr expr_326 (closed_326 v) (closed_326 v)).
Definition expr_327 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 296)) (@Eref VarOrder.T (@Eid VarOrder.T 311)) (@Eref VarOrder.T (@Eid VarOrder.T 326))).
Definition closed_327 (v : leaf_values) : VM.t hvalue := (VM.add 326 (Gval (Fuint 3) (word_326 v)) (VM.add 311 (Gval (Fuint 3) (word_311 v)) (VM.add 296 (Gval (Fuint 1) (word_296 v)) (VM.empty hvalue)))).
Definition word_327 (v : leaf_values) := word_of_eval (eval_hfexpr expr_327 (closed_327 v) (closed_327 v)).
Definition expr_328 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 296)) (@Eref VarOrder.T (@Eid VarOrder.T 327))).
Definition closed_328 (v : leaf_values) : VM.t hvalue := (VM.add 327 (Gval (Fuint 3) (word_327 v)) (VM.add 296 (Gval (Fuint 1) (word_296 v)) (VM.empty hvalue))).
Definition word_328 (v : leaf_values) := word_of_eval (eval_hfexpr expr_328 (closed_328 v) (closed_328 v)).
Definition expr_329 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 292))).
Definition closed_329 (v : leaf_values) : VM.t hvalue := (VM.add 292 (Gval (Fuint 16) (word_292 v)) (VM.empty hvalue)).
Definition word_329 (v : leaf_values) := word_of_eval (eval_hfexpr expr_329 (closed_329 v) (closed_329 v)).
Definition expr_330 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 292))).
Definition closed_330 (v : leaf_values) : VM.t hvalue := (VM.add 292 (Gval (Fuint 16) (word_292 v)) (VM.empty hvalue)).
Definition word_330 (v : leaf_values) := word_of_eval (eval_hfexpr expr_330 (closed_330 v) (closed_330 v)).
Definition expr_331 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 329))).
Definition closed_331 (v : leaf_values) : VM.t hvalue := (VM.add 329 (Gval (Fuint 8) (word_329 v)) (VM.empty hvalue)).
Definition word_331 (v : leaf_values) := word_of_eval (eval_hfexpr expr_331 (closed_331 v) (closed_331 v)).
Definition expr_332 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 329))).
Definition closed_332 (v : leaf_values) : VM.t hvalue := (VM.add 329 (Gval (Fuint 8) (word_329 v)) (VM.empty hvalue)).
Definition word_332 (v : leaf_values) := word_of_eval (eval_hfexpr expr_332 (closed_332 v) (closed_332 v)).
Definition expr_333 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 329))).
Definition closed_333 (v : leaf_values) : VM.t hvalue := (VM.add 329 (Gval (Fuint 8) (word_329 v)) (VM.empty hvalue)).
Definition word_333 (v : leaf_values) := word_of_eval (eval_hfexpr expr_333 (closed_333 v) (closed_333 v)).
Definition expr_334 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 332))).
Definition closed_334 (v : leaf_values) : VM.t hvalue := (VM.add 332 (Gval (Fuint 4) (word_332 v)) (VM.empty hvalue)).
Definition word_334 (v : leaf_values) := word_of_eval (eval_hfexpr expr_334 (closed_334 v) (closed_334 v)).
Definition expr_335 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 332))).
Definition closed_335 (v : leaf_values) : VM.t hvalue := (VM.add 332 (Gval (Fuint 4) (word_332 v)) (VM.empty hvalue)).
Definition word_335 (v : leaf_values) := word_of_eval (eval_hfexpr expr_335 (closed_335 v) (closed_335 v)).
Definition expr_336 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 332))).
Definition closed_336 (v : leaf_values) : VM.t hvalue := (VM.add 332 (Gval (Fuint 4) (word_332 v)) (VM.empty hvalue)).
Definition word_336 (v : leaf_values) := word_of_eval (eval_hfexpr expr_336 (closed_336 v) (closed_336 v)).
Definition expr_337 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 332))).
Definition closed_337 (v : leaf_values) : VM.t hvalue := (VM.add 332 (Gval (Fuint 4) (word_332 v)) (VM.empty hvalue)).
Definition word_337 (v : leaf_values) := word_of_eval (eval_hfexpr expr_337 (closed_337 v) (closed_337 v)).
Definition expr_338 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 336)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 337))).
Definition closed_338 (v : leaf_values) : VM.t hvalue := (VM.add 337 (Gval (Fuint 1) (word_337 v)) (VM.add 336 (Gval (Fuint 1) (word_336 v)) (VM.empty hvalue))).
Definition word_338 (v : leaf_values) := word_of_eval (eval_hfexpr expr_338 (closed_338 v) (closed_338 v)).
Definition expr_339 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 335)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 338))).
Definition closed_339 (v : leaf_values) : VM.t hvalue := (VM.add 338 (Gval (Fuint 2) (word_338 v)) (VM.add 335 (Gval (Fuint 1) (word_335 v)) (VM.empty hvalue))).
Definition word_339 (v : leaf_values) := word_of_eval (eval_hfexpr expr_339 (closed_339 v) (closed_339 v)).
Definition expr_340 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 333))).
Definition closed_340 (v : leaf_values) : VM.t hvalue := (VM.add 333 (Gval (Fuint 4) (word_333 v)) (VM.empty hvalue)).
Definition word_340 (v : leaf_values) := word_of_eval (eval_hfexpr expr_340 (closed_340 v) (closed_340 v)).
Definition expr_341 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 333))).
Definition closed_341 (v : leaf_values) : VM.t hvalue := (VM.add 333 (Gval (Fuint 4) (word_333 v)) (VM.empty hvalue)).
Definition word_341 (v : leaf_values) := word_of_eval (eval_hfexpr expr_341 (closed_341 v) (closed_341 v)).
Definition expr_342 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 333))).
Definition closed_342 (v : leaf_values) : VM.t hvalue := (VM.add 333 (Gval (Fuint 4) (word_333 v)) (VM.empty hvalue)).
Definition word_342 (v : leaf_values) := word_of_eval (eval_hfexpr expr_342 (closed_342 v) (closed_342 v)).
Definition expr_343 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 341)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 342))).
Definition closed_343 (v : leaf_values) : VM.t hvalue := (VM.add 342 (Gval (Fuint 1) (word_342 v)) (VM.add 341 (Gval (Fuint 1) (word_341 v)) (VM.empty hvalue))).
Definition word_343 (v : leaf_values) := word_of_eval (eval_hfexpr expr_343 (closed_343 v) (closed_343 v)).
Definition expr_344 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 340)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 343))).
Definition closed_344 (v : leaf_values) : VM.t hvalue := (VM.add 343 (Gval (Fuint 2) (word_343 v)) (VM.add 340 (Gval (Fuint 1) (word_340 v)) (VM.empty hvalue))).
Definition word_344 (v : leaf_values) := word_of_eval (eval_hfexpr expr_344 (closed_344 v) (closed_344 v)).
Definition expr_345 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 334)) (@Eref VarOrder.T (@Eid VarOrder.T 339)) (@Eref VarOrder.T (@Eid VarOrder.T 344))).
Definition closed_345 (v : leaf_values) : VM.t hvalue := (VM.add 344 (Gval (Fuint 2) (word_344 v)) (VM.add 339 (Gval (Fuint 2) (word_339 v)) (VM.add 334 (Gval (Fuint 1) (word_334 v)) (VM.empty hvalue)))).
Definition word_345 (v : leaf_values) := word_of_eval (eval_hfexpr expr_345 (closed_345 v) (closed_345 v)).
Definition expr_346 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 334)) (@Eref VarOrder.T (@Eid VarOrder.T 345))).
Definition closed_346 (v : leaf_values) : VM.t hvalue := (VM.add 345 (Gval (Fuint 2) (word_345 v)) (VM.add 334 (Gval (Fuint 1) (word_334 v)) (VM.empty hvalue))).
Definition word_346 (v : leaf_values) := word_of_eval (eval_hfexpr expr_346 (closed_346 v) (closed_346 v)).
Definition expr_347 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 4) (@Eref VarOrder.T (@Eid VarOrder.T 330))).
Definition closed_347 (v : leaf_values) : VM.t hvalue := (VM.add 330 (Gval (Fuint 8) (word_330 v)) (VM.empty hvalue)).
Definition word_347 (v : leaf_values) := word_of_eval (eval_hfexpr expr_347 (closed_347 v) (closed_347 v)).
Definition expr_348 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 330))).
Definition closed_348 (v : leaf_values) : VM.t hvalue := (VM.add 330 (Gval (Fuint 8) (word_330 v)) (VM.empty hvalue)).
Definition word_348 (v : leaf_values) := word_of_eval (eval_hfexpr expr_348 (closed_348 v) (closed_348 v)).
Definition expr_349 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 347))).
Definition closed_349 (v : leaf_values) : VM.t hvalue := (VM.add 347 (Gval (Fuint 4) (word_347 v)) (VM.empty hvalue)).
Definition word_349 (v : leaf_values) := word_of_eval (eval_hfexpr expr_349 (closed_349 v) (closed_349 v)).
Definition expr_350 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 347))).
Definition closed_350 (v : leaf_values) : VM.t hvalue := (VM.add 347 (Gval (Fuint 4) (word_347 v)) (VM.empty hvalue)).
Definition word_350 (v : leaf_values) := word_of_eval (eval_hfexpr expr_350 (closed_350 v) (closed_350 v)).
Definition expr_351 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 347))).
Definition closed_351 (v : leaf_values) : VM.t hvalue := (VM.add 347 (Gval (Fuint 4) (word_347 v)) (VM.empty hvalue)).
Definition word_351 (v : leaf_values) := word_of_eval (eval_hfexpr expr_351 (closed_351 v) (closed_351 v)).
Definition expr_352 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 347))).
Definition closed_352 (v : leaf_values) : VM.t hvalue := (VM.add 347 (Gval (Fuint 4) (word_347 v)) (VM.empty hvalue)).
Definition word_352 (v : leaf_values) := word_of_eval (eval_hfexpr expr_352 (closed_352 v) (closed_352 v)).
Definition expr_353 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 351)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 352))).
Definition closed_353 (v : leaf_values) : VM.t hvalue := (VM.add 352 (Gval (Fuint 1) (word_352 v)) (VM.add 351 (Gval (Fuint 1) (word_351 v)) (VM.empty hvalue))).
Definition word_353 (v : leaf_values) := word_of_eval (eval_hfexpr expr_353 (closed_353 v) (closed_353 v)).
Definition expr_354 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 350)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 353))).
Definition closed_354 (v : leaf_values) : VM.t hvalue := (VM.add 353 (Gval (Fuint 2) (word_353 v)) (VM.add 350 (Gval (Fuint 1) (word_350 v)) (VM.empty hvalue))).
Definition word_354 (v : leaf_values) := word_of_eval (eval_hfexpr expr_354 (closed_354 v) (closed_354 v)).
Definition expr_355 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 348))).
Definition closed_355 (v : leaf_values) : VM.t hvalue := (VM.add 348 (Gval (Fuint 4) (word_348 v)) (VM.empty hvalue)).
Definition word_355 (v : leaf_values) := word_of_eval (eval_hfexpr expr_355 (closed_355 v) (closed_355 v)).
Definition expr_356 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 348))).
Definition closed_356 (v : leaf_values) : VM.t hvalue := (VM.add 348 (Gval (Fuint 4) (word_348 v)) (VM.empty hvalue)).
Definition word_356 (v : leaf_values) := word_of_eval (eval_hfexpr expr_356 (closed_356 v) (closed_356 v)).
Definition expr_357 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 348))).
Definition closed_357 (v : leaf_values) : VM.t hvalue := (VM.add 348 (Gval (Fuint 4) (word_348 v)) (VM.empty hvalue)).
Definition word_357 (v : leaf_values) := word_of_eval (eval_hfexpr expr_357 (closed_357 v) (closed_357 v)).
Definition expr_358 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 356)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 357))).
Definition closed_358 (v : leaf_values) : VM.t hvalue := (VM.add 357 (Gval (Fuint 1) (word_357 v)) (VM.add 356 (Gval (Fuint 1) (word_356 v)) (VM.empty hvalue))).
Definition word_358 (v : leaf_values) := word_of_eval (eval_hfexpr expr_358 (closed_358 v) (closed_358 v)).
Definition expr_359 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 355)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 358))).
Definition closed_359 (v : leaf_values) : VM.t hvalue := (VM.add 358 (Gval (Fuint 2) (word_358 v)) (VM.add 355 (Gval (Fuint 1) (word_355 v)) (VM.empty hvalue))).
Definition word_359 (v : leaf_values) := word_of_eval (eval_hfexpr expr_359 (closed_359 v) (closed_359 v)).
Definition expr_360 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 349)) (@Eref VarOrder.T (@Eid VarOrder.T 354)) (@Eref VarOrder.T (@Eid VarOrder.T 359))).
Definition closed_360 (v : leaf_values) : VM.t hvalue := (VM.add 359 (Gval (Fuint 2) (word_359 v)) (VM.add 354 (Gval (Fuint 2) (word_354 v)) (VM.add 349 (Gval (Fuint 1) (word_349 v)) (VM.empty hvalue)))).
Definition word_360 (v : leaf_values) := word_of_eval (eval_hfexpr expr_360 (closed_360 v) (closed_360 v)).
Definition expr_361 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 349)) (@Eref VarOrder.T (@Eid VarOrder.T 360))).
Definition closed_361 (v : leaf_values) : VM.t hvalue := (VM.add 360 (Gval (Fuint 2) (word_360 v)) (VM.add 349 (Gval (Fuint 1) (word_349 v)) (VM.empty hvalue))).
Definition word_361 (v : leaf_values) := word_of_eval (eval_hfexpr expr_361 (closed_361 v) (closed_361 v)).
Definition expr_362 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 331)) (@Eref VarOrder.T (@Eid VarOrder.T 346)) (@Eref VarOrder.T (@Eid VarOrder.T 361))).
Definition closed_362 (v : leaf_values) : VM.t hvalue := (VM.add 361 (Gval (Fuint 3) (word_361 v)) (VM.add 346 (Gval (Fuint 3) (word_346 v)) (VM.add 331 (Gval (Fuint 1) (word_331 v)) (VM.empty hvalue)))).
Definition word_362 (v : leaf_values) := word_of_eval (eval_hfexpr expr_362 (closed_362 v) (closed_362 v)).
Definition expr_363 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 331)) (@Eref VarOrder.T (@Eid VarOrder.T 362))).
Definition closed_363 (v : leaf_values) : VM.t hvalue := (VM.add 362 (Gval (Fuint 3) (word_362 v)) (VM.add 331 (Gval (Fuint 1) (word_331 v)) (VM.empty hvalue))).
Definition word_363 (v : leaf_values) := word_of_eval (eval_hfexpr expr_363 (closed_363 v) (closed_363 v)).
Definition expr_364 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 293)) (@Eref VarOrder.T (@Eid VarOrder.T 328)) (@Eref VarOrder.T (@Eid VarOrder.T 363))).
Definition closed_364 (v : leaf_values) : VM.t hvalue := (VM.add 363 (Gval (Fuint 4) (word_363 v)) (VM.add 328 (Gval (Fuint 4) (word_328 v)) (VM.add 293 (Gval (Fuint 1) (word_293 v)) (VM.empty hvalue)))).
Definition word_364 (v : leaf_values) := word_of_eval (eval_hfexpr expr_364 (closed_364 v) (closed_364 v)).
Definition expr_365 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 293)) (@Eref VarOrder.T (@Eid VarOrder.T 364))).
Definition closed_365 (v : leaf_values) : VM.t hvalue := (VM.add 364 (Gval (Fuint 4) (word_364 v)) (VM.add 293 (Gval (Fuint 1) (word_293 v)) (VM.empty hvalue))).
Definition word_365 (v : leaf_values) := word_of_eval (eval_hfexpr expr_365 (closed_365 v) (closed_365 v)).
Definition expr_366 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 215)) (@Eref VarOrder.T (@Eid VarOrder.T 290)) (@Eref VarOrder.T (@Eid VarOrder.T 365))).
Definition closed_366 (v : leaf_values) : VM.t hvalue := (VM.add 365 (Gval (Fuint 5) (word_365 v)) (VM.add 290 (Gval (Fuint 5) (word_290 v)) (VM.add 215 (Gval (Fuint 1) (word_215 v)) (VM.empty hvalue)))).
Definition word_366 (v : leaf_values) := word_of_eval (eval_hfexpr expr_366 (closed_366 v) (closed_366 v)).
Definition expr_367 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 215)) (@Eref VarOrder.T (@Eid VarOrder.T 366))).
Definition closed_367 (v : leaf_values) : VM.t hvalue := (VM.add 366 (Gval (Fuint 5) (word_366 v)) (VM.add 215 (Gval (Fuint 1) (word_215 v)) (VM.empty hvalue))).
Definition word_367 (v : leaf_values) := word_of_eval (eval_hfexpr expr_367 (closed_367 v) (closed_367 v)).
Definition expr_368 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 212)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 367))).
Definition closed_368 (v : leaf_values) : VM.t hvalue := (VM.add 367 (Gval (Fuint 6) (word_367 v)) (VM.add 212 (Gval (Fuint 1) (word_212 v)) (VM.empty hvalue))).
Definition word_368 (v : leaf_values) := word_of_eval (eval_hfexpr expr_368 (closed_368 v) (closed_368 v)).
Definition expr_369 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 212)) (@Eref VarOrder.T (@Eid VarOrder.T 368))).
Definition closed_369 (v : leaf_values) : VM.t hvalue := (VM.add 368 (Gval (Fuint 6) (word_368 v)) (VM.add 212 (Gval (Fuint 1) (word_212 v)) (VM.empty hvalue))).
Definition word_369 (v : leaf_values) := word_of_eval (eval_hfexpr expr_369 (closed_369 v) (closed_369 v)).
Definition expr_370 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Eref VarOrder.T (@Eid VarOrder.T 209)) (@Eref VarOrder.T (@Eid VarOrder.T 369))).
Definition closed_370 (v : leaf_values) : VM.t hvalue := (VM.add 369 (Gval (Fuint 7) (word_369 v)) (VM.add 209 (Gval (Fuint 7) (word_209 v)) (VM.empty hvalue))).
Definition word_370 (v : leaf_values) := word_of_eval (eval_hfexpr expr_370 (closed_370 v) (closed_370 v)).
Definition expr_371 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 370))).
Definition closed_371 (v : leaf_values) : VM.t hvalue := (VM.add 370 (Gval (Fuint 8) (word_370 v)) (VM.empty hvalue)).
Definition word_371 (v : leaf_values) := word_of_eval (eval_hfexpr expr_371 (closed_371 v) (closed_371 v)).
Definition expr_372 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Bgeq) (@Eref VarOrder.T (@Eid VarOrder.T 371)) (@Econst VarOrder.T (Fuint 6) [::true; true; true; true; true; true])).
Definition closed_372 (v : leaf_values) : VM.t hvalue := (VM.add 371 (Gval (Fuint 7) (word_371 v)) (VM.empty hvalue)).
Definition word_372 (v : leaf_values) := word_of_eval (eval_hfexpr expr_372 (closed_372 v) (closed_372 v)).
Definition expr_373 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 372)) (@Econst VarOrder.T (Fuint 6) [::true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 371))).
Definition closed_373 (v : leaf_values) : VM.t hvalue := (VM.add 372 (Gval (Fuint 1) (word_372 v)) (VM.add 371 (Gval (Fuint 7) (word_371 v)) (VM.empty hvalue))).
Definition word_373 (v : leaf_values) := word_of_eval (eval_hfexpr expr_373 (closed_373 v) (closed_373 v)).
Definition expr_374 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 18)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 373))).
Definition closed_374 (v : leaf_values) : VM.t hvalue := (VM.add 373 (Gval (Fuint 7) (word_373 v)) (VM.add 18 (Gval (Fuint 1) (word_18 v)) (VM.empty hvalue))).
Definition word_374 (v : leaf_values) := word_of_eval (eval_hfexpr expr_374 (closed_374 v) (closed_374 v)).
Definition expr_375 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::false; true; false])).
Definition closed_375 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_375 (v : leaf_values) := word_of_eval (eval_hfexpr expr_375 (closed_375 v) (closed_375 v)).
Definition expr_376 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 43)) (@Eref VarOrder.T (@Eid VarOrder.T 51))).
Definition closed_376 (v : leaf_values) : VM.t hvalue := (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.add 43 (Gval (Fuint 65) (word_43 v)) (VM.empty hvalue))).
Definition word_376 (v : leaf_values) := word_of_eval (eval_hfexpr expr_376 (closed_376 v) (closed_376 v)).
Definition expr_377 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::true; true; false])).
Definition closed_377 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_377 (v : leaf_values) := word_of_eval (eval_hfexpr expr_377 (closed_377 v) (closed_377 v)).
Definition expr_378 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Bgeq) (@Eref VarOrder.T (@Eid VarOrder.T 21)) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_378 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.add 21 (Gval (Fuint 65) (word_21 v)) (VM.empty hvalue))).
Definition word_378 (v : leaf_values) := word_of_eval (eval_hfexpr expr_378 (closed_378 v) (closed_378 v)).
Definition expr_379 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Eref VarOrder.T (@Eid VarOrder.T 21)) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_379 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.add 21 (Gval (Fuint 65) (word_21 v)) (VM.empty hvalue))).
Definition word_379 (v : leaf_values) := word_of_eval (eval_hfexpr expr_379 (closed_379 v) (closed_379 v)).
Definition expr_380 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 379))).
Definition closed_380 (v : leaf_values) : VM.t hvalue := (VM.add 379 (Gval (Fuint 66) (word_379 v)) (VM.empty hvalue)).
Definition word_380 (v : leaf_values) := word_of_eval (eval_hfexpr expr_380 (closed_380 v) (closed_380 v)).
Definition expr_381 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 378)) (@Eref VarOrder.T (@Eid VarOrder.T 380)) (@Eref VarOrder.T (@Eid VarOrder.T 21))).
Definition closed_381 (v : leaf_values) : VM.t hvalue := (VM.add 380 (Gval (Fuint 65) (word_380 v)) (VM.add 378 (Gval (Fuint 1) (word_378 v)) (VM.add 21 (Gval (Fuint 65) (word_21 v)) (VM.empty hvalue)))).
Definition word_381 (v : leaf_values) := word_of_eval (eval_hfexpr expr_381 (closed_381 v) (closed_381 v)).
Definition expr_382 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 63 0) (@Eref VarOrder.T (@Eid VarOrder.T 381))).
Definition closed_382 (v : leaf_values) : VM.t hvalue := (VM.add 381 (Gval (Fuint 65) (word_381 v)) (VM.empty hvalue)).
Definition word_382 (v : leaf_values) := word_of_eval (eval_hfexpr expr_382 (closed_382 v) (closed_382 v)).
Definition expr_383 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 382)) (@Eref VarOrder.T (@Eid VarOrder.T 22))).
Definition closed_383 (v : leaf_values) : VM.t hvalue := (VM.add 382 (Gval (Fuint 64) (word_382 v)) (VM.add 22 (Gval (Fuint 64) (word_22 v)) (VM.empty hvalue))).
Definition word_383 (v : leaf_values) := word_of_eval (eval_hfexpr expr_383 (closed_383 v) (closed_383 v)).
Definition expr_384 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 383)) (@Eref VarOrder.T (@Eid VarOrder.T 378))).
Definition closed_384 (v : leaf_values) : VM.t hvalue := (VM.add 383 (Gval (Fuint 128) (word_383 v)) (VM.add 378 (Gval (Fuint 1) (word_378 v)) (VM.empty hvalue))).
Definition word_384 (v : leaf_values) := word_of_eval (eval_hfexpr expr_384 (closed_384 v) (closed_384 v)).
Definition expr_385 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Econst VarOrder.T (Fuint 6) [::true; true; true; true; true; true])).
Definition closed_385 (v : leaf_values) : VM.t hvalue := (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.empty hvalue)).
Definition word_385 (v : leaf_values) := word_of_eval (eval_hfexpr expr_385 (closed_385 v) (closed_385 v)).
Definition expr_386 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition closed_386 (v : leaf_values) : VM.t hvalue := (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.empty hvalue)).
Definition word_386 (v : leaf_values) := word_of_eval (eval_hfexpr expr_386 (closed_386 v) (closed_386 v)).
Definition expr_387 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 386))).
Definition closed_387 (v : leaf_values) : VM.t hvalue := (VM.add 386 (Gval (Fuint 7) (word_386 v)) (VM.empty hvalue)).
Definition word_387 (v : leaf_values) := word_of_eval (eval_hfexpr expr_387 (closed_387 v) (closed_387 v)).
Definition expr_388 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Econst VarOrder.T (Fuint 6) [::true; true; true; true; true; true])).
Definition closed_388 (v : leaf_values) : VM.t hvalue := (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.empty hvalue)).
Definition word_388 (v : leaf_values) := word_of_eval (eval_hfexpr expr_388 (closed_388 v) (closed_388 v)).
Definition expr_389 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 388)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 13))).
Definition closed_389 (v : leaf_values) : VM.t hvalue := (VM.add 388 (Gval (Fuint 1) (word_388 v)) (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue))).
Definition word_389 (v : leaf_values) := word_of_eval (eval_hfexpr expr_389 (closed_389 v) (closed_389 v)).
Definition expr_390 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition closed_390 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_390 (v : leaf_values) := word_of_eval (eval_hfexpr expr_390 (closed_390 v) (closed_390 v)).
Definition expr_391 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 13))).
Definition closed_391 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.add 7 (Gval (Fuint 1) (word_7 v)) (VM.empty hvalue))).
Definition word_391 (v : leaf_values) := word_of_eval (eval_hfexpr expr_391 (closed_391 v) (closed_391 v)).
Definition expr_392 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 390)) (@Eref VarOrder.T (@Eid VarOrder.T 391)) (@Eref VarOrder.T (@Eid VarOrder.T 13))).
Definition closed_392 (v : leaf_values) : VM.t hvalue := (VM.add 391 (Gval (Fuint 3) (word_391 v)) (VM.add 390 (Gval (Fuint 1) (word_390 v)) (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)))).
Definition word_392 (v : leaf_values) := word_of_eval (eval_hfexpr expr_392 (closed_392 v) (closed_392 v)).
Definition expr_393 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 377)) (@Eref VarOrder.T (@Eid VarOrder.T 384)) (@Eref VarOrder.T (@Eid VarOrder.T 20))).
Definition closed_393 (v : leaf_values) : VM.t hvalue := (VM.add 384 (Gval (Fuint 129) (word_384 v)) (VM.add 377 (Gval (Fuint 1) (word_377 v)) (VM.add 20 (Gval (Fuint 129) (word_20 v)) (VM.empty hvalue)))).
Definition word_393 (v : leaf_values) := word_of_eval (eval_hfexpr expr_393 (closed_393 v) (closed_393 v)).
Definition expr_394 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 377)) (@Eref VarOrder.T (@Eid VarOrder.T 387)) (@Eref VarOrder.T (@Eid VarOrder.T 51))).
Definition closed_394 (v : leaf_values) : VM.t hvalue := (VM.add 387 (Gval (Fuint 6) (word_387 v)) (VM.add 377 (Gval (Fuint 1) (word_377 v)) (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.empty hvalue)))).
Definition word_394 (v : leaf_values) := word_of_eval (eval_hfexpr expr_394 (closed_394 v) (closed_394 v)).
Definition expr_395 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 377)) (@Eref VarOrder.T (@Eid VarOrder.T 389)) (@Eref VarOrder.T (@Eid VarOrder.T 392))).
Definition closed_395 (v : leaf_values) : VM.t hvalue := (VM.add 392 (Gval (Fuint 3) (word_392 v)) (VM.add 389 (Gval (Fuint 3) (word_389 v)) (VM.add 377 (Gval (Fuint 1) (word_377 v)) (VM.empty hvalue)))).
Definition word_395 (v : leaf_values) := word_of_eval (eval_hfexpr expr_395 (closed_395 v) (closed_395 v)).
Definition expr_396 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 375)) (@Eref VarOrder.T (@Eid VarOrder.T 376)) (@Eref VarOrder.T (@Eid VarOrder.T 393))).
Definition closed_396 (v : leaf_values) : VM.t hvalue := (VM.add 393 (Gval (Fuint 129) (word_393 v)) (VM.add 376 (Gval (Fuint 128) (word_376 v)) (VM.add 375 (Gval (Fuint 1) (word_375 v)) (VM.empty hvalue)))).
Definition word_396 (v : leaf_values) := word_of_eval (eval_hfexpr expr_396 (closed_396 v) (closed_396 v)).
Definition expr_397 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 375)) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 395))).
Definition closed_397 (v : leaf_values) : VM.t hvalue := (VM.add 395 (Gval (Fuint 3) (word_395 v)) (VM.add 375 (Gval (Fuint 1) (word_375 v)) (VM.empty hvalue))).
Definition word_397 (v : leaf_values) := word_of_eval (eval_hfexpr expr_397 (closed_397 v) (closed_397 v)).
Definition expr_398 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 375)) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Eref VarOrder.T (@Eid VarOrder.T 394))).
Definition closed_398 (v : leaf_values) : VM.t hvalue := (VM.add 394 (Gval (Fuint 6) (word_394 v)) (VM.add 375 (Gval (Fuint 1) (word_375 v)) (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.empty hvalue)))).
Definition word_398 (v : leaf_values) := word_of_eval (eval_hfexpr expr_398 (closed_398 v) (closed_398 v)).
Definition expr_399 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 52)) (@Eref VarOrder.T (@Eid VarOrder.T 374)) (@Eref VarOrder.T (@Eid VarOrder.T 398))).
Definition closed_399 (v : leaf_values) : VM.t hvalue := (VM.add 398 (Gval (Fuint 6) (word_398 v)) (VM.add 374 (Gval (Fuint 7) (word_374 v)) (VM.add 52 (Gval (Fuint 1) (word_52 v)) (VM.empty hvalue)))).
Definition word_399 (v : leaf_values) := word_of_eval (eval_hfexpr expr_399 (closed_399 v) (closed_399 v)).
Definition expr_400 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 52)) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 397))).
Definition closed_400 (v : leaf_values) : VM.t hvalue := (VM.add 397 (Gval (Fuint 3) (word_397 v)) (VM.add 52 (Gval (Fuint 1) (word_52 v)) (VM.empty hvalue))).
Definition word_400 (v : leaf_values) := word_of_eval (eval_hfexpr expr_400 (closed_400 v) (closed_400 v)).
Definition expr_401 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 52)) (@Eref VarOrder.T (@Eid VarOrder.T 20)) (@Eref VarOrder.T (@Eid VarOrder.T 396))).
Definition closed_401 (v : leaf_values) : VM.t hvalue := (VM.add 396 (Gval (Fuint 129) (word_396 v)) (VM.add 52 (Gval (Fuint 1) (word_52 v)) (VM.add 20 (Gval (Fuint 129) (word_20 v)) (VM.empty hvalue)))).
Definition word_401 (v : leaf_values) := word_of_eval (eval_hfexpr expr_401 (closed_401 v) (closed_401 v)).
Definition expr_402 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 400))).
Definition closed_402 (v : leaf_values) : VM.t hvalue := (VM.add 400 (Gval (Fuint 3) (word_400 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue))).
Definition word_402 (v : leaf_values) := word_of_eval (eval_hfexpr expr_402 (closed_402 v) (closed_402 v)).
Definition expr_403 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Eref VarOrder.T (@Eid VarOrder.T 399))).
Definition closed_403 (v : leaf_values) : VM.t hvalue := (VM.add 399 (Gval (Fuint 7) (word_399 v)) (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)))).
Definition word_403 (v : leaf_values) := word_of_eval (eval_hfexpr expr_403 (closed_403 v) (closed_403 v)).
Definition expr_404 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 16)) (@Eref VarOrder.T (@Eid VarOrder.T 20)) (@Eref VarOrder.T (@Eid VarOrder.T 401))).
Definition closed_404 (v : leaf_values) : VM.t hvalue := (VM.add 401 (Gval (Fuint 129) (word_401 v)) (VM.add 20 (Gval (Fuint 129) (word_20 v)) (VM.add 16 (Gval (Fuint 1) (word_16 v)) (VM.empty hvalue)))).
Definition word_404 (v : leaf_values) := word_of_eval (eval_hfexpr expr_404 (closed_404 v) (closed_404 v)).
Definition expr_405 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 64 1) (@Eref VarOrder.T (@Eid VarOrder.T 21))).
Definition closed_405 (v : leaf_values) : VM.t hvalue := (VM.add 21 (Gval (Fuint 65) (word_21 v)) (VM.empty hvalue)).
Definition word_405 (v : leaf_values) := word_of_eval (eval_hfexpr expr_405 (closed_405 v) (closed_405 v)).
Definition expr_406 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 22))).
Definition closed_406 (v : leaf_values) : VM.t hvalue := (VM.add 22 (Gval (Fuint 64) (word_22 v)) (VM.empty hvalue)).
Definition word_406 (v : leaf_values) := word_of_eval (eval_hfexpr expr_406 (closed_406 v) (closed_406 v)).
Definition expr_407 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Definition closed_407 (v : leaf_values) : VM.t hvalue := (VM.add 406 (Gval (Fuint 65) (word_406 v)) (VM.empty hvalue)).
Definition word_407 (v : leaf_values) := word_of_eval (eval_hfexpr expr_407 (closed_407 v) (closed_407 v)).
Definition expr_408 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 38)) (@Eref VarOrder.T (@Eid VarOrder.T 407)) (@Eref VarOrder.T (@Eid VarOrder.T 22))).
Definition closed_408 (v : leaf_values) : VM.t hvalue := (VM.add 407 (Gval (Fuint 64) (word_407 v)) (VM.add 38 (Gval (Fuint 1) (word_38 v)) (VM.add 22 (Gval (Fuint 64) (word_22 v)) (VM.empty hvalue)))).
Definition word_408 (v : leaf_values) := word_of_eval (eval_hfexpr expr_408 (closed_408 v) (closed_408 v)).
Definition expr_409 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 405))).
Definition closed_409 (v : leaf_values) : VM.t hvalue := (VM.add 405 (Gval (Fuint 64) (word_405 v)) (VM.empty hvalue)).
Definition word_409 (v : leaf_values) := word_of_eval (eval_hfexpr expr_409 (closed_409 v) (closed_409 v)).
Definition expr_410 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 409))).
Definition closed_410 (v : leaf_values) : VM.t hvalue := (VM.add 409 (Gval (Fuint 65) (word_409 v)) (VM.empty hvalue)).
Definition word_410 (v : leaf_values) := word_of_eval (eval_hfexpr expr_410 (closed_410 v) (closed_410 v)).
Definition expr_411 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 33)) (@Eref VarOrder.T (@Eid VarOrder.T 410)) (@Eref VarOrder.T (@Eid VarOrder.T 405))).
Definition closed_411 (v : leaf_values) : VM.t hvalue := (VM.add 410 (Gval (Fuint 64) (word_410 v)) (VM.add 405 (Gval (Fuint 64) (word_405 v)) (VM.add 33 (Gval (Fuint 1) (word_33 v)) (VM.empty hvalue)))).
Definition word_411 (v : leaf_values) := word_of_eval (eval_hfexpr expr_411 (closed_411 v) (closed_411 v)).
Definition expr_412 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 47)) (@Eref VarOrder.T (@Eid VarOrder.T 411)) (@Eref VarOrder.T (@Eid VarOrder.T 408))).
Definition closed_412 (v : leaf_values) : VM.t hvalue := (VM.add 411 (Gval (Fuint 64) (word_411 v)) (VM.add 408 (Gval (Fuint 64) (word_408 v)) (VM.add 47 (Gval (Fuint 1) (word_47 v)) (VM.empty hvalue)))).
Definition word_412 (v : leaf_values) := word_of_eval (eval_hfexpr expr_412 (closed_412 v) (closed_412 v)).
Definition expr_413 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 412))).
Definition closed_413 (v : leaf_values) : VM.t hvalue := (VM.add 412 (Gval (Fuint 64) (word_412 v)) (VM.empty hvalue)).
Definition word_413 (v : leaf_values) := word_of_eval (eval_hfexpr expr_413 (closed_413 v) (closed_413 v)).
Definition expr_414 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 413))).
Definition closed_414 (v : leaf_values) : VM.t hvalue := (VM.add 413 (Gval (Fuint 32) (word_413 v)) (VM.empty hvalue)).
Definition word_414 (v : leaf_values) := word_of_eval (eval_hfexpr expr_414 (closed_414 v) (closed_414 v)).
Definition expr_415 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 414))).
Definition closed_415 (v : leaf_values) : VM.t hvalue := (VM.add 414 (Gval (Fuint 1) (word_414 v)) (VM.empty hvalue)).
Definition word_415 (v : leaf_values) := word_of_eval (eval_hfexpr expr_415 (closed_415 v) (closed_415 v)).
Definition expr_416 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 415)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition closed_416 (v : leaf_values) : VM.t hvalue := (VM.add 415 (Gval (Fuint 1) (word_415 v)) (VM.empty hvalue)).
Definition word_416 (v : leaf_values) := word_of_eval (eval_hfexpr expr_416 (closed_416 v) (closed_416 v)).
Definition expr_417 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 416)) (@Eref VarOrder.T (@Eid VarOrder.T 413))).
Definition closed_417 (v : leaf_values) : VM.t hvalue := (VM.add 416 (Gval (Fuint 32) (word_416 v)) (VM.add 413 (Gval (Fuint 32) (word_413 v)) (VM.empty hvalue))).
Definition word_417 (v : leaf_values) := word_of_eval (eval_hfexpr expr_417 (closed_417 v) (closed_417 v)).
Definition expr_418 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 46)) (@Eref VarOrder.T (@Eid VarOrder.T 417)) (@Eref VarOrder.T (@Eid VarOrder.T 412))).
Definition closed_418 (v : leaf_values) : VM.t hvalue := (VM.add 417 (Gval (Fuint 64) (word_417 v)) (VM.add 412 (Gval (Fuint 64) (word_412 v)) (VM.add 46 (Gval (Fuint 1) (word_46 v)) (VM.empty hvalue)))).
Definition word_418 (v : leaf_values) := word_of_eval (eval_hfexpr expr_418 (closed_418 v) (closed_418 v)).
Definition expr_419 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition closed_419 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_419 (v : leaf_values) := word_of_eval (eval_hfexpr expr_419 (closed_419 v) (closed_419 v)).
Definition expr_421 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 22)) (@Econst VarOrder.T (Fuint 64) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])).
Definition closed_421 (v : leaf_values) : VM.t hvalue := (VM.add 22 (Gval (Fuint 64) (word_22 v)) (VM.empty hvalue)).
Definition word_421 (v : leaf_values) := word_of_eval (eval_hfexpr expr_421 (closed_421 v) (closed_421 v)).
Definition expr_422 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_422 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_422 (v : leaf_values) := word_of_eval (eval_hfexpr expr_422 (closed_422 v) (closed_422 v)).
Definition expr_423 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 422)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_423 (v : leaf_values) : VM.t hvalue := (VM.add 422 (Gval (Fuint 1) (word_422 v)) (VM.empty hvalue)).
Definition word_423 (v : leaf_values) := word_of_eval (eval_hfexpr expr_423 (closed_423 v) (closed_423 v)).
Definition expr_424 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 421)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_424 (v : leaf_values) : VM.t hvalue := (VM.add 421 (Gval (Fuint 1) (word_421 v)) (VM.empty hvalue)).
Definition word_424 (v : leaf_values) := word_of_eval (eval_hfexpr expr_424 (closed_424 v) (closed_424 v)).
Definition expr_425 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 64 1) (@Eref VarOrder.T (@Eid VarOrder.T 43))).
Definition closed_425 (v : leaf_values) : VM.t hvalue := (VM.add 43 (Gval (Fuint 65) (word_43 v)) (VM.empty hvalue)).
Definition word_425 (v : leaf_values) := word_of_eval (eval_hfexpr expr_425 (closed_425 v) (closed_425 v)).
Definition expr_426 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 405)) (@Eref VarOrder.T (@Eid VarOrder.T 425))).
Definition closed_426 (v : leaf_values) : VM.t hvalue := (VM.add 425 (Gval (Fuint 64) (word_425 v)) (VM.add 405 (Gval (Fuint 64) (word_405 v)) (VM.empty hvalue))).
Definition word_426 (v : leaf_values) := word_of_eval (eval_hfexpr expr_426 (closed_426 v) (closed_426 v)).
Definition expr_427 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_427 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_427 (v : leaf_values) := word_of_eval (eval_hfexpr expr_427 (closed_427 v) (closed_427 v)).
Definition expr_428 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 427)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_428 (v : leaf_values) : VM.t hvalue := (VM.add 427 (Gval (Fuint 1) (word_427 v)) (VM.empty hvalue)).
Definition word_428 (v : leaf_values) := word_of_eval (eval_hfexpr expr_428 (closed_428 v) (closed_428 v)).
Definition expr_429 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 426)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_429 (v : leaf_values) : VM.t hvalue := (VM.add 426 (Gval (Fuint 1) (word_426 v)) (VM.empty hvalue)).
Definition word_429 (v : leaf_values) := word_of_eval (eval_hfexpr expr_429 (closed_429 v) (closed_429 v)).
Definition expr_430 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Bneq) (@Eref VarOrder.T (@Eid VarOrder.T 40)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_430 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.empty hvalue)).
Definition word_430 (v : leaf_values) := word_of_eval (eval_hfexpr expr_430 (closed_430 v) (closed_430 v)).
Definition expr_431 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_431 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_431 (v : leaf_values) := word_of_eval (eval_hfexpr expr_431 (closed_431 v) (closed_431 v)).
Definition expr_432 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 431)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_432 (v : leaf_values) : VM.t hvalue := (VM.add 431 (Gval (Fuint 1) (word_431 v)) (VM.empty hvalue)).
Definition word_432 (v : leaf_values) := word_of_eval (eval_hfexpr expr_432 (closed_432 v) (closed_432 v)).
Definition expr_433 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 430)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_433 (v : leaf_values) : VM.t hvalue := (VM.add 430 (Gval (Fuint 1) (word_430 v)) (VM.empty hvalue)).
Definition word_433 (v : leaf_values) := word_of_eval (eval_hfexpr expr_433 (closed_433 v) (closed_433 v)).
Definition expr_434 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bmul (@Eref VarOrder.T (@Eid VarOrder.T 22)) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_434 (v : leaf_values) : VM.t hvalue := (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.add 22 (Gval (Fuint 64) (word_22 v)) (VM.empty hvalue))).
Definition word_434 (v : leaf_values) := word_of_eval (eval_hfexpr expr_434 (closed_434 v) (closed_434 v)).
Definition expr_435 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 434)) (@Eref VarOrder.T (@Eid VarOrder.T 405))).
Definition closed_435 (v : leaf_values) : VM.t hvalue := (VM.add 434 (Gval (Fuint 128) (word_434 v)) (VM.add 405 (Gval (Fuint 64) (word_405 v)) (VM.empty hvalue))).
Definition word_435 (v : leaf_values) := word_of_eval (eval_hfexpr expr_435 (closed_435 v) (closed_435 v)).
Definition expr_436 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 64 1) (@Eref VarOrder.T (@Eid VarOrder.T 43))).
Definition closed_436 (v : leaf_values) : VM.t hvalue := (VM.add 43 (Gval (Fuint 65) (word_43 v)) (VM.empty hvalue)).
Definition word_436 (v : leaf_values) := word_of_eval (eval_hfexpr expr_436 (closed_436 v) (closed_436 v)).
Definition expr_437 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 435)) (@Eref VarOrder.T (@Eid VarOrder.T 436))).
Definition closed_437 (v : leaf_values) : VM.t hvalue := (VM.add 436 (Gval (Fuint 64) (word_436 v)) (VM.add 435 (Gval (Fuint 129) (word_435 v)) (VM.empty hvalue))).
Definition word_437 (v : leaf_values) := word_of_eval (eval_hfexpr expr_437 (closed_437 v) (closed_437 v)).
Definition expr_438 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_438 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_438 (v : leaf_values) := word_of_eval (eval_hfexpr expr_438 (closed_438 v) (closed_438 v)).
Definition expr_439 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 438)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_439 (v : leaf_values) : VM.t hvalue := (VM.add 438 (Gval (Fuint 1) (word_438 v)) (VM.empty hvalue)).
Definition word_439 (v : leaf_values) := word_of_eval (eval_hfexpr expr_439 (closed_439 v) (closed_439 v)).
Definition expr_440 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 437)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_440 (v : leaf_values) : VM.t hvalue := (VM.add 437 (Gval (Fuint 1) (word_437 v)) (VM.empty hvalue)).
Definition word_440 (v : leaf_values) := word_of_eval (eval_hfexpr expr_440 (closed_440 v) (closed_440 v)).
Definition expr_441 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Blt) (@Eref VarOrder.T (@Eid VarOrder.T 405)) (@Eref VarOrder.T (@Eid VarOrder.T 40))).
Definition closed_441 (v : leaf_values) : VM.t hvalue := (VM.add 405 (Gval (Fuint 64) (word_405 v)) (VM.add 40 (Gval (Fuint 64) (word_40 v)) (VM.empty hvalue))).
Definition word_441 (v : leaf_values) := word_of_eval (eval_hfexpr expr_441 (closed_441 v) (closed_441 v)).
Definition expr_442 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_442 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_442 (v : leaf_values) := word_of_eval (eval_hfexpr expr_442 (closed_442 v) (closed_442 v)).
Definition expr_443 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 442)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_443 (v : leaf_values) : VM.t hvalue := (VM.add 442 (Gval (Fuint 1) (word_442 v)) (VM.empty hvalue)).
Definition word_443 (v : leaf_values) := word_of_eval (eval_hfexpr expr_443 (closed_443 v) (closed_443 v)).
Definition expr_444 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 441)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_444 (v : leaf_values) : VM.t hvalue := (VM.add 441 (Gval (Fuint 1) (word_441 v)) (VM.empty hvalue)).
Definition word_444 (v : leaf_values) := word_of_eval (eval_hfexpr expr_444 (closed_444 v) (closed_444 v)).
Definition expr_448 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 446)) (@Econst VarOrder.T (Fuint 3) [::true; false; false])).
Definition closed_448 (v : leaf_values) : VM.t hvalue := (VM.add 446 (Gval (Fuint 3) (word_446 v)) (VM.empty hvalue)).
Definition word_448 (v : leaf_values) := word_of_eval (eval_hfexpr expr_448 (closed_448 v) (closed_448 v)).
Definition expr_449 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::false; true; false])).
Definition closed_449 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_449 (v : leaf_values) := word_of_eval (eval_hfexpr expr_449 (closed_449 v) (closed_449 v)).
Definition expr_450 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_450 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_450 (v : leaf_values) := word_of_eval (eval_hfexpr expr_450 (closed_450 v) (closed_450 v)).
Definition expr_451 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 450)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_451 (v : leaf_values) : VM.t hvalue := (VM.add 450 (Gval (Fuint 1) (word_450 v)) (VM.empty hvalue)).
Definition word_451 (v : leaf_values) := word_of_eval (eval_hfexpr expr_451 (closed_451 v) (closed_451 v)).
Definition expr_452 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 449)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_452 (v : leaf_values) : VM.t hvalue := (VM.add 449 (Gval (Fuint 1) (word_449 v)) (VM.empty hvalue)).
Definition word_452 (v : leaf_values) := word_of_eval (eval_hfexpr expr_452 (closed_452 v) (closed_452 v)).
Definition expr_453 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 446)) (@Econst VarOrder.T (Fuint 3) [::false; true; false])).
Definition closed_453 (v : leaf_values) : VM.t hvalue := (VM.add 446 (Gval (Fuint 3) (word_446 v)) (VM.empty hvalue)).
Definition word_453 (v : leaf_values) := word_of_eval (eval_hfexpr expr_453 (closed_453 v) (closed_453 v)).
Definition expr_454 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Econst VarOrder.T (Fuint 3) [::true; true; false])).
Definition closed_454 (v : leaf_values) : VM.t hvalue := (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue)).
Definition word_454 (v : leaf_values) := word_of_eval (eval_hfexpr expr_454 (closed_454 v) (closed_454 v)).
Definition expr_455 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_455 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_455 (v : leaf_values) := word_of_eval (eval_hfexpr expr_455 (closed_455 v) (closed_455 v)).
Definition expr_456 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 455)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_456 (v : leaf_values) : VM.t hvalue := (VM.add 455 (Gval (Fuint 1) (word_455 v)) (VM.empty hvalue)).
Definition word_456 (v : leaf_values) := word_of_eval (eval_hfexpr expr_456 (closed_456 v) (closed_456 v)).
Definition expr_457 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 454)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_457 (v : leaf_values) : VM.t hvalue := (VM.add 454 (Gval (Fuint 1) (word_454 v)) (VM.empty hvalue)).
Definition word_457 (v : leaf_values) := word_of_eval (eval_hfexpr expr_457 (closed_457 v) (closed_457 v)).
Definition expr_458 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 446)) (@Econst VarOrder.T (Fuint 3) [::true; true; false])).
Definition closed_458 (v : leaf_values) : VM.t hvalue := (VM.add 446 (Gval (Fuint 3) (word_446 v)) (VM.empty hvalue)).
Definition word_458 (v : leaf_values) := word_of_eval (eval_hfexpr expr_458 (closed_458 v) (closed_458 v)).
Definition expr_459 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Econst VarOrder.T (Fuint 6) [::true; true; true; true; true; true])).
Definition closed_459 (v : leaf_values) : VM.t hvalue := (VM.add 447 (Gval (Fuint 6) (word_447 v)) (VM.empty hvalue)).
Definition word_459 (v : leaf_values) := word_of_eval (eval_hfexpr expr_459 (closed_459 v) (closed_459 v)).
Definition expr_460 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 459)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Econst VarOrder.T (Fuint 3) [::true; true; false])).
Definition closed_460 (v : leaf_values) : VM.t hvalue := (VM.add 459 (Gval (Fuint 1) (word_459 v)) (VM.empty hvalue)).
Definition word_460 (v : leaf_values) := word_of_eval (eval_hfexpr expr_460 (closed_460 v) (closed_460 v)).
Definition expr_461 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 13)) (@Eref VarOrder.T (@Eid VarOrder.T 460))).
Definition closed_461 (v : leaf_values) : VM.t hvalue := (VM.add 460 (Gval (Fuint 3) (word_460 v)) (VM.add 13 (Gval (Fuint 3) (word_13 v)) (VM.empty hvalue))).
Definition word_461 (v : leaf_values) := word_of_eval (eval_hfexpr expr_461 (closed_461 v) (closed_461 v)).
Definition expr_462 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_462 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_462 (v : leaf_values) := word_of_eval (eval_hfexpr expr_462 (closed_462 v) (closed_462 v)).
Definition expr_463 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 462)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_463 (v : leaf_values) : VM.t hvalue := (VM.add 462 (Gval (Fuint 1) (word_462 v)) (VM.empty hvalue)).
Definition word_463 (v : leaf_values) := word_of_eval (eval_hfexpr expr_463 (closed_463 v) (closed_463 v)).
Definition expr_464 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 461)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_464 (v : leaf_values) : VM.t hvalue := (VM.add 461 (Gval (Fuint 1) (word_461 v)) (VM.empty hvalue)).
Definition word_464 (v : leaf_values) := word_of_eval (eval_hfexpr expr_464 (closed_464 v) (closed_464 v)).
Definition expr_465 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Econst VarOrder.T (Fuint 6) [::true; true; true; true; true; true])).
Definition closed_465 (v : leaf_values) : VM.t hvalue := (VM.add 447 (Gval (Fuint 6) (word_447 v)) (VM.empty hvalue)).
Definition word_465 (v : leaf_values) := word_of_eval (eval_hfexpr expr_465 (closed_465 v) (closed_465 v)).
Definition expr_466 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition closed_466 (v : leaf_values) : VM.t hvalue := (VM.add 447 (Gval (Fuint 6) (word_447 v)) (VM.empty hvalue)).
Definition word_466 (v : leaf_values) := word_of_eval (eval_hfexpr expr_466 (closed_466 v) (closed_466 v)).
Definition expr_467 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 466))).
Definition closed_467 (v : leaf_values) : VM.t hvalue := (VM.add 466 (Gval (Fuint 7) (word_466 v)) (VM.empty hvalue)).
Definition word_467 (v : leaf_values) := word_of_eval (eval_hfexpr expr_467 (closed_467 v) (closed_467 v)).
Definition expr_468 : @hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 465)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 467))).
Definition closed_468 (v : leaf_values) : VM.t hvalue := (VM.add 467 (Gval (Fuint 6) (word_467 v)) (VM.add 465 (Gval (Fuint 1) (word_465 v)) (VM.empty hvalue))).
Definition word_468 (v : leaf_values) := word_of_eval (eval_hfexpr expr_468 (closed_468 v) (closed_468 v)).
Definition expr_469 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 51)) (@Eref VarOrder.T (@Eid VarOrder.T 468))).
Definition closed_469 (v : leaf_values) : VM.t hvalue := (VM.add 468 (Gval (Fuint 6) (word_468 v)) (VM.add 51 (Gval (Fuint 6) (word_51 v)) (VM.empty hvalue))).
Definition word_469 (v : leaf_values) := word_of_eval (eval_hfexpr expr_469 (closed_469 v) (closed_469 v)).
Definition expr_470 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_470 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_470 (v : leaf_values) := word_of_eval (eval_hfexpr expr_470 (closed_470 v) (closed_470 v)).
Definition expr_471 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 470)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_471 (v : leaf_values) : VM.t hvalue := (VM.add 470 (Gval (Fuint 1) (word_470 v)) (VM.empty hvalue)).
Definition word_471 (v : leaf_values) := word_of_eval (eval_hfexpr expr_471 (closed_471 v) (closed_471 v)).
Definition expr_472 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 469)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_472 (v : leaf_values) : VM.t hvalue := (VM.add 469 (Gval (Fuint 1) (word_469 v)) (VM.empty hvalue)).
Definition word_472 (v : leaf_values) := word_of_eval (eval_hfexpr expr_472 (closed_472 v) (closed_472 v)).
Definition expr_473 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_473 (v : leaf_values) : VM.t hvalue := (VM.add 7 (Gval (Fuint 1) (word_7 v)) (VM.empty hvalue)).
Definition word_473 (v : leaf_values) := word_of_eval (eval_hfexpr expr_473 (closed_473 v) (closed_473 v)).
Definition expr_8 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 419)).
Definition closed_8 (v : leaf_values) : VM.t hvalue := (VM.add 419 (Gval (Fuint 1) (word_419 v)) (VM.empty hvalue)).
Definition word_8 (v : leaf_values) := word_of_eval (eval_hfexpr expr_8 (closed_8 v) (closed_8 v)).
Definition expr_474 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 8)) (@Eref VarOrder.T (@Eid VarOrder.T 473))).
Definition closed_474 (v : leaf_values) : VM.t hvalue := (VM.add 473 (Gval (Fuint 1) (word_473 v)) (VM.add 8 (Gval (Fuint 1) (word_8 v)) (VM.empty hvalue))).
Definition word_474 (v : leaf_values) := word_of_eval (eval_hfexpr expr_474 (closed_474 v) (closed_474 v)).
Definition expr_477 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_477 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_477 (v : leaf_values) := word_of_eval (eval_hfexpr expr_477 (closed_477 v) (closed_477 v)).
Definition expr_478 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 477)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_478 (v : leaf_values) : VM.t hvalue := (VM.add 477 (Gval (Fuint 1) (word_477 v)) (VM.empty hvalue)).
Definition word_478 (v : leaf_values) := word_of_eval (eval_hfexpr expr_478 (closed_478 v) (closed_478 v)).
Definition expr_479 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 8)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_479 (v : leaf_values) : VM.t hvalue := (VM.add 8 (Gval (Fuint 1) (word_8 v)) (VM.empty hvalue)).
Definition word_479 (v : leaf_values) := word_of_eval (eval_hfexpr expr_479 (closed_479 v) (closed_479 v)).
Definition expr_9 : @hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 418)).
Definition closed_9 (v : leaf_values) : VM.t hvalue := (VM.add 418 (Gval (Fuint 64) (word_418 v)) (VM.empty hvalue)).
Definition word_9 (v : leaf_values) := word_of_eval (eval_hfexpr expr_9 (closed_9 v) (closed_9 v)).
Definition expr_480 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 9)) (@Eref VarOrder.T (@Eid VarOrder.T 476))).
Definition closed_480 (v : leaf_values) : VM.t hvalue := (VM.add 476 (Gval (Fuint 64) (word_476 v)) (VM.add 9 (Gval (Fuint 64) (word_9 v)) (VM.empty hvalue))).
Definition word_480 (v : leaf_values) := word_of_eval (eval_hfexpr expr_480 (closed_480 v) (closed_480 v)).
Definition expr_481 : @hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Definition closed_481 (v : leaf_values) : VM.t hvalue := (VM.add 1 (Gval (Fuint 1) (word_1 v)) (VM.empty hvalue)).
Definition word_481 (v : leaf_values) := word_of_eval (eval_hfexpr expr_481 (closed_481 v) (closed_481 v)).
Definition expr_482 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 481)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_482 (v : leaf_values) : VM.t hvalue := (VM.add 481 (Gval (Fuint 1) (word_481 v)) (VM.empty hvalue)).
Definition word_482 (v : leaf_values) := word_of_eval (eval_hfexpr expr_482 (closed_482 v) (closed_482 v)).
Definition expr_483 : @hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition closed_483 (v : leaf_values) : VM.t hvalue := (VM.add 480 (Gval (Fuint 1) (word_480 v)) (VM.empty hvalue)).
Definition word_483 (v : leaf_values) := word_of_eval (eval_hfexpr expr_483 (closed_483 v) (closed_483 v)).
Opaque word_0 word_1 word_2 word_3 word_4 word_5 word_6 word_7 word_8 word_9 word_10 word_11 word_12 word_13 word_14 word_15 word_16 word_17 word_18 word_19 word_20 word_21 word_22 word_23 word_24 word_25 word_26 word_27 word_28 word_29 word_30 word_31 word_32 word_33 word_34 word_35 word_36 word_37 word_38 word_39 word_40 word_41 word_42 word_43 word_44 word_45 word_46 word_47 word_48 word_49 word_50 word_51 word_52 word_53 word_54 word_55 word_56 word_57 word_58 word_59 word_60 word_61 word_62 word_63 word_64 word_65 word_66 word_67 word_68 word_69 word_70 word_71 word_72 word_73 word_74 word_75 word_76 word_77 word_78 word_79 word_80 word_81 word_82 word_83 word_84 word_85 word_86 word_87 word_88 word_89 word_90 word_91 word_92 word_93 word_94 word_95 word_96 word_97 word_98 word_99 word_100 word_101 word_102 word_103 word_104 word_105 word_106 word_107 word_108 word_109 word_110 word_111 word_112 word_113 word_114 word_115 word_116 word_117 word_118 word_119 word_120 word_121 word_122 word_123 word_124 word_125 word_126 word_127 word_128 word_129 word_130 word_131 word_132 word_133 word_134 word_135 word_136 word_137 word_138 word_139 word_140 word_141 word_142 word_143 word_144 word_145 word_146 word_147 word_148 word_149 word_150 word_151 word_152 word_153 word_154 word_155 word_156 word_157 word_158 word_159 word_160 word_161 word_162 word_163 word_164 word_165 word_166 word_167 word_168 word_169 word_170 word_171 word_172 word_173 word_174 word_175 word_176 word_177 word_178 word_179 word_180 word_181 word_182 word_183 word_184 word_185 word_186 word_187 word_188 word_189 word_190 word_191 word_192 word_193 word_194 word_195 word_196 word_197 word_198 word_199 word_200 word_201 word_202 word_203 word_204 word_205 word_206 word_207 word_208 word_209 word_210 word_211 word_212 word_213 word_214 word_215 word_216 word_217 word_218 word_219 word_220 word_221 word_222 word_223 word_224 word_225 word_226 word_227 word_228 word_229 word_230 word_231 word_232 word_233 word_234 word_235 word_236 word_237 word_238 word_239 word_240 word_241 word_242 word_243 word_244 word_245 word_246 word_247 word_248 word_249 word_250 word_251 word_252 word_253 word_254 word_255 word_256 word_257 word_258 word_259 word_260 word_261 word_262 word_263 word_264 word_265 word_266 word_267 word_268 word_269 word_270 word_271 word_272 word_273 word_274 word_275 word_276 word_277 word_278 word_279 word_280 word_281 word_282 word_283 word_284 word_285 word_286 word_287 word_288 word_289 word_290 word_291 word_292 word_293 word_294 word_295 word_296 word_297 word_298 word_299 word_300 word_301 word_302 word_303 word_304 word_305 word_306 word_307 word_308 word_309 word_310 word_311 word_312 word_313 word_314 word_315 word_316 word_317 word_318 word_319 word_320 word_321 word_322 word_323 word_324 word_325 word_326 word_327 word_328 word_329 word_330 word_331 word_332 word_333 word_334 word_335 word_336 word_337 word_338 word_339 word_340 word_341 word_342 word_343 word_344 word_345 word_346 word_347 word_348 word_349 word_350 word_351 word_352 word_353 word_354 word_355 word_356 word_357 word_358 word_359 word_360 word_361 word_362 word_363 word_364 word_365 word_366 word_367 word_368 word_369 word_370 word_371 word_372 word_373 word_374 word_375 word_376 word_377 word_378 word_379 word_380 word_381 word_382 word_383 word_384 word_385 word_386 word_387 word_388 word_389 word_390 word_391 word_392 word_393 word_394 word_395 word_396 word_397 word_398 word_399 word_400 word_401 word_402 word_403 word_404 word_405 word_406 word_407 word_408 word_409 word_410 word_411 word_412 word_413 word_414 word_415 word_416 word_417 word_418 word_419 word_420 word_421 word_422 word_423 word_424 word_425 word_426 word_427 word_428 word_429 word_430 word_431 word_432 word_433 word_434 word_435 word_436 word_437 word_438 word_439 word_440 word_441 word_442 word_443 word_444 word_445 word_446 word_447 word_448 word_449 word_450 word_451 word_452 word_453 word_454 word_455 word_456 word_457 word_458 word_459 word_460 word_461 word_462 word_463 word_464 word_465 word_466 word_467 word_468 word_469 word_470 word_471 word_472 word_473 word_474 word_475 word_476 word_477 word_478 word_479 word_480 word_481 word_482 word_483.
Definition stable_shape (values : N -> hvalue) : VM.t hvalue := Eval vm_compute in
  (VM.add 483 (values 483) (VM.add 482 (values 482) (VM.add 481 (values 481) (VM.add 480 (values 480) (VM.add 479 (values 479) (VM.add 478 (values 478) (VM.add 477 (values 477) (VM.add 476 (values 476) (VM.add 475 (values 475) (VM.add 474 (values 474) (VM.add 473 (values 473) (VM.add 472 (values 472) (VM.add 471 (values 471) (VM.add 470 (values 470) (VM.add 469 (values 469) (VM.add 468 (values 468) (VM.add 467 (values 467) (VM.add 466 (values 466) (VM.add 465 (values 465) (VM.add 464 (values 464) (VM.add 463 (values 463) (VM.add 462 (values 462) (VM.add 461 (values 461) (VM.add 460 (values 460) (VM.add 459 (values 459) (VM.add 458 (values 458) (VM.add 457 (values 457) (VM.add 456 (values 456) (VM.add 455 (values 455) (VM.add 454 (values 454) (VM.add 453 (values 453) (VM.add 452 (values 452) (VM.add 451 (values 451) (VM.add 450 (values 450) (VM.add 449 (values 449) (VM.add 448 (values 448) (VM.add 447 (values 447) (VM.add 446 (values 446) (VM.add 445 (values 445) (VM.add 444 (values 444) (VM.add 443 (values 443) (VM.add 442 (values 442) (VM.add 441 (values 441) (VM.add 440 (values 440) (VM.add 439 (values 439) (VM.add 438 (values 438) (VM.add 437 (values 437) (VM.add 436 (values 436) (VM.add 435 (values 435) (VM.add 434 (values 434) (VM.add 433 (values 433) (VM.add 432 (values 432) (VM.add 431 (values 431) (VM.add 430 (values 430) (VM.add 429 (values 429) (VM.add 428 (values 428) (VM.add 427 (values 427) (VM.add 426 (values 426) (VM.add 425 (values 425) (VM.add 424 (values 424) (VM.add 423 (values 423) (VM.add 422 (values 422) (VM.add 421 (values 421) (VM.add 420 (values 420) (VM.add 419 (values 419) (VM.add 418 (values 418) (VM.add 417 (values 417) (VM.add 416 (values 416) (VM.add 415 (values 415) (VM.add 414 (values 414) (VM.add 413 (values 413) (VM.add 412 (values 412) (VM.add 411 (values 411) (VM.add 410 (values 410) (VM.add 409 (values 409) (VM.add 408 (values 408) (VM.add 407 (values 407) (VM.add 406 (values 406) (VM.add 405 (values 405) (VM.add 404 (values 404) (VM.add 403 (values 403) (VM.add 402 (values 402) (VM.add 401 (values 401) (VM.add 400 (values 400) (VM.add 399 (values 399) (VM.add 398 (values 398) (VM.add 397 (values 397) (VM.add 396 (values 396) (VM.add 395 (values 395) (VM.add 394 (values 394) (VM.add 393 (values 393) (VM.add 392 (values 392) (VM.add 391 (values 391) (VM.add 390 (values 390) (VM.add 389 (values 389) (VM.add 388 (values 388) (VM.add 387 (values 387) (VM.add 386 (values 386) (VM.add 385 (values 385) (VM.add 384 (values 384) (VM.add 383 (values 383) (VM.add 382 (values 382) (VM.add 381 (values 381) (VM.add 380 (values 380) (VM.add 379 (values 379) (VM.add 378 (values 378) (VM.add 377 (values 377) (VM.add 376 (values 376) (VM.add 375 (values 375) (VM.add 374 (values 374) (VM.add 373 (values 373) (VM.add 372 (values 372) (VM.add 371 (values 371) (VM.add 370 (values 370) (VM.add 369 (values 369) (VM.add 368 (values 368) (VM.add 367 (values 367) (VM.add 366 (values 366) (VM.add 365 (values 365) (VM.add 364 (values 364) (VM.add 363 (values 363) (VM.add 362 (values 362) (VM.add 361 (values 361) (VM.add 360 (values 360) (VM.add 359 (values 359) (VM.add 358 (values 358) (VM.add 357 (values 357) (VM.add 356 (values 356) (VM.add 355 (values 355) (VM.add 354 (values 354) (VM.add 353 (values 353) (VM.add 352 (values 352) (VM.add 351 (values 351) (VM.add 350 (values 350) (VM.add 349 (values 349) (VM.add 348 (values 348) (VM.add 347 (values 347) (VM.add 346 (values 346) (VM.add 345 (values 345) (VM.add 344 (values 344) (VM.add 343 (values 343) (VM.add 342 (values 342) (VM.add 341 (values 341) (VM.add 340 (values 340) (VM.add 339 (values 339) (VM.add 338 (values 338) (VM.add 337 (values 337) (VM.add 336 (values 336) (VM.add 335 (values 335) (VM.add 334 (values 334) (VM.add 333 (values 333) (VM.add 332 (values 332) (VM.add 331 (values 331) (VM.add 330 (values 330) (VM.add 329 (values 329) (VM.add 328 (values 328) (VM.add 327 (values 327) (VM.add 326 (values 326) (VM.add 325 (values 325) (VM.add 324 (values 324) (VM.add 323 (values 323) (VM.add 322 (values 322) (VM.add 321 (values 321) (VM.add 320 (values 320) (VM.add 319 (values 319) (VM.add 318 (values 318) (VM.add 317 (values 317) (VM.add 316 (values 316) (VM.add 315 (values 315) (VM.add 314 (values 314) (VM.add 313 (values 313) (VM.add 312 (values 312) (VM.add 311 (values 311) (VM.add 310 (values 310) (VM.add 309 (values 309) (VM.add 308 (values 308) (VM.add 307 (values 307) (VM.add 306 (values 306) (VM.add 305 (values 305) (VM.add 304 (values 304) (VM.add 303 (values 303) (VM.add 302 (values 302) (VM.add 301 (values 301) (VM.add 300 (values 300) (VM.add 299 (values 299) (VM.add 298 (values 298) (VM.add 297 (values 297) (VM.add 296 (values 296) (VM.add 295 (values 295) (VM.add 294 (values 294) (VM.add 293 (values 293) (VM.add 292 (values 292) (VM.add 291 (values 291) (VM.add 290 (values 290) (VM.add 289 (values 289) (VM.add 288 (values 288) (VM.add 287 (values 287) (VM.add 286 (values 286) (VM.add 285 (values 285) (VM.add 284 (values 284) (VM.add 283 (values 283) (VM.add 282 (values 282) (VM.add 281 (values 281) (VM.add 280 (values 280) (VM.add 279 (values 279) (VM.add 278 (values 278) (VM.add 277 (values 277) (VM.add 276 (values 276) (VM.add 275 (values 275) (VM.add 274 (values 274) (VM.add 273 (values 273) (VM.add 272 (values 272) (VM.add 271 (values 271) (VM.add 270 (values 270) (VM.add 269 (values 269) (VM.add 268 (values 268) (VM.add 267 (values 267) (VM.add 266 (values 266) (VM.add 265 (values 265) (VM.add 264 (values 264) (VM.add 263 (values 263) (VM.add 262 (values 262) (VM.add 261 (values 261) (VM.add 260 (values 260) (VM.add 259 (values 259) (VM.add 258 (values 258) (VM.add 257 (values 257) (VM.add 256 (values 256) (VM.add 255 (values 255) (VM.add 254 (values 254) (VM.add 253 (values 253) (VM.add 252 (values 252) (VM.add 251 (values 251) (VM.add 250 (values 250) (VM.add 249 (values 249) (VM.add 248 (values 248) (VM.add 247 (values 247) (VM.add 246 (values 246) (VM.add 245 (values 245) (VM.add 244 (values 244) (VM.add 243 (values 243) (VM.add 242 (values 242) (VM.add 241 (values 241) (VM.add 240 (values 240) (VM.add 239 (values 239) (VM.add 238 (values 238) (VM.add 237 (values 237) (VM.add 236 (values 236) (VM.add 235 (values 235) (VM.add 234 (values 234) (VM.add 233 (values 233) (VM.add 232 (values 232) (VM.add 231 (values 231) (VM.add 230 (values 230) (VM.add 229 (values 229) (VM.add 228 (values 228) (VM.add 227 (values 227) (VM.add 226 (values 226) (VM.add 225 (values 225) (VM.add 224 (values 224) (VM.add 223 (values 223) (VM.add 222 (values 222) (VM.add 221 (values 221) (VM.add 220 (values 220) (VM.add 219 (values 219) (VM.add 218 (values 218) (VM.add 217 (values 217) (VM.add 216 (values 216) (VM.add 215 (values 215) (VM.add 214 (values 214) (VM.add 213 (values 213) (VM.add 212 (values 212) (VM.add 211 (values 211) (VM.add 210 (values 210) (VM.add 209 (values 209) (VM.add 208 (values 208) (VM.add 207 (values 207) (VM.add 206 (values 206) (VM.add 205 (values 205) (VM.add 204 (values 204) (VM.add 203 (values 203) (VM.add 202 (values 202) (VM.add 201 (values 201) (VM.add 200 (values 200) (VM.add 199 (values 199) (VM.add 198 (values 198) (VM.add 197 (values 197) (VM.add 196 (values 196) (VM.add 195 (values 195) (VM.add 194 (values 194) (VM.add 193 (values 193) (VM.add 192 (values 192) (VM.add 191 (values 191) (VM.add 190 (values 190) (VM.add 189 (values 189) (VM.add 188 (values 188) (VM.add 187 (values 187) (VM.add 186 (values 186) (VM.add 185 (values 185) (VM.add 184 (values 184) (VM.add 183 (values 183) (VM.add 182 (values 182) (VM.add 181 (values 181) (VM.add 180 (values 180) (VM.add 179 (values 179) (VM.add 178 (values 178) (VM.add 177 (values 177) (VM.add 176 (values 176) (VM.add 175 (values 175) (VM.add 174 (values 174) (VM.add 173 (values 173) (VM.add 172 (values 172) (VM.add 171 (values 171) (VM.add 170 (values 170) (VM.add 169 (values 169) (VM.add 168 (values 168) (VM.add 167 (values 167) (VM.add 166 (values 166) (VM.add 165 (values 165) (VM.add 164 (values 164) (VM.add 163 (values 163) (VM.add 162 (values 162) (VM.add 161 (values 161) (VM.add 160 (values 160) (VM.add 159 (values 159) (VM.add 158 (values 158) (VM.add 157 (values 157) (VM.add 156 (values 156) (VM.add 155 (values 155) (VM.add 154 (values 154) (VM.add 153 (values 153) (VM.add 152 (values 152) (VM.add 151 (values 151) (VM.add 150 (values 150) (VM.add 149 (values 149) (VM.add 148 (values 148) (VM.add 147 (values 147) (VM.add 146 (values 146) (VM.add 145 (values 145) (VM.add 144 (values 144) (VM.add 143 (values 143) (VM.add 142 (values 142) (VM.add 141 (values 141) (VM.add 140 (values 140) (VM.add 139 (values 139) (VM.add 138 (values 138) (VM.add 137 (values 137) (VM.add 136 (values 136) (VM.add 135 (values 135) (VM.add 134 (values 134) (VM.add 133 (values 133) (VM.add 132 (values 132) (VM.add 131 (values 131) (VM.add 130 (values 130) (VM.add 129 (values 129) (VM.add 128 (values 128) (VM.add 127 (values 127) (VM.add 126 (values 126) (VM.add 125 (values 125) (VM.add 124 (values 124) (VM.add 123 (values 123) (VM.add 122 (values 122) (VM.add 121 (values 121) (VM.add 120 (values 120) (VM.add 119 (values 119) (VM.add 118 (values 118) (VM.add 117 (values 117) (VM.add 116 (values 116) (VM.add 115 (values 115) (VM.add 114 (values 114) (VM.add 113 (values 113) (VM.add 112 (values 112) (VM.add 111 (values 111) (VM.add 110 (values 110) (VM.add 109 (values 109) (VM.add 108 (values 108) (VM.add 107 (values 107) (VM.add 106 (values 106) (VM.add 105 (values 105) (VM.add 104 (values 104) (VM.add 103 (values 103) (VM.add 102 (values 102) (VM.add 101 (values 101) (VM.add 100 (values 100) (VM.add 99 (values 99) (VM.add 98 (values 98) (VM.add 97 (values 97) (VM.add 96 (values 96) (VM.add 95 (values 95) (VM.add 94 (values 94) (VM.add 93 (values 93) (VM.add 92 (values 92) (VM.add 91 (values 91) (VM.add 90 (values 90) (VM.add 89 (values 89) (VM.add 88 (values 88) (VM.add 87 (values 87) (VM.add 86 (values 86) (VM.add 85 (values 85) (VM.add 84 (values 84) (VM.add 83 (values 83) (VM.add 82 (values 82) (VM.add 81 (values 81) (VM.add 80 (values 80) (VM.add 79 (values 79) (VM.add 78 (values 78) (VM.add 77 (values 77) (VM.add 76 (values 76) (VM.add 75 (values 75) (VM.add 74 (values 74) (VM.add 73 (values 73) (VM.add 72 (values 72) (VM.add 71 (values 71) (VM.add 70 (values 70) (VM.add 69 (values 69) (VM.add 68 (values 68) (VM.add 67 (values 67) (VM.add 66 (values 66) (VM.add 65 (values 65) (VM.add 64 (values 64) (VM.add 63 (values 63) (VM.add 62 (values 62) (VM.add 61 (values 61) (VM.add 60 (values 60) (VM.add 59 (values 59) (VM.add 58 (values 58) (VM.add 57 (values 57) (VM.add 56 (values 56) (VM.add 55 (values 55) (VM.add 54 (values 54) (VM.add 53 (values 53) (VM.add 52 (values 52) (VM.add 51 (values 51) (VM.add 50 (values 50) (VM.add 49 (values 49) (VM.add 48 (values 48) (VM.add 47 (values 47) (VM.add 46 (values 46) (VM.add 45 (values 45) (VM.add 44 (values 44) (VM.add 43 (values 43) (VM.add 42 (values 42) (VM.add 41 (values 41) (VM.add 40 (values 40) (VM.add 39 (values 39) (VM.add 38 (values 38) (VM.add 37 (values 37) (VM.add 36 (values 36) (VM.add 35 (values 35) (VM.add 34 (values 34) (VM.add 33 (values 33) (VM.add 32 (values 32) (VM.add 31 (values 31) (VM.add 30 (values 30) (VM.add 29 (values 29) (VM.add 28 (values 28) (VM.add 27 (values 27) (VM.add 26 (values 26) (VM.add 25 (values 25) (VM.add 24 (values 24) (VM.add 23 (values 23) (VM.add 22 (values 22) (VM.add 21 (values 21) (VM.add 20 (values 20) (VM.add 19 (values 19) (VM.add 18 (values 18) (VM.add 17 (values 17) (VM.add 16 (values 16) (VM.add 15 (values 15) (VM.add 14 (values 14) (VM.add 13 (values 13) (VM.add 12 (values 12) (VM.add 11 (values 11) (VM.add 10 (values 10) (VM.add 9 (values 9) (VM.add 8 (values 8) (VM.add 7 (values 7) (VM.add 6 (values 6) (VM.add 5 (values 5) (VM.add 4 (values 4) (VM.add 3 (values 3) (VM.add 2 (values 2) (VM.add 1 (values 1) (VM.add 0 (values 0) (VM.empty hvalue))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition stable_values (v : leaf_values) (id : N) : hvalue := match id with
| 0 => Gval Fclock (word_0 v)
| 1 => Gval (Fuint 1) (word_1 v)
| 2 => Gval (Fuint 1) (word_2 v)
| 3 => Gval (Fuint 1) (word_3 v)
| 4 => Gval (Fuint 64) (word_4 v)
| 5 => Gval (Fuint 64) (word_5 v)
| 6 => Gval (Fuint 64) (word_6 v)
| 7 => Gval (Fuint 1) (word_7 v)
| 8 => Gval (Fuint 1) (word_8 v)
| 9 => Gval (Fuint 64) (word_9 v)
| 10 => Gval (Fuint 1) (word_10 v)
| 11 => Gval (Fuint 1) (word_11 v)
| 12 => Gval (Fuint 1) (word_12 v)
| 13 => Gval (Fuint 3) (word_13 v)
| 14 => Gval (Fuint 1) (word_14 v)
| 15 => Gval (Fuint 1) (word_15 v)
| 16 => Gval (Fuint 1) (word_16 v)
| 17 => Gval (Fuint 1) (word_17 v)
| 18 => Gval (Fuint 1) (word_18 v)
| 19 => Gval (Fuint 1) (word_19 v)
| 20 => Gval (Fuint 129) (word_20 v)
| 21 => Gval (Fuint 65) (word_21 v)
| 22 => Gval (Fuint 64) (word_22 v)
| 23 => Gval (Fuint 1) (word_23 v)
| 24 => Gval (Fuint 1) (word_24 v)
| 25 => Gval (Fuint 65) (word_25 v)
| 26 => Gval (Fuint 64) (word_26 v)
| 27 => Gval (Fuint 64) (word_27 v)
| 28 => Gval (Fuint 1) (word_28 v)
| 29 => Gval (Fuint 1) (word_29 v)
| 30 => Gval (Fuint 65) (word_30 v)
| 31 => Gval (Fuint 64) (word_31 v)
| 32 => Gval (Fuint 64) (word_32 v)
| 33 => Gval (Fuint 1) (word_33 v)
| 34 => Gval (Fuint 1) (word_34 v)
| 35 => Gval (Fuint 1) (word_35 v)
| 36 => Gval (Fuint 1) (word_36 v)
| 37 => Gval (Fuint 1) (word_37 v)
| 38 => Gval (Fuint 1) (word_38 v)
| 39 => Gval (Fuint 1) (word_39 v)
| 40 => Gval (Fuint 64) (word_40 v)
| 41 => Gval (Fuint 64) (word_41 v)
| 42 => Gval (Fuint 65) (word_42 v)
| 43 => Gval (Fuint 65) (word_43 v)
| 44 => Gval (Fuint 65) (word_44 v)
| 45 => Gval (Fuint 1) (word_45 v)
| 46 => Gval (Fuint 1) (word_46 v)
| 47 => Gval (Fuint 1) (word_47 v)
| 48 => Gval (Fuint 1) (word_48 v)
| 49 => Gval (Fuint 1) (word_49 v)
| 50 => Gval (Fuint 1) (word_50 v)
| 51 => Gval (Fuint 6) (word_51 v)
| 52 => Gval (Fuint 1) (word_52 v)
| 53 => Gval (Fuint 32) (word_53 v)
| 54 => Gval (Fuint 32) (word_54 v)
| 55 => Gval (Fuint 1) (word_55 v)
| 56 => Gval (Fuint 16) (word_56 v)
| 57 => Gval (Fuint 16) (word_57 v)
| 58 => Gval (Fuint 1) (word_58 v)
| 59 => Gval (Fuint 8) (word_59 v)
| 60 => Gval (Fuint 8) (word_60 v)
| 61 => Gval (Fuint 1) (word_61 v)
| 62 => Gval (Fuint 4) (word_62 v)
| 63 => Gval (Fuint 4) (word_63 v)
| 64 => Gval (Fuint 1) (word_64 v)
| 65 => Gval (Fuint 1) (word_65 v)
| 66 => Gval (Fuint 1) (word_66 v)
| 67 => Gval (Fuint 1) (word_67 v)
| 68 => Gval (Fuint 2) (word_68 v)
| 69 => Gval (Fuint 2) (word_69 v)
| 70 => Gval (Fuint 1) (word_70 v)
| 71 => Gval (Fuint 1) (word_71 v)
| 72 => Gval (Fuint 1) (word_72 v)
| 73 => Gval (Fuint 2) (word_73 v)
| 74 => Gval (Fuint 2) (word_74 v)
| 75 => Gval (Fuint 2) (word_75 v)
| 76 => Gval (Fuint 3) (word_76 v)
| 77 => Gval (Fuint 4) (word_77 v)
| 78 => Gval (Fuint 4) (word_78 v)
| 79 => Gval (Fuint 1) (word_79 v)
| 80 => Gval (Fuint 1) (word_80 v)
| 81 => Gval (Fuint 1) (word_81 v)
| 82 => Gval (Fuint 1) (word_82 v)
| 83 => Gval (Fuint 2) (word_83 v)
| 84 => Gval (Fuint 2) (word_84 v)
| 85 => Gval (Fuint 1) (word_85 v)
| 86 => Gval (Fuint 1) (word_86 v)
| 87 => Gval (Fuint 1) (word_87 v)
| 88 => Gval (Fuint 2) (word_88 v)
| 89 => Gval (Fuint 2) (word_89 v)
| 90 => Gval (Fuint 2) (word_90 v)
| 91 => Gval (Fuint 3) (word_91 v)
| 92 => Gval (Fuint 3) (word_92 v)
| 93 => Gval (Fuint 4) (word_93 v)
| 94 => Gval (Fuint 8) (word_94 v)
| 95 => Gval (Fuint 8) (word_95 v)
| 96 => Gval (Fuint 1) (word_96 v)
| 97 => Gval (Fuint 4) (word_97 v)
| 98 => Gval (Fuint 4) (word_98 v)
| 99 => Gval (Fuint 1) (word_99 v)
| 100 => Gval (Fuint 1) (word_100 v)
| 101 => Gval (Fuint 1) (word_101 v)
| 102 => Gval (Fuint 1) (word_102 v)
| 103 => Gval (Fuint 2) (word_103 v)
| 104 => Gval (Fuint 2) (word_104 v)
| 105 => Gval (Fuint 1) (word_105 v)
| 106 => Gval (Fuint 1) (word_106 v)
| 107 => Gval (Fuint 1) (word_107 v)
| 108 => Gval (Fuint 2) (word_108 v)
| 109 => Gval (Fuint 2) (word_109 v)
| 110 => Gval (Fuint 2) (word_110 v)
| 111 => Gval (Fuint 3) (word_111 v)
| 112 => Gval (Fuint 4) (word_112 v)
| 113 => Gval (Fuint 4) (word_113 v)
| 114 => Gval (Fuint 1) (word_114 v)
| 115 => Gval (Fuint 1) (word_115 v)
| 116 => Gval (Fuint 1) (word_116 v)
| 117 => Gval (Fuint 1) (word_117 v)
| 118 => Gval (Fuint 2) (word_118 v)
| 119 => Gval (Fuint 2) (word_119 v)
| 120 => Gval (Fuint 1) (word_120 v)
| 121 => Gval (Fuint 1) (word_121 v)
| 122 => Gval (Fuint 1) (word_122 v)
| 123 => Gval (Fuint 2) (word_123 v)
| 124 => Gval (Fuint 2) (word_124 v)
| 125 => Gval (Fuint 2) (word_125 v)
| 126 => Gval (Fuint 3) (word_126 v)
| 127 => Gval (Fuint 3) (word_127 v)
| 128 => Gval (Fuint 4) (word_128 v)
| 129 => Gval (Fuint 4) (word_129 v)
| 130 => Gval (Fuint 5) (word_130 v)
| 131 => Gval (Fuint 16) (word_131 v)
| 132 => Gval (Fuint 16) (word_132 v)
| 133 => Gval (Fuint 1) (word_133 v)
| 134 => Gval (Fuint 8) (word_134 v)
| 135 => Gval (Fuint 8) (word_135 v)
| 136 => Gval (Fuint 1) (word_136 v)
| 137 => Gval (Fuint 4) (word_137 v)
| 138 => Gval (Fuint 4) (word_138 v)
| 139 => Gval (Fuint 1) (word_139 v)
| 140 => Gval (Fuint 1) (word_140 v)
| 141 => Gval (Fuint 1) (word_141 v)
| 142 => Gval (Fuint 1) (word_142 v)
| 143 => Gval (Fuint 2) (word_143 v)
| 144 => Gval (Fuint 2) (word_144 v)
| 145 => Gval (Fuint 1) (word_145 v)
| 146 => Gval (Fuint 1) (word_146 v)
| 147 => Gval (Fuint 1) (word_147 v)
| 148 => Gval (Fuint 2) (word_148 v)
| 149 => Gval (Fuint 2) (word_149 v)
| 150 => Gval (Fuint 2) (word_150 v)
| 151 => Gval (Fuint 3) (word_151 v)
| 152 => Gval (Fuint 4) (word_152 v)
| 153 => Gval (Fuint 4) (word_153 v)
| 154 => Gval (Fuint 1) (word_154 v)
| 155 => Gval (Fuint 1) (word_155 v)
| 156 => Gval (Fuint 1) (word_156 v)
| 157 => Gval (Fuint 1) (word_157 v)
| 158 => Gval (Fuint 2) (word_158 v)
| 159 => Gval (Fuint 2) (word_159 v)
| 160 => Gval (Fuint 1) (word_160 v)
| 161 => Gval (Fuint 1) (word_161 v)
| 162 => Gval (Fuint 1) (word_162 v)
| 163 => Gval (Fuint 2) (word_163 v)
| 164 => Gval (Fuint 2) (word_164 v)
| 165 => Gval (Fuint 2) (word_165 v)
| 166 => Gval (Fuint 3) (word_166 v)
| 167 => Gval (Fuint 3) (word_167 v)
| 168 => Gval (Fuint 4) (word_168 v)
| 169 => Gval (Fuint 8) (word_169 v)
| 170 => Gval (Fuint 8) (word_170 v)
| 171 => Gval (Fuint 1) (word_171 v)
| 172 => Gval (Fuint 4) (word_172 v)
| 173 => Gval (Fuint 4) (word_173 v)
| 174 => Gval (Fuint 1) (word_174 v)
| 175 => Gval (Fuint 1) (word_175 v)
| 176 => Gval (Fuint 1) (word_176 v)
| 177 => Gval (Fuint 1) (word_177 v)
| 178 => Gval (Fuint 2) (word_178 v)
| 179 => Gval (Fuint 2) (word_179 v)
| 180 => Gval (Fuint 1) (word_180 v)
| 181 => Gval (Fuint 1) (word_181 v)
| 182 => Gval (Fuint 1) (word_182 v)
| 183 => Gval (Fuint 2) (word_183 v)
| 184 => Gval (Fuint 2) (word_184 v)
| 185 => Gval (Fuint 2) (word_185 v)
| 186 => Gval (Fuint 3) (word_186 v)
| 187 => Gval (Fuint 4) (word_187 v)
| 188 => Gval (Fuint 4) (word_188 v)
| 189 => Gval (Fuint 1) (word_189 v)
| 190 => Gval (Fuint 1) (word_190 v)
| 191 => Gval (Fuint 1) (word_191 v)
| 192 => Gval (Fuint 1) (word_192 v)
| 193 => Gval (Fuint 2) (word_193 v)
| 194 => Gval (Fuint 2) (word_194 v)
| 195 => Gval (Fuint 1) (word_195 v)
| 196 => Gval (Fuint 1) (word_196 v)
| 197 => Gval (Fuint 1) (word_197 v)
| 198 => Gval (Fuint 2) (word_198 v)
| 199 => Gval (Fuint 2) (word_199 v)
| 200 => Gval (Fuint 2) (word_200 v)
| 201 => Gval (Fuint 3) (word_201 v)
| 202 => Gval (Fuint 3) (word_202 v)
| 203 => Gval (Fuint 4) (word_203 v)
| 204 => Gval (Fuint 4) (word_204 v)
| 205 => Gval (Fuint 5) (word_205 v)
| 206 => Gval (Fuint 5) (word_206 v)
| 207 => Gval (Fuint 6) (word_207 v)
| 208 => Gval (Fuint 8) (word_208 v)
| 209 => Gval (Fuint 7) (word_209 v)
| 210 => Gval (Fuint 1) (word_210 v)
| 211 => Gval (Fuint 64) (word_211 v)
| 212 => Gval (Fuint 1) (word_212 v)
| 213 => Gval (Fuint 32) (word_213 v)
| 214 => Gval (Fuint 32) (word_214 v)
| 215 => Gval (Fuint 1) (word_215 v)
| 216 => Gval (Fuint 16) (word_216 v)
| 217 => Gval (Fuint 16) (word_217 v)
| 218 => Gval (Fuint 1) (word_218 v)
| 219 => Gval (Fuint 8) (word_219 v)
| 220 => Gval (Fuint 8) (word_220 v)
| 221 => Gval (Fuint 1) (word_221 v)
| 222 => Gval (Fuint 4) (word_222 v)
| 223 => Gval (Fuint 4) (word_223 v)
| 224 => Gval (Fuint 1) (word_224 v)
| 225 => Gval (Fuint 1) (word_225 v)
| 226 => Gval (Fuint 1) (word_226 v)
| 227 => Gval (Fuint 1) (word_227 v)
| 228 => Gval (Fuint 2) (word_228 v)
| 229 => Gval (Fuint 2) (word_229 v)
| 230 => Gval (Fuint 1) (word_230 v)
| 231 => Gval (Fuint 1) (word_231 v)
| 232 => Gval (Fuint 1) (word_232 v)
| 233 => Gval (Fuint 2) (word_233 v)
| 234 => Gval (Fuint 2) (word_234 v)
| 235 => Gval (Fuint 2) (word_235 v)
| 236 => Gval (Fuint 3) (word_236 v)
| 237 => Gval (Fuint 4) (word_237 v)
| 238 => Gval (Fuint 4) (word_238 v)
| 239 => Gval (Fuint 1) (word_239 v)
| 240 => Gval (Fuint 1) (word_240 v)
| 241 => Gval (Fuint 1) (word_241 v)
| 242 => Gval (Fuint 1) (word_242 v)
| 243 => Gval (Fuint 2) (word_243 v)
| 244 => Gval (Fuint 2) (word_244 v)
| 245 => Gval (Fuint 1) (word_245 v)
| 246 => Gval (Fuint 1) (word_246 v)
| 247 => Gval (Fuint 1) (word_247 v)
| 248 => Gval (Fuint 2) (word_248 v)
| 249 => Gval (Fuint 2) (word_249 v)
| 250 => Gval (Fuint 2) (word_250 v)
| 251 => Gval (Fuint 3) (word_251 v)
| 252 => Gval (Fuint 3) (word_252 v)
| 253 => Gval (Fuint 4) (word_253 v)
| 254 => Gval (Fuint 8) (word_254 v)
| 255 => Gval (Fuint 8) (word_255 v)
| 256 => Gval (Fuint 1) (word_256 v)
| 257 => Gval (Fuint 4) (word_257 v)
| 258 => Gval (Fuint 4) (word_258 v)
| 259 => Gval (Fuint 1) (word_259 v)
| 260 => Gval (Fuint 1) (word_260 v)
| 261 => Gval (Fuint 1) (word_261 v)
| 262 => Gval (Fuint 1) (word_262 v)
| 263 => Gval (Fuint 2) (word_263 v)
| 264 => Gval (Fuint 2) (word_264 v)
| 265 => Gval (Fuint 1) (word_265 v)
| 266 => Gval (Fuint 1) (word_266 v)
| 267 => Gval (Fuint 1) (word_267 v)
| 268 => Gval (Fuint 2) (word_268 v)
| 269 => Gval (Fuint 2) (word_269 v)
| 270 => Gval (Fuint 2) (word_270 v)
| 271 => Gval (Fuint 3) (word_271 v)
| 272 => Gval (Fuint 4) (word_272 v)
| 273 => Gval (Fuint 4) (word_273 v)
| 274 => Gval (Fuint 1) (word_274 v)
| 275 => Gval (Fuint 1) (word_275 v)
| 276 => Gval (Fuint 1) (word_276 v)
| 277 => Gval (Fuint 1) (word_277 v)
| 278 => Gval (Fuint 2) (word_278 v)
| 279 => Gval (Fuint 2) (word_279 v)
| 280 => Gval (Fuint 1) (word_280 v)
| 281 => Gval (Fuint 1) (word_281 v)
| 282 => Gval (Fuint 1) (word_282 v)
| 283 => Gval (Fuint 2) (word_283 v)
| 284 => Gval (Fuint 2) (word_284 v)
| 285 => Gval (Fuint 2) (word_285 v)
| 286 => Gval (Fuint 3) (word_286 v)
| 287 => Gval (Fuint 3) (word_287 v)
| 288 => Gval (Fuint 4) (word_288 v)
| 289 => Gval (Fuint 4) (word_289 v)
| 290 => Gval (Fuint 5) (word_290 v)
| 291 => Gval (Fuint 16) (word_291 v)
| 292 => Gval (Fuint 16) (word_292 v)
| 293 => Gval (Fuint 1) (word_293 v)
| 294 => Gval (Fuint 8) (word_294 v)
| 295 => Gval (Fuint 8) (word_295 v)
| 296 => Gval (Fuint 1) (word_296 v)
| 297 => Gval (Fuint 4) (word_297 v)
| 298 => Gval (Fuint 4) (word_298 v)
| 299 => Gval (Fuint 1) (word_299 v)
| 300 => Gval (Fuint 1) (word_300 v)
| 301 => Gval (Fuint 1) (word_301 v)
| 302 => Gval (Fuint 1) (word_302 v)
| 303 => Gval (Fuint 2) (word_303 v)
| 304 => Gval (Fuint 2) (word_304 v)
| 305 => Gval (Fuint 1) (word_305 v)
| 306 => Gval (Fuint 1) (word_306 v)
| 307 => Gval (Fuint 1) (word_307 v)
| 308 => Gval (Fuint 2) (word_308 v)
| 309 => Gval (Fuint 2) (word_309 v)
| 310 => Gval (Fuint 2) (word_310 v)
| 311 => Gval (Fuint 3) (word_311 v)
| 312 => Gval (Fuint 4) (word_312 v)
| 313 => Gval (Fuint 4) (word_313 v)
| 314 => Gval (Fuint 1) (word_314 v)
| 315 => Gval (Fuint 1) (word_315 v)
| 316 => Gval (Fuint 1) (word_316 v)
| 317 => Gval (Fuint 1) (word_317 v)
| 318 => Gval (Fuint 2) (word_318 v)
| 319 => Gval (Fuint 2) (word_319 v)
| 320 => Gval (Fuint 1) (word_320 v)
| 321 => Gval (Fuint 1) (word_321 v)
| 322 => Gval (Fuint 1) (word_322 v)
| 323 => Gval (Fuint 2) (word_323 v)
| 324 => Gval (Fuint 2) (word_324 v)
| 325 => Gval (Fuint 2) (word_325 v)
| 326 => Gval (Fuint 3) (word_326 v)
| 327 => Gval (Fuint 3) (word_327 v)
| 328 => Gval (Fuint 4) (word_328 v)
| 329 => Gval (Fuint 8) (word_329 v)
| 330 => Gval (Fuint 8) (word_330 v)
| 331 => Gval (Fuint 1) (word_331 v)
| 332 => Gval (Fuint 4) (word_332 v)
| 333 => Gval (Fuint 4) (word_333 v)
| 334 => Gval (Fuint 1) (word_334 v)
| 335 => Gval (Fuint 1) (word_335 v)
| 336 => Gval (Fuint 1) (word_336 v)
| 337 => Gval (Fuint 1) (word_337 v)
| 338 => Gval (Fuint 2) (word_338 v)
| 339 => Gval (Fuint 2) (word_339 v)
| 340 => Gval (Fuint 1) (word_340 v)
| 341 => Gval (Fuint 1) (word_341 v)
| 342 => Gval (Fuint 1) (word_342 v)
| 343 => Gval (Fuint 2) (word_343 v)
| 344 => Gval (Fuint 2) (word_344 v)
| 345 => Gval (Fuint 2) (word_345 v)
| 346 => Gval (Fuint 3) (word_346 v)
| 347 => Gval (Fuint 4) (word_347 v)
| 348 => Gval (Fuint 4) (word_348 v)
| 349 => Gval (Fuint 1) (word_349 v)
| 350 => Gval (Fuint 1) (word_350 v)
| 351 => Gval (Fuint 1) (word_351 v)
| 352 => Gval (Fuint 1) (word_352 v)
| 353 => Gval (Fuint 2) (word_353 v)
| 354 => Gval (Fuint 2) (word_354 v)
| 355 => Gval (Fuint 1) (word_355 v)
| 356 => Gval (Fuint 1) (word_356 v)
| 357 => Gval (Fuint 1) (word_357 v)
| 358 => Gval (Fuint 2) (word_358 v)
| 359 => Gval (Fuint 2) (word_359 v)
| 360 => Gval (Fuint 2) (word_360 v)
| 361 => Gval (Fuint 3) (word_361 v)
| 362 => Gval (Fuint 3) (word_362 v)
| 363 => Gval (Fuint 4) (word_363 v)
| 364 => Gval (Fuint 4) (word_364 v)
| 365 => Gval (Fuint 5) (word_365 v)
| 366 => Gval (Fuint 5) (word_366 v)
| 367 => Gval (Fuint 6) (word_367 v)
| 368 => Gval (Fuint 6) (word_368 v)
| 369 => Gval (Fuint 7) (word_369 v)
| 370 => Gval (Fuint 8) (word_370 v)
| 371 => Gval (Fuint 7) (word_371 v)
| 372 => Gval (Fuint 1) (word_372 v)
| 373 => Gval (Fuint 7) (word_373 v)
| 374 => Gval (Fuint 7) (word_374 v)
| 375 => Gval (Fuint 1) (word_375 v)
| 376 => Gval (Fuint 128) (word_376 v)
| 377 => Gval (Fuint 1) (word_377 v)
| 378 => Gval (Fuint 1) (word_378 v)
| 379 => Gval (Fuint 66) (word_379 v)
| 380 => Gval (Fuint 65) (word_380 v)
| 381 => Gval (Fuint 65) (word_381 v)
| 382 => Gval (Fuint 64) (word_382 v)
| 383 => Gval (Fuint 128) (word_383 v)
| 384 => Gval (Fuint 129) (word_384 v)
| 385 => Gval (Fuint 1) (word_385 v)
| 386 => Gval (Fuint 7) (word_386 v)
| 387 => Gval (Fuint 6) (word_387 v)
| 388 => Gval (Fuint 1) (word_388 v)
| 389 => Gval (Fuint 3) (word_389 v)
| 390 => Gval (Fuint 1) (word_390 v)
| 391 => Gval (Fuint 3) (word_391 v)
| 392 => Gval (Fuint 3) (word_392 v)
| 393 => Gval (Fuint 129) (word_393 v)
| 394 => Gval (Fuint 6) (word_394 v)
| 395 => Gval (Fuint 3) (word_395 v)
| 396 => Gval (Fuint 129) (word_396 v)
| 397 => Gval (Fuint 3) (word_397 v)
| 398 => Gval (Fuint 6) (word_398 v)
| 399 => Gval (Fuint 7) (word_399 v)
| 400 => Gval (Fuint 3) (word_400 v)
| 401 => Gval (Fuint 129) (word_401 v)
| 402 => Gval (Fuint 3) (word_402 v)
| 403 => Gval (Fuint 7) (word_403 v)
| 404 => Gval (Fuint 129) (word_404 v)
| 405 => Gval (Fuint 64) (word_405 v)
| 406 => Gval (Fuint 65) (word_406 v)
| 407 => Gval (Fuint 64) (word_407 v)
| 408 => Gval (Fuint 64) (word_408 v)
| 409 => Gval (Fuint 65) (word_409 v)
| 410 => Gval (Fuint 64) (word_410 v)
| 411 => Gval (Fuint 64) (word_411 v)
| 412 => Gval (Fuint 64) (word_412 v)
| 413 => Gval (Fuint 32) (word_413 v)
| 414 => Gval (Fuint 1) (word_414 v)
| 415 => Gval (Fuint 1) (word_415 v)
| 416 => Gval (Fuint 32) (word_416 v)
| 417 => Gval (Fuint 64) (word_417 v)
| 418 => Gval (Fuint 64) (word_418 v)
| 419 => Gval (Fuint 1) (word_419 v)
| 420 => Gval (Fuint 1) (word_420 v)
| 421 => Gval (Fuint 1) (word_421 v)
| 422 => Gval (Fuint 1) (word_422 v)
| 423 => Gval (Fuint 1) (word_423 v)
| 424 => Gval (Fuint 1) (word_424 v)
| 425 => Gval (Fuint 64) (word_425 v)
| 426 => Gval (Fuint 1) (word_426 v)
| 427 => Gval (Fuint 1) (word_427 v)
| 428 => Gval (Fuint 1) (word_428 v)
| 429 => Gval (Fuint 1) (word_429 v)
| 430 => Gval (Fuint 1) (word_430 v)
| 431 => Gval (Fuint 1) (word_431 v)
| 432 => Gval (Fuint 1) (word_432 v)
| 433 => Gval (Fuint 1) (word_433 v)
| 434 => Gval (Fuint 128) (word_434 v)
| 435 => Gval (Fuint 129) (word_435 v)
| 436 => Gval (Fuint 64) (word_436 v)
| 437 => Gval (Fuint 1) (word_437 v)
| 438 => Gval (Fuint 1) (word_438 v)
| 439 => Gval (Fuint 1) (word_439 v)
| 440 => Gval (Fuint 1) (word_440 v)
| 441 => Gval (Fuint 1) (word_441 v)
| 442 => Gval (Fuint 1) (word_442 v)
| 443 => Gval (Fuint 1) (word_443 v)
| 444 => Gval (Fuint 1) (word_444 v)
| 445 => Gval (Fuint 1) (word_445 v)
| 446 => Gval (Fuint 3) (word_446 v)
| 447 => Gval (Fuint 6) (word_447 v)
| 448 => Gval (Fuint 1) (word_448 v)
| 449 => Gval (Fuint 1) (word_449 v)
| 450 => Gval (Fuint 1) (word_450 v)
| 451 => Gval (Fuint 1) (word_451 v)
| 452 => Gval (Fuint 1) (word_452 v)
| 453 => Gval (Fuint 1) (word_453 v)
| 454 => Gval (Fuint 1) (word_454 v)
| 455 => Gval (Fuint 1) (word_455 v)
| 456 => Gval (Fuint 1) (word_456 v)
| 457 => Gval (Fuint 1) (word_457 v)
| 458 => Gval (Fuint 1) (word_458 v)
| 459 => Gval (Fuint 1) (word_459 v)
| 460 => Gval (Fuint 3) (word_460 v)
| 461 => Gval (Fuint 1) (word_461 v)
| 462 => Gval (Fuint 1) (word_462 v)
| 463 => Gval (Fuint 1) (word_463 v)
| 464 => Gval (Fuint 1) (word_464 v)
| 465 => Gval (Fuint 1) (word_465 v)
| 466 => Gval (Fuint 7) (word_466 v)
| 467 => Gval (Fuint 6) (word_467 v)
| 468 => Gval (Fuint 6) (word_468 v)
| 469 => Gval (Fuint 1) (word_469 v)
| 470 => Gval (Fuint 1) (word_470 v)
| 471 => Gval (Fuint 1) (word_471 v)
| 472 => Gval (Fuint 1) (word_472 v)
| 473 => Gval (Fuint 1) (word_473 v)
| 474 => Gval (Fuint 1) (word_474 v)
| 475 => Gval (Fuint 1) (word_475 v)
| 476 => Gval (Fuint 64) (word_476 v)
| 477 => Gval (Fuint 1) (word_477 v)
| 478 => Gval (Fuint 1) (word_478 v)
| 479 => Gval (Fuint 1) (word_479 v)
| 480 => Gval (Fuint 1) (word_480 v)
| 481 => Gval (Fuint 1) (word_481 v)
| 482 => Gval (Fuint 1) (word_482 v)
| 483 => Gval (Fuint 1) (word_483 v)
| _ => Needtobedefined (Gtyp (Fuint 0)) end.
Definition stable_env v := stable_shape (stable_values v).
Opaque word_0 word_1 word_2 word_3 word_4 word_5 word_6 word_7 word_8 word_9 word_10 word_11 word_12 word_13 word_14 word_15 word_16 word_17 word_18 word_19 word_20 word_21 word_22 word_23 word_24 word_25 word_26 word_27 word_28 word_29 word_30 word_31 word_32 word_33 word_34 word_35 word_36 word_37 word_38 word_39 word_40 word_41 word_42 word_43 word_44 word_45 word_46 word_47 word_48 word_49 word_50 word_51 word_52 word_53 word_54 word_55 word_56 word_57 word_58 word_59 word_60 word_61 word_62 word_63 word_64 word_65 word_66 word_67 word_68 word_69 word_70 word_71 word_72 word_73 word_74 word_75 word_76 word_77 word_78 word_79 word_80 word_81 word_82 word_83 word_84 word_85 word_86 word_87 word_88 word_89 word_90 word_91 word_92 word_93 word_94 word_95 word_96 word_97 word_98 word_99 word_100 word_101 word_102 word_103 word_104 word_105 word_106 word_107 word_108 word_109 word_110 word_111 word_112 word_113 word_114 word_115 word_116 word_117 word_118 word_119 word_120 word_121 word_122 word_123 word_124 word_125 word_126 word_127 word_128 word_129 word_130 word_131 word_132 word_133 word_134 word_135 word_136 word_137 word_138 word_139 word_140 word_141 word_142 word_143 word_144 word_145 word_146 word_147 word_148 word_149 word_150 word_151 word_152 word_153 word_154 word_155 word_156 word_157 word_158 word_159 word_160 word_161 word_162 word_163 word_164 word_165 word_166 word_167 word_168 word_169 word_170 word_171 word_172 word_173 word_174 word_175 word_176 word_177 word_178 word_179 word_180 word_181 word_182 word_183 word_184 word_185 word_186 word_187 word_188 word_189 word_190 word_191 word_192 word_193 word_194 word_195 word_196 word_197 word_198 word_199 word_200 word_201 word_202 word_203 word_204 word_205 word_206 word_207 word_208 word_209 word_210 word_211 word_212 word_213 word_214 word_215 word_216 word_217 word_218 word_219 word_220 word_221 word_222 word_223 word_224 word_225 word_226 word_227 word_228 word_229 word_230 word_231 word_232 word_233 word_234 word_235 word_236 word_237 word_238 word_239 word_240 word_241 word_242 word_243 word_244 word_245 word_246 word_247 word_248 word_249 word_250 word_251 word_252 word_253 word_254 word_255 word_256 word_257 word_258 word_259 word_260 word_261 word_262 word_263 word_264 word_265 word_266 word_267 word_268 word_269 word_270 word_271 word_272 word_273 word_274 word_275 word_276 word_277 word_278 word_279 word_280 word_281 word_282 word_283 word_284 word_285 word_286 word_287 word_288 word_289 word_290 word_291 word_292 word_293 word_294 word_295 word_296 word_297 word_298 word_299 word_300 word_301 word_302 word_303 word_304 word_305 word_306 word_307 word_308 word_309 word_310 word_311 word_312 word_313 word_314 word_315 word_316 word_317 word_318 word_319 word_320 word_321 word_322 word_323 word_324 word_325 word_326 word_327 word_328 word_329 word_330 word_331 word_332 word_333 word_334 word_335 word_336 word_337 word_338 word_339 word_340 word_341 word_342 word_343 word_344 word_345 word_346 word_347 word_348 word_349 word_350 word_351 word_352 word_353 word_354 word_355 word_356 word_357 word_358 word_359 word_360 word_361 word_362 word_363 word_364 word_365 word_366 word_367 word_368 word_369 word_370 word_371 word_372 word_373 word_374 word_375 word_376 word_377 word_378 word_379 word_380 word_381 word_382 word_383 word_384 word_385 word_386 word_387 word_388 word_389 word_390 word_391 word_392 word_393 word_394 word_395 word_396 word_397 word_398 word_399 word_400 word_401 word_402 word_403 word_404 word_405 word_406 word_407 word_408 word_409 word_410 word_411 word_412 word_413 word_414 word_415 word_416 word_417 word_418 word_419 word_420 word_421 word_422 word_423 word_424 word_425 word_426 word_427 word_428 word_429 word_430 word_431 word_432 word_433 word_434 word_435 word_436 word_437 word_438 word_439 word_440 word_441 word_442 word_443 word_444 word_445 word_446 word_447 word_448 word_449 word_450 word_451 word_452 word_453 word_454 word_455 word_456 word_457 word_458 word_459 word_460 word_461 word_462 word_463 word_464 word_465 word_466 word_467 word_468 word_469 word_470 word_471 word_472 word_473 word_474 word_475 word_476 word_477 word_478 word_479 word_480 word_481 word_482 word_483.
Lemma source_14 : find_driver 14 generated_module_0_stmts_0 = Some expr_14.
Proof. vm_compute. reflexivity. Qed.
Transparent word_14.
Lemma closed_14_value v : eval_hfexpr expr_14 (closed_14 v) (closed_14 v) = Some (Gval (Fuint 1) (word_14 v)).
Proof. unfold word_14, closed_14, expr_14, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_14.
Lemma node_14_value v : eval_hfexpr expr_14 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_14 v)).
Proof. change (eval_hfexpr expr_14 (closed_14 v) (closed_14 v) = Some (Gval (Fuint 1) (word_14 v))). apply closed_14_value. Qed.
Lemma source_420 : find_driver 420 generated_module_0_stmts_0 = Some expr_420.
Proof. vm_compute. reflexivity. Qed.
Transparent word_420.
Lemma closed_420_value v : eval_hfexpr expr_420 (closed_420 v) (closed_420 v) = Some (Gval (Fuint 1) (word_420 v)).
Proof. unfold word_420, closed_420, expr_420, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_420.
Lemma node_420_value v : eval_hfexpr expr_420 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_420 v)).
Proof. change (eval_hfexpr expr_420 (closed_420 v) (closed_420 v) = Some (Gval (Fuint 1) (word_420 v))). apply closed_420_value. Qed.
Lemma source_2 : find_driver 2 generated_module_0_stmts_0 = Some expr_2.
Proof. vm_compute. reflexivity. Qed.
Transparent word_2.
Lemma closed_2_value v : eval_hfexpr expr_2 (closed_2 v) (closed_2 v) = Some (Gval (Fuint 1) (word_2 v)).
Proof. unfold word_2, closed_2, expr_2, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_2.
Lemma node_2_value v : eval_hfexpr expr_2 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_2 v)).
Proof. change (eval_hfexpr expr_2 (closed_2 v) (closed_2 v) = Some (Gval (Fuint 1) (word_2 v))). apply closed_2_value. Qed.
Lemma source_15 : find_driver 15 generated_module_0_stmts_0 = Some expr_15.
Proof. vm_compute. reflexivity. Qed.
Transparent word_15.
Lemma closed_15_value v : eval_hfexpr expr_15 (closed_15 v) (closed_15 v) = Some (Gval (Fuint 1) (word_15 v)).
Proof. unfold word_15, closed_15, expr_15, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_15.
Lemma node_15_value v : eval_hfexpr expr_15 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_15 v)).
Proof. change (eval_hfexpr expr_15 (closed_15 v) (closed_15 v) = Some (Gval (Fuint 1) (word_15 v))). apply closed_15_value. Qed.
Lemma source_16 : find_driver 16 generated_module_0_stmts_0 = Some expr_16.
Proof. vm_compute. reflexivity. Qed.
Transparent word_16.
Lemma closed_16_value v : eval_hfexpr expr_16 (closed_16 v) (closed_16 v) = Some (Gval (Fuint 1) (word_16 v)).
Proof. unfold word_16, closed_16, expr_16, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_16.
Lemma node_16_value v : eval_hfexpr expr_16 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_16 v)).
Proof. change (eval_hfexpr expr_16 (closed_16 v) (closed_16 v) = Some (Gval (Fuint 1) (word_16 v))). apply closed_16_value. Qed.
Lemma source_17 : find_driver 17 generated_module_0_stmts_0 = Some expr_17.
Proof. vm_compute. reflexivity. Qed.
Transparent word_17.
Lemma closed_17_value v : eval_hfexpr expr_17 (closed_17 v) (closed_17 v) = Some (Gval (Fuint 1) (word_17 v)).
Proof. unfold word_17, closed_17, expr_17, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_17.
Lemma node_17_value v : eval_hfexpr expr_17 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_17 v)).
Proof. change (eval_hfexpr expr_17 (closed_17 v) (closed_17 v) = Some (Gval (Fuint 1) (word_17 v))). apply closed_17_value. Qed.
Lemma source_19 : find_driver 19 generated_module_0_stmts_0 = Some expr_19.
Proof. vm_compute. reflexivity. Qed.
Transparent word_19.
Lemma closed_19_value v : eval_hfexpr expr_19 (closed_19 v) (closed_19 v) = Some (Gval (Fuint 1) (word_19 v)).
Proof. unfold word_19, closed_19, expr_19, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_19.
Lemma node_19_value v : eval_hfexpr expr_19 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_19 v)).
Proof. change (eval_hfexpr expr_19 (closed_19 v) (closed_19 v) = Some (Gval (Fuint 1) (word_19 v))). apply closed_19_value. Qed.
Lemma source_21 : find_driver 21 generated_module_0_stmts_0 = Some expr_21.
Proof. vm_compute. reflexivity. Qed.
Transparent word_21.
Lemma closed_21_value v : eval_hfexpr expr_21 (closed_21 v) (closed_21 v) = Some (Gval (Fuint 65) (word_21 v)).
Proof. unfold word_21, closed_21, expr_21, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_21.
Lemma node_21_value v : eval_hfexpr expr_21 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_21 v)).
Proof. change (eval_hfexpr expr_21 (closed_21 v) (closed_21 v) = Some (Gval (Fuint 65) (word_21 v))). apply closed_21_value. Qed.
Lemma source_22 : find_driver 22 generated_module_0_stmts_0 = Some expr_22.
Proof. vm_compute. reflexivity. Qed.
Transparent word_22.
Lemma closed_22_value v : eval_hfexpr expr_22 (closed_22 v) (closed_22 v) = Some (Gval (Fuint 64) (word_22 v)).
Proof. unfold word_22, closed_22, expr_22, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_22.
Lemma node_22_value v : eval_hfexpr expr_22 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_22 v)).
Proof. change (eval_hfexpr expr_22 (closed_22 v) (closed_22 v) = Some (Gval (Fuint 64) (word_22 v))). apply closed_22_value. Qed.
Lemma source_23 : find_driver 23 generated_module_0_stmts_0 = Some expr_23.
Proof. vm_compute. reflexivity. Qed.
Transparent word_23.
Lemma closed_23_value v : eval_hfexpr expr_23 (closed_23 v) (closed_23 v) = Some (Gval (Fuint 1) (word_23 v)).
Proof. unfold word_23, closed_23, expr_23, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_23.
Lemma node_23_value v : eval_hfexpr expr_23 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_23 v)).
Proof. change (eval_hfexpr expr_23 (closed_23 v) (closed_23 v) = Some (Gval (Fuint 1) (word_23 v))). apply closed_23_value. Qed.
Lemma source_24 : find_driver 24 generated_module_0_stmts_0 = Some expr_24.
Proof. vm_compute. reflexivity. Qed.
Transparent word_24.
Lemma closed_24_value v : eval_hfexpr expr_24 (closed_24 v) (closed_24 v) = Some (Gval (Fuint 1) (word_24 v)).
Proof. unfold word_24, closed_24, expr_24, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_24.
Lemma node_24_value v : eval_hfexpr expr_24 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_24 v)).
Proof. change (eval_hfexpr expr_24 (closed_24 v) (closed_24 v) = Some (Gval (Fuint 1) (word_24 v))). apply closed_24_value. Qed.
Lemma source_25 : find_driver 25 generated_module_0_stmts_0 = Some expr_25.
Proof. vm_compute. reflexivity. Qed.
Transparent word_25.
Lemma closed_25_value v : eval_hfexpr expr_25 (closed_25 v) (closed_25 v) = Some (Gval (Fuint 65) (word_25 v)).
Proof. unfold word_25, closed_25, expr_25, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_25.
Lemma node_25_value v : eval_hfexpr expr_25 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_25 v)).
Proof. change (eval_hfexpr expr_25 (closed_25 v) (closed_25 v) = Some (Gval (Fuint 65) (word_25 v))). apply closed_25_value. Qed.
Lemma source_26 : find_driver 26 generated_module_0_stmts_0 = Some expr_26.
Proof. vm_compute. reflexivity. Qed.
Transparent word_26.
Lemma closed_26_value v : eval_hfexpr expr_26 (closed_26 v) (closed_26 v) = Some (Gval (Fuint 64) (word_26 v)).
Proof. unfold word_26, closed_26, expr_26, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_26.
Lemma node_26_value v : eval_hfexpr expr_26 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_26 v)).
Proof. change (eval_hfexpr expr_26 (closed_26 v) (closed_26 v) = Some (Gval (Fuint 64) (word_26 v))). apply closed_26_value. Qed.
Lemma source_27 : find_driver 27 generated_module_0_stmts_0 = Some expr_27.
Proof. vm_compute. reflexivity. Qed.
Transparent word_27.
Lemma closed_27_value v : eval_hfexpr expr_27 (closed_27 v) (closed_27 v) = Some (Gval (Fuint 64) (word_27 v)).
Proof. unfold word_27, closed_27, expr_27, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_27.
Lemma node_27_value v : eval_hfexpr expr_27 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_27 v)).
Proof. change (eval_hfexpr expr_27 (closed_27 v) (closed_27 v) = Some (Gval (Fuint 64) (word_27 v))). apply closed_27_value. Qed.
Lemma source_28 : find_driver 28 generated_module_0_stmts_0 = Some expr_28.
Proof. vm_compute. reflexivity. Qed.
Transparent word_28.
Lemma closed_28_value v : eval_hfexpr expr_28 (closed_28 v) (closed_28 v) = Some (Gval (Fuint 1) (word_28 v)).
Proof. unfold word_28, closed_28, expr_28, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_28.
Lemma node_28_value v : eval_hfexpr expr_28 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_28 v)).
Proof. change (eval_hfexpr expr_28 (closed_28 v) (closed_28 v) = Some (Gval (Fuint 1) (word_28 v))). apply closed_28_value. Qed.
Lemma source_29 : find_driver 29 generated_module_0_stmts_0 = Some expr_29.
Proof. vm_compute. reflexivity. Qed.
Transparent word_29.
Lemma closed_29_value v : eval_hfexpr expr_29 (closed_29 v) (closed_29 v) = Some (Gval (Fuint 1) (word_29 v)).
Proof. unfold word_29, closed_29, expr_29, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_29.
Lemma node_29_value v : eval_hfexpr expr_29 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_29 v)).
Proof. change (eval_hfexpr expr_29 (closed_29 v) (closed_29 v) = Some (Gval (Fuint 1) (word_29 v))). apply closed_29_value. Qed.
Lemma source_30 : find_driver 30 generated_module_0_stmts_0 = Some expr_30.
Proof. vm_compute. reflexivity. Qed.
Transparent word_30.
Lemma closed_30_value v : eval_hfexpr expr_30 (closed_30 v) (closed_30 v) = Some (Gval (Fuint 65) (word_30 v)).
Proof. unfold word_30, closed_30, expr_30, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_30.
Lemma node_30_value v : eval_hfexpr expr_30 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_30 v)).
Proof. change (eval_hfexpr expr_30 (closed_30 v) (closed_30 v) = Some (Gval (Fuint 65) (word_30 v))). apply closed_30_value. Qed.
Lemma source_31 : find_driver 31 generated_module_0_stmts_0 = Some expr_31.
Proof. vm_compute. reflexivity. Qed.
Transparent word_31.
Lemma closed_31_value v : eval_hfexpr expr_31 (closed_31 v) (closed_31 v) = Some (Gval (Fuint 64) (word_31 v)).
Proof. unfold word_31, closed_31, expr_31, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_31.
Lemma node_31_value v : eval_hfexpr expr_31 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_31 v)).
Proof. change (eval_hfexpr expr_31 (closed_31 v) (closed_31 v) = Some (Gval (Fuint 64) (word_31 v))). apply closed_31_value. Qed.
Lemma source_32 : find_driver 32 generated_module_0_stmts_0 = Some expr_32.
Proof. vm_compute. reflexivity. Qed.
Transparent word_32.
Lemma closed_32_value v : eval_hfexpr expr_32 (closed_32 v) (closed_32 v) = Some (Gval (Fuint 64) (word_32 v)).
Proof. unfold word_32, closed_32, expr_32, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_32.
Lemma node_32_value v : eval_hfexpr expr_32 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_32 v)).
Proof. change (eval_hfexpr expr_32 (closed_32 v) (closed_32 v) = Some (Gval (Fuint 64) (word_32 v))). apply closed_32_value. Qed.
Lemma source_34 : find_driver 34 generated_module_0_stmts_0 = Some expr_34.
Proof. vm_compute. reflexivity. Qed.
Transparent word_34.
Lemma closed_34_value v : eval_hfexpr expr_34 (closed_34 v) (closed_34 v) = Some (Gval (Fuint 1) (word_34 v)).
Proof. unfold word_34, closed_34, expr_34, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_34.
Lemma node_34_value v : eval_hfexpr expr_34 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_34 v)).
Proof. change (eval_hfexpr expr_34 (closed_34 v) (closed_34 v) = Some (Gval (Fuint 1) (word_34 v))). apply closed_34_value. Qed.
Lemma source_35 : find_driver 35 generated_module_0_stmts_0 = Some expr_35.
Proof. vm_compute. reflexivity. Qed.
Transparent word_35.
Lemma closed_35_value v : eval_hfexpr expr_35 (closed_35 v) (closed_35 v) = Some (Gval (Fuint 1) (word_35 v)).
Proof. unfold word_35, closed_35, expr_35, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_35.
Lemma node_35_value v : eval_hfexpr expr_35 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_35 v)).
Proof. change (eval_hfexpr expr_35 (closed_35 v) (closed_35 v) = Some (Gval (Fuint 1) (word_35 v))). apply closed_35_value. Qed.
Lemma source_36 : find_driver 36 generated_module_0_stmts_0 = Some expr_36.
Proof. vm_compute. reflexivity. Qed.
Transparent word_36.
Lemma closed_36_value v : eval_hfexpr expr_36 (closed_36 v) (closed_36 v) = Some (Gval (Fuint 1) (word_36 v)).
Proof. unfold word_36, closed_36, expr_36, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_36.
Lemma node_36_value v : eval_hfexpr expr_36 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_36 v)).
Proof. change (eval_hfexpr expr_36 (closed_36 v) (closed_36 v) = Some (Gval (Fuint 1) (word_36 v))). apply closed_36_value. Qed.
Lemma source_37 : find_driver 37 generated_module_0_stmts_0 = Some expr_37.
Proof. vm_compute. reflexivity. Qed.
Transparent word_37.
Lemma closed_37_value v : eval_hfexpr expr_37 (closed_37 v) (closed_37 v) = Some (Gval (Fuint 1) (word_37 v)).
Proof. unfold word_37, closed_37, expr_37, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_37.
Lemma node_37_value v : eval_hfexpr expr_37 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_37 v)).
Proof. change (eval_hfexpr expr_37 (closed_37 v) (closed_37 v) = Some (Gval (Fuint 1) (word_37 v))). apply closed_37_value. Qed.
Lemma source_39 : find_driver 39 generated_module_0_stmts_0 = Some expr_39.
Proof. vm_compute. reflexivity. Qed.
Transparent word_39.
Lemma closed_39_value v : eval_hfexpr expr_39 (closed_39 v) (closed_39 v) = Some (Gval (Fuint 1) (word_39 v)).
Proof. unfold word_39, closed_39, expr_39, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_39.
Lemma node_39_value v : eval_hfexpr expr_39 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_39 v)).
Proof. change (eval_hfexpr expr_39 (closed_39 v) (closed_39 v) = Some (Gval (Fuint 1) (word_39 v))). apply closed_39_value. Qed.
Lemma source_41 : find_driver 41 generated_module_0_stmts_0 = Some expr_41.
Proof. vm_compute. reflexivity. Qed.
Transparent word_41.
Lemma closed_41_value v : eval_hfexpr expr_41 (closed_41 v) (closed_41 v) = Some (Gval (Fuint 64) (word_41 v)).
Proof. unfold word_41, closed_41, expr_41, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_41.
Lemma node_41_value v : eval_hfexpr expr_41 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_41 v)).
Proof. change (eval_hfexpr expr_41 (closed_41 v) (closed_41 v) = Some (Gval (Fuint 64) (word_41 v))). apply closed_41_value. Qed.
Lemma source_42 : find_driver 42 generated_module_0_stmts_0 = Some expr_42.
Proof. vm_compute. reflexivity. Qed.
Transparent word_42.
Lemma closed_42_value v : eval_hfexpr expr_42 (closed_42 v) (closed_42 v) = Some (Gval (Fuint 65) (word_42 v)).
Proof. unfold word_42, closed_42, expr_42, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_42.
Lemma node_42_value v : eval_hfexpr expr_42 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_42 v)).
Proof. change (eval_hfexpr expr_42 (closed_42 v) (closed_42 v) = Some (Gval (Fuint 65) (word_42 v))). apply closed_42_value. Qed.
Lemma source_44 : find_driver 44 generated_module_0_stmts_0 = Some expr_44.
Proof. vm_compute. reflexivity. Qed.
Transparent word_44.
Lemma closed_44_value v : eval_hfexpr expr_44 (closed_44 v) (closed_44 v) = Some (Gval (Fuint 65) (word_44 v)).
Proof. unfold word_44, closed_44, expr_44, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_44.
Lemma node_44_value v : eval_hfexpr expr_44 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_44 v)).
Proof. change (eval_hfexpr expr_44 (closed_44 v) (closed_44 v) = Some (Gval (Fuint 65) (word_44 v))). apply closed_44_value. Qed.
Lemma source_48 : find_driver 48 generated_module_0_stmts_0 = Some expr_48.
Proof. vm_compute. reflexivity. Qed.
Transparent word_48.
Lemma closed_48_value v : eval_hfexpr expr_48 (closed_48 v) (closed_48 v) = Some (Gval (Fuint 1) (word_48 v)).
Proof. unfold word_48, closed_48, expr_48, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_48.
Lemma node_48_value v : eval_hfexpr expr_48 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_48 v)).
Proof. change (eval_hfexpr expr_48 (closed_48 v) (closed_48 v) = Some (Gval (Fuint 1) (word_48 v))). apply closed_48_value. Qed.
Lemma source_49 : find_driver 49 generated_module_0_stmts_0 = Some expr_49.
Proof. vm_compute. reflexivity. Qed.
Transparent word_49.
Lemma closed_49_value v : eval_hfexpr expr_49 (closed_49 v) (closed_49 v) = Some (Gval (Fuint 1) (word_49 v)).
Proof. unfold word_49, closed_49, expr_49, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_49.
Lemma node_49_value v : eval_hfexpr expr_49 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_49 v)).
Proof. change (eval_hfexpr expr_49 (closed_49 v) (closed_49 v) = Some (Gval (Fuint 1) (word_49 v))). apply closed_49_value. Qed.
Lemma source_50 : find_driver 50 generated_module_0_stmts_0 = Some expr_50.
Proof. vm_compute. reflexivity. Qed.
Transparent word_50.
Lemma closed_50_value v : eval_hfexpr expr_50 (closed_50 v) (closed_50 v) = Some (Gval (Fuint 1) (word_50 v)).
Proof. unfold word_50, closed_50, expr_50, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_50.
Lemma node_50_value v : eval_hfexpr expr_50 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_50 v)).
Proof. change (eval_hfexpr expr_50 (closed_50 v) (closed_50 v) = Some (Gval (Fuint 1) (word_50 v))). apply closed_50_value. Qed.
Lemma source_52 : find_driver 52 generated_module_0_stmts_0 = Some expr_52.
Proof. vm_compute. reflexivity. Qed.
Transparent word_52.
Lemma closed_52_value v : eval_hfexpr expr_52 (closed_52 v) (closed_52 v) = Some (Gval (Fuint 1) (word_52 v)).
Proof. unfold word_52, closed_52, expr_52, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_52.
Lemma node_52_value v : eval_hfexpr expr_52 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_52 v)).
Proof. change (eval_hfexpr expr_52 (closed_52 v) (closed_52 v) = Some (Gval (Fuint 1) (word_52 v))). apply closed_52_value. Qed.
Lemma source_53 : find_driver 53 generated_module_0_stmts_0 = Some expr_53.
Proof. vm_compute. reflexivity. Qed.
Transparent word_53.
Lemma closed_53_value v : eval_hfexpr expr_53 (closed_53 v) (closed_53 v) = Some (Gval (Fuint 32) (word_53 v)).
Proof. unfold word_53, closed_53, expr_53, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_53.
Lemma node_53_value v : eval_hfexpr expr_53 (stable_env v) (stable_env v) = Some (Gval (Fuint 32) (word_53 v)).
Proof. change (eval_hfexpr expr_53 (closed_53 v) (closed_53 v) = Some (Gval (Fuint 32) (word_53 v))). apply closed_53_value. Qed.
Lemma source_54 : find_driver 54 generated_module_0_stmts_0 = Some expr_54.
Proof. vm_compute. reflexivity. Qed.
Transparent word_54.
Lemma closed_54_value v : eval_hfexpr expr_54 (closed_54 v) (closed_54 v) = Some (Gval (Fuint 32) (word_54 v)).
Proof. unfold word_54, closed_54, expr_54, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_54.
Lemma node_54_value v : eval_hfexpr expr_54 (stable_env v) (stable_env v) = Some (Gval (Fuint 32) (word_54 v)).
Proof. change (eval_hfexpr expr_54 (closed_54 v) (closed_54 v) = Some (Gval (Fuint 32) (word_54 v))). apply closed_54_value. Qed.
Lemma source_55 : find_driver 55 generated_module_0_stmts_0 = Some expr_55.
Proof. vm_compute. reflexivity. Qed.
Transparent word_55.
Lemma closed_55_value v : eval_hfexpr expr_55 (closed_55 v) (closed_55 v) = Some (Gval (Fuint 1) (word_55 v)).
Proof. unfold word_55, closed_55, expr_55, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_55.
Lemma node_55_value v : eval_hfexpr expr_55 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_55 v)).
Proof. change (eval_hfexpr expr_55 (closed_55 v) (closed_55 v) = Some (Gval (Fuint 1) (word_55 v))). apply closed_55_value. Qed.
Lemma source_56 : find_driver 56 generated_module_0_stmts_0 = Some expr_56.
Proof. vm_compute. reflexivity. Qed.
Transparent word_56.
Lemma closed_56_value v : eval_hfexpr expr_56 (closed_56 v) (closed_56 v) = Some (Gval (Fuint 16) (word_56 v)).
Proof. unfold word_56, closed_56, expr_56, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_56.
Lemma node_56_value v : eval_hfexpr expr_56 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_56 v)).
Proof. change (eval_hfexpr expr_56 (closed_56 v) (closed_56 v) = Some (Gval (Fuint 16) (word_56 v))). apply closed_56_value. Qed.
Lemma source_57 : find_driver 57 generated_module_0_stmts_0 = Some expr_57.
Proof. vm_compute. reflexivity. Qed.
Transparent word_57.
Lemma closed_57_value v : eval_hfexpr expr_57 (closed_57 v) (closed_57 v) = Some (Gval (Fuint 16) (word_57 v)).
Proof. unfold word_57, closed_57, expr_57, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_57.
Lemma node_57_value v : eval_hfexpr expr_57 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_57 v)).
Proof. change (eval_hfexpr expr_57 (closed_57 v) (closed_57 v) = Some (Gval (Fuint 16) (word_57 v))). apply closed_57_value. Qed.
Lemma source_58 : find_driver 58 generated_module_0_stmts_0 = Some expr_58.
Proof. vm_compute. reflexivity. Qed.
Transparent word_58.
Lemma closed_58_value v : eval_hfexpr expr_58 (closed_58 v) (closed_58 v) = Some (Gval (Fuint 1) (word_58 v)).
Proof. unfold word_58, closed_58, expr_58, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_58.
Lemma node_58_value v : eval_hfexpr expr_58 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_58 v)).
Proof. change (eval_hfexpr expr_58 (closed_58 v) (closed_58 v) = Some (Gval (Fuint 1) (word_58 v))). apply closed_58_value. Qed.
Lemma source_59 : find_driver 59 generated_module_0_stmts_0 = Some expr_59.
Proof. vm_compute. reflexivity. Qed.
Transparent word_59.
Lemma closed_59_value v : eval_hfexpr expr_59 (closed_59 v) (closed_59 v) = Some (Gval (Fuint 8) (word_59 v)).
Proof. unfold word_59, closed_59, expr_59, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_59.
Lemma node_59_value v : eval_hfexpr expr_59 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_59 v)).
Proof. change (eval_hfexpr expr_59 (closed_59 v) (closed_59 v) = Some (Gval (Fuint 8) (word_59 v))). apply closed_59_value. Qed.
Lemma source_60 : find_driver 60 generated_module_0_stmts_0 = Some expr_60.
Proof. vm_compute. reflexivity. Qed.
Transparent word_60.
Lemma closed_60_value v : eval_hfexpr expr_60 (closed_60 v) (closed_60 v) = Some (Gval (Fuint 8) (word_60 v)).
Proof. unfold word_60, closed_60, expr_60, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_60.
Lemma node_60_value v : eval_hfexpr expr_60 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_60 v)).
Proof. change (eval_hfexpr expr_60 (closed_60 v) (closed_60 v) = Some (Gval (Fuint 8) (word_60 v))). apply closed_60_value. Qed.
Lemma source_61 : find_driver 61 generated_module_0_stmts_0 = Some expr_61.
Proof. vm_compute. reflexivity. Qed.
Transparent word_61.
Lemma closed_61_value v : eval_hfexpr expr_61 (closed_61 v) (closed_61 v) = Some (Gval (Fuint 1) (word_61 v)).
Proof. unfold word_61, closed_61, expr_61, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_61.
Lemma node_61_value v : eval_hfexpr expr_61 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_61 v)).
Proof. change (eval_hfexpr expr_61 (closed_61 v) (closed_61 v) = Some (Gval (Fuint 1) (word_61 v))). apply closed_61_value. Qed.
Lemma source_62 : find_driver 62 generated_module_0_stmts_0 = Some expr_62.
Proof. vm_compute. reflexivity. Qed.
Transparent word_62.
Lemma closed_62_value v : eval_hfexpr expr_62 (closed_62 v) (closed_62 v) = Some (Gval (Fuint 4) (word_62 v)).
Proof. unfold word_62, closed_62, expr_62, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_62.
Lemma node_62_value v : eval_hfexpr expr_62 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_62 v)).
Proof. change (eval_hfexpr expr_62 (closed_62 v) (closed_62 v) = Some (Gval (Fuint 4) (word_62 v))). apply closed_62_value. Qed.
Lemma source_63 : find_driver 63 generated_module_0_stmts_0 = Some expr_63.
Proof. vm_compute. reflexivity. Qed.
Transparent word_63.
Lemma closed_63_value v : eval_hfexpr expr_63 (closed_63 v) (closed_63 v) = Some (Gval (Fuint 4) (word_63 v)).
Proof. unfold word_63, closed_63, expr_63, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_63.
Lemma node_63_value v : eval_hfexpr expr_63 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_63 v)).
Proof. change (eval_hfexpr expr_63 (closed_63 v) (closed_63 v) = Some (Gval (Fuint 4) (word_63 v))). apply closed_63_value. Qed.
Lemma source_64 : find_driver 64 generated_module_0_stmts_0 = Some expr_64.
Proof. vm_compute. reflexivity. Qed.
Transparent word_64.
Lemma closed_64_value v : eval_hfexpr expr_64 (closed_64 v) (closed_64 v) = Some (Gval (Fuint 1) (word_64 v)).
Proof. unfold word_64, closed_64, expr_64, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_64.
Lemma node_64_value v : eval_hfexpr expr_64 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_64 v)).
Proof. change (eval_hfexpr expr_64 (closed_64 v) (closed_64 v) = Some (Gval (Fuint 1) (word_64 v))). apply closed_64_value. Qed.
Lemma source_65 : find_driver 65 generated_module_0_stmts_0 = Some expr_65.
Proof. vm_compute. reflexivity. Qed.
Transparent word_65.
Lemma closed_65_value v : eval_hfexpr expr_65 (closed_65 v) (closed_65 v) = Some (Gval (Fuint 1) (word_65 v)).
Proof. unfold word_65, closed_65, expr_65, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_65.
Lemma node_65_value v : eval_hfexpr expr_65 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_65 v)).
Proof. change (eval_hfexpr expr_65 (closed_65 v) (closed_65 v) = Some (Gval (Fuint 1) (word_65 v))). apply closed_65_value. Qed.
Lemma source_66 : find_driver 66 generated_module_0_stmts_0 = Some expr_66.
Proof. vm_compute. reflexivity. Qed.
Transparent word_66.
Lemma closed_66_value v : eval_hfexpr expr_66 (closed_66 v) (closed_66 v) = Some (Gval (Fuint 1) (word_66 v)).
Proof. unfold word_66, closed_66, expr_66, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_66.
Lemma node_66_value v : eval_hfexpr expr_66 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_66 v)).
Proof. change (eval_hfexpr expr_66 (closed_66 v) (closed_66 v) = Some (Gval (Fuint 1) (word_66 v))). apply closed_66_value. Qed.
Lemma source_67 : find_driver 67 generated_module_0_stmts_0 = Some expr_67.
Proof. vm_compute. reflexivity. Qed.
Transparent word_67.
Lemma closed_67_value v : eval_hfexpr expr_67 (closed_67 v) (closed_67 v) = Some (Gval (Fuint 1) (word_67 v)).
Proof. unfold word_67, closed_67, expr_67, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_67.
Lemma node_67_value v : eval_hfexpr expr_67 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_67 v)).
Proof. change (eval_hfexpr expr_67 (closed_67 v) (closed_67 v) = Some (Gval (Fuint 1) (word_67 v))). apply closed_67_value. Qed.
Lemma source_68 : find_driver 68 generated_module_0_stmts_0 = Some expr_68.
Proof. vm_compute. reflexivity. Qed.
Transparent word_68.
Lemma closed_68_value v : eval_hfexpr expr_68 (closed_68 v) (closed_68 v) = Some (Gval (Fuint 2) (word_68 v)).
Proof. unfold word_68, closed_68, expr_68, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_68.
Lemma node_68_value v : eval_hfexpr expr_68 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_68 v)).
Proof. change (eval_hfexpr expr_68 (closed_68 v) (closed_68 v) = Some (Gval (Fuint 2) (word_68 v))). apply closed_68_value. Qed.
Lemma source_69 : find_driver 69 generated_module_0_stmts_0 = Some expr_69.
Proof. vm_compute. reflexivity. Qed.
Transparent word_69.
Lemma closed_69_value v : eval_hfexpr expr_69 (closed_69 v) (closed_69 v) = Some (Gval (Fuint 2) (word_69 v)).
Proof. unfold word_69, closed_69, expr_69, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_69.
Lemma node_69_value v : eval_hfexpr expr_69 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_69 v)).
Proof. change (eval_hfexpr expr_69 (closed_69 v) (closed_69 v) = Some (Gval (Fuint 2) (word_69 v))). apply closed_69_value. Qed.
Lemma source_70 : find_driver 70 generated_module_0_stmts_0 = Some expr_70.
Proof. vm_compute. reflexivity. Qed.
Transparent word_70.
Lemma closed_70_value v : eval_hfexpr expr_70 (closed_70 v) (closed_70 v) = Some (Gval (Fuint 1) (word_70 v)).
Proof. unfold word_70, closed_70, expr_70, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_70.
Lemma node_70_value v : eval_hfexpr expr_70 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_70 v)).
Proof. change (eval_hfexpr expr_70 (closed_70 v) (closed_70 v) = Some (Gval (Fuint 1) (word_70 v))). apply closed_70_value. Qed.
Lemma source_71 : find_driver 71 generated_module_0_stmts_0 = Some expr_71.
Proof. vm_compute. reflexivity. Qed.
Transparent word_71.
Lemma closed_71_value v : eval_hfexpr expr_71 (closed_71 v) (closed_71 v) = Some (Gval (Fuint 1) (word_71 v)).
Proof. unfold word_71, closed_71, expr_71, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_71.
Lemma node_71_value v : eval_hfexpr expr_71 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_71 v)).
Proof. change (eval_hfexpr expr_71 (closed_71 v) (closed_71 v) = Some (Gval (Fuint 1) (word_71 v))). apply closed_71_value. Qed.
Lemma source_72 : find_driver 72 generated_module_0_stmts_0 = Some expr_72.
Proof. vm_compute. reflexivity. Qed.
Transparent word_72.
Lemma closed_72_value v : eval_hfexpr expr_72 (closed_72 v) (closed_72 v) = Some (Gval (Fuint 1) (word_72 v)).
Proof. unfold word_72, closed_72, expr_72, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_72.
Lemma node_72_value v : eval_hfexpr expr_72 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_72 v)).
Proof. change (eval_hfexpr expr_72 (closed_72 v) (closed_72 v) = Some (Gval (Fuint 1) (word_72 v))). apply closed_72_value. Qed.
Lemma source_73 : find_driver 73 generated_module_0_stmts_0 = Some expr_73.
Proof. vm_compute. reflexivity. Qed.
Transparent word_73.
Lemma closed_73_value v : eval_hfexpr expr_73 (closed_73 v) (closed_73 v) = Some (Gval (Fuint 2) (word_73 v)).
Proof. unfold word_73, closed_73, expr_73, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_73.
Lemma node_73_value v : eval_hfexpr expr_73 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_73 v)).
Proof. change (eval_hfexpr expr_73 (closed_73 v) (closed_73 v) = Some (Gval (Fuint 2) (word_73 v))). apply closed_73_value. Qed.
Lemma source_74 : find_driver 74 generated_module_0_stmts_0 = Some expr_74.
Proof. vm_compute. reflexivity. Qed.
Transparent word_74.
Lemma closed_74_value v : eval_hfexpr expr_74 (closed_74 v) (closed_74 v) = Some (Gval (Fuint 2) (word_74 v)).
Proof. unfold word_74, closed_74, expr_74, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_74.
Lemma node_74_value v : eval_hfexpr expr_74 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_74 v)).
Proof. change (eval_hfexpr expr_74 (closed_74 v) (closed_74 v) = Some (Gval (Fuint 2) (word_74 v))). apply closed_74_value. Qed.
Lemma source_75 : find_driver 75 generated_module_0_stmts_0 = Some expr_75.
Proof. vm_compute. reflexivity. Qed.
Transparent word_75.
Lemma closed_75_value v : eval_hfexpr expr_75 (closed_75 v) (closed_75 v) = Some (Gval (Fuint 2) (word_75 v)).
Proof. unfold word_75, closed_75, expr_75, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_75.
Lemma node_75_value v : eval_hfexpr expr_75 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_75 v)).
Proof. change (eval_hfexpr expr_75 (closed_75 v) (closed_75 v) = Some (Gval (Fuint 2) (word_75 v))). apply closed_75_value. Qed.
Lemma source_76 : find_driver 76 generated_module_0_stmts_0 = Some expr_76.
Proof. vm_compute. reflexivity. Qed.
Transparent word_76.
Lemma closed_76_value v : eval_hfexpr expr_76 (closed_76 v) (closed_76 v) = Some (Gval (Fuint 3) (word_76 v)).
Proof. unfold word_76, closed_76, expr_76, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_76.
Lemma node_76_value v : eval_hfexpr expr_76 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_76 v)).
Proof. change (eval_hfexpr expr_76 (closed_76 v) (closed_76 v) = Some (Gval (Fuint 3) (word_76 v))). apply closed_76_value. Qed.
Lemma source_77 : find_driver 77 generated_module_0_stmts_0 = Some expr_77.
Proof. vm_compute. reflexivity. Qed.
Transparent word_77.
Lemma closed_77_value v : eval_hfexpr expr_77 (closed_77 v) (closed_77 v) = Some (Gval (Fuint 4) (word_77 v)).
Proof. unfold word_77, closed_77, expr_77, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_77.
Lemma node_77_value v : eval_hfexpr expr_77 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_77 v)).
Proof. change (eval_hfexpr expr_77 (closed_77 v) (closed_77 v) = Some (Gval (Fuint 4) (word_77 v))). apply closed_77_value. Qed.
Lemma source_78 : find_driver 78 generated_module_0_stmts_0 = Some expr_78.
Proof. vm_compute. reflexivity. Qed.
Transparent word_78.
Lemma closed_78_value v : eval_hfexpr expr_78 (closed_78 v) (closed_78 v) = Some (Gval (Fuint 4) (word_78 v)).
Proof. unfold word_78, closed_78, expr_78, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_78.
Lemma node_78_value v : eval_hfexpr expr_78 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_78 v)).
Proof. change (eval_hfexpr expr_78 (closed_78 v) (closed_78 v) = Some (Gval (Fuint 4) (word_78 v))). apply closed_78_value. Qed.
Lemma source_79 : find_driver 79 generated_module_0_stmts_0 = Some expr_79.
Proof. vm_compute. reflexivity. Qed.
Transparent word_79.
Lemma closed_79_value v : eval_hfexpr expr_79 (closed_79 v) (closed_79 v) = Some (Gval (Fuint 1) (word_79 v)).
Proof. unfold word_79, closed_79, expr_79, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_79.
Lemma node_79_value v : eval_hfexpr expr_79 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_79 v)).
Proof. change (eval_hfexpr expr_79 (closed_79 v) (closed_79 v) = Some (Gval (Fuint 1) (word_79 v))). apply closed_79_value. Qed.
Lemma source_80 : find_driver 80 generated_module_0_stmts_0 = Some expr_80.
Proof. vm_compute. reflexivity. Qed.
Transparent word_80.
Lemma closed_80_value v : eval_hfexpr expr_80 (closed_80 v) (closed_80 v) = Some (Gval (Fuint 1) (word_80 v)).
Proof. unfold word_80, closed_80, expr_80, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_80.
Lemma node_80_value v : eval_hfexpr expr_80 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_80 v)).
Proof. change (eval_hfexpr expr_80 (closed_80 v) (closed_80 v) = Some (Gval (Fuint 1) (word_80 v))). apply closed_80_value. Qed.
Lemma source_81 : find_driver 81 generated_module_0_stmts_0 = Some expr_81.
Proof. vm_compute. reflexivity. Qed.
Transparent word_81.
Lemma closed_81_value v : eval_hfexpr expr_81 (closed_81 v) (closed_81 v) = Some (Gval (Fuint 1) (word_81 v)).
Proof. unfold word_81, closed_81, expr_81, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_81.
Lemma node_81_value v : eval_hfexpr expr_81 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_81 v)).
Proof. change (eval_hfexpr expr_81 (closed_81 v) (closed_81 v) = Some (Gval (Fuint 1) (word_81 v))). apply closed_81_value. Qed.
Lemma source_82 : find_driver 82 generated_module_0_stmts_0 = Some expr_82.
Proof. vm_compute. reflexivity. Qed.
Transparent word_82.
Lemma closed_82_value v : eval_hfexpr expr_82 (closed_82 v) (closed_82 v) = Some (Gval (Fuint 1) (word_82 v)).
Proof. unfold word_82, closed_82, expr_82, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_82.
Lemma node_82_value v : eval_hfexpr expr_82 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_82 v)).
Proof. change (eval_hfexpr expr_82 (closed_82 v) (closed_82 v) = Some (Gval (Fuint 1) (word_82 v))). apply closed_82_value. Qed.
Lemma source_83 : find_driver 83 generated_module_0_stmts_0 = Some expr_83.
Proof. vm_compute. reflexivity. Qed.
Transparent word_83.
Lemma closed_83_value v : eval_hfexpr expr_83 (closed_83 v) (closed_83 v) = Some (Gval (Fuint 2) (word_83 v)).
Proof. unfold word_83, closed_83, expr_83, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_83.
Lemma node_83_value v : eval_hfexpr expr_83 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_83 v)).
Proof. change (eval_hfexpr expr_83 (closed_83 v) (closed_83 v) = Some (Gval (Fuint 2) (word_83 v))). apply closed_83_value. Qed.
Lemma source_84 : find_driver 84 generated_module_0_stmts_0 = Some expr_84.
Proof. vm_compute. reflexivity. Qed.
Transparent word_84.
Lemma closed_84_value v : eval_hfexpr expr_84 (closed_84 v) (closed_84 v) = Some (Gval (Fuint 2) (word_84 v)).
Proof. unfold word_84, closed_84, expr_84, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_84.
Lemma node_84_value v : eval_hfexpr expr_84 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_84 v)).
Proof. change (eval_hfexpr expr_84 (closed_84 v) (closed_84 v) = Some (Gval (Fuint 2) (word_84 v))). apply closed_84_value. Qed.
Lemma source_85 : find_driver 85 generated_module_0_stmts_0 = Some expr_85.
Proof. vm_compute. reflexivity. Qed.
Transparent word_85.
Lemma closed_85_value v : eval_hfexpr expr_85 (closed_85 v) (closed_85 v) = Some (Gval (Fuint 1) (word_85 v)).
Proof. unfold word_85, closed_85, expr_85, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_85.
Lemma node_85_value v : eval_hfexpr expr_85 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_85 v)).
Proof. change (eval_hfexpr expr_85 (closed_85 v) (closed_85 v) = Some (Gval (Fuint 1) (word_85 v))). apply closed_85_value. Qed.
Lemma source_86 : find_driver 86 generated_module_0_stmts_0 = Some expr_86.
Proof. vm_compute. reflexivity. Qed.
Transparent word_86.
Lemma closed_86_value v : eval_hfexpr expr_86 (closed_86 v) (closed_86 v) = Some (Gval (Fuint 1) (word_86 v)).
Proof. unfold word_86, closed_86, expr_86, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_86.
Lemma node_86_value v : eval_hfexpr expr_86 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_86 v)).
Proof. change (eval_hfexpr expr_86 (closed_86 v) (closed_86 v) = Some (Gval (Fuint 1) (word_86 v))). apply closed_86_value. Qed.
Lemma source_87 : find_driver 87 generated_module_0_stmts_0 = Some expr_87.
Proof. vm_compute. reflexivity. Qed.
Transparent word_87.
Lemma closed_87_value v : eval_hfexpr expr_87 (closed_87 v) (closed_87 v) = Some (Gval (Fuint 1) (word_87 v)).
Proof. unfold word_87, closed_87, expr_87, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_87.
Lemma node_87_value v : eval_hfexpr expr_87 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_87 v)).
Proof. change (eval_hfexpr expr_87 (closed_87 v) (closed_87 v) = Some (Gval (Fuint 1) (word_87 v))). apply closed_87_value. Qed.
Lemma source_88 : find_driver 88 generated_module_0_stmts_0 = Some expr_88.
Proof. vm_compute. reflexivity. Qed.
Transparent word_88.
Lemma closed_88_value v : eval_hfexpr expr_88 (closed_88 v) (closed_88 v) = Some (Gval (Fuint 2) (word_88 v)).
Proof. unfold word_88, closed_88, expr_88, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_88.
Lemma node_88_value v : eval_hfexpr expr_88 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_88 v)).
Proof. change (eval_hfexpr expr_88 (closed_88 v) (closed_88 v) = Some (Gval (Fuint 2) (word_88 v))). apply closed_88_value. Qed.
Lemma source_89 : find_driver 89 generated_module_0_stmts_0 = Some expr_89.
Proof. vm_compute. reflexivity. Qed.
Transparent word_89.
Lemma closed_89_value v : eval_hfexpr expr_89 (closed_89 v) (closed_89 v) = Some (Gval (Fuint 2) (word_89 v)).
Proof. unfold word_89, closed_89, expr_89, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_89.
Lemma node_89_value v : eval_hfexpr expr_89 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_89 v)).
Proof. change (eval_hfexpr expr_89 (closed_89 v) (closed_89 v) = Some (Gval (Fuint 2) (word_89 v))). apply closed_89_value. Qed.
Lemma source_90 : find_driver 90 generated_module_0_stmts_0 = Some expr_90.
Proof. vm_compute. reflexivity. Qed.
Transparent word_90.
Lemma closed_90_value v : eval_hfexpr expr_90 (closed_90 v) (closed_90 v) = Some (Gval (Fuint 2) (word_90 v)).
Proof. unfold word_90, closed_90, expr_90, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_90.
Lemma node_90_value v : eval_hfexpr expr_90 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_90 v)).
Proof. change (eval_hfexpr expr_90 (closed_90 v) (closed_90 v) = Some (Gval (Fuint 2) (word_90 v))). apply closed_90_value. Qed.
Lemma source_91 : find_driver 91 generated_module_0_stmts_0 = Some expr_91.
Proof. vm_compute. reflexivity. Qed.
Transparent word_91.
Lemma closed_91_value v : eval_hfexpr expr_91 (closed_91 v) (closed_91 v) = Some (Gval (Fuint 3) (word_91 v)).
Proof. unfold word_91, closed_91, expr_91, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_91.
Lemma node_91_value v : eval_hfexpr expr_91 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_91 v)).
Proof. change (eval_hfexpr expr_91 (closed_91 v) (closed_91 v) = Some (Gval (Fuint 3) (word_91 v))). apply closed_91_value. Qed.
Lemma source_92 : find_driver 92 generated_module_0_stmts_0 = Some expr_92.
Proof. vm_compute. reflexivity. Qed.
Transparent word_92.
Lemma closed_92_value v : eval_hfexpr expr_92 (closed_92 v) (closed_92 v) = Some (Gval (Fuint 3) (word_92 v)).
Proof. unfold word_92, closed_92, expr_92, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_92.
Lemma node_92_value v : eval_hfexpr expr_92 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_92 v)).
Proof. change (eval_hfexpr expr_92 (closed_92 v) (closed_92 v) = Some (Gval (Fuint 3) (word_92 v))). apply closed_92_value. Qed.
Lemma source_93 : find_driver 93 generated_module_0_stmts_0 = Some expr_93.
Proof. vm_compute. reflexivity. Qed.
Transparent word_93.
Lemma closed_93_value v : eval_hfexpr expr_93 (closed_93 v) (closed_93 v) = Some (Gval (Fuint 4) (word_93 v)).
Proof. unfold word_93, closed_93, expr_93, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_93.
Lemma node_93_value v : eval_hfexpr expr_93 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_93 v)).
Proof. change (eval_hfexpr expr_93 (closed_93 v) (closed_93 v) = Some (Gval (Fuint 4) (word_93 v))). apply closed_93_value. Qed.
Lemma source_94 : find_driver 94 generated_module_0_stmts_0 = Some expr_94.
Proof. vm_compute. reflexivity. Qed.
Transparent word_94.
Lemma closed_94_value v : eval_hfexpr expr_94 (closed_94 v) (closed_94 v) = Some (Gval (Fuint 8) (word_94 v)).
Proof. unfold word_94, closed_94, expr_94, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_94.
Lemma node_94_value v : eval_hfexpr expr_94 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_94 v)).
Proof. change (eval_hfexpr expr_94 (closed_94 v) (closed_94 v) = Some (Gval (Fuint 8) (word_94 v))). apply closed_94_value. Qed.
Lemma source_95 : find_driver 95 generated_module_0_stmts_0 = Some expr_95.
Proof. vm_compute. reflexivity. Qed.
Transparent word_95.
Lemma closed_95_value v : eval_hfexpr expr_95 (closed_95 v) (closed_95 v) = Some (Gval (Fuint 8) (word_95 v)).
Proof. unfold word_95, closed_95, expr_95, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_95.
Lemma node_95_value v : eval_hfexpr expr_95 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_95 v)).
Proof. change (eval_hfexpr expr_95 (closed_95 v) (closed_95 v) = Some (Gval (Fuint 8) (word_95 v))). apply closed_95_value. Qed.
Lemma source_96 : find_driver 96 generated_module_0_stmts_0 = Some expr_96.
Proof. vm_compute. reflexivity. Qed.
Transparent word_96.
Lemma closed_96_value v : eval_hfexpr expr_96 (closed_96 v) (closed_96 v) = Some (Gval (Fuint 1) (word_96 v)).
Proof. unfold word_96, closed_96, expr_96, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_96.
Lemma node_96_value v : eval_hfexpr expr_96 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_96 v)).
Proof. change (eval_hfexpr expr_96 (closed_96 v) (closed_96 v) = Some (Gval (Fuint 1) (word_96 v))). apply closed_96_value. Qed.
Lemma source_97 : find_driver 97 generated_module_0_stmts_0 = Some expr_97.
Proof. vm_compute. reflexivity. Qed.
Transparent word_97.
Lemma closed_97_value v : eval_hfexpr expr_97 (closed_97 v) (closed_97 v) = Some (Gval (Fuint 4) (word_97 v)).
Proof. unfold word_97, closed_97, expr_97, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_97.
Lemma node_97_value v : eval_hfexpr expr_97 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_97 v)).
Proof. change (eval_hfexpr expr_97 (closed_97 v) (closed_97 v) = Some (Gval (Fuint 4) (word_97 v))). apply closed_97_value. Qed.
Lemma source_98 : find_driver 98 generated_module_0_stmts_0 = Some expr_98.
Proof. vm_compute. reflexivity. Qed.
Transparent word_98.
Lemma closed_98_value v : eval_hfexpr expr_98 (closed_98 v) (closed_98 v) = Some (Gval (Fuint 4) (word_98 v)).
Proof. unfold word_98, closed_98, expr_98, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_98.
Lemma node_98_value v : eval_hfexpr expr_98 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_98 v)).
Proof. change (eval_hfexpr expr_98 (closed_98 v) (closed_98 v) = Some (Gval (Fuint 4) (word_98 v))). apply closed_98_value. Qed.
Lemma source_99 : find_driver 99 generated_module_0_stmts_0 = Some expr_99.
Proof. vm_compute. reflexivity. Qed.
Transparent word_99.
Lemma closed_99_value v : eval_hfexpr expr_99 (closed_99 v) (closed_99 v) = Some (Gval (Fuint 1) (word_99 v)).
Proof. unfold word_99, closed_99, expr_99, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_99.
Lemma node_99_value v : eval_hfexpr expr_99 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_99 v)).
Proof. change (eval_hfexpr expr_99 (closed_99 v) (closed_99 v) = Some (Gval (Fuint 1) (word_99 v))). apply closed_99_value. Qed.
Lemma source_100 : find_driver 100 generated_module_0_stmts_0 = Some expr_100.
Proof. vm_compute. reflexivity. Qed.
Transparent word_100.
Lemma closed_100_value v : eval_hfexpr expr_100 (closed_100 v) (closed_100 v) = Some (Gval (Fuint 1) (word_100 v)).
Proof. unfold word_100, closed_100, expr_100, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_100.
Lemma node_100_value v : eval_hfexpr expr_100 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_100 v)).
Proof. change (eval_hfexpr expr_100 (closed_100 v) (closed_100 v) = Some (Gval (Fuint 1) (word_100 v))). apply closed_100_value. Qed.
Lemma source_101 : find_driver 101 generated_module_0_stmts_0 = Some expr_101.
Proof. vm_compute. reflexivity. Qed.
Transparent word_101.
Lemma closed_101_value v : eval_hfexpr expr_101 (closed_101 v) (closed_101 v) = Some (Gval (Fuint 1) (word_101 v)).
Proof. unfold word_101, closed_101, expr_101, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_101.
Lemma node_101_value v : eval_hfexpr expr_101 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_101 v)).
Proof. change (eval_hfexpr expr_101 (closed_101 v) (closed_101 v) = Some (Gval (Fuint 1) (word_101 v))). apply closed_101_value. Qed.
Lemma source_102 : find_driver 102 generated_module_0_stmts_0 = Some expr_102.
Proof. vm_compute. reflexivity. Qed.
Transparent word_102.
Lemma closed_102_value v : eval_hfexpr expr_102 (closed_102 v) (closed_102 v) = Some (Gval (Fuint 1) (word_102 v)).
Proof. unfold word_102, closed_102, expr_102, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_102.
Lemma node_102_value v : eval_hfexpr expr_102 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_102 v)).
Proof. change (eval_hfexpr expr_102 (closed_102 v) (closed_102 v) = Some (Gval (Fuint 1) (word_102 v))). apply closed_102_value. Qed.
Lemma source_103 : find_driver 103 generated_module_0_stmts_0 = Some expr_103.
Proof. vm_compute. reflexivity. Qed.
Transparent word_103.
Lemma closed_103_value v : eval_hfexpr expr_103 (closed_103 v) (closed_103 v) = Some (Gval (Fuint 2) (word_103 v)).
Proof. unfold word_103, closed_103, expr_103, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_103.
Lemma node_103_value v : eval_hfexpr expr_103 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_103 v)).
Proof. change (eval_hfexpr expr_103 (closed_103 v) (closed_103 v) = Some (Gval (Fuint 2) (word_103 v))). apply closed_103_value. Qed.
Lemma source_104 : find_driver 104 generated_module_0_stmts_0 = Some expr_104.
Proof. vm_compute. reflexivity. Qed.
Transparent word_104.
Lemma closed_104_value v : eval_hfexpr expr_104 (closed_104 v) (closed_104 v) = Some (Gval (Fuint 2) (word_104 v)).
Proof. unfold word_104, closed_104, expr_104, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_104.
Lemma node_104_value v : eval_hfexpr expr_104 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_104 v)).
Proof. change (eval_hfexpr expr_104 (closed_104 v) (closed_104 v) = Some (Gval (Fuint 2) (word_104 v))). apply closed_104_value. Qed.
Lemma source_105 : find_driver 105 generated_module_0_stmts_0 = Some expr_105.
Proof. vm_compute. reflexivity. Qed.
Transparent word_105.
Lemma closed_105_value v : eval_hfexpr expr_105 (closed_105 v) (closed_105 v) = Some (Gval (Fuint 1) (word_105 v)).
Proof. unfold word_105, closed_105, expr_105, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_105.
Lemma node_105_value v : eval_hfexpr expr_105 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_105 v)).
Proof. change (eval_hfexpr expr_105 (closed_105 v) (closed_105 v) = Some (Gval (Fuint 1) (word_105 v))). apply closed_105_value. Qed.
Lemma source_106 : find_driver 106 generated_module_0_stmts_0 = Some expr_106.
Proof. vm_compute. reflexivity. Qed.
Transparent word_106.
Lemma closed_106_value v : eval_hfexpr expr_106 (closed_106 v) (closed_106 v) = Some (Gval (Fuint 1) (word_106 v)).
Proof. unfold word_106, closed_106, expr_106, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_106.
Lemma node_106_value v : eval_hfexpr expr_106 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_106 v)).
Proof. change (eval_hfexpr expr_106 (closed_106 v) (closed_106 v) = Some (Gval (Fuint 1) (word_106 v))). apply closed_106_value. Qed.
Lemma source_107 : find_driver 107 generated_module_0_stmts_0 = Some expr_107.
Proof. vm_compute. reflexivity. Qed.
Transparent word_107.
Lemma closed_107_value v : eval_hfexpr expr_107 (closed_107 v) (closed_107 v) = Some (Gval (Fuint 1) (word_107 v)).
Proof. unfold word_107, closed_107, expr_107, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_107.
Lemma node_107_value v : eval_hfexpr expr_107 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_107 v)).
Proof. change (eval_hfexpr expr_107 (closed_107 v) (closed_107 v) = Some (Gval (Fuint 1) (word_107 v))). apply closed_107_value. Qed.
Lemma source_108 : find_driver 108 generated_module_0_stmts_0 = Some expr_108.
Proof. vm_compute. reflexivity. Qed.
Transparent word_108.
Lemma closed_108_value v : eval_hfexpr expr_108 (closed_108 v) (closed_108 v) = Some (Gval (Fuint 2) (word_108 v)).
Proof. unfold word_108, closed_108, expr_108, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_108.
Lemma node_108_value v : eval_hfexpr expr_108 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_108 v)).
Proof. change (eval_hfexpr expr_108 (closed_108 v) (closed_108 v) = Some (Gval (Fuint 2) (word_108 v))). apply closed_108_value. Qed.
Lemma source_109 : find_driver 109 generated_module_0_stmts_0 = Some expr_109.
Proof. vm_compute. reflexivity. Qed.
Transparent word_109.
Lemma closed_109_value v : eval_hfexpr expr_109 (closed_109 v) (closed_109 v) = Some (Gval (Fuint 2) (word_109 v)).
Proof. unfold word_109, closed_109, expr_109, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_109.
Lemma node_109_value v : eval_hfexpr expr_109 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_109 v)).
Proof. change (eval_hfexpr expr_109 (closed_109 v) (closed_109 v) = Some (Gval (Fuint 2) (word_109 v))). apply closed_109_value. Qed.
Lemma source_110 : find_driver 110 generated_module_0_stmts_0 = Some expr_110.
Proof. vm_compute. reflexivity. Qed.
Transparent word_110.
Lemma closed_110_value v : eval_hfexpr expr_110 (closed_110 v) (closed_110 v) = Some (Gval (Fuint 2) (word_110 v)).
Proof. unfold word_110, closed_110, expr_110, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_110.
Lemma node_110_value v : eval_hfexpr expr_110 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_110 v)).
Proof. change (eval_hfexpr expr_110 (closed_110 v) (closed_110 v) = Some (Gval (Fuint 2) (word_110 v))). apply closed_110_value. Qed.
Lemma source_111 : find_driver 111 generated_module_0_stmts_0 = Some expr_111.
Proof. vm_compute. reflexivity. Qed.
Transparent word_111.
Lemma closed_111_value v : eval_hfexpr expr_111 (closed_111 v) (closed_111 v) = Some (Gval (Fuint 3) (word_111 v)).
Proof. unfold word_111, closed_111, expr_111, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_111.
Lemma node_111_value v : eval_hfexpr expr_111 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_111 v)).
Proof. change (eval_hfexpr expr_111 (closed_111 v) (closed_111 v) = Some (Gval (Fuint 3) (word_111 v))). apply closed_111_value. Qed.
Lemma source_112 : find_driver 112 generated_module_0_stmts_0 = Some expr_112.
Proof. vm_compute. reflexivity. Qed.
Transparent word_112.
Lemma closed_112_value v : eval_hfexpr expr_112 (closed_112 v) (closed_112 v) = Some (Gval (Fuint 4) (word_112 v)).
Proof. unfold word_112, closed_112, expr_112, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_112.
Lemma node_112_value v : eval_hfexpr expr_112 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_112 v)).
Proof. change (eval_hfexpr expr_112 (closed_112 v) (closed_112 v) = Some (Gval (Fuint 4) (word_112 v))). apply closed_112_value. Qed.
Lemma source_113 : find_driver 113 generated_module_0_stmts_0 = Some expr_113.
Proof. vm_compute. reflexivity. Qed.
Transparent word_113.
Lemma closed_113_value v : eval_hfexpr expr_113 (closed_113 v) (closed_113 v) = Some (Gval (Fuint 4) (word_113 v)).
Proof. unfold word_113, closed_113, expr_113, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_113.
Lemma node_113_value v : eval_hfexpr expr_113 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_113 v)).
Proof. change (eval_hfexpr expr_113 (closed_113 v) (closed_113 v) = Some (Gval (Fuint 4) (word_113 v))). apply closed_113_value. Qed.
Lemma source_114 : find_driver 114 generated_module_0_stmts_0 = Some expr_114.
Proof. vm_compute. reflexivity. Qed.
Transparent word_114.
Lemma closed_114_value v : eval_hfexpr expr_114 (closed_114 v) (closed_114 v) = Some (Gval (Fuint 1) (word_114 v)).
Proof. unfold word_114, closed_114, expr_114, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_114.
Lemma node_114_value v : eval_hfexpr expr_114 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_114 v)).
Proof. change (eval_hfexpr expr_114 (closed_114 v) (closed_114 v) = Some (Gval (Fuint 1) (word_114 v))). apply closed_114_value. Qed.
Lemma source_115 : find_driver 115 generated_module_0_stmts_0 = Some expr_115.
Proof. vm_compute. reflexivity. Qed.
Transparent word_115.
Lemma closed_115_value v : eval_hfexpr expr_115 (closed_115 v) (closed_115 v) = Some (Gval (Fuint 1) (word_115 v)).
Proof. unfold word_115, closed_115, expr_115, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_115.
Lemma node_115_value v : eval_hfexpr expr_115 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_115 v)).
Proof. change (eval_hfexpr expr_115 (closed_115 v) (closed_115 v) = Some (Gval (Fuint 1) (word_115 v))). apply closed_115_value. Qed.
Lemma source_116 : find_driver 116 generated_module_0_stmts_0 = Some expr_116.
Proof. vm_compute. reflexivity. Qed.
Transparent word_116.
Lemma closed_116_value v : eval_hfexpr expr_116 (closed_116 v) (closed_116 v) = Some (Gval (Fuint 1) (word_116 v)).
Proof. unfold word_116, closed_116, expr_116, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_116.
Lemma node_116_value v : eval_hfexpr expr_116 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_116 v)).
Proof. change (eval_hfexpr expr_116 (closed_116 v) (closed_116 v) = Some (Gval (Fuint 1) (word_116 v))). apply closed_116_value. Qed.
Lemma source_117 : find_driver 117 generated_module_0_stmts_0 = Some expr_117.
Proof. vm_compute. reflexivity. Qed.
Transparent word_117.
Lemma closed_117_value v : eval_hfexpr expr_117 (closed_117 v) (closed_117 v) = Some (Gval (Fuint 1) (word_117 v)).
Proof. unfold word_117, closed_117, expr_117, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_117.
Lemma node_117_value v : eval_hfexpr expr_117 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_117 v)).
Proof. change (eval_hfexpr expr_117 (closed_117 v) (closed_117 v) = Some (Gval (Fuint 1) (word_117 v))). apply closed_117_value. Qed.
Lemma source_118 : find_driver 118 generated_module_0_stmts_0 = Some expr_118.
Proof. vm_compute. reflexivity. Qed.
Transparent word_118.
Lemma closed_118_value v : eval_hfexpr expr_118 (closed_118 v) (closed_118 v) = Some (Gval (Fuint 2) (word_118 v)).
Proof. unfold word_118, closed_118, expr_118, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_118.
Lemma node_118_value v : eval_hfexpr expr_118 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_118 v)).
Proof. change (eval_hfexpr expr_118 (closed_118 v) (closed_118 v) = Some (Gval (Fuint 2) (word_118 v))). apply closed_118_value. Qed.
Lemma source_119 : find_driver 119 generated_module_0_stmts_0 = Some expr_119.
Proof. vm_compute. reflexivity. Qed.
Transparent word_119.
Lemma closed_119_value v : eval_hfexpr expr_119 (closed_119 v) (closed_119 v) = Some (Gval (Fuint 2) (word_119 v)).
Proof. unfold word_119, closed_119, expr_119, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_119.
Lemma node_119_value v : eval_hfexpr expr_119 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_119 v)).
Proof. change (eval_hfexpr expr_119 (closed_119 v) (closed_119 v) = Some (Gval (Fuint 2) (word_119 v))). apply closed_119_value. Qed.
Lemma source_120 : find_driver 120 generated_module_0_stmts_0 = Some expr_120.
Proof. vm_compute. reflexivity. Qed.
Transparent word_120.
Lemma closed_120_value v : eval_hfexpr expr_120 (closed_120 v) (closed_120 v) = Some (Gval (Fuint 1) (word_120 v)).
Proof. unfold word_120, closed_120, expr_120, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_120.
Lemma node_120_value v : eval_hfexpr expr_120 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_120 v)).
Proof. change (eval_hfexpr expr_120 (closed_120 v) (closed_120 v) = Some (Gval (Fuint 1) (word_120 v))). apply closed_120_value. Qed.
Lemma source_121 : find_driver 121 generated_module_0_stmts_0 = Some expr_121.
Proof. vm_compute. reflexivity. Qed.
Transparent word_121.
Lemma closed_121_value v : eval_hfexpr expr_121 (closed_121 v) (closed_121 v) = Some (Gval (Fuint 1) (word_121 v)).
Proof. unfold word_121, closed_121, expr_121, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_121.
Lemma node_121_value v : eval_hfexpr expr_121 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_121 v)).
Proof. change (eval_hfexpr expr_121 (closed_121 v) (closed_121 v) = Some (Gval (Fuint 1) (word_121 v))). apply closed_121_value. Qed.
Lemma source_122 : find_driver 122 generated_module_0_stmts_0 = Some expr_122.
Proof. vm_compute. reflexivity. Qed.
Transparent word_122.
Lemma closed_122_value v : eval_hfexpr expr_122 (closed_122 v) (closed_122 v) = Some (Gval (Fuint 1) (word_122 v)).
Proof. unfold word_122, closed_122, expr_122, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_122.
Lemma node_122_value v : eval_hfexpr expr_122 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_122 v)).
Proof. change (eval_hfexpr expr_122 (closed_122 v) (closed_122 v) = Some (Gval (Fuint 1) (word_122 v))). apply closed_122_value. Qed.
Lemma source_123 : find_driver 123 generated_module_0_stmts_0 = Some expr_123.
Proof. vm_compute. reflexivity. Qed.
Transparent word_123.
Lemma closed_123_value v : eval_hfexpr expr_123 (closed_123 v) (closed_123 v) = Some (Gval (Fuint 2) (word_123 v)).
Proof. unfold word_123, closed_123, expr_123, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_123.
Lemma node_123_value v : eval_hfexpr expr_123 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_123 v)).
Proof. change (eval_hfexpr expr_123 (closed_123 v) (closed_123 v) = Some (Gval (Fuint 2) (word_123 v))). apply closed_123_value. Qed.
Lemma source_124 : find_driver 124 generated_module_0_stmts_0 = Some expr_124.
Proof. vm_compute. reflexivity. Qed.
Transparent word_124.
Lemma closed_124_value v : eval_hfexpr expr_124 (closed_124 v) (closed_124 v) = Some (Gval (Fuint 2) (word_124 v)).
Proof. unfold word_124, closed_124, expr_124, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_124.
Lemma node_124_value v : eval_hfexpr expr_124 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_124 v)).
Proof. change (eval_hfexpr expr_124 (closed_124 v) (closed_124 v) = Some (Gval (Fuint 2) (word_124 v))). apply closed_124_value. Qed.
Lemma source_125 : find_driver 125 generated_module_0_stmts_0 = Some expr_125.
Proof. vm_compute. reflexivity. Qed.
Transparent word_125.
Lemma closed_125_value v : eval_hfexpr expr_125 (closed_125 v) (closed_125 v) = Some (Gval (Fuint 2) (word_125 v)).
Proof. unfold word_125, closed_125, expr_125, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_125.
Lemma node_125_value v : eval_hfexpr expr_125 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_125 v)).
Proof. change (eval_hfexpr expr_125 (closed_125 v) (closed_125 v) = Some (Gval (Fuint 2) (word_125 v))). apply closed_125_value. Qed.
Lemma source_126 : find_driver 126 generated_module_0_stmts_0 = Some expr_126.
Proof. vm_compute. reflexivity. Qed.
Transparent word_126.
Lemma closed_126_value v : eval_hfexpr expr_126 (closed_126 v) (closed_126 v) = Some (Gval (Fuint 3) (word_126 v)).
Proof. unfold word_126, closed_126, expr_126, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_126.
Lemma node_126_value v : eval_hfexpr expr_126 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_126 v)).
Proof. change (eval_hfexpr expr_126 (closed_126 v) (closed_126 v) = Some (Gval (Fuint 3) (word_126 v))). apply closed_126_value. Qed.
Lemma source_127 : find_driver 127 generated_module_0_stmts_0 = Some expr_127.
Proof. vm_compute. reflexivity. Qed.
Transparent word_127.
Lemma closed_127_value v : eval_hfexpr expr_127 (closed_127 v) (closed_127 v) = Some (Gval (Fuint 3) (word_127 v)).
Proof. unfold word_127, closed_127, expr_127, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_127.
Lemma node_127_value v : eval_hfexpr expr_127 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_127 v)).
Proof. change (eval_hfexpr expr_127 (closed_127 v) (closed_127 v) = Some (Gval (Fuint 3) (word_127 v))). apply closed_127_value. Qed.
Lemma source_128 : find_driver 128 generated_module_0_stmts_0 = Some expr_128.
Proof. vm_compute. reflexivity. Qed.
Transparent word_128.
Lemma closed_128_value v : eval_hfexpr expr_128 (closed_128 v) (closed_128 v) = Some (Gval (Fuint 4) (word_128 v)).
Proof. unfold word_128, closed_128, expr_128, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_128.
Lemma node_128_value v : eval_hfexpr expr_128 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_128 v)).
Proof. change (eval_hfexpr expr_128 (closed_128 v) (closed_128 v) = Some (Gval (Fuint 4) (word_128 v))). apply closed_128_value. Qed.
Lemma source_129 : find_driver 129 generated_module_0_stmts_0 = Some expr_129.
Proof. vm_compute. reflexivity. Qed.
Transparent word_129.
Lemma closed_129_value v : eval_hfexpr expr_129 (closed_129 v) (closed_129 v) = Some (Gval (Fuint 4) (word_129 v)).
Proof. unfold word_129, closed_129, expr_129, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_129.
Lemma node_129_value v : eval_hfexpr expr_129 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_129 v)).
Proof. change (eval_hfexpr expr_129 (closed_129 v) (closed_129 v) = Some (Gval (Fuint 4) (word_129 v))). apply closed_129_value. Qed.
Lemma source_130 : find_driver 130 generated_module_0_stmts_0 = Some expr_130.
Proof. vm_compute. reflexivity. Qed.
Transparent word_130.
Lemma closed_130_value v : eval_hfexpr expr_130 (closed_130 v) (closed_130 v) = Some (Gval (Fuint 5) (word_130 v)).
Proof. unfold word_130, closed_130, expr_130, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_130.
Lemma node_130_value v : eval_hfexpr expr_130 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_130 v)).
Proof. change (eval_hfexpr expr_130 (closed_130 v) (closed_130 v) = Some (Gval (Fuint 5) (word_130 v))). apply closed_130_value. Qed.
Lemma source_131 : find_driver 131 generated_module_0_stmts_0 = Some expr_131.
Proof. vm_compute. reflexivity. Qed.
Transparent word_131.
Lemma closed_131_value v : eval_hfexpr expr_131 (closed_131 v) (closed_131 v) = Some (Gval (Fuint 16) (word_131 v)).
Proof. unfold word_131, closed_131, expr_131, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_131.
Lemma node_131_value v : eval_hfexpr expr_131 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_131 v)).
Proof. change (eval_hfexpr expr_131 (closed_131 v) (closed_131 v) = Some (Gval (Fuint 16) (word_131 v))). apply closed_131_value. Qed.
Lemma source_132 : find_driver 132 generated_module_0_stmts_0 = Some expr_132.
Proof. vm_compute. reflexivity. Qed.
Transparent word_132.
Lemma closed_132_value v : eval_hfexpr expr_132 (closed_132 v) (closed_132 v) = Some (Gval (Fuint 16) (word_132 v)).
Proof. unfold word_132, closed_132, expr_132, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_132.
Lemma node_132_value v : eval_hfexpr expr_132 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_132 v)).
Proof. change (eval_hfexpr expr_132 (closed_132 v) (closed_132 v) = Some (Gval (Fuint 16) (word_132 v))). apply closed_132_value. Qed.
Lemma source_133 : find_driver 133 generated_module_0_stmts_0 = Some expr_133.
Proof. vm_compute. reflexivity. Qed.
Transparent word_133.
Lemma closed_133_value v : eval_hfexpr expr_133 (closed_133 v) (closed_133 v) = Some (Gval (Fuint 1) (word_133 v)).
Proof. unfold word_133, closed_133, expr_133, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_133.
Lemma node_133_value v : eval_hfexpr expr_133 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_133 v)).
Proof. change (eval_hfexpr expr_133 (closed_133 v) (closed_133 v) = Some (Gval (Fuint 1) (word_133 v))). apply closed_133_value. Qed.
Lemma source_134 : find_driver 134 generated_module_0_stmts_0 = Some expr_134.
Proof. vm_compute. reflexivity. Qed.
Transparent word_134.
Lemma closed_134_value v : eval_hfexpr expr_134 (closed_134 v) (closed_134 v) = Some (Gval (Fuint 8) (word_134 v)).
Proof. unfold word_134, closed_134, expr_134, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_134.
Lemma node_134_value v : eval_hfexpr expr_134 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_134 v)).
Proof. change (eval_hfexpr expr_134 (closed_134 v) (closed_134 v) = Some (Gval (Fuint 8) (word_134 v))). apply closed_134_value. Qed.
Lemma source_135 : find_driver 135 generated_module_0_stmts_0 = Some expr_135.
Proof. vm_compute. reflexivity. Qed.
Transparent word_135.
Lemma closed_135_value v : eval_hfexpr expr_135 (closed_135 v) (closed_135 v) = Some (Gval (Fuint 8) (word_135 v)).
Proof. unfold word_135, closed_135, expr_135, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_135.
Lemma node_135_value v : eval_hfexpr expr_135 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_135 v)).
Proof. change (eval_hfexpr expr_135 (closed_135 v) (closed_135 v) = Some (Gval (Fuint 8) (word_135 v))). apply closed_135_value. Qed.
Lemma source_136 : find_driver 136 generated_module_0_stmts_0 = Some expr_136.
Proof. vm_compute. reflexivity. Qed.
Transparent word_136.
Lemma closed_136_value v : eval_hfexpr expr_136 (closed_136 v) (closed_136 v) = Some (Gval (Fuint 1) (word_136 v)).
Proof. unfold word_136, closed_136, expr_136, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_136.
Lemma node_136_value v : eval_hfexpr expr_136 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_136 v)).
Proof. change (eval_hfexpr expr_136 (closed_136 v) (closed_136 v) = Some (Gval (Fuint 1) (word_136 v))). apply closed_136_value. Qed.
Lemma source_137 : find_driver 137 generated_module_0_stmts_0 = Some expr_137.
Proof. vm_compute. reflexivity. Qed.
Transparent word_137.
Lemma closed_137_value v : eval_hfexpr expr_137 (closed_137 v) (closed_137 v) = Some (Gval (Fuint 4) (word_137 v)).
Proof. unfold word_137, closed_137, expr_137, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_137.
Lemma node_137_value v : eval_hfexpr expr_137 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_137 v)).
Proof. change (eval_hfexpr expr_137 (closed_137 v) (closed_137 v) = Some (Gval (Fuint 4) (word_137 v))). apply closed_137_value. Qed.
Lemma source_138 : find_driver 138 generated_module_0_stmts_0 = Some expr_138.
Proof. vm_compute. reflexivity. Qed.
Transparent word_138.
Lemma closed_138_value v : eval_hfexpr expr_138 (closed_138 v) (closed_138 v) = Some (Gval (Fuint 4) (word_138 v)).
Proof. unfold word_138, closed_138, expr_138, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_138.
Lemma node_138_value v : eval_hfexpr expr_138 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_138 v)).
Proof. change (eval_hfexpr expr_138 (closed_138 v) (closed_138 v) = Some (Gval (Fuint 4) (word_138 v))). apply closed_138_value. Qed.
Lemma source_139 : find_driver 139 generated_module_0_stmts_0 = Some expr_139.
Proof. vm_compute. reflexivity. Qed.
Transparent word_139.
Lemma closed_139_value v : eval_hfexpr expr_139 (closed_139 v) (closed_139 v) = Some (Gval (Fuint 1) (word_139 v)).
Proof. unfold word_139, closed_139, expr_139, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_139.
Lemma node_139_value v : eval_hfexpr expr_139 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_139 v)).
Proof. change (eval_hfexpr expr_139 (closed_139 v) (closed_139 v) = Some (Gval (Fuint 1) (word_139 v))). apply closed_139_value. Qed.
Lemma source_140 : find_driver 140 generated_module_0_stmts_0 = Some expr_140.
Proof. vm_compute. reflexivity. Qed.
Transparent word_140.
Lemma closed_140_value v : eval_hfexpr expr_140 (closed_140 v) (closed_140 v) = Some (Gval (Fuint 1) (word_140 v)).
Proof. unfold word_140, closed_140, expr_140, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_140.
Lemma node_140_value v : eval_hfexpr expr_140 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_140 v)).
Proof. change (eval_hfexpr expr_140 (closed_140 v) (closed_140 v) = Some (Gval (Fuint 1) (word_140 v))). apply closed_140_value. Qed.
Lemma source_141 : find_driver 141 generated_module_0_stmts_0 = Some expr_141.
Proof. vm_compute. reflexivity. Qed.
Transparent word_141.
Lemma closed_141_value v : eval_hfexpr expr_141 (closed_141 v) (closed_141 v) = Some (Gval (Fuint 1) (word_141 v)).
Proof. unfold word_141, closed_141, expr_141, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_141.
Lemma node_141_value v : eval_hfexpr expr_141 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_141 v)).
Proof. change (eval_hfexpr expr_141 (closed_141 v) (closed_141 v) = Some (Gval (Fuint 1) (word_141 v))). apply closed_141_value. Qed.
Lemma source_142 : find_driver 142 generated_module_0_stmts_0 = Some expr_142.
Proof. vm_compute. reflexivity. Qed.
Transparent word_142.
Lemma closed_142_value v : eval_hfexpr expr_142 (closed_142 v) (closed_142 v) = Some (Gval (Fuint 1) (word_142 v)).
Proof. unfold word_142, closed_142, expr_142, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_142.
Lemma node_142_value v : eval_hfexpr expr_142 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_142 v)).
Proof. change (eval_hfexpr expr_142 (closed_142 v) (closed_142 v) = Some (Gval (Fuint 1) (word_142 v))). apply closed_142_value. Qed.
Lemma source_143 : find_driver 143 generated_module_0_stmts_0 = Some expr_143.
Proof. vm_compute. reflexivity. Qed.
Transparent word_143.
Lemma closed_143_value v : eval_hfexpr expr_143 (closed_143 v) (closed_143 v) = Some (Gval (Fuint 2) (word_143 v)).
Proof. unfold word_143, closed_143, expr_143, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_143.
Lemma node_143_value v : eval_hfexpr expr_143 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_143 v)).
Proof. change (eval_hfexpr expr_143 (closed_143 v) (closed_143 v) = Some (Gval (Fuint 2) (word_143 v))). apply closed_143_value. Qed.
Lemma source_144 : find_driver 144 generated_module_0_stmts_0 = Some expr_144.
Proof. vm_compute. reflexivity. Qed.
Transparent word_144.
Lemma closed_144_value v : eval_hfexpr expr_144 (closed_144 v) (closed_144 v) = Some (Gval (Fuint 2) (word_144 v)).
Proof. unfold word_144, closed_144, expr_144, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_144.
Lemma node_144_value v : eval_hfexpr expr_144 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_144 v)).
Proof. change (eval_hfexpr expr_144 (closed_144 v) (closed_144 v) = Some (Gval (Fuint 2) (word_144 v))). apply closed_144_value. Qed.
Lemma source_145 : find_driver 145 generated_module_0_stmts_0 = Some expr_145.
Proof. vm_compute. reflexivity. Qed.
Transparent word_145.
Lemma closed_145_value v : eval_hfexpr expr_145 (closed_145 v) (closed_145 v) = Some (Gval (Fuint 1) (word_145 v)).
Proof. unfold word_145, closed_145, expr_145, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_145.
Lemma node_145_value v : eval_hfexpr expr_145 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_145 v)).
Proof. change (eval_hfexpr expr_145 (closed_145 v) (closed_145 v) = Some (Gval (Fuint 1) (word_145 v))). apply closed_145_value. Qed.
Lemma source_146 : find_driver 146 generated_module_0_stmts_0 = Some expr_146.
Proof. vm_compute. reflexivity. Qed.
Transparent word_146.
Lemma closed_146_value v : eval_hfexpr expr_146 (closed_146 v) (closed_146 v) = Some (Gval (Fuint 1) (word_146 v)).
Proof. unfold word_146, closed_146, expr_146, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_146.
Lemma node_146_value v : eval_hfexpr expr_146 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_146 v)).
Proof. change (eval_hfexpr expr_146 (closed_146 v) (closed_146 v) = Some (Gval (Fuint 1) (word_146 v))). apply closed_146_value. Qed.
Lemma source_147 : find_driver 147 generated_module_0_stmts_0 = Some expr_147.
Proof. vm_compute. reflexivity. Qed.
Transparent word_147.
Lemma closed_147_value v : eval_hfexpr expr_147 (closed_147 v) (closed_147 v) = Some (Gval (Fuint 1) (word_147 v)).
Proof. unfold word_147, closed_147, expr_147, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_147.
Lemma node_147_value v : eval_hfexpr expr_147 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_147 v)).
Proof. change (eval_hfexpr expr_147 (closed_147 v) (closed_147 v) = Some (Gval (Fuint 1) (word_147 v))). apply closed_147_value. Qed.
Lemma source_148 : find_driver 148 generated_module_0_stmts_0 = Some expr_148.
Proof. vm_compute. reflexivity. Qed.
Transparent word_148.
Lemma closed_148_value v : eval_hfexpr expr_148 (closed_148 v) (closed_148 v) = Some (Gval (Fuint 2) (word_148 v)).
Proof. unfold word_148, closed_148, expr_148, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_148.
Lemma node_148_value v : eval_hfexpr expr_148 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_148 v)).
Proof. change (eval_hfexpr expr_148 (closed_148 v) (closed_148 v) = Some (Gval (Fuint 2) (word_148 v))). apply closed_148_value. Qed.
Lemma source_149 : find_driver 149 generated_module_0_stmts_0 = Some expr_149.
Proof. vm_compute. reflexivity. Qed.
Transparent word_149.
Lemma closed_149_value v : eval_hfexpr expr_149 (closed_149 v) (closed_149 v) = Some (Gval (Fuint 2) (word_149 v)).
Proof. unfold word_149, closed_149, expr_149, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_149.
Lemma node_149_value v : eval_hfexpr expr_149 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_149 v)).
Proof. change (eval_hfexpr expr_149 (closed_149 v) (closed_149 v) = Some (Gval (Fuint 2) (word_149 v))). apply closed_149_value. Qed.
Lemma source_150 : find_driver 150 generated_module_0_stmts_0 = Some expr_150.
Proof. vm_compute. reflexivity. Qed.
Transparent word_150.
Lemma closed_150_value v : eval_hfexpr expr_150 (closed_150 v) (closed_150 v) = Some (Gval (Fuint 2) (word_150 v)).
Proof. unfold word_150, closed_150, expr_150, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_150.
Lemma node_150_value v : eval_hfexpr expr_150 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_150 v)).
Proof. change (eval_hfexpr expr_150 (closed_150 v) (closed_150 v) = Some (Gval (Fuint 2) (word_150 v))). apply closed_150_value. Qed.
Lemma source_151 : find_driver 151 generated_module_0_stmts_0 = Some expr_151.
Proof. vm_compute. reflexivity. Qed.
Transparent word_151.
Lemma closed_151_value v : eval_hfexpr expr_151 (closed_151 v) (closed_151 v) = Some (Gval (Fuint 3) (word_151 v)).
Proof. unfold word_151, closed_151, expr_151, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_151.
Lemma node_151_value v : eval_hfexpr expr_151 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_151 v)).
Proof. change (eval_hfexpr expr_151 (closed_151 v) (closed_151 v) = Some (Gval (Fuint 3) (word_151 v))). apply closed_151_value. Qed.
Lemma source_152 : find_driver 152 generated_module_0_stmts_0 = Some expr_152.
Proof. vm_compute. reflexivity. Qed.
Transparent word_152.
Lemma closed_152_value v : eval_hfexpr expr_152 (closed_152 v) (closed_152 v) = Some (Gval (Fuint 4) (word_152 v)).
Proof. unfold word_152, closed_152, expr_152, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_152.
Lemma node_152_value v : eval_hfexpr expr_152 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_152 v)).
Proof. change (eval_hfexpr expr_152 (closed_152 v) (closed_152 v) = Some (Gval (Fuint 4) (word_152 v))). apply closed_152_value. Qed.
Lemma source_153 : find_driver 153 generated_module_0_stmts_0 = Some expr_153.
Proof. vm_compute. reflexivity. Qed.
Transparent word_153.
Lemma closed_153_value v : eval_hfexpr expr_153 (closed_153 v) (closed_153 v) = Some (Gval (Fuint 4) (word_153 v)).
Proof. unfold word_153, closed_153, expr_153, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_153.
Lemma node_153_value v : eval_hfexpr expr_153 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_153 v)).
Proof. change (eval_hfexpr expr_153 (closed_153 v) (closed_153 v) = Some (Gval (Fuint 4) (word_153 v))). apply closed_153_value. Qed.
Lemma source_154 : find_driver 154 generated_module_0_stmts_0 = Some expr_154.
Proof. vm_compute. reflexivity. Qed.
Transparent word_154.
Lemma closed_154_value v : eval_hfexpr expr_154 (closed_154 v) (closed_154 v) = Some (Gval (Fuint 1) (word_154 v)).
Proof. unfold word_154, closed_154, expr_154, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_154.
Lemma node_154_value v : eval_hfexpr expr_154 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_154 v)).
Proof. change (eval_hfexpr expr_154 (closed_154 v) (closed_154 v) = Some (Gval (Fuint 1) (word_154 v))). apply closed_154_value. Qed.
Lemma source_155 : find_driver 155 generated_module_0_stmts_0 = Some expr_155.
Proof. vm_compute. reflexivity. Qed.
Transparent word_155.
Lemma closed_155_value v : eval_hfexpr expr_155 (closed_155 v) (closed_155 v) = Some (Gval (Fuint 1) (word_155 v)).
Proof. unfold word_155, closed_155, expr_155, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_155.
Lemma node_155_value v : eval_hfexpr expr_155 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_155 v)).
Proof. change (eval_hfexpr expr_155 (closed_155 v) (closed_155 v) = Some (Gval (Fuint 1) (word_155 v))). apply closed_155_value. Qed.
Lemma source_156 : find_driver 156 generated_module_0_stmts_0 = Some expr_156.
Proof. vm_compute. reflexivity. Qed.
Transparent word_156.
Lemma closed_156_value v : eval_hfexpr expr_156 (closed_156 v) (closed_156 v) = Some (Gval (Fuint 1) (word_156 v)).
Proof. unfold word_156, closed_156, expr_156, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_156.
Lemma node_156_value v : eval_hfexpr expr_156 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_156 v)).
Proof. change (eval_hfexpr expr_156 (closed_156 v) (closed_156 v) = Some (Gval (Fuint 1) (word_156 v))). apply closed_156_value. Qed.
Lemma source_157 : find_driver 157 generated_module_0_stmts_0 = Some expr_157.
Proof. vm_compute. reflexivity. Qed.
Transparent word_157.
Lemma closed_157_value v : eval_hfexpr expr_157 (closed_157 v) (closed_157 v) = Some (Gval (Fuint 1) (word_157 v)).
Proof. unfold word_157, closed_157, expr_157, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_157.
Lemma node_157_value v : eval_hfexpr expr_157 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_157 v)).
Proof. change (eval_hfexpr expr_157 (closed_157 v) (closed_157 v) = Some (Gval (Fuint 1) (word_157 v))). apply closed_157_value. Qed.
Lemma source_158 : find_driver 158 generated_module_0_stmts_0 = Some expr_158.
Proof. vm_compute. reflexivity. Qed.
Transparent word_158.
Lemma closed_158_value v : eval_hfexpr expr_158 (closed_158 v) (closed_158 v) = Some (Gval (Fuint 2) (word_158 v)).
Proof. unfold word_158, closed_158, expr_158, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_158.
Lemma node_158_value v : eval_hfexpr expr_158 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_158 v)).
Proof. change (eval_hfexpr expr_158 (closed_158 v) (closed_158 v) = Some (Gval (Fuint 2) (word_158 v))). apply closed_158_value. Qed.
Lemma source_159 : find_driver 159 generated_module_0_stmts_0 = Some expr_159.
Proof. vm_compute. reflexivity. Qed.
Transparent word_159.
Lemma closed_159_value v : eval_hfexpr expr_159 (closed_159 v) (closed_159 v) = Some (Gval (Fuint 2) (word_159 v)).
Proof. unfold word_159, closed_159, expr_159, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_159.
Lemma node_159_value v : eval_hfexpr expr_159 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_159 v)).
Proof. change (eval_hfexpr expr_159 (closed_159 v) (closed_159 v) = Some (Gval (Fuint 2) (word_159 v))). apply closed_159_value. Qed.
Lemma source_160 : find_driver 160 generated_module_0_stmts_0 = Some expr_160.
Proof. vm_compute. reflexivity. Qed.
Transparent word_160.
Lemma closed_160_value v : eval_hfexpr expr_160 (closed_160 v) (closed_160 v) = Some (Gval (Fuint 1) (word_160 v)).
Proof. unfold word_160, closed_160, expr_160, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_160.
Lemma node_160_value v : eval_hfexpr expr_160 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_160 v)).
Proof. change (eval_hfexpr expr_160 (closed_160 v) (closed_160 v) = Some (Gval (Fuint 1) (word_160 v))). apply closed_160_value. Qed.
Lemma source_161 : find_driver 161 generated_module_0_stmts_0 = Some expr_161.
Proof. vm_compute. reflexivity. Qed.
Transparent word_161.
Lemma closed_161_value v : eval_hfexpr expr_161 (closed_161 v) (closed_161 v) = Some (Gval (Fuint 1) (word_161 v)).
Proof. unfold word_161, closed_161, expr_161, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_161.
Lemma node_161_value v : eval_hfexpr expr_161 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_161 v)).
Proof. change (eval_hfexpr expr_161 (closed_161 v) (closed_161 v) = Some (Gval (Fuint 1) (word_161 v))). apply closed_161_value. Qed.
Lemma source_162 : find_driver 162 generated_module_0_stmts_0 = Some expr_162.
Proof. vm_compute. reflexivity. Qed.
Transparent word_162.
Lemma closed_162_value v : eval_hfexpr expr_162 (closed_162 v) (closed_162 v) = Some (Gval (Fuint 1) (word_162 v)).
Proof. unfold word_162, closed_162, expr_162, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_162.
Lemma node_162_value v : eval_hfexpr expr_162 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_162 v)).
Proof. change (eval_hfexpr expr_162 (closed_162 v) (closed_162 v) = Some (Gval (Fuint 1) (word_162 v))). apply closed_162_value. Qed.
Lemma source_163 : find_driver 163 generated_module_0_stmts_0 = Some expr_163.
Proof. vm_compute. reflexivity. Qed.
Transparent word_163.
Lemma closed_163_value v : eval_hfexpr expr_163 (closed_163 v) (closed_163 v) = Some (Gval (Fuint 2) (word_163 v)).
Proof. unfold word_163, closed_163, expr_163, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_163.
Lemma node_163_value v : eval_hfexpr expr_163 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_163 v)).
Proof. change (eval_hfexpr expr_163 (closed_163 v) (closed_163 v) = Some (Gval (Fuint 2) (word_163 v))). apply closed_163_value. Qed.
Lemma source_164 : find_driver 164 generated_module_0_stmts_0 = Some expr_164.
Proof. vm_compute. reflexivity. Qed.
Transparent word_164.
Lemma closed_164_value v : eval_hfexpr expr_164 (closed_164 v) (closed_164 v) = Some (Gval (Fuint 2) (word_164 v)).
Proof. unfold word_164, closed_164, expr_164, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_164.
Lemma node_164_value v : eval_hfexpr expr_164 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_164 v)).
Proof. change (eval_hfexpr expr_164 (closed_164 v) (closed_164 v) = Some (Gval (Fuint 2) (word_164 v))). apply closed_164_value. Qed.
Lemma source_165 : find_driver 165 generated_module_0_stmts_0 = Some expr_165.
Proof. vm_compute. reflexivity. Qed.
Transparent word_165.
Lemma closed_165_value v : eval_hfexpr expr_165 (closed_165 v) (closed_165 v) = Some (Gval (Fuint 2) (word_165 v)).
Proof. unfold word_165, closed_165, expr_165, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_165.
Lemma node_165_value v : eval_hfexpr expr_165 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_165 v)).
Proof. change (eval_hfexpr expr_165 (closed_165 v) (closed_165 v) = Some (Gval (Fuint 2) (word_165 v))). apply closed_165_value. Qed.
Lemma source_166 : find_driver 166 generated_module_0_stmts_0 = Some expr_166.
Proof. vm_compute. reflexivity. Qed.
Transparent word_166.
Lemma closed_166_value v : eval_hfexpr expr_166 (closed_166 v) (closed_166 v) = Some (Gval (Fuint 3) (word_166 v)).
Proof. unfold word_166, closed_166, expr_166, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_166.
Lemma node_166_value v : eval_hfexpr expr_166 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_166 v)).
Proof. change (eval_hfexpr expr_166 (closed_166 v) (closed_166 v) = Some (Gval (Fuint 3) (word_166 v))). apply closed_166_value. Qed.
Lemma source_167 : find_driver 167 generated_module_0_stmts_0 = Some expr_167.
Proof. vm_compute. reflexivity. Qed.
Transparent word_167.
Lemma closed_167_value v : eval_hfexpr expr_167 (closed_167 v) (closed_167 v) = Some (Gval (Fuint 3) (word_167 v)).
Proof. unfold word_167, closed_167, expr_167, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_167.
Lemma node_167_value v : eval_hfexpr expr_167 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_167 v)).
Proof. change (eval_hfexpr expr_167 (closed_167 v) (closed_167 v) = Some (Gval (Fuint 3) (word_167 v))). apply closed_167_value. Qed.
Lemma source_168 : find_driver 168 generated_module_0_stmts_0 = Some expr_168.
Proof. vm_compute. reflexivity. Qed.
Transparent word_168.
Lemma closed_168_value v : eval_hfexpr expr_168 (closed_168 v) (closed_168 v) = Some (Gval (Fuint 4) (word_168 v)).
Proof. unfold word_168, closed_168, expr_168, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_168.
Lemma node_168_value v : eval_hfexpr expr_168 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_168 v)).
Proof. change (eval_hfexpr expr_168 (closed_168 v) (closed_168 v) = Some (Gval (Fuint 4) (word_168 v))). apply closed_168_value. Qed.
Lemma source_169 : find_driver 169 generated_module_0_stmts_0 = Some expr_169.
Proof. vm_compute. reflexivity. Qed.
Transparent word_169.
Lemma closed_169_value v : eval_hfexpr expr_169 (closed_169 v) (closed_169 v) = Some (Gval (Fuint 8) (word_169 v)).
Proof. unfold word_169, closed_169, expr_169, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_169.
Lemma node_169_value v : eval_hfexpr expr_169 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_169 v)).
Proof. change (eval_hfexpr expr_169 (closed_169 v) (closed_169 v) = Some (Gval (Fuint 8) (word_169 v))). apply closed_169_value. Qed.
Lemma source_170 : find_driver 170 generated_module_0_stmts_0 = Some expr_170.
Proof. vm_compute. reflexivity. Qed.
Transparent word_170.
Lemma closed_170_value v : eval_hfexpr expr_170 (closed_170 v) (closed_170 v) = Some (Gval (Fuint 8) (word_170 v)).
Proof. unfold word_170, closed_170, expr_170, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_170.
Lemma node_170_value v : eval_hfexpr expr_170 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_170 v)).
Proof. change (eval_hfexpr expr_170 (closed_170 v) (closed_170 v) = Some (Gval (Fuint 8) (word_170 v))). apply closed_170_value. Qed.
Lemma source_171 : find_driver 171 generated_module_0_stmts_0 = Some expr_171.
Proof. vm_compute. reflexivity. Qed.
Transparent word_171.
Lemma closed_171_value v : eval_hfexpr expr_171 (closed_171 v) (closed_171 v) = Some (Gval (Fuint 1) (word_171 v)).
Proof. unfold word_171, closed_171, expr_171, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_171.
Lemma node_171_value v : eval_hfexpr expr_171 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_171 v)).
Proof. change (eval_hfexpr expr_171 (closed_171 v) (closed_171 v) = Some (Gval (Fuint 1) (word_171 v))). apply closed_171_value. Qed.
Lemma source_172 : find_driver 172 generated_module_0_stmts_0 = Some expr_172.
Proof. vm_compute. reflexivity. Qed.
Transparent word_172.
Lemma closed_172_value v : eval_hfexpr expr_172 (closed_172 v) (closed_172 v) = Some (Gval (Fuint 4) (word_172 v)).
Proof. unfold word_172, closed_172, expr_172, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_172.
Lemma node_172_value v : eval_hfexpr expr_172 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_172 v)).
Proof. change (eval_hfexpr expr_172 (closed_172 v) (closed_172 v) = Some (Gval (Fuint 4) (word_172 v))). apply closed_172_value. Qed.
Lemma source_173 : find_driver 173 generated_module_0_stmts_0 = Some expr_173.
Proof. vm_compute. reflexivity. Qed.
Transparent word_173.
Lemma closed_173_value v : eval_hfexpr expr_173 (closed_173 v) (closed_173 v) = Some (Gval (Fuint 4) (word_173 v)).
Proof. unfold word_173, closed_173, expr_173, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_173.
Lemma node_173_value v : eval_hfexpr expr_173 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_173 v)).
Proof. change (eval_hfexpr expr_173 (closed_173 v) (closed_173 v) = Some (Gval (Fuint 4) (word_173 v))). apply closed_173_value. Qed.
Lemma source_174 : find_driver 174 generated_module_0_stmts_0 = Some expr_174.
Proof. vm_compute. reflexivity. Qed.
Transparent word_174.
Lemma closed_174_value v : eval_hfexpr expr_174 (closed_174 v) (closed_174 v) = Some (Gval (Fuint 1) (word_174 v)).
Proof. unfold word_174, closed_174, expr_174, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_174.
Lemma node_174_value v : eval_hfexpr expr_174 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_174 v)).
Proof. change (eval_hfexpr expr_174 (closed_174 v) (closed_174 v) = Some (Gval (Fuint 1) (word_174 v))). apply closed_174_value. Qed.
Lemma source_175 : find_driver 175 generated_module_0_stmts_0 = Some expr_175.
Proof. vm_compute. reflexivity. Qed.
Transparent word_175.
Lemma closed_175_value v : eval_hfexpr expr_175 (closed_175 v) (closed_175 v) = Some (Gval (Fuint 1) (word_175 v)).
Proof. unfold word_175, closed_175, expr_175, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_175.
Lemma node_175_value v : eval_hfexpr expr_175 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_175 v)).
Proof. change (eval_hfexpr expr_175 (closed_175 v) (closed_175 v) = Some (Gval (Fuint 1) (word_175 v))). apply closed_175_value. Qed.
Lemma source_176 : find_driver 176 generated_module_0_stmts_0 = Some expr_176.
Proof. vm_compute. reflexivity. Qed.
Transparent word_176.
Lemma closed_176_value v : eval_hfexpr expr_176 (closed_176 v) (closed_176 v) = Some (Gval (Fuint 1) (word_176 v)).
Proof. unfold word_176, closed_176, expr_176, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_176.
Lemma node_176_value v : eval_hfexpr expr_176 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_176 v)).
Proof. change (eval_hfexpr expr_176 (closed_176 v) (closed_176 v) = Some (Gval (Fuint 1) (word_176 v))). apply closed_176_value. Qed.
Lemma source_177 : find_driver 177 generated_module_0_stmts_0 = Some expr_177.
Proof. vm_compute. reflexivity. Qed.
Transparent word_177.
Lemma closed_177_value v : eval_hfexpr expr_177 (closed_177 v) (closed_177 v) = Some (Gval (Fuint 1) (word_177 v)).
Proof. unfold word_177, closed_177, expr_177, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_177.
Lemma node_177_value v : eval_hfexpr expr_177 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_177 v)).
Proof. change (eval_hfexpr expr_177 (closed_177 v) (closed_177 v) = Some (Gval (Fuint 1) (word_177 v))). apply closed_177_value. Qed.
Lemma source_178 : find_driver 178 generated_module_0_stmts_0 = Some expr_178.
Proof. vm_compute. reflexivity. Qed.
Transparent word_178.
Lemma closed_178_value v : eval_hfexpr expr_178 (closed_178 v) (closed_178 v) = Some (Gval (Fuint 2) (word_178 v)).
Proof. unfold word_178, closed_178, expr_178, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_178.
Lemma node_178_value v : eval_hfexpr expr_178 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_178 v)).
Proof. change (eval_hfexpr expr_178 (closed_178 v) (closed_178 v) = Some (Gval (Fuint 2) (word_178 v))). apply closed_178_value. Qed.
Lemma source_179 : find_driver 179 generated_module_0_stmts_0 = Some expr_179.
Proof. vm_compute. reflexivity. Qed.
Transparent word_179.
Lemma closed_179_value v : eval_hfexpr expr_179 (closed_179 v) (closed_179 v) = Some (Gval (Fuint 2) (word_179 v)).
Proof. unfold word_179, closed_179, expr_179, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_179.
Lemma node_179_value v : eval_hfexpr expr_179 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_179 v)).
Proof. change (eval_hfexpr expr_179 (closed_179 v) (closed_179 v) = Some (Gval (Fuint 2) (word_179 v))). apply closed_179_value. Qed.
Lemma source_180 : find_driver 180 generated_module_0_stmts_0 = Some expr_180.
Proof. vm_compute. reflexivity. Qed.
Transparent word_180.
Lemma closed_180_value v : eval_hfexpr expr_180 (closed_180 v) (closed_180 v) = Some (Gval (Fuint 1) (word_180 v)).
Proof. unfold word_180, closed_180, expr_180, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_180.
Lemma node_180_value v : eval_hfexpr expr_180 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_180 v)).
Proof. change (eval_hfexpr expr_180 (closed_180 v) (closed_180 v) = Some (Gval (Fuint 1) (word_180 v))). apply closed_180_value. Qed.
Lemma source_181 : find_driver 181 generated_module_0_stmts_0 = Some expr_181.
Proof. vm_compute. reflexivity. Qed.
Transparent word_181.
Lemma closed_181_value v : eval_hfexpr expr_181 (closed_181 v) (closed_181 v) = Some (Gval (Fuint 1) (word_181 v)).
Proof. unfold word_181, closed_181, expr_181, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_181.
Lemma node_181_value v : eval_hfexpr expr_181 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_181 v)).
Proof. change (eval_hfexpr expr_181 (closed_181 v) (closed_181 v) = Some (Gval (Fuint 1) (word_181 v))). apply closed_181_value. Qed.
Lemma source_182 : find_driver 182 generated_module_0_stmts_0 = Some expr_182.
Proof. vm_compute. reflexivity. Qed.
Transparent word_182.
Lemma closed_182_value v : eval_hfexpr expr_182 (closed_182 v) (closed_182 v) = Some (Gval (Fuint 1) (word_182 v)).
Proof. unfold word_182, closed_182, expr_182, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_182.
Lemma node_182_value v : eval_hfexpr expr_182 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_182 v)).
Proof. change (eval_hfexpr expr_182 (closed_182 v) (closed_182 v) = Some (Gval (Fuint 1) (word_182 v))). apply closed_182_value. Qed.
Lemma source_183 : find_driver 183 generated_module_0_stmts_0 = Some expr_183.
Proof. vm_compute. reflexivity. Qed.
Transparent word_183.
Lemma closed_183_value v : eval_hfexpr expr_183 (closed_183 v) (closed_183 v) = Some (Gval (Fuint 2) (word_183 v)).
Proof. unfold word_183, closed_183, expr_183, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_183.
Lemma node_183_value v : eval_hfexpr expr_183 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_183 v)).
Proof. change (eval_hfexpr expr_183 (closed_183 v) (closed_183 v) = Some (Gval (Fuint 2) (word_183 v))). apply closed_183_value. Qed.
Lemma source_184 : find_driver 184 generated_module_0_stmts_0 = Some expr_184.
Proof. vm_compute. reflexivity. Qed.
Transparent word_184.
Lemma closed_184_value v : eval_hfexpr expr_184 (closed_184 v) (closed_184 v) = Some (Gval (Fuint 2) (word_184 v)).
Proof. unfold word_184, closed_184, expr_184, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_184.
Lemma node_184_value v : eval_hfexpr expr_184 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_184 v)).
Proof. change (eval_hfexpr expr_184 (closed_184 v) (closed_184 v) = Some (Gval (Fuint 2) (word_184 v))). apply closed_184_value. Qed.
Lemma source_185 : find_driver 185 generated_module_0_stmts_0 = Some expr_185.
Proof. vm_compute. reflexivity. Qed.
Transparent word_185.
Lemma closed_185_value v : eval_hfexpr expr_185 (closed_185 v) (closed_185 v) = Some (Gval (Fuint 2) (word_185 v)).
Proof. unfold word_185, closed_185, expr_185, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_185.
Lemma node_185_value v : eval_hfexpr expr_185 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_185 v)).
Proof. change (eval_hfexpr expr_185 (closed_185 v) (closed_185 v) = Some (Gval (Fuint 2) (word_185 v))). apply closed_185_value. Qed.
Lemma source_186 : find_driver 186 generated_module_0_stmts_0 = Some expr_186.
Proof. vm_compute. reflexivity. Qed.
Transparent word_186.
Lemma closed_186_value v : eval_hfexpr expr_186 (closed_186 v) (closed_186 v) = Some (Gval (Fuint 3) (word_186 v)).
Proof. unfold word_186, closed_186, expr_186, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_186.
Lemma node_186_value v : eval_hfexpr expr_186 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_186 v)).
Proof. change (eval_hfexpr expr_186 (closed_186 v) (closed_186 v) = Some (Gval (Fuint 3) (word_186 v))). apply closed_186_value. Qed.
Lemma source_187 : find_driver 187 generated_module_0_stmts_0 = Some expr_187.
Proof. vm_compute. reflexivity. Qed.
Transparent word_187.
Lemma closed_187_value v : eval_hfexpr expr_187 (closed_187 v) (closed_187 v) = Some (Gval (Fuint 4) (word_187 v)).
Proof. unfold word_187, closed_187, expr_187, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_187.
Lemma node_187_value v : eval_hfexpr expr_187 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_187 v)).
Proof. change (eval_hfexpr expr_187 (closed_187 v) (closed_187 v) = Some (Gval (Fuint 4) (word_187 v))). apply closed_187_value. Qed.
Lemma source_188 : find_driver 188 generated_module_0_stmts_0 = Some expr_188.
Proof. vm_compute. reflexivity. Qed.
Transparent word_188.
Lemma closed_188_value v : eval_hfexpr expr_188 (closed_188 v) (closed_188 v) = Some (Gval (Fuint 4) (word_188 v)).
Proof. unfold word_188, closed_188, expr_188, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_188.
Lemma node_188_value v : eval_hfexpr expr_188 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_188 v)).
Proof. change (eval_hfexpr expr_188 (closed_188 v) (closed_188 v) = Some (Gval (Fuint 4) (word_188 v))). apply closed_188_value. Qed.
Lemma source_189 : find_driver 189 generated_module_0_stmts_0 = Some expr_189.
Proof. vm_compute. reflexivity. Qed.
Transparent word_189.
Lemma closed_189_value v : eval_hfexpr expr_189 (closed_189 v) (closed_189 v) = Some (Gval (Fuint 1) (word_189 v)).
Proof. unfold word_189, closed_189, expr_189, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_189.
Lemma node_189_value v : eval_hfexpr expr_189 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_189 v)).
Proof. change (eval_hfexpr expr_189 (closed_189 v) (closed_189 v) = Some (Gval (Fuint 1) (word_189 v))). apply closed_189_value. Qed.
Lemma source_190 : find_driver 190 generated_module_0_stmts_0 = Some expr_190.
Proof. vm_compute. reflexivity. Qed.
Transparent word_190.
Lemma closed_190_value v : eval_hfexpr expr_190 (closed_190 v) (closed_190 v) = Some (Gval (Fuint 1) (word_190 v)).
Proof. unfold word_190, closed_190, expr_190, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_190.
Lemma node_190_value v : eval_hfexpr expr_190 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_190 v)).
Proof. change (eval_hfexpr expr_190 (closed_190 v) (closed_190 v) = Some (Gval (Fuint 1) (word_190 v))). apply closed_190_value. Qed.
Lemma source_191 : find_driver 191 generated_module_0_stmts_0 = Some expr_191.
Proof. vm_compute. reflexivity. Qed.
Transparent word_191.
Lemma closed_191_value v : eval_hfexpr expr_191 (closed_191 v) (closed_191 v) = Some (Gval (Fuint 1) (word_191 v)).
Proof. unfold word_191, closed_191, expr_191, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_191.
Lemma node_191_value v : eval_hfexpr expr_191 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_191 v)).
Proof. change (eval_hfexpr expr_191 (closed_191 v) (closed_191 v) = Some (Gval (Fuint 1) (word_191 v))). apply closed_191_value. Qed.
Lemma source_192 : find_driver 192 generated_module_0_stmts_0 = Some expr_192.
Proof. vm_compute. reflexivity. Qed.
Transparent word_192.
Lemma closed_192_value v : eval_hfexpr expr_192 (closed_192 v) (closed_192 v) = Some (Gval (Fuint 1) (word_192 v)).
Proof. unfold word_192, closed_192, expr_192, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_192.
Lemma node_192_value v : eval_hfexpr expr_192 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_192 v)).
Proof. change (eval_hfexpr expr_192 (closed_192 v) (closed_192 v) = Some (Gval (Fuint 1) (word_192 v))). apply closed_192_value. Qed.
Lemma source_193 : find_driver 193 generated_module_0_stmts_0 = Some expr_193.
Proof. vm_compute. reflexivity. Qed.
Transparent word_193.
Lemma closed_193_value v : eval_hfexpr expr_193 (closed_193 v) (closed_193 v) = Some (Gval (Fuint 2) (word_193 v)).
Proof. unfold word_193, closed_193, expr_193, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_193.
Lemma node_193_value v : eval_hfexpr expr_193 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_193 v)).
Proof. change (eval_hfexpr expr_193 (closed_193 v) (closed_193 v) = Some (Gval (Fuint 2) (word_193 v))). apply closed_193_value. Qed.
Lemma source_194 : find_driver 194 generated_module_0_stmts_0 = Some expr_194.
Proof. vm_compute. reflexivity. Qed.
Transparent word_194.
Lemma closed_194_value v : eval_hfexpr expr_194 (closed_194 v) (closed_194 v) = Some (Gval (Fuint 2) (word_194 v)).
Proof. unfold word_194, closed_194, expr_194, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_194.
Lemma node_194_value v : eval_hfexpr expr_194 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_194 v)).
Proof. change (eval_hfexpr expr_194 (closed_194 v) (closed_194 v) = Some (Gval (Fuint 2) (word_194 v))). apply closed_194_value. Qed.
Lemma source_195 : find_driver 195 generated_module_0_stmts_0 = Some expr_195.
Proof. vm_compute. reflexivity. Qed.
Transparent word_195.
Lemma closed_195_value v : eval_hfexpr expr_195 (closed_195 v) (closed_195 v) = Some (Gval (Fuint 1) (word_195 v)).
Proof. unfold word_195, closed_195, expr_195, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_195.
Lemma node_195_value v : eval_hfexpr expr_195 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_195 v)).
Proof. change (eval_hfexpr expr_195 (closed_195 v) (closed_195 v) = Some (Gval (Fuint 1) (word_195 v))). apply closed_195_value. Qed.
Lemma source_196 : find_driver 196 generated_module_0_stmts_0 = Some expr_196.
Proof. vm_compute. reflexivity. Qed.
Transparent word_196.
Lemma closed_196_value v : eval_hfexpr expr_196 (closed_196 v) (closed_196 v) = Some (Gval (Fuint 1) (word_196 v)).
Proof. unfold word_196, closed_196, expr_196, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_196.
Lemma node_196_value v : eval_hfexpr expr_196 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_196 v)).
Proof. change (eval_hfexpr expr_196 (closed_196 v) (closed_196 v) = Some (Gval (Fuint 1) (word_196 v))). apply closed_196_value. Qed.
Lemma source_197 : find_driver 197 generated_module_0_stmts_0 = Some expr_197.
Proof. vm_compute. reflexivity. Qed.
Transparent word_197.
Lemma closed_197_value v : eval_hfexpr expr_197 (closed_197 v) (closed_197 v) = Some (Gval (Fuint 1) (word_197 v)).
Proof. unfold word_197, closed_197, expr_197, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_197.
Lemma node_197_value v : eval_hfexpr expr_197 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_197 v)).
Proof. change (eval_hfexpr expr_197 (closed_197 v) (closed_197 v) = Some (Gval (Fuint 1) (word_197 v))). apply closed_197_value. Qed.
Lemma source_198 : find_driver 198 generated_module_0_stmts_0 = Some expr_198.
Proof. vm_compute. reflexivity. Qed.
Transparent word_198.
Lemma closed_198_value v : eval_hfexpr expr_198 (closed_198 v) (closed_198 v) = Some (Gval (Fuint 2) (word_198 v)).
Proof. unfold word_198, closed_198, expr_198, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_198.
Lemma node_198_value v : eval_hfexpr expr_198 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_198 v)).
Proof. change (eval_hfexpr expr_198 (closed_198 v) (closed_198 v) = Some (Gval (Fuint 2) (word_198 v))). apply closed_198_value. Qed.
Lemma source_199 : find_driver 199 generated_module_0_stmts_0 = Some expr_199.
Proof. vm_compute. reflexivity. Qed.
Transparent word_199.
Lemma closed_199_value v : eval_hfexpr expr_199 (closed_199 v) (closed_199 v) = Some (Gval (Fuint 2) (word_199 v)).
Proof. unfold word_199, closed_199, expr_199, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_199.
Lemma node_199_value v : eval_hfexpr expr_199 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_199 v)).
Proof. change (eval_hfexpr expr_199 (closed_199 v) (closed_199 v) = Some (Gval (Fuint 2) (word_199 v))). apply closed_199_value. Qed.
Lemma source_200 : find_driver 200 generated_module_0_stmts_0 = Some expr_200.
Proof. vm_compute. reflexivity. Qed.
Transparent word_200.
Lemma closed_200_value v : eval_hfexpr expr_200 (closed_200 v) (closed_200 v) = Some (Gval (Fuint 2) (word_200 v)).
Proof. unfold word_200, closed_200, expr_200, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_200.
Lemma node_200_value v : eval_hfexpr expr_200 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_200 v)).
Proof. change (eval_hfexpr expr_200 (closed_200 v) (closed_200 v) = Some (Gval (Fuint 2) (word_200 v))). apply closed_200_value. Qed.
Lemma source_201 : find_driver 201 generated_module_0_stmts_0 = Some expr_201.
Proof. vm_compute. reflexivity. Qed.
Transparent word_201.
Lemma closed_201_value v : eval_hfexpr expr_201 (closed_201 v) (closed_201 v) = Some (Gval (Fuint 3) (word_201 v)).
Proof. unfold word_201, closed_201, expr_201, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_201.
Lemma node_201_value v : eval_hfexpr expr_201 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_201 v)).
Proof. change (eval_hfexpr expr_201 (closed_201 v) (closed_201 v) = Some (Gval (Fuint 3) (word_201 v))). apply closed_201_value. Qed.
Lemma source_202 : find_driver 202 generated_module_0_stmts_0 = Some expr_202.
Proof. vm_compute. reflexivity. Qed.
Transparent word_202.
Lemma closed_202_value v : eval_hfexpr expr_202 (closed_202 v) (closed_202 v) = Some (Gval (Fuint 3) (word_202 v)).
Proof. unfold word_202, closed_202, expr_202, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_202.
Lemma node_202_value v : eval_hfexpr expr_202 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_202 v)).
Proof. change (eval_hfexpr expr_202 (closed_202 v) (closed_202 v) = Some (Gval (Fuint 3) (word_202 v))). apply closed_202_value. Qed.
Lemma source_203 : find_driver 203 generated_module_0_stmts_0 = Some expr_203.
Proof. vm_compute. reflexivity. Qed.
Transparent word_203.
Lemma closed_203_value v : eval_hfexpr expr_203 (closed_203 v) (closed_203 v) = Some (Gval (Fuint 4) (word_203 v)).
Proof. unfold word_203, closed_203, expr_203, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_203.
Lemma node_203_value v : eval_hfexpr expr_203 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_203 v)).
Proof. change (eval_hfexpr expr_203 (closed_203 v) (closed_203 v) = Some (Gval (Fuint 4) (word_203 v))). apply closed_203_value. Qed.
Lemma source_204 : find_driver 204 generated_module_0_stmts_0 = Some expr_204.
Proof. vm_compute. reflexivity. Qed.
Transparent word_204.
Lemma closed_204_value v : eval_hfexpr expr_204 (closed_204 v) (closed_204 v) = Some (Gval (Fuint 4) (word_204 v)).
Proof. unfold word_204, closed_204, expr_204, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_204.
Lemma node_204_value v : eval_hfexpr expr_204 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_204 v)).
Proof. change (eval_hfexpr expr_204 (closed_204 v) (closed_204 v) = Some (Gval (Fuint 4) (word_204 v))). apply closed_204_value. Qed.
Lemma source_205 : find_driver 205 generated_module_0_stmts_0 = Some expr_205.
Proof. vm_compute. reflexivity. Qed.
Transparent word_205.
Lemma closed_205_value v : eval_hfexpr expr_205 (closed_205 v) (closed_205 v) = Some (Gval (Fuint 5) (word_205 v)).
Proof. unfold word_205, closed_205, expr_205, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_205.
Lemma node_205_value v : eval_hfexpr expr_205 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_205 v)).
Proof. change (eval_hfexpr expr_205 (closed_205 v) (closed_205 v) = Some (Gval (Fuint 5) (word_205 v))). apply closed_205_value. Qed.
Lemma source_206 : find_driver 206 generated_module_0_stmts_0 = Some expr_206.
Proof. vm_compute. reflexivity. Qed.
Transparent word_206.
Lemma closed_206_value v : eval_hfexpr expr_206 (closed_206 v) (closed_206 v) = Some (Gval (Fuint 5) (word_206 v)).
Proof. unfold word_206, closed_206, expr_206, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_206.
Lemma node_206_value v : eval_hfexpr expr_206 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_206 v)).
Proof. change (eval_hfexpr expr_206 (closed_206 v) (closed_206 v) = Some (Gval (Fuint 5) (word_206 v))). apply closed_206_value. Qed.
Lemma source_207 : find_driver 207 generated_module_0_stmts_0 = Some expr_207.
Proof. vm_compute. reflexivity. Qed.
Transparent word_207.
Lemma closed_207_value v : eval_hfexpr expr_207 (closed_207 v) (closed_207 v) = Some (Gval (Fuint 6) (word_207 v)).
Proof. unfold word_207, closed_207, expr_207, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_207.
Lemma node_207_value v : eval_hfexpr expr_207 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_207 v)).
Proof. change (eval_hfexpr expr_207 (closed_207 v) (closed_207 v) = Some (Gval (Fuint 6) (word_207 v))). apply closed_207_value. Qed.
Lemma source_208 : find_driver 208 generated_module_0_stmts_0 = Some expr_208.
Proof. vm_compute. reflexivity. Qed.
Transparent word_208.
Lemma closed_208_value v : eval_hfexpr expr_208 (closed_208 v) (closed_208 v) = Some (Gval (Fuint 8) (word_208 v)).
Proof. unfold word_208, closed_208, expr_208, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_208.
Lemma node_208_value v : eval_hfexpr expr_208 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_208 v)).
Proof. change (eval_hfexpr expr_208 (closed_208 v) (closed_208 v) = Some (Gval (Fuint 8) (word_208 v))). apply closed_208_value. Qed.
Lemma source_209 : find_driver 209 generated_module_0_stmts_0 = Some expr_209.
Proof. vm_compute. reflexivity. Qed.
Transparent word_209.
Lemma closed_209_value v : eval_hfexpr expr_209 (closed_209 v) (closed_209 v) = Some (Gval (Fuint 7) (word_209 v)).
Proof. unfold word_209, closed_209, expr_209, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_209.
Lemma node_209_value v : eval_hfexpr expr_209 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_209 v)).
Proof. change (eval_hfexpr expr_209 (closed_209 v) (closed_209 v) = Some (Gval (Fuint 7) (word_209 v))). apply closed_209_value. Qed.
Lemma source_210 : find_driver 210 generated_module_0_stmts_0 = Some expr_210.
Proof. vm_compute. reflexivity. Qed.
Transparent word_210.
Lemma closed_210_value v : eval_hfexpr expr_210 (closed_210 v) (closed_210 v) = Some (Gval (Fuint 1) (word_210 v)).
Proof. unfold word_210, closed_210, expr_210, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_210.
Lemma node_210_value v : eval_hfexpr expr_210 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_210 v)).
Proof. change (eval_hfexpr expr_210 (closed_210 v) (closed_210 v) = Some (Gval (Fuint 1) (word_210 v))). apply closed_210_value. Qed.
Lemma source_211 : find_driver 211 generated_module_0_stmts_0 = Some expr_211.
Proof. vm_compute. reflexivity. Qed.
Transparent word_211.
Lemma closed_211_value v : eval_hfexpr expr_211 (closed_211 v) (closed_211 v) = Some (Gval (Fuint 64) (word_211 v)).
Proof. unfold word_211, closed_211, expr_211, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_211.
Lemma node_211_value v : eval_hfexpr expr_211 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_211 v)).
Proof. change (eval_hfexpr expr_211 (closed_211 v) (closed_211 v) = Some (Gval (Fuint 64) (word_211 v))). apply closed_211_value. Qed.
Lemma source_212 : find_driver 212 generated_module_0_stmts_0 = Some expr_212.
Proof. vm_compute. reflexivity. Qed.
Transparent word_212.
Lemma closed_212_value v : eval_hfexpr expr_212 (closed_212 v) (closed_212 v) = Some (Gval (Fuint 1) (word_212 v)).
Proof. unfold word_212, closed_212, expr_212, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_212.
Lemma node_212_value v : eval_hfexpr expr_212 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_212 v)).
Proof. change (eval_hfexpr expr_212 (closed_212 v) (closed_212 v) = Some (Gval (Fuint 1) (word_212 v))). apply closed_212_value. Qed.
Lemma source_213 : find_driver 213 generated_module_0_stmts_0 = Some expr_213.
Proof. vm_compute. reflexivity. Qed.
Transparent word_213.
Lemma closed_213_value v : eval_hfexpr expr_213 (closed_213 v) (closed_213 v) = Some (Gval (Fuint 32) (word_213 v)).
Proof. unfold word_213, closed_213, expr_213, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_213.
Lemma node_213_value v : eval_hfexpr expr_213 (stable_env v) (stable_env v) = Some (Gval (Fuint 32) (word_213 v)).
Proof. change (eval_hfexpr expr_213 (closed_213 v) (closed_213 v) = Some (Gval (Fuint 32) (word_213 v))). apply closed_213_value. Qed.
Lemma source_214 : find_driver 214 generated_module_0_stmts_0 = Some expr_214.
Proof. vm_compute. reflexivity. Qed.
Transparent word_214.
Lemma closed_214_value v : eval_hfexpr expr_214 (closed_214 v) (closed_214 v) = Some (Gval (Fuint 32) (word_214 v)).
Proof. unfold word_214, closed_214, expr_214, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_214.
Lemma node_214_value v : eval_hfexpr expr_214 (stable_env v) (stable_env v) = Some (Gval (Fuint 32) (word_214 v)).
Proof. change (eval_hfexpr expr_214 (closed_214 v) (closed_214 v) = Some (Gval (Fuint 32) (word_214 v))). apply closed_214_value. Qed.
Lemma source_215 : find_driver 215 generated_module_0_stmts_0 = Some expr_215.
Proof. vm_compute. reflexivity. Qed.
Transparent word_215.
Lemma closed_215_value v : eval_hfexpr expr_215 (closed_215 v) (closed_215 v) = Some (Gval (Fuint 1) (word_215 v)).
Proof. unfold word_215, closed_215, expr_215, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_215.
Lemma node_215_value v : eval_hfexpr expr_215 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_215 v)).
Proof. change (eval_hfexpr expr_215 (closed_215 v) (closed_215 v) = Some (Gval (Fuint 1) (word_215 v))). apply closed_215_value. Qed.
Lemma source_216 : find_driver 216 generated_module_0_stmts_0 = Some expr_216.
Proof. vm_compute. reflexivity. Qed.
Transparent word_216.
Lemma closed_216_value v : eval_hfexpr expr_216 (closed_216 v) (closed_216 v) = Some (Gval (Fuint 16) (word_216 v)).
Proof. unfold word_216, closed_216, expr_216, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_216.
Lemma node_216_value v : eval_hfexpr expr_216 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_216 v)).
Proof. change (eval_hfexpr expr_216 (closed_216 v) (closed_216 v) = Some (Gval (Fuint 16) (word_216 v))). apply closed_216_value. Qed.
Lemma source_217 : find_driver 217 generated_module_0_stmts_0 = Some expr_217.
Proof. vm_compute. reflexivity. Qed.
Transparent word_217.
Lemma closed_217_value v : eval_hfexpr expr_217 (closed_217 v) (closed_217 v) = Some (Gval (Fuint 16) (word_217 v)).
Proof. unfold word_217, closed_217, expr_217, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_217.
Lemma node_217_value v : eval_hfexpr expr_217 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_217 v)).
Proof. change (eval_hfexpr expr_217 (closed_217 v) (closed_217 v) = Some (Gval (Fuint 16) (word_217 v))). apply closed_217_value. Qed.
Lemma source_218 : find_driver 218 generated_module_0_stmts_0 = Some expr_218.
Proof. vm_compute. reflexivity. Qed.
Transparent word_218.
Lemma closed_218_value v : eval_hfexpr expr_218 (closed_218 v) (closed_218 v) = Some (Gval (Fuint 1) (word_218 v)).
Proof. unfold word_218, closed_218, expr_218, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_218.
Lemma node_218_value v : eval_hfexpr expr_218 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_218 v)).
Proof. change (eval_hfexpr expr_218 (closed_218 v) (closed_218 v) = Some (Gval (Fuint 1) (word_218 v))). apply closed_218_value. Qed.
Lemma source_219 : find_driver 219 generated_module_0_stmts_0 = Some expr_219.
Proof. vm_compute. reflexivity. Qed.
Transparent word_219.
Lemma closed_219_value v : eval_hfexpr expr_219 (closed_219 v) (closed_219 v) = Some (Gval (Fuint 8) (word_219 v)).
Proof. unfold word_219, closed_219, expr_219, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_219.
Lemma node_219_value v : eval_hfexpr expr_219 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_219 v)).
Proof. change (eval_hfexpr expr_219 (closed_219 v) (closed_219 v) = Some (Gval (Fuint 8) (word_219 v))). apply closed_219_value. Qed.
Lemma source_220 : find_driver 220 generated_module_0_stmts_0 = Some expr_220.
Proof. vm_compute. reflexivity. Qed.
Transparent word_220.
Lemma closed_220_value v : eval_hfexpr expr_220 (closed_220 v) (closed_220 v) = Some (Gval (Fuint 8) (word_220 v)).
Proof. unfold word_220, closed_220, expr_220, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_220.
Lemma node_220_value v : eval_hfexpr expr_220 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_220 v)).
Proof. change (eval_hfexpr expr_220 (closed_220 v) (closed_220 v) = Some (Gval (Fuint 8) (word_220 v))). apply closed_220_value. Qed.
Lemma source_221 : find_driver 221 generated_module_0_stmts_0 = Some expr_221.
Proof. vm_compute. reflexivity. Qed.
Transparent word_221.
Lemma closed_221_value v : eval_hfexpr expr_221 (closed_221 v) (closed_221 v) = Some (Gval (Fuint 1) (word_221 v)).
Proof. unfold word_221, closed_221, expr_221, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_221.
Lemma node_221_value v : eval_hfexpr expr_221 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_221 v)).
Proof. change (eval_hfexpr expr_221 (closed_221 v) (closed_221 v) = Some (Gval (Fuint 1) (word_221 v))). apply closed_221_value. Qed.
Lemma source_222 : find_driver 222 generated_module_0_stmts_0 = Some expr_222.
Proof. vm_compute. reflexivity. Qed.
Transparent word_222.
Lemma closed_222_value v : eval_hfexpr expr_222 (closed_222 v) (closed_222 v) = Some (Gval (Fuint 4) (word_222 v)).
Proof. unfold word_222, closed_222, expr_222, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_222.
Lemma node_222_value v : eval_hfexpr expr_222 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_222 v)).
Proof. change (eval_hfexpr expr_222 (closed_222 v) (closed_222 v) = Some (Gval (Fuint 4) (word_222 v))). apply closed_222_value. Qed.
Lemma source_223 : find_driver 223 generated_module_0_stmts_0 = Some expr_223.
Proof. vm_compute. reflexivity. Qed.
Transparent word_223.
Lemma closed_223_value v : eval_hfexpr expr_223 (closed_223 v) (closed_223 v) = Some (Gval (Fuint 4) (word_223 v)).
Proof. unfold word_223, closed_223, expr_223, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_223.
Lemma node_223_value v : eval_hfexpr expr_223 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_223 v)).
Proof. change (eval_hfexpr expr_223 (closed_223 v) (closed_223 v) = Some (Gval (Fuint 4) (word_223 v))). apply closed_223_value. Qed.
Lemma source_224 : find_driver 224 generated_module_0_stmts_0 = Some expr_224.
Proof. vm_compute. reflexivity. Qed.
Transparent word_224.
Lemma closed_224_value v : eval_hfexpr expr_224 (closed_224 v) (closed_224 v) = Some (Gval (Fuint 1) (word_224 v)).
Proof. unfold word_224, closed_224, expr_224, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_224.
Lemma node_224_value v : eval_hfexpr expr_224 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_224 v)).
Proof. change (eval_hfexpr expr_224 (closed_224 v) (closed_224 v) = Some (Gval (Fuint 1) (word_224 v))). apply closed_224_value. Qed.
Lemma source_225 : find_driver 225 generated_module_0_stmts_0 = Some expr_225.
Proof. vm_compute. reflexivity. Qed.
Transparent word_225.
Lemma closed_225_value v : eval_hfexpr expr_225 (closed_225 v) (closed_225 v) = Some (Gval (Fuint 1) (word_225 v)).
Proof. unfold word_225, closed_225, expr_225, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_225.
Lemma node_225_value v : eval_hfexpr expr_225 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_225 v)).
Proof. change (eval_hfexpr expr_225 (closed_225 v) (closed_225 v) = Some (Gval (Fuint 1) (word_225 v))). apply closed_225_value. Qed.
Lemma source_226 : find_driver 226 generated_module_0_stmts_0 = Some expr_226.
Proof. vm_compute. reflexivity. Qed.
Transparent word_226.
Lemma closed_226_value v : eval_hfexpr expr_226 (closed_226 v) (closed_226 v) = Some (Gval (Fuint 1) (word_226 v)).
Proof. unfold word_226, closed_226, expr_226, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_226.
Lemma node_226_value v : eval_hfexpr expr_226 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_226 v)).
Proof. change (eval_hfexpr expr_226 (closed_226 v) (closed_226 v) = Some (Gval (Fuint 1) (word_226 v))). apply closed_226_value. Qed.
Lemma source_227 : find_driver 227 generated_module_0_stmts_0 = Some expr_227.
Proof. vm_compute. reflexivity. Qed.
Transparent word_227.
Lemma closed_227_value v : eval_hfexpr expr_227 (closed_227 v) (closed_227 v) = Some (Gval (Fuint 1) (word_227 v)).
Proof. unfold word_227, closed_227, expr_227, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_227.
Lemma node_227_value v : eval_hfexpr expr_227 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_227 v)).
Proof. change (eval_hfexpr expr_227 (closed_227 v) (closed_227 v) = Some (Gval (Fuint 1) (word_227 v))). apply closed_227_value. Qed.
Lemma source_228 : find_driver 228 generated_module_0_stmts_0 = Some expr_228.
Proof. vm_compute. reflexivity. Qed.
Transparent word_228.
Lemma closed_228_value v : eval_hfexpr expr_228 (closed_228 v) (closed_228 v) = Some (Gval (Fuint 2) (word_228 v)).
Proof. unfold word_228, closed_228, expr_228, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_228.
Lemma node_228_value v : eval_hfexpr expr_228 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_228 v)).
Proof. change (eval_hfexpr expr_228 (closed_228 v) (closed_228 v) = Some (Gval (Fuint 2) (word_228 v))). apply closed_228_value. Qed.
Lemma source_229 : find_driver 229 generated_module_0_stmts_0 = Some expr_229.
Proof. vm_compute. reflexivity. Qed.
Transparent word_229.
Lemma closed_229_value v : eval_hfexpr expr_229 (closed_229 v) (closed_229 v) = Some (Gval (Fuint 2) (word_229 v)).
Proof. unfold word_229, closed_229, expr_229, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_229.
Lemma node_229_value v : eval_hfexpr expr_229 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_229 v)).
Proof. change (eval_hfexpr expr_229 (closed_229 v) (closed_229 v) = Some (Gval (Fuint 2) (word_229 v))). apply closed_229_value. Qed.
Lemma source_230 : find_driver 230 generated_module_0_stmts_0 = Some expr_230.
Proof. vm_compute. reflexivity. Qed.
Transparent word_230.
Lemma closed_230_value v : eval_hfexpr expr_230 (closed_230 v) (closed_230 v) = Some (Gval (Fuint 1) (word_230 v)).
Proof. unfold word_230, closed_230, expr_230, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_230.
Lemma node_230_value v : eval_hfexpr expr_230 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_230 v)).
Proof. change (eval_hfexpr expr_230 (closed_230 v) (closed_230 v) = Some (Gval (Fuint 1) (word_230 v))). apply closed_230_value. Qed.
Lemma source_231 : find_driver 231 generated_module_0_stmts_0 = Some expr_231.
Proof. vm_compute. reflexivity. Qed.
Transparent word_231.
Lemma closed_231_value v : eval_hfexpr expr_231 (closed_231 v) (closed_231 v) = Some (Gval (Fuint 1) (word_231 v)).
Proof. unfold word_231, closed_231, expr_231, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_231.
Lemma node_231_value v : eval_hfexpr expr_231 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_231 v)).
Proof. change (eval_hfexpr expr_231 (closed_231 v) (closed_231 v) = Some (Gval (Fuint 1) (word_231 v))). apply closed_231_value. Qed.
Lemma source_232 : find_driver 232 generated_module_0_stmts_0 = Some expr_232.
Proof. vm_compute. reflexivity. Qed.
Transparent word_232.
Lemma closed_232_value v : eval_hfexpr expr_232 (closed_232 v) (closed_232 v) = Some (Gval (Fuint 1) (word_232 v)).
Proof. unfold word_232, closed_232, expr_232, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_232.
Lemma node_232_value v : eval_hfexpr expr_232 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_232 v)).
Proof. change (eval_hfexpr expr_232 (closed_232 v) (closed_232 v) = Some (Gval (Fuint 1) (word_232 v))). apply closed_232_value. Qed.
Lemma source_233 : find_driver 233 generated_module_0_stmts_0 = Some expr_233.
Proof. vm_compute. reflexivity. Qed.
Transparent word_233.
Lemma closed_233_value v : eval_hfexpr expr_233 (closed_233 v) (closed_233 v) = Some (Gval (Fuint 2) (word_233 v)).
Proof. unfold word_233, closed_233, expr_233, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_233.
Lemma node_233_value v : eval_hfexpr expr_233 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_233 v)).
Proof. change (eval_hfexpr expr_233 (closed_233 v) (closed_233 v) = Some (Gval (Fuint 2) (word_233 v))). apply closed_233_value. Qed.
Lemma source_234 : find_driver 234 generated_module_0_stmts_0 = Some expr_234.
Proof. vm_compute. reflexivity. Qed.
Transparent word_234.
Lemma closed_234_value v : eval_hfexpr expr_234 (closed_234 v) (closed_234 v) = Some (Gval (Fuint 2) (word_234 v)).
Proof. unfold word_234, closed_234, expr_234, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_234.
Lemma node_234_value v : eval_hfexpr expr_234 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_234 v)).
Proof. change (eval_hfexpr expr_234 (closed_234 v) (closed_234 v) = Some (Gval (Fuint 2) (word_234 v))). apply closed_234_value. Qed.
Lemma source_235 : find_driver 235 generated_module_0_stmts_0 = Some expr_235.
Proof. vm_compute. reflexivity. Qed.
Transparent word_235.
Lemma closed_235_value v : eval_hfexpr expr_235 (closed_235 v) (closed_235 v) = Some (Gval (Fuint 2) (word_235 v)).
Proof. unfold word_235, closed_235, expr_235, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_235.
Lemma node_235_value v : eval_hfexpr expr_235 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_235 v)).
Proof. change (eval_hfexpr expr_235 (closed_235 v) (closed_235 v) = Some (Gval (Fuint 2) (word_235 v))). apply closed_235_value. Qed.
Lemma source_236 : find_driver 236 generated_module_0_stmts_0 = Some expr_236.
Proof. vm_compute. reflexivity. Qed.
Transparent word_236.
Lemma closed_236_value v : eval_hfexpr expr_236 (closed_236 v) (closed_236 v) = Some (Gval (Fuint 3) (word_236 v)).
Proof. unfold word_236, closed_236, expr_236, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_236.
Lemma node_236_value v : eval_hfexpr expr_236 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_236 v)).
Proof. change (eval_hfexpr expr_236 (closed_236 v) (closed_236 v) = Some (Gval (Fuint 3) (word_236 v))). apply closed_236_value. Qed.
Lemma source_237 : find_driver 237 generated_module_0_stmts_0 = Some expr_237.
Proof. vm_compute. reflexivity. Qed.
Transparent word_237.
Lemma closed_237_value v : eval_hfexpr expr_237 (closed_237 v) (closed_237 v) = Some (Gval (Fuint 4) (word_237 v)).
Proof. unfold word_237, closed_237, expr_237, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_237.
Lemma node_237_value v : eval_hfexpr expr_237 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_237 v)).
Proof. change (eval_hfexpr expr_237 (closed_237 v) (closed_237 v) = Some (Gval (Fuint 4) (word_237 v))). apply closed_237_value. Qed.
Lemma source_238 : find_driver 238 generated_module_0_stmts_0 = Some expr_238.
Proof. vm_compute. reflexivity. Qed.
Transparent word_238.
Lemma closed_238_value v : eval_hfexpr expr_238 (closed_238 v) (closed_238 v) = Some (Gval (Fuint 4) (word_238 v)).
Proof. unfold word_238, closed_238, expr_238, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_238.
Lemma node_238_value v : eval_hfexpr expr_238 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_238 v)).
Proof. change (eval_hfexpr expr_238 (closed_238 v) (closed_238 v) = Some (Gval (Fuint 4) (word_238 v))). apply closed_238_value. Qed.
Lemma source_239 : find_driver 239 generated_module_0_stmts_0 = Some expr_239.
Proof. vm_compute. reflexivity. Qed.
Transparent word_239.
Lemma closed_239_value v : eval_hfexpr expr_239 (closed_239 v) (closed_239 v) = Some (Gval (Fuint 1) (word_239 v)).
Proof. unfold word_239, closed_239, expr_239, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_239.
Lemma node_239_value v : eval_hfexpr expr_239 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_239 v)).
Proof. change (eval_hfexpr expr_239 (closed_239 v) (closed_239 v) = Some (Gval (Fuint 1) (word_239 v))). apply closed_239_value. Qed.
Lemma source_240 : find_driver 240 generated_module_0_stmts_0 = Some expr_240.
Proof. vm_compute. reflexivity. Qed.
Transparent word_240.
Lemma closed_240_value v : eval_hfexpr expr_240 (closed_240 v) (closed_240 v) = Some (Gval (Fuint 1) (word_240 v)).
Proof. unfold word_240, closed_240, expr_240, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_240.
Lemma node_240_value v : eval_hfexpr expr_240 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_240 v)).
Proof. change (eval_hfexpr expr_240 (closed_240 v) (closed_240 v) = Some (Gval (Fuint 1) (word_240 v))). apply closed_240_value. Qed.
Lemma source_241 : find_driver 241 generated_module_0_stmts_0 = Some expr_241.
Proof. vm_compute. reflexivity. Qed.
Transparent word_241.
Lemma closed_241_value v : eval_hfexpr expr_241 (closed_241 v) (closed_241 v) = Some (Gval (Fuint 1) (word_241 v)).
Proof. unfold word_241, closed_241, expr_241, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_241.
Lemma node_241_value v : eval_hfexpr expr_241 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_241 v)).
Proof. change (eval_hfexpr expr_241 (closed_241 v) (closed_241 v) = Some (Gval (Fuint 1) (word_241 v))). apply closed_241_value. Qed.
Lemma source_242 : find_driver 242 generated_module_0_stmts_0 = Some expr_242.
Proof. vm_compute. reflexivity. Qed.
Transparent word_242.
Lemma closed_242_value v : eval_hfexpr expr_242 (closed_242 v) (closed_242 v) = Some (Gval (Fuint 1) (word_242 v)).
Proof. unfold word_242, closed_242, expr_242, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_242.
Lemma node_242_value v : eval_hfexpr expr_242 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_242 v)).
Proof. change (eval_hfexpr expr_242 (closed_242 v) (closed_242 v) = Some (Gval (Fuint 1) (word_242 v))). apply closed_242_value. Qed.
Lemma source_243 : find_driver 243 generated_module_0_stmts_0 = Some expr_243.
Proof. vm_compute. reflexivity. Qed.
Transparent word_243.
Lemma closed_243_value v : eval_hfexpr expr_243 (closed_243 v) (closed_243 v) = Some (Gval (Fuint 2) (word_243 v)).
Proof. unfold word_243, closed_243, expr_243, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_243.
Lemma node_243_value v : eval_hfexpr expr_243 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_243 v)).
Proof. change (eval_hfexpr expr_243 (closed_243 v) (closed_243 v) = Some (Gval (Fuint 2) (word_243 v))). apply closed_243_value. Qed.
Lemma source_244 : find_driver 244 generated_module_0_stmts_0 = Some expr_244.
Proof. vm_compute. reflexivity. Qed.
Transparent word_244.
Lemma closed_244_value v : eval_hfexpr expr_244 (closed_244 v) (closed_244 v) = Some (Gval (Fuint 2) (word_244 v)).
Proof. unfold word_244, closed_244, expr_244, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_244.
Lemma node_244_value v : eval_hfexpr expr_244 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_244 v)).
Proof. change (eval_hfexpr expr_244 (closed_244 v) (closed_244 v) = Some (Gval (Fuint 2) (word_244 v))). apply closed_244_value. Qed.
Lemma source_245 : find_driver 245 generated_module_0_stmts_0 = Some expr_245.
Proof. vm_compute. reflexivity. Qed.
Transparent word_245.
Lemma closed_245_value v : eval_hfexpr expr_245 (closed_245 v) (closed_245 v) = Some (Gval (Fuint 1) (word_245 v)).
Proof. unfold word_245, closed_245, expr_245, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_245.
Lemma node_245_value v : eval_hfexpr expr_245 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_245 v)).
Proof. change (eval_hfexpr expr_245 (closed_245 v) (closed_245 v) = Some (Gval (Fuint 1) (word_245 v))). apply closed_245_value. Qed.
Lemma source_246 : find_driver 246 generated_module_0_stmts_0 = Some expr_246.
Proof. vm_compute. reflexivity. Qed.
Transparent word_246.
Lemma closed_246_value v : eval_hfexpr expr_246 (closed_246 v) (closed_246 v) = Some (Gval (Fuint 1) (word_246 v)).
Proof. unfold word_246, closed_246, expr_246, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_246.
Lemma node_246_value v : eval_hfexpr expr_246 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_246 v)).
Proof. change (eval_hfexpr expr_246 (closed_246 v) (closed_246 v) = Some (Gval (Fuint 1) (word_246 v))). apply closed_246_value. Qed.
Lemma source_247 : find_driver 247 generated_module_0_stmts_0 = Some expr_247.
Proof. vm_compute. reflexivity. Qed.
Transparent word_247.
Lemma closed_247_value v : eval_hfexpr expr_247 (closed_247 v) (closed_247 v) = Some (Gval (Fuint 1) (word_247 v)).
Proof. unfold word_247, closed_247, expr_247, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_247.
Lemma node_247_value v : eval_hfexpr expr_247 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_247 v)).
Proof. change (eval_hfexpr expr_247 (closed_247 v) (closed_247 v) = Some (Gval (Fuint 1) (word_247 v))). apply closed_247_value. Qed.
Lemma source_248 : find_driver 248 generated_module_0_stmts_0 = Some expr_248.
Proof. vm_compute. reflexivity. Qed.
Transparent word_248.
Lemma closed_248_value v : eval_hfexpr expr_248 (closed_248 v) (closed_248 v) = Some (Gval (Fuint 2) (word_248 v)).
Proof. unfold word_248, closed_248, expr_248, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_248.
Lemma node_248_value v : eval_hfexpr expr_248 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_248 v)).
Proof. change (eval_hfexpr expr_248 (closed_248 v) (closed_248 v) = Some (Gval (Fuint 2) (word_248 v))). apply closed_248_value. Qed.
Lemma source_249 : find_driver 249 generated_module_0_stmts_0 = Some expr_249.
Proof. vm_compute. reflexivity. Qed.
Transparent word_249.
Lemma closed_249_value v : eval_hfexpr expr_249 (closed_249 v) (closed_249 v) = Some (Gval (Fuint 2) (word_249 v)).
Proof. unfold word_249, closed_249, expr_249, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_249.
Lemma node_249_value v : eval_hfexpr expr_249 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_249 v)).
Proof. change (eval_hfexpr expr_249 (closed_249 v) (closed_249 v) = Some (Gval (Fuint 2) (word_249 v))). apply closed_249_value. Qed.
Lemma source_250 : find_driver 250 generated_module_0_stmts_0 = Some expr_250.
Proof. vm_compute. reflexivity. Qed.
Transparent word_250.
Lemma closed_250_value v : eval_hfexpr expr_250 (closed_250 v) (closed_250 v) = Some (Gval (Fuint 2) (word_250 v)).
Proof. unfold word_250, closed_250, expr_250, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_250.
Lemma node_250_value v : eval_hfexpr expr_250 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_250 v)).
Proof. change (eval_hfexpr expr_250 (closed_250 v) (closed_250 v) = Some (Gval (Fuint 2) (word_250 v))). apply closed_250_value. Qed.
Lemma source_251 : find_driver 251 generated_module_0_stmts_0 = Some expr_251.
Proof. vm_compute. reflexivity. Qed.
Transparent word_251.
Lemma closed_251_value v : eval_hfexpr expr_251 (closed_251 v) (closed_251 v) = Some (Gval (Fuint 3) (word_251 v)).
Proof. unfold word_251, closed_251, expr_251, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_251.
Lemma node_251_value v : eval_hfexpr expr_251 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_251 v)).
Proof. change (eval_hfexpr expr_251 (closed_251 v) (closed_251 v) = Some (Gval (Fuint 3) (word_251 v))). apply closed_251_value. Qed.
Lemma source_252 : find_driver 252 generated_module_0_stmts_0 = Some expr_252.
Proof. vm_compute. reflexivity. Qed.
Transparent word_252.
Lemma closed_252_value v : eval_hfexpr expr_252 (closed_252 v) (closed_252 v) = Some (Gval (Fuint 3) (word_252 v)).
Proof. unfold word_252, closed_252, expr_252, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_252.
Lemma node_252_value v : eval_hfexpr expr_252 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_252 v)).
Proof. change (eval_hfexpr expr_252 (closed_252 v) (closed_252 v) = Some (Gval (Fuint 3) (word_252 v))). apply closed_252_value. Qed.
Lemma source_253 : find_driver 253 generated_module_0_stmts_0 = Some expr_253.
Proof. vm_compute. reflexivity. Qed.
Transparent word_253.
Lemma closed_253_value v : eval_hfexpr expr_253 (closed_253 v) (closed_253 v) = Some (Gval (Fuint 4) (word_253 v)).
Proof. unfold word_253, closed_253, expr_253, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_253.
Lemma node_253_value v : eval_hfexpr expr_253 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_253 v)).
Proof. change (eval_hfexpr expr_253 (closed_253 v) (closed_253 v) = Some (Gval (Fuint 4) (word_253 v))). apply closed_253_value. Qed.
Lemma source_254 : find_driver 254 generated_module_0_stmts_0 = Some expr_254.
Proof. vm_compute. reflexivity. Qed.
Transparent word_254.
Lemma closed_254_value v : eval_hfexpr expr_254 (closed_254 v) (closed_254 v) = Some (Gval (Fuint 8) (word_254 v)).
Proof. unfold word_254, closed_254, expr_254, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_254.
Lemma node_254_value v : eval_hfexpr expr_254 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_254 v)).
Proof. change (eval_hfexpr expr_254 (closed_254 v) (closed_254 v) = Some (Gval (Fuint 8) (word_254 v))). apply closed_254_value. Qed.
Lemma source_255 : find_driver 255 generated_module_0_stmts_0 = Some expr_255.
Proof. vm_compute. reflexivity. Qed.
Transparent word_255.
Lemma closed_255_value v : eval_hfexpr expr_255 (closed_255 v) (closed_255 v) = Some (Gval (Fuint 8) (word_255 v)).
Proof. unfold word_255, closed_255, expr_255, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_255.
Lemma node_255_value v : eval_hfexpr expr_255 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_255 v)).
Proof. change (eval_hfexpr expr_255 (closed_255 v) (closed_255 v) = Some (Gval (Fuint 8) (word_255 v))). apply closed_255_value. Qed.
Lemma source_256 : find_driver 256 generated_module_0_stmts_0 = Some expr_256.
Proof. vm_compute. reflexivity. Qed.
Transparent word_256.
Lemma closed_256_value v : eval_hfexpr expr_256 (closed_256 v) (closed_256 v) = Some (Gval (Fuint 1) (word_256 v)).
Proof. unfold word_256, closed_256, expr_256, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_256.
Lemma node_256_value v : eval_hfexpr expr_256 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_256 v)).
Proof. change (eval_hfexpr expr_256 (closed_256 v) (closed_256 v) = Some (Gval (Fuint 1) (word_256 v))). apply closed_256_value. Qed.
Lemma source_257 : find_driver 257 generated_module_0_stmts_0 = Some expr_257.
Proof. vm_compute. reflexivity. Qed.
Transparent word_257.
Lemma closed_257_value v : eval_hfexpr expr_257 (closed_257 v) (closed_257 v) = Some (Gval (Fuint 4) (word_257 v)).
Proof. unfold word_257, closed_257, expr_257, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_257.
Lemma node_257_value v : eval_hfexpr expr_257 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_257 v)).
Proof. change (eval_hfexpr expr_257 (closed_257 v) (closed_257 v) = Some (Gval (Fuint 4) (word_257 v))). apply closed_257_value. Qed.
Lemma source_258 : find_driver 258 generated_module_0_stmts_0 = Some expr_258.
Proof. vm_compute. reflexivity. Qed.
Transparent word_258.
Lemma closed_258_value v : eval_hfexpr expr_258 (closed_258 v) (closed_258 v) = Some (Gval (Fuint 4) (word_258 v)).
Proof. unfold word_258, closed_258, expr_258, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_258.
Lemma node_258_value v : eval_hfexpr expr_258 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_258 v)).
Proof. change (eval_hfexpr expr_258 (closed_258 v) (closed_258 v) = Some (Gval (Fuint 4) (word_258 v))). apply closed_258_value. Qed.
Lemma source_259 : find_driver 259 generated_module_0_stmts_0 = Some expr_259.
Proof. vm_compute. reflexivity. Qed.
Transparent word_259.
Lemma closed_259_value v : eval_hfexpr expr_259 (closed_259 v) (closed_259 v) = Some (Gval (Fuint 1) (word_259 v)).
Proof. unfold word_259, closed_259, expr_259, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_259.
Lemma node_259_value v : eval_hfexpr expr_259 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_259 v)).
Proof. change (eval_hfexpr expr_259 (closed_259 v) (closed_259 v) = Some (Gval (Fuint 1) (word_259 v))). apply closed_259_value. Qed.
Lemma source_260 : find_driver 260 generated_module_0_stmts_0 = Some expr_260.
Proof. vm_compute. reflexivity. Qed.
Transparent word_260.
Lemma closed_260_value v : eval_hfexpr expr_260 (closed_260 v) (closed_260 v) = Some (Gval (Fuint 1) (word_260 v)).
Proof. unfold word_260, closed_260, expr_260, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_260.
Lemma node_260_value v : eval_hfexpr expr_260 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_260 v)).
Proof. change (eval_hfexpr expr_260 (closed_260 v) (closed_260 v) = Some (Gval (Fuint 1) (word_260 v))). apply closed_260_value. Qed.
Lemma source_261 : find_driver 261 generated_module_0_stmts_0 = Some expr_261.
Proof. vm_compute. reflexivity. Qed.
Transparent word_261.
Lemma closed_261_value v : eval_hfexpr expr_261 (closed_261 v) (closed_261 v) = Some (Gval (Fuint 1) (word_261 v)).
Proof. unfold word_261, closed_261, expr_261, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_261.
Lemma node_261_value v : eval_hfexpr expr_261 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_261 v)).
Proof. change (eval_hfexpr expr_261 (closed_261 v) (closed_261 v) = Some (Gval (Fuint 1) (word_261 v))). apply closed_261_value. Qed.
Lemma source_262 : find_driver 262 generated_module_0_stmts_0 = Some expr_262.
Proof. vm_compute. reflexivity. Qed.
Transparent word_262.
Lemma closed_262_value v : eval_hfexpr expr_262 (closed_262 v) (closed_262 v) = Some (Gval (Fuint 1) (word_262 v)).
Proof. unfold word_262, closed_262, expr_262, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_262.
Lemma node_262_value v : eval_hfexpr expr_262 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_262 v)).
Proof. change (eval_hfexpr expr_262 (closed_262 v) (closed_262 v) = Some (Gval (Fuint 1) (word_262 v))). apply closed_262_value. Qed.
Lemma source_263 : find_driver 263 generated_module_0_stmts_0 = Some expr_263.
Proof. vm_compute. reflexivity. Qed.
Transparent word_263.
Lemma closed_263_value v : eval_hfexpr expr_263 (closed_263 v) (closed_263 v) = Some (Gval (Fuint 2) (word_263 v)).
Proof. unfold word_263, closed_263, expr_263, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_263.
Lemma node_263_value v : eval_hfexpr expr_263 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_263 v)).
Proof. change (eval_hfexpr expr_263 (closed_263 v) (closed_263 v) = Some (Gval (Fuint 2) (word_263 v))). apply closed_263_value. Qed.
Lemma source_264 : find_driver 264 generated_module_0_stmts_0 = Some expr_264.
Proof. vm_compute. reflexivity. Qed.
Transparent word_264.
Lemma closed_264_value v : eval_hfexpr expr_264 (closed_264 v) (closed_264 v) = Some (Gval (Fuint 2) (word_264 v)).
Proof. unfold word_264, closed_264, expr_264, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_264.
Lemma node_264_value v : eval_hfexpr expr_264 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_264 v)).
Proof. change (eval_hfexpr expr_264 (closed_264 v) (closed_264 v) = Some (Gval (Fuint 2) (word_264 v))). apply closed_264_value. Qed.
Lemma source_265 : find_driver 265 generated_module_0_stmts_0 = Some expr_265.
Proof. vm_compute. reflexivity. Qed.
Transparent word_265.
Lemma closed_265_value v : eval_hfexpr expr_265 (closed_265 v) (closed_265 v) = Some (Gval (Fuint 1) (word_265 v)).
Proof. unfold word_265, closed_265, expr_265, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_265.
Lemma node_265_value v : eval_hfexpr expr_265 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_265 v)).
Proof. change (eval_hfexpr expr_265 (closed_265 v) (closed_265 v) = Some (Gval (Fuint 1) (word_265 v))). apply closed_265_value. Qed.
Lemma source_266 : find_driver 266 generated_module_0_stmts_0 = Some expr_266.
Proof. vm_compute. reflexivity. Qed.
Transparent word_266.
Lemma closed_266_value v : eval_hfexpr expr_266 (closed_266 v) (closed_266 v) = Some (Gval (Fuint 1) (word_266 v)).
Proof. unfold word_266, closed_266, expr_266, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_266.
Lemma node_266_value v : eval_hfexpr expr_266 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_266 v)).
Proof. change (eval_hfexpr expr_266 (closed_266 v) (closed_266 v) = Some (Gval (Fuint 1) (word_266 v))). apply closed_266_value. Qed.
Lemma source_267 : find_driver 267 generated_module_0_stmts_0 = Some expr_267.
Proof. vm_compute. reflexivity. Qed.
Transparent word_267.
Lemma closed_267_value v : eval_hfexpr expr_267 (closed_267 v) (closed_267 v) = Some (Gval (Fuint 1) (word_267 v)).
Proof. unfold word_267, closed_267, expr_267, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_267.
Lemma node_267_value v : eval_hfexpr expr_267 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_267 v)).
Proof. change (eval_hfexpr expr_267 (closed_267 v) (closed_267 v) = Some (Gval (Fuint 1) (word_267 v))). apply closed_267_value. Qed.
Lemma source_268 : find_driver 268 generated_module_0_stmts_0 = Some expr_268.
Proof. vm_compute. reflexivity. Qed.
Transparent word_268.
Lemma closed_268_value v : eval_hfexpr expr_268 (closed_268 v) (closed_268 v) = Some (Gval (Fuint 2) (word_268 v)).
Proof. unfold word_268, closed_268, expr_268, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_268.
Lemma node_268_value v : eval_hfexpr expr_268 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_268 v)).
Proof. change (eval_hfexpr expr_268 (closed_268 v) (closed_268 v) = Some (Gval (Fuint 2) (word_268 v))). apply closed_268_value. Qed.
Lemma source_269 : find_driver 269 generated_module_0_stmts_0 = Some expr_269.
Proof. vm_compute. reflexivity. Qed.
Transparent word_269.
Lemma closed_269_value v : eval_hfexpr expr_269 (closed_269 v) (closed_269 v) = Some (Gval (Fuint 2) (word_269 v)).
Proof. unfold word_269, closed_269, expr_269, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_269.
Lemma node_269_value v : eval_hfexpr expr_269 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_269 v)).
Proof. change (eval_hfexpr expr_269 (closed_269 v) (closed_269 v) = Some (Gval (Fuint 2) (word_269 v))). apply closed_269_value. Qed.
Lemma source_270 : find_driver 270 generated_module_0_stmts_0 = Some expr_270.
Proof. vm_compute. reflexivity. Qed.
Transparent word_270.
Lemma closed_270_value v : eval_hfexpr expr_270 (closed_270 v) (closed_270 v) = Some (Gval (Fuint 2) (word_270 v)).
Proof. unfold word_270, closed_270, expr_270, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_270.
Lemma node_270_value v : eval_hfexpr expr_270 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_270 v)).
Proof. change (eval_hfexpr expr_270 (closed_270 v) (closed_270 v) = Some (Gval (Fuint 2) (word_270 v))). apply closed_270_value. Qed.
Lemma source_271 : find_driver 271 generated_module_0_stmts_0 = Some expr_271.
Proof. vm_compute. reflexivity. Qed.
Transparent word_271.
Lemma closed_271_value v : eval_hfexpr expr_271 (closed_271 v) (closed_271 v) = Some (Gval (Fuint 3) (word_271 v)).
Proof. unfold word_271, closed_271, expr_271, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_271.
Lemma node_271_value v : eval_hfexpr expr_271 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_271 v)).
Proof. change (eval_hfexpr expr_271 (closed_271 v) (closed_271 v) = Some (Gval (Fuint 3) (word_271 v))). apply closed_271_value. Qed.
Lemma source_272 : find_driver 272 generated_module_0_stmts_0 = Some expr_272.
Proof. vm_compute. reflexivity. Qed.
Transparent word_272.
Lemma closed_272_value v : eval_hfexpr expr_272 (closed_272 v) (closed_272 v) = Some (Gval (Fuint 4) (word_272 v)).
Proof. unfold word_272, closed_272, expr_272, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_272.
Lemma node_272_value v : eval_hfexpr expr_272 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_272 v)).
Proof. change (eval_hfexpr expr_272 (closed_272 v) (closed_272 v) = Some (Gval (Fuint 4) (word_272 v))). apply closed_272_value. Qed.
Lemma source_273 : find_driver 273 generated_module_0_stmts_0 = Some expr_273.
Proof. vm_compute. reflexivity. Qed.
Transparent word_273.
Lemma closed_273_value v : eval_hfexpr expr_273 (closed_273 v) (closed_273 v) = Some (Gval (Fuint 4) (word_273 v)).
Proof. unfold word_273, closed_273, expr_273, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_273.
Lemma node_273_value v : eval_hfexpr expr_273 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_273 v)).
Proof. change (eval_hfexpr expr_273 (closed_273 v) (closed_273 v) = Some (Gval (Fuint 4) (word_273 v))). apply closed_273_value. Qed.
Lemma source_274 : find_driver 274 generated_module_0_stmts_0 = Some expr_274.
Proof. vm_compute. reflexivity. Qed.
Transparent word_274.
Lemma closed_274_value v : eval_hfexpr expr_274 (closed_274 v) (closed_274 v) = Some (Gval (Fuint 1) (word_274 v)).
Proof. unfold word_274, closed_274, expr_274, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_274.
Lemma node_274_value v : eval_hfexpr expr_274 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_274 v)).
Proof. change (eval_hfexpr expr_274 (closed_274 v) (closed_274 v) = Some (Gval (Fuint 1) (word_274 v))). apply closed_274_value. Qed.
Lemma source_275 : find_driver 275 generated_module_0_stmts_0 = Some expr_275.
Proof. vm_compute. reflexivity. Qed.
Transparent word_275.
Lemma closed_275_value v : eval_hfexpr expr_275 (closed_275 v) (closed_275 v) = Some (Gval (Fuint 1) (word_275 v)).
Proof. unfold word_275, closed_275, expr_275, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_275.
Lemma node_275_value v : eval_hfexpr expr_275 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_275 v)).
Proof. change (eval_hfexpr expr_275 (closed_275 v) (closed_275 v) = Some (Gval (Fuint 1) (word_275 v))). apply closed_275_value. Qed.
Lemma source_276 : find_driver 276 generated_module_0_stmts_0 = Some expr_276.
Proof. vm_compute. reflexivity. Qed.
Transparent word_276.
Lemma closed_276_value v : eval_hfexpr expr_276 (closed_276 v) (closed_276 v) = Some (Gval (Fuint 1) (word_276 v)).
Proof. unfold word_276, closed_276, expr_276, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_276.
Lemma node_276_value v : eval_hfexpr expr_276 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_276 v)).
Proof. change (eval_hfexpr expr_276 (closed_276 v) (closed_276 v) = Some (Gval (Fuint 1) (word_276 v))). apply closed_276_value. Qed.
Lemma source_277 : find_driver 277 generated_module_0_stmts_0 = Some expr_277.
Proof. vm_compute. reflexivity. Qed.
Transparent word_277.
Lemma closed_277_value v : eval_hfexpr expr_277 (closed_277 v) (closed_277 v) = Some (Gval (Fuint 1) (word_277 v)).
Proof. unfold word_277, closed_277, expr_277, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_277.
Lemma node_277_value v : eval_hfexpr expr_277 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_277 v)).
Proof. change (eval_hfexpr expr_277 (closed_277 v) (closed_277 v) = Some (Gval (Fuint 1) (word_277 v))). apply closed_277_value. Qed.
Lemma source_278 : find_driver 278 generated_module_0_stmts_0 = Some expr_278.
Proof. vm_compute. reflexivity. Qed.
Transparent word_278.
Lemma closed_278_value v : eval_hfexpr expr_278 (closed_278 v) (closed_278 v) = Some (Gval (Fuint 2) (word_278 v)).
Proof. unfold word_278, closed_278, expr_278, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_278.
Lemma node_278_value v : eval_hfexpr expr_278 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_278 v)).
Proof. change (eval_hfexpr expr_278 (closed_278 v) (closed_278 v) = Some (Gval (Fuint 2) (word_278 v))). apply closed_278_value. Qed.
Lemma source_279 : find_driver 279 generated_module_0_stmts_0 = Some expr_279.
Proof. vm_compute. reflexivity. Qed.
Transparent word_279.
Lemma closed_279_value v : eval_hfexpr expr_279 (closed_279 v) (closed_279 v) = Some (Gval (Fuint 2) (word_279 v)).
Proof. unfold word_279, closed_279, expr_279, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_279.
Lemma node_279_value v : eval_hfexpr expr_279 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_279 v)).
Proof. change (eval_hfexpr expr_279 (closed_279 v) (closed_279 v) = Some (Gval (Fuint 2) (word_279 v))). apply closed_279_value. Qed.
Lemma source_280 : find_driver 280 generated_module_0_stmts_0 = Some expr_280.
Proof. vm_compute. reflexivity. Qed.
Transparent word_280.
Lemma closed_280_value v : eval_hfexpr expr_280 (closed_280 v) (closed_280 v) = Some (Gval (Fuint 1) (word_280 v)).
Proof. unfold word_280, closed_280, expr_280, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_280.
Lemma node_280_value v : eval_hfexpr expr_280 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_280 v)).
Proof. change (eval_hfexpr expr_280 (closed_280 v) (closed_280 v) = Some (Gval (Fuint 1) (word_280 v))). apply closed_280_value. Qed.
Lemma source_281 : find_driver 281 generated_module_0_stmts_0 = Some expr_281.
Proof. vm_compute. reflexivity. Qed.
Transparent word_281.
Lemma closed_281_value v : eval_hfexpr expr_281 (closed_281 v) (closed_281 v) = Some (Gval (Fuint 1) (word_281 v)).
Proof. unfold word_281, closed_281, expr_281, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_281.
Lemma node_281_value v : eval_hfexpr expr_281 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_281 v)).
Proof. change (eval_hfexpr expr_281 (closed_281 v) (closed_281 v) = Some (Gval (Fuint 1) (word_281 v))). apply closed_281_value. Qed.
Lemma source_282 : find_driver 282 generated_module_0_stmts_0 = Some expr_282.
Proof. vm_compute. reflexivity. Qed.
Transparent word_282.
Lemma closed_282_value v : eval_hfexpr expr_282 (closed_282 v) (closed_282 v) = Some (Gval (Fuint 1) (word_282 v)).
Proof. unfold word_282, closed_282, expr_282, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_282.
Lemma node_282_value v : eval_hfexpr expr_282 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_282 v)).
Proof. change (eval_hfexpr expr_282 (closed_282 v) (closed_282 v) = Some (Gval (Fuint 1) (word_282 v))). apply closed_282_value. Qed.
Lemma source_283 : find_driver 283 generated_module_0_stmts_0 = Some expr_283.
Proof. vm_compute. reflexivity. Qed.
Transparent word_283.
Lemma closed_283_value v : eval_hfexpr expr_283 (closed_283 v) (closed_283 v) = Some (Gval (Fuint 2) (word_283 v)).
Proof. unfold word_283, closed_283, expr_283, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_283.
Lemma node_283_value v : eval_hfexpr expr_283 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_283 v)).
Proof. change (eval_hfexpr expr_283 (closed_283 v) (closed_283 v) = Some (Gval (Fuint 2) (word_283 v))). apply closed_283_value. Qed.
Lemma source_284 : find_driver 284 generated_module_0_stmts_0 = Some expr_284.
Proof. vm_compute. reflexivity. Qed.
Transparent word_284.
Lemma closed_284_value v : eval_hfexpr expr_284 (closed_284 v) (closed_284 v) = Some (Gval (Fuint 2) (word_284 v)).
Proof. unfold word_284, closed_284, expr_284, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_284.
Lemma node_284_value v : eval_hfexpr expr_284 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_284 v)).
Proof. change (eval_hfexpr expr_284 (closed_284 v) (closed_284 v) = Some (Gval (Fuint 2) (word_284 v))). apply closed_284_value. Qed.
Lemma source_285 : find_driver 285 generated_module_0_stmts_0 = Some expr_285.
Proof. vm_compute. reflexivity. Qed.
Transparent word_285.
Lemma closed_285_value v : eval_hfexpr expr_285 (closed_285 v) (closed_285 v) = Some (Gval (Fuint 2) (word_285 v)).
Proof. unfold word_285, closed_285, expr_285, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_285.
Lemma node_285_value v : eval_hfexpr expr_285 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_285 v)).
Proof. change (eval_hfexpr expr_285 (closed_285 v) (closed_285 v) = Some (Gval (Fuint 2) (word_285 v))). apply closed_285_value. Qed.
Lemma source_286 : find_driver 286 generated_module_0_stmts_0 = Some expr_286.
Proof. vm_compute. reflexivity. Qed.
Transparent word_286.
Lemma closed_286_value v : eval_hfexpr expr_286 (closed_286 v) (closed_286 v) = Some (Gval (Fuint 3) (word_286 v)).
Proof. unfold word_286, closed_286, expr_286, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_286.
Lemma node_286_value v : eval_hfexpr expr_286 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_286 v)).
Proof. change (eval_hfexpr expr_286 (closed_286 v) (closed_286 v) = Some (Gval (Fuint 3) (word_286 v))). apply closed_286_value. Qed.
Lemma source_287 : find_driver 287 generated_module_0_stmts_0 = Some expr_287.
Proof. vm_compute. reflexivity. Qed.
Transparent word_287.
Lemma closed_287_value v : eval_hfexpr expr_287 (closed_287 v) (closed_287 v) = Some (Gval (Fuint 3) (word_287 v)).
Proof. unfold word_287, closed_287, expr_287, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_287.
Lemma node_287_value v : eval_hfexpr expr_287 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_287 v)).
Proof. change (eval_hfexpr expr_287 (closed_287 v) (closed_287 v) = Some (Gval (Fuint 3) (word_287 v))). apply closed_287_value. Qed.
Lemma source_288 : find_driver 288 generated_module_0_stmts_0 = Some expr_288.
Proof. vm_compute. reflexivity. Qed.
Transparent word_288.
Lemma closed_288_value v : eval_hfexpr expr_288 (closed_288 v) (closed_288 v) = Some (Gval (Fuint 4) (word_288 v)).
Proof. unfold word_288, closed_288, expr_288, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_288.
Lemma node_288_value v : eval_hfexpr expr_288 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_288 v)).
Proof. change (eval_hfexpr expr_288 (closed_288 v) (closed_288 v) = Some (Gval (Fuint 4) (word_288 v))). apply closed_288_value. Qed.
Lemma source_289 : find_driver 289 generated_module_0_stmts_0 = Some expr_289.
Proof. vm_compute. reflexivity. Qed.
Transparent word_289.
Lemma closed_289_value v : eval_hfexpr expr_289 (closed_289 v) (closed_289 v) = Some (Gval (Fuint 4) (word_289 v)).
Proof. unfold word_289, closed_289, expr_289, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_289.
Lemma node_289_value v : eval_hfexpr expr_289 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_289 v)).
Proof. change (eval_hfexpr expr_289 (closed_289 v) (closed_289 v) = Some (Gval (Fuint 4) (word_289 v))). apply closed_289_value. Qed.
Lemma source_290 : find_driver 290 generated_module_0_stmts_0 = Some expr_290.
Proof. vm_compute. reflexivity. Qed.
Transparent word_290.
Lemma closed_290_value v : eval_hfexpr expr_290 (closed_290 v) (closed_290 v) = Some (Gval (Fuint 5) (word_290 v)).
Proof. unfold word_290, closed_290, expr_290, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_290.
Lemma node_290_value v : eval_hfexpr expr_290 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_290 v)).
Proof. change (eval_hfexpr expr_290 (closed_290 v) (closed_290 v) = Some (Gval (Fuint 5) (word_290 v))). apply closed_290_value. Qed.
Lemma source_291 : find_driver 291 generated_module_0_stmts_0 = Some expr_291.
Proof. vm_compute. reflexivity. Qed.
Transparent word_291.
Lemma closed_291_value v : eval_hfexpr expr_291 (closed_291 v) (closed_291 v) = Some (Gval (Fuint 16) (word_291 v)).
Proof. unfold word_291, closed_291, expr_291, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_291.
Lemma node_291_value v : eval_hfexpr expr_291 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_291 v)).
Proof. change (eval_hfexpr expr_291 (closed_291 v) (closed_291 v) = Some (Gval (Fuint 16) (word_291 v))). apply closed_291_value. Qed.
Lemma source_292 : find_driver 292 generated_module_0_stmts_0 = Some expr_292.
Proof. vm_compute. reflexivity. Qed.
Transparent word_292.
Lemma closed_292_value v : eval_hfexpr expr_292 (closed_292 v) (closed_292 v) = Some (Gval (Fuint 16) (word_292 v)).
Proof. unfold word_292, closed_292, expr_292, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_292.
Lemma node_292_value v : eval_hfexpr expr_292 (stable_env v) (stable_env v) = Some (Gval (Fuint 16) (word_292 v)).
Proof. change (eval_hfexpr expr_292 (closed_292 v) (closed_292 v) = Some (Gval (Fuint 16) (word_292 v))). apply closed_292_value. Qed.
Lemma source_293 : find_driver 293 generated_module_0_stmts_0 = Some expr_293.
Proof. vm_compute. reflexivity. Qed.
Transparent word_293.
Lemma closed_293_value v : eval_hfexpr expr_293 (closed_293 v) (closed_293 v) = Some (Gval (Fuint 1) (word_293 v)).
Proof. unfold word_293, closed_293, expr_293, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_293.
Lemma node_293_value v : eval_hfexpr expr_293 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_293 v)).
Proof. change (eval_hfexpr expr_293 (closed_293 v) (closed_293 v) = Some (Gval (Fuint 1) (word_293 v))). apply closed_293_value. Qed.
Lemma source_294 : find_driver 294 generated_module_0_stmts_0 = Some expr_294.
Proof. vm_compute. reflexivity. Qed.
Transparent word_294.
Lemma closed_294_value v : eval_hfexpr expr_294 (closed_294 v) (closed_294 v) = Some (Gval (Fuint 8) (word_294 v)).
Proof. unfold word_294, closed_294, expr_294, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_294.
Lemma node_294_value v : eval_hfexpr expr_294 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_294 v)).
Proof. change (eval_hfexpr expr_294 (closed_294 v) (closed_294 v) = Some (Gval (Fuint 8) (word_294 v))). apply closed_294_value. Qed.
Lemma source_295 : find_driver 295 generated_module_0_stmts_0 = Some expr_295.
Proof. vm_compute. reflexivity. Qed.
Transparent word_295.
Lemma closed_295_value v : eval_hfexpr expr_295 (closed_295 v) (closed_295 v) = Some (Gval (Fuint 8) (word_295 v)).
Proof. unfold word_295, closed_295, expr_295, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_295.
Lemma node_295_value v : eval_hfexpr expr_295 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_295 v)).
Proof. change (eval_hfexpr expr_295 (closed_295 v) (closed_295 v) = Some (Gval (Fuint 8) (word_295 v))). apply closed_295_value. Qed.
Lemma source_296 : find_driver 296 generated_module_0_stmts_0 = Some expr_296.
Proof. vm_compute. reflexivity. Qed.
Transparent word_296.
Lemma closed_296_value v : eval_hfexpr expr_296 (closed_296 v) (closed_296 v) = Some (Gval (Fuint 1) (word_296 v)).
Proof. unfold word_296, closed_296, expr_296, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_296.
Lemma node_296_value v : eval_hfexpr expr_296 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_296 v)).
Proof. change (eval_hfexpr expr_296 (closed_296 v) (closed_296 v) = Some (Gval (Fuint 1) (word_296 v))). apply closed_296_value. Qed.
Lemma source_297 : find_driver 297 generated_module_0_stmts_0 = Some expr_297.
Proof. vm_compute. reflexivity. Qed.
Transparent word_297.
Lemma closed_297_value v : eval_hfexpr expr_297 (closed_297 v) (closed_297 v) = Some (Gval (Fuint 4) (word_297 v)).
Proof. unfold word_297, closed_297, expr_297, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_297.
Lemma node_297_value v : eval_hfexpr expr_297 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_297 v)).
Proof. change (eval_hfexpr expr_297 (closed_297 v) (closed_297 v) = Some (Gval (Fuint 4) (word_297 v))). apply closed_297_value. Qed.
Lemma source_298 : find_driver 298 generated_module_0_stmts_0 = Some expr_298.
Proof. vm_compute. reflexivity. Qed.
Transparent word_298.
Lemma closed_298_value v : eval_hfexpr expr_298 (closed_298 v) (closed_298 v) = Some (Gval (Fuint 4) (word_298 v)).
Proof. unfold word_298, closed_298, expr_298, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_298.
Lemma node_298_value v : eval_hfexpr expr_298 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_298 v)).
Proof. change (eval_hfexpr expr_298 (closed_298 v) (closed_298 v) = Some (Gval (Fuint 4) (word_298 v))). apply closed_298_value. Qed.
Lemma source_299 : find_driver 299 generated_module_0_stmts_0 = Some expr_299.
Proof. vm_compute. reflexivity. Qed.
Transparent word_299.
Lemma closed_299_value v : eval_hfexpr expr_299 (closed_299 v) (closed_299 v) = Some (Gval (Fuint 1) (word_299 v)).
Proof. unfold word_299, closed_299, expr_299, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_299.
Lemma node_299_value v : eval_hfexpr expr_299 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_299 v)).
Proof. change (eval_hfexpr expr_299 (closed_299 v) (closed_299 v) = Some (Gval (Fuint 1) (word_299 v))). apply closed_299_value. Qed.
Lemma source_300 : find_driver 300 generated_module_0_stmts_0 = Some expr_300.
Proof. vm_compute. reflexivity. Qed.
Transparent word_300.
Lemma closed_300_value v : eval_hfexpr expr_300 (closed_300 v) (closed_300 v) = Some (Gval (Fuint 1) (word_300 v)).
Proof. unfold word_300, closed_300, expr_300, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_300.
Lemma node_300_value v : eval_hfexpr expr_300 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_300 v)).
Proof. change (eval_hfexpr expr_300 (closed_300 v) (closed_300 v) = Some (Gval (Fuint 1) (word_300 v))). apply closed_300_value. Qed.
Lemma source_301 : find_driver 301 generated_module_0_stmts_0 = Some expr_301.
Proof. vm_compute. reflexivity. Qed.
Transparent word_301.
Lemma closed_301_value v : eval_hfexpr expr_301 (closed_301 v) (closed_301 v) = Some (Gval (Fuint 1) (word_301 v)).
Proof. unfold word_301, closed_301, expr_301, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_301.
Lemma node_301_value v : eval_hfexpr expr_301 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_301 v)).
Proof. change (eval_hfexpr expr_301 (closed_301 v) (closed_301 v) = Some (Gval (Fuint 1) (word_301 v))). apply closed_301_value. Qed.
Lemma source_302 : find_driver 302 generated_module_0_stmts_0 = Some expr_302.
Proof. vm_compute. reflexivity. Qed.
Transparent word_302.
Lemma closed_302_value v : eval_hfexpr expr_302 (closed_302 v) (closed_302 v) = Some (Gval (Fuint 1) (word_302 v)).
Proof. unfold word_302, closed_302, expr_302, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_302.
Lemma node_302_value v : eval_hfexpr expr_302 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_302 v)).
Proof. change (eval_hfexpr expr_302 (closed_302 v) (closed_302 v) = Some (Gval (Fuint 1) (word_302 v))). apply closed_302_value. Qed.
Lemma source_303 : find_driver 303 generated_module_0_stmts_0 = Some expr_303.
Proof. vm_compute. reflexivity. Qed.
Transparent word_303.
Lemma closed_303_value v : eval_hfexpr expr_303 (closed_303 v) (closed_303 v) = Some (Gval (Fuint 2) (word_303 v)).
Proof. unfold word_303, closed_303, expr_303, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_303.
Lemma node_303_value v : eval_hfexpr expr_303 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_303 v)).
Proof. change (eval_hfexpr expr_303 (closed_303 v) (closed_303 v) = Some (Gval (Fuint 2) (word_303 v))). apply closed_303_value. Qed.
Lemma source_304 : find_driver 304 generated_module_0_stmts_0 = Some expr_304.
Proof. vm_compute. reflexivity. Qed.
Transparent word_304.
Lemma closed_304_value v : eval_hfexpr expr_304 (closed_304 v) (closed_304 v) = Some (Gval (Fuint 2) (word_304 v)).
Proof. unfold word_304, closed_304, expr_304, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_304.
Lemma node_304_value v : eval_hfexpr expr_304 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_304 v)).
Proof. change (eval_hfexpr expr_304 (closed_304 v) (closed_304 v) = Some (Gval (Fuint 2) (word_304 v))). apply closed_304_value. Qed.
Lemma source_305 : find_driver 305 generated_module_0_stmts_0 = Some expr_305.
Proof. vm_compute. reflexivity. Qed.
Transparent word_305.
Lemma closed_305_value v : eval_hfexpr expr_305 (closed_305 v) (closed_305 v) = Some (Gval (Fuint 1) (word_305 v)).
Proof. unfold word_305, closed_305, expr_305, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_305.
Lemma node_305_value v : eval_hfexpr expr_305 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_305 v)).
Proof. change (eval_hfexpr expr_305 (closed_305 v) (closed_305 v) = Some (Gval (Fuint 1) (word_305 v))). apply closed_305_value. Qed.
Lemma source_306 : find_driver 306 generated_module_0_stmts_0 = Some expr_306.
Proof. vm_compute. reflexivity. Qed.
Transparent word_306.
Lemma closed_306_value v : eval_hfexpr expr_306 (closed_306 v) (closed_306 v) = Some (Gval (Fuint 1) (word_306 v)).
Proof. unfold word_306, closed_306, expr_306, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_306.
Lemma node_306_value v : eval_hfexpr expr_306 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_306 v)).
Proof. change (eval_hfexpr expr_306 (closed_306 v) (closed_306 v) = Some (Gval (Fuint 1) (word_306 v))). apply closed_306_value. Qed.
Lemma source_307 : find_driver 307 generated_module_0_stmts_0 = Some expr_307.
Proof. vm_compute. reflexivity. Qed.
Transparent word_307.
Lemma closed_307_value v : eval_hfexpr expr_307 (closed_307 v) (closed_307 v) = Some (Gval (Fuint 1) (word_307 v)).
Proof. unfold word_307, closed_307, expr_307, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_307.
Lemma node_307_value v : eval_hfexpr expr_307 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_307 v)).
Proof. change (eval_hfexpr expr_307 (closed_307 v) (closed_307 v) = Some (Gval (Fuint 1) (word_307 v))). apply closed_307_value. Qed.
Lemma source_308 : find_driver 308 generated_module_0_stmts_0 = Some expr_308.
Proof. vm_compute. reflexivity. Qed.
Transparent word_308.
Lemma closed_308_value v : eval_hfexpr expr_308 (closed_308 v) (closed_308 v) = Some (Gval (Fuint 2) (word_308 v)).
Proof. unfold word_308, closed_308, expr_308, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_308.
Lemma node_308_value v : eval_hfexpr expr_308 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_308 v)).
Proof. change (eval_hfexpr expr_308 (closed_308 v) (closed_308 v) = Some (Gval (Fuint 2) (word_308 v))). apply closed_308_value. Qed.
Lemma source_309 : find_driver 309 generated_module_0_stmts_0 = Some expr_309.
Proof. vm_compute. reflexivity. Qed.
Transparent word_309.
Lemma closed_309_value v : eval_hfexpr expr_309 (closed_309 v) (closed_309 v) = Some (Gval (Fuint 2) (word_309 v)).
Proof. unfold word_309, closed_309, expr_309, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_309.
Lemma node_309_value v : eval_hfexpr expr_309 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_309 v)).
Proof. change (eval_hfexpr expr_309 (closed_309 v) (closed_309 v) = Some (Gval (Fuint 2) (word_309 v))). apply closed_309_value. Qed.
Lemma source_310 : find_driver 310 generated_module_0_stmts_0 = Some expr_310.
Proof. vm_compute. reflexivity. Qed.
Transparent word_310.
Lemma closed_310_value v : eval_hfexpr expr_310 (closed_310 v) (closed_310 v) = Some (Gval (Fuint 2) (word_310 v)).
Proof. unfold word_310, closed_310, expr_310, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_310.
Lemma node_310_value v : eval_hfexpr expr_310 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_310 v)).
Proof. change (eval_hfexpr expr_310 (closed_310 v) (closed_310 v) = Some (Gval (Fuint 2) (word_310 v))). apply closed_310_value. Qed.
Lemma source_311 : find_driver 311 generated_module_0_stmts_0 = Some expr_311.
Proof. vm_compute. reflexivity. Qed.
Transparent word_311.
Lemma closed_311_value v : eval_hfexpr expr_311 (closed_311 v) (closed_311 v) = Some (Gval (Fuint 3) (word_311 v)).
Proof. unfold word_311, closed_311, expr_311, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_311.
Lemma node_311_value v : eval_hfexpr expr_311 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_311 v)).
Proof. change (eval_hfexpr expr_311 (closed_311 v) (closed_311 v) = Some (Gval (Fuint 3) (word_311 v))). apply closed_311_value. Qed.
Lemma source_312 : find_driver 312 generated_module_0_stmts_0 = Some expr_312.
Proof. vm_compute. reflexivity. Qed.
Transparent word_312.
Lemma closed_312_value v : eval_hfexpr expr_312 (closed_312 v) (closed_312 v) = Some (Gval (Fuint 4) (word_312 v)).
Proof. unfold word_312, closed_312, expr_312, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_312.
Lemma node_312_value v : eval_hfexpr expr_312 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_312 v)).
Proof. change (eval_hfexpr expr_312 (closed_312 v) (closed_312 v) = Some (Gval (Fuint 4) (word_312 v))). apply closed_312_value. Qed.
Lemma source_313 : find_driver 313 generated_module_0_stmts_0 = Some expr_313.
Proof. vm_compute. reflexivity. Qed.
Transparent word_313.
Lemma closed_313_value v : eval_hfexpr expr_313 (closed_313 v) (closed_313 v) = Some (Gval (Fuint 4) (word_313 v)).
Proof. unfold word_313, closed_313, expr_313, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_313.
Lemma node_313_value v : eval_hfexpr expr_313 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_313 v)).
Proof. change (eval_hfexpr expr_313 (closed_313 v) (closed_313 v) = Some (Gval (Fuint 4) (word_313 v))). apply closed_313_value. Qed.
Lemma source_314 : find_driver 314 generated_module_0_stmts_0 = Some expr_314.
Proof. vm_compute. reflexivity. Qed.
Transparent word_314.
Lemma closed_314_value v : eval_hfexpr expr_314 (closed_314 v) (closed_314 v) = Some (Gval (Fuint 1) (word_314 v)).
Proof. unfold word_314, closed_314, expr_314, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_314.
Lemma node_314_value v : eval_hfexpr expr_314 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_314 v)).
Proof. change (eval_hfexpr expr_314 (closed_314 v) (closed_314 v) = Some (Gval (Fuint 1) (word_314 v))). apply closed_314_value. Qed.
Lemma source_315 : find_driver 315 generated_module_0_stmts_0 = Some expr_315.
Proof. vm_compute. reflexivity. Qed.
Transparent word_315.
Lemma closed_315_value v : eval_hfexpr expr_315 (closed_315 v) (closed_315 v) = Some (Gval (Fuint 1) (word_315 v)).
Proof. unfold word_315, closed_315, expr_315, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_315.
Lemma node_315_value v : eval_hfexpr expr_315 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_315 v)).
Proof. change (eval_hfexpr expr_315 (closed_315 v) (closed_315 v) = Some (Gval (Fuint 1) (word_315 v))). apply closed_315_value. Qed.
Lemma source_316 : find_driver 316 generated_module_0_stmts_0 = Some expr_316.
Proof. vm_compute. reflexivity. Qed.
Transparent word_316.
Lemma closed_316_value v : eval_hfexpr expr_316 (closed_316 v) (closed_316 v) = Some (Gval (Fuint 1) (word_316 v)).
Proof. unfold word_316, closed_316, expr_316, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_316.
Lemma node_316_value v : eval_hfexpr expr_316 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_316 v)).
Proof. change (eval_hfexpr expr_316 (closed_316 v) (closed_316 v) = Some (Gval (Fuint 1) (word_316 v))). apply closed_316_value. Qed.
Lemma source_317 : find_driver 317 generated_module_0_stmts_0 = Some expr_317.
Proof. vm_compute. reflexivity. Qed.
Transparent word_317.
Lemma closed_317_value v : eval_hfexpr expr_317 (closed_317 v) (closed_317 v) = Some (Gval (Fuint 1) (word_317 v)).
Proof. unfold word_317, closed_317, expr_317, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_317.
Lemma node_317_value v : eval_hfexpr expr_317 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_317 v)).
Proof. change (eval_hfexpr expr_317 (closed_317 v) (closed_317 v) = Some (Gval (Fuint 1) (word_317 v))). apply closed_317_value. Qed.
Lemma source_318 : find_driver 318 generated_module_0_stmts_0 = Some expr_318.
Proof. vm_compute. reflexivity. Qed.
Transparent word_318.
Lemma closed_318_value v : eval_hfexpr expr_318 (closed_318 v) (closed_318 v) = Some (Gval (Fuint 2) (word_318 v)).
Proof. unfold word_318, closed_318, expr_318, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_318.
Lemma node_318_value v : eval_hfexpr expr_318 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_318 v)).
Proof. change (eval_hfexpr expr_318 (closed_318 v) (closed_318 v) = Some (Gval (Fuint 2) (word_318 v))). apply closed_318_value. Qed.
Lemma source_319 : find_driver 319 generated_module_0_stmts_0 = Some expr_319.
Proof. vm_compute. reflexivity. Qed.
Transparent word_319.
Lemma closed_319_value v : eval_hfexpr expr_319 (closed_319 v) (closed_319 v) = Some (Gval (Fuint 2) (word_319 v)).
Proof. unfold word_319, closed_319, expr_319, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_319.
Lemma node_319_value v : eval_hfexpr expr_319 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_319 v)).
Proof. change (eval_hfexpr expr_319 (closed_319 v) (closed_319 v) = Some (Gval (Fuint 2) (word_319 v))). apply closed_319_value. Qed.
Lemma source_320 : find_driver 320 generated_module_0_stmts_0 = Some expr_320.
Proof. vm_compute. reflexivity. Qed.
Transparent word_320.
Lemma closed_320_value v : eval_hfexpr expr_320 (closed_320 v) (closed_320 v) = Some (Gval (Fuint 1) (word_320 v)).
Proof. unfold word_320, closed_320, expr_320, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_320.
Lemma node_320_value v : eval_hfexpr expr_320 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_320 v)).
Proof. change (eval_hfexpr expr_320 (closed_320 v) (closed_320 v) = Some (Gval (Fuint 1) (word_320 v))). apply closed_320_value. Qed.
Lemma source_321 : find_driver 321 generated_module_0_stmts_0 = Some expr_321.
Proof. vm_compute. reflexivity. Qed.
Transparent word_321.
Lemma closed_321_value v : eval_hfexpr expr_321 (closed_321 v) (closed_321 v) = Some (Gval (Fuint 1) (word_321 v)).
Proof. unfold word_321, closed_321, expr_321, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_321.
Lemma node_321_value v : eval_hfexpr expr_321 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_321 v)).
Proof. change (eval_hfexpr expr_321 (closed_321 v) (closed_321 v) = Some (Gval (Fuint 1) (word_321 v))). apply closed_321_value. Qed.
Lemma source_322 : find_driver 322 generated_module_0_stmts_0 = Some expr_322.
Proof. vm_compute. reflexivity. Qed.
Transparent word_322.
Lemma closed_322_value v : eval_hfexpr expr_322 (closed_322 v) (closed_322 v) = Some (Gval (Fuint 1) (word_322 v)).
Proof. unfold word_322, closed_322, expr_322, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_322.
Lemma node_322_value v : eval_hfexpr expr_322 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_322 v)).
Proof. change (eval_hfexpr expr_322 (closed_322 v) (closed_322 v) = Some (Gval (Fuint 1) (word_322 v))). apply closed_322_value. Qed.
Lemma source_323 : find_driver 323 generated_module_0_stmts_0 = Some expr_323.
Proof. vm_compute. reflexivity. Qed.
Transparent word_323.
Lemma closed_323_value v : eval_hfexpr expr_323 (closed_323 v) (closed_323 v) = Some (Gval (Fuint 2) (word_323 v)).
Proof. unfold word_323, closed_323, expr_323, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_323.
Lemma node_323_value v : eval_hfexpr expr_323 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_323 v)).
Proof. change (eval_hfexpr expr_323 (closed_323 v) (closed_323 v) = Some (Gval (Fuint 2) (word_323 v))). apply closed_323_value. Qed.
Lemma source_324 : find_driver 324 generated_module_0_stmts_0 = Some expr_324.
Proof. vm_compute. reflexivity. Qed.
Transparent word_324.
Lemma closed_324_value v : eval_hfexpr expr_324 (closed_324 v) (closed_324 v) = Some (Gval (Fuint 2) (word_324 v)).
Proof. unfold word_324, closed_324, expr_324, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_324.
Lemma node_324_value v : eval_hfexpr expr_324 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_324 v)).
Proof. change (eval_hfexpr expr_324 (closed_324 v) (closed_324 v) = Some (Gval (Fuint 2) (word_324 v))). apply closed_324_value. Qed.
Lemma source_325 : find_driver 325 generated_module_0_stmts_0 = Some expr_325.
Proof. vm_compute. reflexivity. Qed.
Transparent word_325.
Lemma closed_325_value v : eval_hfexpr expr_325 (closed_325 v) (closed_325 v) = Some (Gval (Fuint 2) (word_325 v)).
Proof. unfold word_325, closed_325, expr_325, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_325.
Lemma node_325_value v : eval_hfexpr expr_325 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_325 v)).
Proof. change (eval_hfexpr expr_325 (closed_325 v) (closed_325 v) = Some (Gval (Fuint 2) (word_325 v))). apply closed_325_value. Qed.
Lemma source_326 : find_driver 326 generated_module_0_stmts_0 = Some expr_326.
Proof. vm_compute. reflexivity. Qed.
Transparent word_326.
Lemma closed_326_value v : eval_hfexpr expr_326 (closed_326 v) (closed_326 v) = Some (Gval (Fuint 3) (word_326 v)).
Proof. unfold word_326, closed_326, expr_326, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_326.
Lemma node_326_value v : eval_hfexpr expr_326 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_326 v)).
Proof. change (eval_hfexpr expr_326 (closed_326 v) (closed_326 v) = Some (Gval (Fuint 3) (word_326 v))). apply closed_326_value. Qed.
Lemma source_327 : find_driver 327 generated_module_0_stmts_0 = Some expr_327.
Proof. vm_compute. reflexivity. Qed.
Transparent word_327.
Lemma closed_327_value v : eval_hfexpr expr_327 (closed_327 v) (closed_327 v) = Some (Gval (Fuint 3) (word_327 v)).
Proof. unfold word_327, closed_327, expr_327, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_327.
Lemma node_327_value v : eval_hfexpr expr_327 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_327 v)).
Proof. change (eval_hfexpr expr_327 (closed_327 v) (closed_327 v) = Some (Gval (Fuint 3) (word_327 v))). apply closed_327_value. Qed.
Lemma source_328 : find_driver 328 generated_module_0_stmts_0 = Some expr_328.
Proof. vm_compute. reflexivity. Qed.
Transparent word_328.
Lemma closed_328_value v : eval_hfexpr expr_328 (closed_328 v) (closed_328 v) = Some (Gval (Fuint 4) (word_328 v)).
Proof. unfold word_328, closed_328, expr_328, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_328.
Lemma node_328_value v : eval_hfexpr expr_328 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_328 v)).
Proof. change (eval_hfexpr expr_328 (closed_328 v) (closed_328 v) = Some (Gval (Fuint 4) (word_328 v))). apply closed_328_value. Qed.
Lemma source_329 : find_driver 329 generated_module_0_stmts_0 = Some expr_329.
Proof. vm_compute. reflexivity. Qed.
Transparent word_329.
Lemma closed_329_value v : eval_hfexpr expr_329 (closed_329 v) (closed_329 v) = Some (Gval (Fuint 8) (word_329 v)).
Proof. unfold word_329, closed_329, expr_329, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_329.
Lemma node_329_value v : eval_hfexpr expr_329 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_329 v)).
Proof. change (eval_hfexpr expr_329 (closed_329 v) (closed_329 v) = Some (Gval (Fuint 8) (word_329 v))). apply closed_329_value. Qed.
Lemma source_330 : find_driver 330 generated_module_0_stmts_0 = Some expr_330.
Proof. vm_compute. reflexivity. Qed.
Transparent word_330.
Lemma closed_330_value v : eval_hfexpr expr_330 (closed_330 v) (closed_330 v) = Some (Gval (Fuint 8) (word_330 v)).
Proof. unfold word_330, closed_330, expr_330, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_330.
Lemma node_330_value v : eval_hfexpr expr_330 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_330 v)).
Proof. change (eval_hfexpr expr_330 (closed_330 v) (closed_330 v) = Some (Gval (Fuint 8) (word_330 v))). apply closed_330_value. Qed.
Lemma source_331 : find_driver 331 generated_module_0_stmts_0 = Some expr_331.
Proof. vm_compute. reflexivity. Qed.
Transparent word_331.
Lemma closed_331_value v : eval_hfexpr expr_331 (closed_331 v) (closed_331 v) = Some (Gval (Fuint 1) (word_331 v)).
Proof. unfold word_331, closed_331, expr_331, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_331.
Lemma node_331_value v : eval_hfexpr expr_331 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_331 v)).
Proof. change (eval_hfexpr expr_331 (closed_331 v) (closed_331 v) = Some (Gval (Fuint 1) (word_331 v))). apply closed_331_value. Qed.
Lemma source_332 : find_driver 332 generated_module_0_stmts_0 = Some expr_332.
Proof. vm_compute. reflexivity. Qed.
Transparent word_332.
Lemma closed_332_value v : eval_hfexpr expr_332 (closed_332 v) (closed_332 v) = Some (Gval (Fuint 4) (word_332 v)).
Proof. unfold word_332, closed_332, expr_332, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_332.
Lemma node_332_value v : eval_hfexpr expr_332 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_332 v)).
Proof. change (eval_hfexpr expr_332 (closed_332 v) (closed_332 v) = Some (Gval (Fuint 4) (word_332 v))). apply closed_332_value. Qed.
Lemma source_333 : find_driver 333 generated_module_0_stmts_0 = Some expr_333.
Proof. vm_compute. reflexivity. Qed.
Transparent word_333.
Lemma closed_333_value v : eval_hfexpr expr_333 (closed_333 v) (closed_333 v) = Some (Gval (Fuint 4) (word_333 v)).
Proof. unfold word_333, closed_333, expr_333, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_333.
Lemma node_333_value v : eval_hfexpr expr_333 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_333 v)).
Proof. change (eval_hfexpr expr_333 (closed_333 v) (closed_333 v) = Some (Gval (Fuint 4) (word_333 v))). apply closed_333_value. Qed.
Lemma source_334 : find_driver 334 generated_module_0_stmts_0 = Some expr_334.
Proof. vm_compute. reflexivity. Qed.
Transparent word_334.
Lemma closed_334_value v : eval_hfexpr expr_334 (closed_334 v) (closed_334 v) = Some (Gval (Fuint 1) (word_334 v)).
Proof. unfold word_334, closed_334, expr_334, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_334.
Lemma node_334_value v : eval_hfexpr expr_334 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_334 v)).
Proof. change (eval_hfexpr expr_334 (closed_334 v) (closed_334 v) = Some (Gval (Fuint 1) (word_334 v))). apply closed_334_value. Qed.
Lemma source_335 : find_driver 335 generated_module_0_stmts_0 = Some expr_335.
Proof. vm_compute. reflexivity. Qed.
Transparent word_335.
Lemma closed_335_value v : eval_hfexpr expr_335 (closed_335 v) (closed_335 v) = Some (Gval (Fuint 1) (word_335 v)).
Proof. unfold word_335, closed_335, expr_335, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_335.
Lemma node_335_value v : eval_hfexpr expr_335 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_335 v)).
Proof. change (eval_hfexpr expr_335 (closed_335 v) (closed_335 v) = Some (Gval (Fuint 1) (word_335 v))). apply closed_335_value. Qed.
Lemma source_336 : find_driver 336 generated_module_0_stmts_0 = Some expr_336.
Proof. vm_compute. reflexivity. Qed.
Transparent word_336.
Lemma closed_336_value v : eval_hfexpr expr_336 (closed_336 v) (closed_336 v) = Some (Gval (Fuint 1) (word_336 v)).
Proof. unfold word_336, closed_336, expr_336, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_336.
Lemma node_336_value v : eval_hfexpr expr_336 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_336 v)).
Proof. change (eval_hfexpr expr_336 (closed_336 v) (closed_336 v) = Some (Gval (Fuint 1) (word_336 v))). apply closed_336_value. Qed.
Lemma source_337 : find_driver 337 generated_module_0_stmts_0 = Some expr_337.
Proof. vm_compute. reflexivity. Qed.
Transparent word_337.
Lemma closed_337_value v : eval_hfexpr expr_337 (closed_337 v) (closed_337 v) = Some (Gval (Fuint 1) (word_337 v)).
Proof. unfold word_337, closed_337, expr_337, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_337.
Lemma node_337_value v : eval_hfexpr expr_337 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_337 v)).
Proof. change (eval_hfexpr expr_337 (closed_337 v) (closed_337 v) = Some (Gval (Fuint 1) (word_337 v))). apply closed_337_value. Qed.
Lemma source_338 : find_driver 338 generated_module_0_stmts_0 = Some expr_338.
Proof. vm_compute. reflexivity. Qed.
Transparent word_338.
Lemma closed_338_value v : eval_hfexpr expr_338 (closed_338 v) (closed_338 v) = Some (Gval (Fuint 2) (word_338 v)).
Proof. unfold word_338, closed_338, expr_338, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_338.
Lemma node_338_value v : eval_hfexpr expr_338 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_338 v)).
Proof. change (eval_hfexpr expr_338 (closed_338 v) (closed_338 v) = Some (Gval (Fuint 2) (word_338 v))). apply closed_338_value. Qed.
Lemma source_339 : find_driver 339 generated_module_0_stmts_0 = Some expr_339.
Proof. vm_compute. reflexivity. Qed.
Transparent word_339.
Lemma closed_339_value v : eval_hfexpr expr_339 (closed_339 v) (closed_339 v) = Some (Gval (Fuint 2) (word_339 v)).
Proof. unfold word_339, closed_339, expr_339, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_339.
Lemma node_339_value v : eval_hfexpr expr_339 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_339 v)).
Proof. change (eval_hfexpr expr_339 (closed_339 v) (closed_339 v) = Some (Gval (Fuint 2) (word_339 v))). apply closed_339_value. Qed.
Lemma source_340 : find_driver 340 generated_module_0_stmts_0 = Some expr_340.
Proof. vm_compute. reflexivity. Qed.
Transparent word_340.
Lemma closed_340_value v : eval_hfexpr expr_340 (closed_340 v) (closed_340 v) = Some (Gval (Fuint 1) (word_340 v)).
Proof. unfold word_340, closed_340, expr_340, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_340.
Lemma node_340_value v : eval_hfexpr expr_340 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_340 v)).
Proof. change (eval_hfexpr expr_340 (closed_340 v) (closed_340 v) = Some (Gval (Fuint 1) (word_340 v))). apply closed_340_value. Qed.
Lemma source_341 : find_driver 341 generated_module_0_stmts_0 = Some expr_341.
Proof. vm_compute. reflexivity. Qed.
Transparent word_341.
Lemma closed_341_value v : eval_hfexpr expr_341 (closed_341 v) (closed_341 v) = Some (Gval (Fuint 1) (word_341 v)).
Proof. unfold word_341, closed_341, expr_341, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_341.
Lemma node_341_value v : eval_hfexpr expr_341 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_341 v)).
Proof. change (eval_hfexpr expr_341 (closed_341 v) (closed_341 v) = Some (Gval (Fuint 1) (word_341 v))). apply closed_341_value. Qed.
Lemma source_342 : find_driver 342 generated_module_0_stmts_0 = Some expr_342.
Proof. vm_compute. reflexivity. Qed.
Transparent word_342.
Lemma closed_342_value v : eval_hfexpr expr_342 (closed_342 v) (closed_342 v) = Some (Gval (Fuint 1) (word_342 v)).
Proof. unfold word_342, closed_342, expr_342, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_342.
Lemma node_342_value v : eval_hfexpr expr_342 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_342 v)).
Proof. change (eval_hfexpr expr_342 (closed_342 v) (closed_342 v) = Some (Gval (Fuint 1) (word_342 v))). apply closed_342_value. Qed.
Lemma source_343 : find_driver 343 generated_module_0_stmts_0 = Some expr_343.
Proof. vm_compute. reflexivity. Qed.
Transparent word_343.
Lemma closed_343_value v : eval_hfexpr expr_343 (closed_343 v) (closed_343 v) = Some (Gval (Fuint 2) (word_343 v)).
Proof. unfold word_343, closed_343, expr_343, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_343.
Lemma node_343_value v : eval_hfexpr expr_343 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_343 v)).
Proof. change (eval_hfexpr expr_343 (closed_343 v) (closed_343 v) = Some (Gval (Fuint 2) (word_343 v))). apply closed_343_value. Qed.
Lemma source_344 : find_driver 344 generated_module_0_stmts_0 = Some expr_344.
Proof. vm_compute. reflexivity. Qed.
Transparent word_344.
Lemma closed_344_value v : eval_hfexpr expr_344 (closed_344 v) (closed_344 v) = Some (Gval (Fuint 2) (word_344 v)).
Proof. unfold word_344, closed_344, expr_344, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_344.
Lemma node_344_value v : eval_hfexpr expr_344 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_344 v)).
Proof. change (eval_hfexpr expr_344 (closed_344 v) (closed_344 v) = Some (Gval (Fuint 2) (word_344 v))). apply closed_344_value. Qed.
Lemma source_345 : find_driver 345 generated_module_0_stmts_0 = Some expr_345.
Proof. vm_compute. reflexivity. Qed.
Transparent word_345.
Lemma closed_345_value v : eval_hfexpr expr_345 (closed_345 v) (closed_345 v) = Some (Gval (Fuint 2) (word_345 v)).
Proof. unfold word_345, closed_345, expr_345, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_345.
Lemma node_345_value v : eval_hfexpr expr_345 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_345 v)).
Proof. change (eval_hfexpr expr_345 (closed_345 v) (closed_345 v) = Some (Gval (Fuint 2) (word_345 v))). apply closed_345_value. Qed.
Lemma source_346 : find_driver 346 generated_module_0_stmts_0 = Some expr_346.
Proof. vm_compute. reflexivity. Qed.
Transparent word_346.
Lemma closed_346_value v : eval_hfexpr expr_346 (closed_346 v) (closed_346 v) = Some (Gval (Fuint 3) (word_346 v)).
Proof. unfold word_346, closed_346, expr_346, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_346.
Lemma node_346_value v : eval_hfexpr expr_346 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_346 v)).
Proof. change (eval_hfexpr expr_346 (closed_346 v) (closed_346 v) = Some (Gval (Fuint 3) (word_346 v))). apply closed_346_value. Qed.
Lemma source_347 : find_driver 347 generated_module_0_stmts_0 = Some expr_347.
Proof. vm_compute. reflexivity. Qed.
Transparent word_347.
Lemma closed_347_value v : eval_hfexpr expr_347 (closed_347 v) (closed_347 v) = Some (Gval (Fuint 4) (word_347 v)).
Proof. unfold word_347, closed_347, expr_347, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_347.
Lemma node_347_value v : eval_hfexpr expr_347 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_347 v)).
Proof. change (eval_hfexpr expr_347 (closed_347 v) (closed_347 v) = Some (Gval (Fuint 4) (word_347 v))). apply closed_347_value. Qed.
Lemma source_348 : find_driver 348 generated_module_0_stmts_0 = Some expr_348.
Proof. vm_compute. reflexivity. Qed.
Transparent word_348.
Lemma closed_348_value v : eval_hfexpr expr_348 (closed_348 v) (closed_348 v) = Some (Gval (Fuint 4) (word_348 v)).
Proof. unfold word_348, closed_348, expr_348, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_348.
Lemma node_348_value v : eval_hfexpr expr_348 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_348 v)).
Proof. change (eval_hfexpr expr_348 (closed_348 v) (closed_348 v) = Some (Gval (Fuint 4) (word_348 v))). apply closed_348_value. Qed.
Lemma source_349 : find_driver 349 generated_module_0_stmts_0 = Some expr_349.
Proof. vm_compute. reflexivity. Qed.
Transparent word_349.
Lemma closed_349_value v : eval_hfexpr expr_349 (closed_349 v) (closed_349 v) = Some (Gval (Fuint 1) (word_349 v)).
Proof. unfold word_349, closed_349, expr_349, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_349.
Lemma node_349_value v : eval_hfexpr expr_349 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_349 v)).
Proof. change (eval_hfexpr expr_349 (closed_349 v) (closed_349 v) = Some (Gval (Fuint 1) (word_349 v))). apply closed_349_value. Qed.
Lemma source_350 : find_driver 350 generated_module_0_stmts_0 = Some expr_350.
Proof. vm_compute. reflexivity. Qed.
Transparent word_350.
Lemma closed_350_value v : eval_hfexpr expr_350 (closed_350 v) (closed_350 v) = Some (Gval (Fuint 1) (word_350 v)).
Proof. unfold word_350, closed_350, expr_350, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_350.
Lemma node_350_value v : eval_hfexpr expr_350 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_350 v)).
Proof. change (eval_hfexpr expr_350 (closed_350 v) (closed_350 v) = Some (Gval (Fuint 1) (word_350 v))). apply closed_350_value. Qed.
Lemma source_351 : find_driver 351 generated_module_0_stmts_0 = Some expr_351.
Proof. vm_compute. reflexivity. Qed.
Transparent word_351.
Lemma closed_351_value v : eval_hfexpr expr_351 (closed_351 v) (closed_351 v) = Some (Gval (Fuint 1) (word_351 v)).
Proof. unfold word_351, closed_351, expr_351, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_351.
Lemma node_351_value v : eval_hfexpr expr_351 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_351 v)).
Proof. change (eval_hfexpr expr_351 (closed_351 v) (closed_351 v) = Some (Gval (Fuint 1) (word_351 v))). apply closed_351_value. Qed.
Lemma source_352 : find_driver 352 generated_module_0_stmts_0 = Some expr_352.
Proof. vm_compute. reflexivity. Qed.
Transparent word_352.
Lemma closed_352_value v : eval_hfexpr expr_352 (closed_352 v) (closed_352 v) = Some (Gval (Fuint 1) (word_352 v)).
Proof. unfold word_352, closed_352, expr_352, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_352.
Lemma node_352_value v : eval_hfexpr expr_352 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_352 v)).
Proof. change (eval_hfexpr expr_352 (closed_352 v) (closed_352 v) = Some (Gval (Fuint 1) (word_352 v))). apply closed_352_value. Qed.
Lemma source_353 : find_driver 353 generated_module_0_stmts_0 = Some expr_353.
Proof. vm_compute. reflexivity. Qed.
Transparent word_353.
Lemma closed_353_value v : eval_hfexpr expr_353 (closed_353 v) (closed_353 v) = Some (Gval (Fuint 2) (word_353 v)).
Proof. unfold word_353, closed_353, expr_353, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_353.
Lemma node_353_value v : eval_hfexpr expr_353 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_353 v)).
Proof. change (eval_hfexpr expr_353 (closed_353 v) (closed_353 v) = Some (Gval (Fuint 2) (word_353 v))). apply closed_353_value. Qed.
Lemma source_354 : find_driver 354 generated_module_0_stmts_0 = Some expr_354.
Proof. vm_compute. reflexivity. Qed.
Transparent word_354.
Lemma closed_354_value v : eval_hfexpr expr_354 (closed_354 v) (closed_354 v) = Some (Gval (Fuint 2) (word_354 v)).
Proof. unfold word_354, closed_354, expr_354, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_354.
Lemma node_354_value v : eval_hfexpr expr_354 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_354 v)).
Proof. change (eval_hfexpr expr_354 (closed_354 v) (closed_354 v) = Some (Gval (Fuint 2) (word_354 v))). apply closed_354_value. Qed.
Lemma source_355 : find_driver 355 generated_module_0_stmts_0 = Some expr_355.
Proof. vm_compute. reflexivity. Qed.
Transparent word_355.
Lemma closed_355_value v : eval_hfexpr expr_355 (closed_355 v) (closed_355 v) = Some (Gval (Fuint 1) (word_355 v)).
Proof. unfold word_355, closed_355, expr_355, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_355.
Lemma node_355_value v : eval_hfexpr expr_355 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_355 v)).
Proof. change (eval_hfexpr expr_355 (closed_355 v) (closed_355 v) = Some (Gval (Fuint 1) (word_355 v))). apply closed_355_value. Qed.
Lemma source_356 : find_driver 356 generated_module_0_stmts_0 = Some expr_356.
Proof. vm_compute. reflexivity. Qed.
Transparent word_356.
Lemma closed_356_value v : eval_hfexpr expr_356 (closed_356 v) (closed_356 v) = Some (Gval (Fuint 1) (word_356 v)).
Proof. unfold word_356, closed_356, expr_356, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_356.
Lemma node_356_value v : eval_hfexpr expr_356 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_356 v)).
Proof. change (eval_hfexpr expr_356 (closed_356 v) (closed_356 v) = Some (Gval (Fuint 1) (word_356 v))). apply closed_356_value. Qed.
Lemma source_357 : find_driver 357 generated_module_0_stmts_0 = Some expr_357.
Proof. vm_compute. reflexivity. Qed.
Transparent word_357.
Lemma closed_357_value v : eval_hfexpr expr_357 (closed_357 v) (closed_357 v) = Some (Gval (Fuint 1) (word_357 v)).
Proof. unfold word_357, closed_357, expr_357, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_357.
Lemma node_357_value v : eval_hfexpr expr_357 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_357 v)).
Proof. change (eval_hfexpr expr_357 (closed_357 v) (closed_357 v) = Some (Gval (Fuint 1) (word_357 v))). apply closed_357_value. Qed.
Lemma source_358 : find_driver 358 generated_module_0_stmts_0 = Some expr_358.
Proof. vm_compute. reflexivity. Qed.
Transparent word_358.
Lemma closed_358_value v : eval_hfexpr expr_358 (closed_358 v) (closed_358 v) = Some (Gval (Fuint 2) (word_358 v)).
Proof. unfold word_358, closed_358, expr_358, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_358.
Lemma node_358_value v : eval_hfexpr expr_358 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_358 v)).
Proof. change (eval_hfexpr expr_358 (closed_358 v) (closed_358 v) = Some (Gval (Fuint 2) (word_358 v))). apply closed_358_value. Qed.
Lemma source_359 : find_driver 359 generated_module_0_stmts_0 = Some expr_359.
Proof. vm_compute. reflexivity. Qed.
Transparent word_359.
Lemma closed_359_value v : eval_hfexpr expr_359 (closed_359 v) (closed_359 v) = Some (Gval (Fuint 2) (word_359 v)).
Proof. unfold word_359, closed_359, expr_359, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_359.
Lemma node_359_value v : eval_hfexpr expr_359 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_359 v)).
Proof. change (eval_hfexpr expr_359 (closed_359 v) (closed_359 v) = Some (Gval (Fuint 2) (word_359 v))). apply closed_359_value. Qed.
Lemma source_360 : find_driver 360 generated_module_0_stmts_0 = Some expr_360.
Proof. vm_compute. reflexivity. Qed.
Transparent word_360.
Lemma closed_360_value v : eval_hfexpr expr_360 (closed_360 v) (closed_360 v) = Some (Gval (Fuint 2) (word_360 v)).
Proof. unfold word_360, closed_360, expr_360, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_360.
Lemma node_360_value v : eval_hfexpr expr_360 (stable_env v) (stable_env v) = Some (Gval (Fuint 2) (word_360 v)).
Proof. change (eval_hfexpr expr_360 (closed_360 v) (closed_360 v) = Some (Gval (Fuint 2) (word_360 v))). apply closed_360_value. Qed.
Lemma source_361 : find_driver 361 generated_module_0_stmts_0 = Some expr_361.
Proof. vm_compute. reflexivity. Qed.
Transparent word_361.
Lemma closed_361_value v : eval_hfexpr expr_361 (closed_361 v) (closed_361 v) = Some (Gval (Fuint 3) (word_361 v)).
Proof. unfold word_361, closed_361, expr_361, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_361.
Lemma node_361_value v : eval_hfexpr expr_361 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_361 v)).
Proof. change (eval_hfexpr expr_361 (closed_361 v) (closed_361 v) = Some (Gval (Fuint 3) (word_361 v))). apply closed_361_value. Qed.
Lemma source_362 : find_driver 362 generated_module_0_stmts_0 = Some expr_362.
Proof. vm_compute. reflexivity. Qed.
Transparent word_362.
Lemma closed_362_value v : eval_hfexpr expr_362 (closed_362 v) (closed_362 v) = Some (Gval (Fuint 3) (word_362 v)).
Proof. unfold word_362, closed_362, expr_362, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_362.
Lemma node_362_value v : eval_hfexpr expr_362 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_362 v)).
Proof. change (eval_hfexpr expr_362 (closed_362 v) (closed_362 v) = Some (Gval (Fuint 3) (word_362 v))). apply closed_362_value. Qed.
Lemma source_363 : find_driver 363 generated_module_0_stmts_0 = Some expr_363.
Proof. vm_compute. reflexivity. Qed.
Transparent word_363.
Lemma closed_363_value v : eval_hfexpr expr_363 (closed_363 v) (closed_363 v) = Some (Gval (Fuint 4) (word_363 v)).
Proof. unfold word_363, closed_363, expr_363, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_363.
Lemma node_363_value v : eval_hfexpr expr_363 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_363 v)).
Proof. change (eval_hfexpr expr_363 (closed_363 v) (closed_363 v) = Some (Gval (Fuint 4) (word_363 v))). apply closed_363_value. Qed.
Lemma source_364 : find_driver 364 generated_module_0_stmts_0 = Some expr_364.
Proof. vm_compute. reflexivity. Qed.
Transparent word_364.
Lemma closed_364_value v : eval_hfexpr expr_364 (closed_364 v) (closed_364 v) = Some (Gval (Fuint 4) (word_364 v)).
Proof. unfold word_364, closed_364, expr_364, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_364.
Lemma node_364_value v : eval_hfexpr expr_364 (stable_env v) (stable_env v) = Some (Gval (Fuint 4) (word_364 v)).
Proof. change (eval_hfexpr expr_364 (closed_364 v) (closed_364 v) = Some (Gval (Fuint 4) (word_364 v))). apply closed_364_value. Qed.
Lemma source_365 : find_driver 365 generated_module_0_stmts_0 = Some expr_365.
Proof. vm_compute. reflexivity. Qed.
Transparent word_365.
Lemma closed_365_value v : eval_hfexpr expr_365 (closed_365 v) (closed_365 v) = Some (Gval (Fuint 5) (word_365 v)).
Proof. unfold word_365, closed_365, expr_365, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_365.
Lemma node_365_value v : eval_hfexpr expr_365 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_365 v)).
Proof. change (eval_hfexpr expr_365 (closed_365 v) (closed_365 v) = Some (Gval (Fuint 5) (word_365 v))). apply closed_365_value. Qed.
Lemma source_366 : find_driver 366 generated_module_0_stmts_0 = Some expr_366.
Proof. vm_compute. reflexivity. Qed.
Transparent word_366.
Lemma closed_366_value v : eval_hfexpr expr_366 (closed_366 v) (closed_366 v) = Some (Gval (Fuint 5) (word_366 v)).
Proof. unfold word_366, closed_366, expr_366, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_366.
Lemma node_366_value v : eval_hfexpr expr_366 (stable_env v) (stable_env v) = Some (Gval (Fuint 5) (word_366 v)).
Proof. change (eval_hfexpr expr_366 (closed_366 v) (closed_366 v) = Some (Gval (Fuint 5) (word_366 v))). apply closed_366_value. Qed.
Lemma source_367 : find_driver 367 generated_module_0_stmts_0 = Some expr_367.
Proof. vm_compute. reflexivity. Qed.
Transparent word_367.
Lemma closed_367_value v : eval_hfexpr expr_367 (closed_367 v) (closed_367 v) = Some (Gval (Fuint 6) (word_367 v)).
Proof. unfold word_367, closed_367, expr_367, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_367.
Lemma node_367_value v : eval_hfexpr expr_367 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_367 v)).
Proof. change (eval_hfexpr expr_367 (closed_367 v) (closed_367 v) = Some (Gval (Fuint 6) (word_367 v))). apply closed_367_value. Qed.
Lemma source_368 : find_driver 368 generated_module_0_stmts_0 = Some expr_368.
Proof. vm_compute. reflexivity. Qed.
Transparent word_368.
Lemma closed_368_value v : eval_hfexpr expr_368 (closed_368 v) (closed_368 v) = Some (Gval (Fuint 6) (word_368 v)).
Proof. unfold word_368, closed_368, expr_368, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_368.
Lemma node_368_value v : eval_hfexpr expr_368 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_368 v)).
Proof. change (eval_hfexpr expr_368 (closed_368 v) (closed_368 v) = Some (Gval (Fuint 6) (word_368 v))). apply closed_368_value. Qed.
Lemma source_369 : find_driver 369 generated_module_0_stmts_0 = Some expr_369.
Proof. vm_compute. reflexivity. Qed.
Transparent word_369.
Lemma closed_369_value v : eval_hfexpr expr_369 (closed_369 v) (closed_369 v) = Some (Gval (Fuint 7) (word_369 v)).
Proof. unfold word_369, closed_369, expr_369, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_369.
Lemma node_369_value v : eval_hfexpr expr_369 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_369 v)).
Proof. change (eval_hfexpr expr_369 (closed_369 v) (closed_369 v) = Some (Gval (Fuint 7) (word_369 v))). apply closed_369_value. Qed.
Lemma source_370 : find_driver 370 generated_module_0_stmts_0 = Some expr_370.
Proof. vm_compute. reflexivity. Qed.
Transparent word_370.
Lemma closed_370_value v : eval_hfexpr expr_370 (closed_370 v) (closed_370 v) = Some (Gval (Fuint 8) (word_370 v)).
Proof. unfold word_370, closed_370, expr_370, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_370.
Lemma node_370_value v : eval_hfexpr expr_370 (stable_env v) (stable_env v) = Some (Gval (Fuint 8) (word_370 v)).
Proof. change (eval_hfexpr expr_370 (closed_370 v) (closed_370 v) = Some (Gval (Fuint 8) (word_370 v))). apply closed_370_value. Qed.
Lemma source_371 : find_driver 371 generated_module_0_stmts_0 = Some expr_371.
Proof. vm_compute. reflexivity. Qed.
Transparent word_371.
Lemma closed_371_value v : eval_hfexpr expr_371 (closed_371 v) (closed_371 v) = Some (Gval (Fuint 7) (word_371 v)).
Proof. unfold word_371, closed_371, expr_371, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_371.
Lemma node_371_value v : eval_hfexpr expr_371 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_371 v)).
Proof. change (eval_hfexpr expr_371 (closed_371 v) (closed_371 v) = Some (Gval (Fuint 7) (word_371 v))). apply closed_371_value. Qed.
Lemma source_372 : find_driver 372 generated_module_0_stmts_0 = Some expr_372.
Proof. vm_compute. reflexivity. Qed.
Transparent word_372.
Lemma closed_372_value v : eval_hfexpr expr_372 (closed_372 v) (closed_372 v) = Some (Gval (Fuint 1) (word_372 v)).
Proof. unfold word_372, closed_372, expr_372, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_372.
Lemma node_372_value v : eval_hfexpr expr_372 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_372 v)).
Proof. change (eval_hfexpr expr_372 (closed_372 v) (closed_372 v) = Some (Gval (Fuint 1) (word_372 v))). apply closed_372_value. Qed.
Lemma source_373 : find_driver 373 generated_module_0_stmts_0 = Some expr_373.
Proof. vm_compute. reflexivity. Qed.
Transparent word_373.
Lemma closed_373_value v : eval_hfexpr expr_373 (closed_373 v) (closed_373 v) = Some (Gval (Fuint 7) (word_373 v)).
Proof. unfold word_373, closed_373, expr_373, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_373.
Lemma node_373_value v : eval_hfexpr expr_373 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_373 v)).
Proof. change (eval_hfexpr expr_373 (closed_373 v) (closed_373 v) = Some (Gval (Fuint 7) (word_373 v))). apply closed_373_value. Qed.
Lemma source_374 : find_driver 374 generated_module_0_stmts_0 = Some expr_374.
Proof. vm_compute. reflexivity. Qed.
Transparent word_374.
Lemma closed_374_value v : eval_hfexpr expr_374 (closed_374 v) (closed_374 v) = Some (Gval (Fuint 7) (word_374 v)).
Proof. unfold word_374, closed_374, expr_374, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_374.
Lemma node_374_value v : eval_hfexpr expr_374 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_374 v)).
Proof. change (eval_hfexpr expr_374 (closed_374 v) (closed_374 v) = Some (Gval (Fuint 7) (word_374 v))). apply closed_374_value. Qed.
Lemma source_375 : find_driver 375 generated_module_0_stmts_0 = Some expr_375.
Proof. vm_compute. reflexivity. Qed.
Transparent word_375.
Lemma closed_375_value v : eval_hfexpr expr_375 (closed_375 v) (closed_375 v) = Some (Gval (Fuint 1) (word_375 v)).
Proof. unfold word_375, closed_375, expr_375, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_375.
Lemma node_375_value v : eval_hfexpr expr_375 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_375 v)).
Proof. change (eval_hfexpr expr_375 (closed_375 v) (closed_375 v) = Some (Gval (Fuint 1) (word_375 v))). apply closed_375_value. Qed.
Lemma source_376 : find_driver 376 generated_module_0_stmts_0 = Some expr_376.
Proof. vm_compute. reflexivity. Qed.
Transparent word_376.
Lemma closed_376_value v : eval_hfexpr expr_376 (closed_376 v) (closed_376 v) = Some (Gval (Fuint 128) (word_376 v)).
Proof. unfold word_376, closed_376, expr_376, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_376.
Lemma node_376_value v : eval_hfexpr expr_376 (stable_env v) (stable_env v) = Some (Gval (Fuint 128) (word_376 v)).
Proof. change (eval_hfexpr expr_376 (closed_376 v) (closed_376 v) = Some (Gval (Fuint 128) (word_376 v))). apply closed_376_value. Qed.
Lemma source_377 : find_driver 377 generated_module_0_stmts_0 = Some expr_377.
Proof. vm_compute. reflexivity. Qed.
Transparent word_377.
Lemma closed_377_value v : eval_hfexpr expr_377 (closed_377 v) (closed_377 v) = Some (Gval (Fuint 1) (word_377 v)).
Proof. unfold word_377, closed_377, expr_377, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_377.
Lemma node_377_value v : eval_hfexpr expr_377 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_377 v)).
Proof. change (eval_hfexpr expr_377 (closed_377 v) (closed_377 v) = Some (Gval (Fuint 1) (word_377 v))). apply closed_377_value. Qed.
Lemma source_378 : find_driver 378 generated_module_0_stmts_0 = Some expr_378.
Proof. vm_compute. reflexivity. Qed.
Transparent word_378.
Lemma closed_378_value v : eval_hfexpr expr_378 (closed_378 v) (closed_378 v) = Some (Gval (Fuint 1) (word_378 v)).
Proof. unfold word_378, closed_378, expr_378, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_378.
Lemma node_378_value v : eval_hfexpr expr_378 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_378 v)).
Proof. change (eval_hfexpr expr_378 (closed_378 v) (closed_378 v) = Some (Gval (Fuint 1) (word_378 v))). apply closed_378_value. Qed.
Lemma source_379 : find_driver 379 generated_module_0_stmts_0 = Some expr_379.
Proof. vm_compute. reflexivity. Qed.
Transparent word_379.
Lemma closed_379_value v : eval_hfexpr expr_379 (closed_379 v) (closed_379 v) = Some (Gval (Fuint 66) (word_379 v)).
Proof. unfold word_379, closed_379, expr_379, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_379.
Lemma node_379_value v : eval_hfexpr expr_379 (stable_env v) (stable_env v) = Some (Gval (Fuint 66) (word_379 v)).
Proof. change (eval_hfexpr expr_379 (closed_379 v) (closed_379 v) = Some (Gval (Fuint 66) (word_379 v))). apply closed_379_value. Qed.
Lemma source_380 : find_driver 380 generated_module_0_stmts_0 = Some expr_380.
Proof. vm_compute. reflexivity. Qed.
Transparent word_380.
Lemma closed_380_value v : eval_hfexpr expr_380 (closed_380 v) (closed_380 v) = Some (Gval (Fuint 65) (word_380 v)).
Proof. unfold word_380, closed_380, expr_380, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_380.
Lemma node_380_value v : eval_hfexpr expr_380 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_380 v)).
Proof. change (eval_hfexpr expr_380 (closed_380 v) (closed_380 v) = Some (Gval (Fuint 65) (word_380 v))). apply closed_380_value. Qed.
Lemma source_381 : find_driver 381 generated_module_0_stmts_0 = Some expr_381.
Proof. vm_compute. reflexivity. Qed.
Transparent word_381.
Lemma closed_381_value v : eval_hfexpr expr_381 (closed_381 v) (closed_381 v) = Some (Gval (Fuint 65) (word_381 v)).
Proof. unfold word_381, closed_381, expr_381, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_381.
Lemma node_381_value v : eval_hfexpr expr_381 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_381 v)).
Proof. change (eval_hfexpr expr_381 (closed_381 v) (closed_381 v) = Some (Gval (Fuint 65) (word_381 v))). apply closed_381_value. Qed.
Lemma source_382 : find_driver 382 generated_module_0_stmts_0 = Some expr_382.
Proof. vm_compute. reflexivity. Qed.
Transparent word_382.
Lemma closed_382_value v : eval_hfexpr expr_382 (closed_382 v) (closed_382 v) = Some (Gval (Fuint 64) (word_382 v)).
Proof. unfold word_382, closed_382, expr_382, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_382.
Lemma node_382_value v : eval_hfexpr expr_382 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_382 v)).
Proof. change (eval_hfexpr expr_382 (closed_382 v) (closed_382 v) = Some (Gval (Fuint 64) (word_382 v))). apply closed_382_value. Qed.
Lemma source_383 : find_driver 383 generated_module_0_stmts_0 = Some expr_383.
Proof. vm_compute. reflexivity. Qed.
Transparent word_383.
Lemma closed_383_value v : eval_hfexpr expr_383 (closed_383 v) (closed_383 v) = Some (Gval (Fuint 128) (word_383 v)).
Proof. unfold word_383, closed_383, expr_383, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_383.
Lemma node_383_value v : eval_hfexpr expr_383 (stable_env v) (stable_env v) = Some (Gval (Fuint 128) (word_383 v)).
Proof. change (eval_hfexpr expr_383 (closed_383 v) (closed_383 v) = Some (Gval (Fuint 128) (word_383 v))). apply closed_383_value. Qed.
Lemma source_384 : find_driver 384 generated_module_0_stmts_0 = Some expr_384.
Proof. vm_compute. reflexivity. Qed.
Transparent word_384.
Lemma closed_384_value v : eval_hfexpr expr_384 (closed_384 v) (closed_384 v) = Some (Gval (Fuint 129) (word_384 v)).
Proof. unfold word_384, closed_384, expr_384, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_384.
Lemma node_384_value v : eval_hfexpr expr_384 (stable_env v) (stable_env v) = Some (Gval (Fuint 129) (word_384 v)).
Proof. change (eval_hfexpr expr_384 (closed_384 v) (closed_384 v) = Some (Gval (Fuint 129) (word_384 v))). apply closed_384_value. Qed.
Lemma source_385 : find_driver 385 generated_module_0_stmts_0 = Some expr_385.
Proof. vm_compute. reflexivity. Qed.
Transparent word_385.
Lemma closed_385_value v : eval_hfexpr expr_385 (closed_385 v) (closed_385 v) = Some (Gval (Fuint 1) (word_385 v)).
Proof. unfold word_385, closed_385, expr_385, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_385.
Lemma node_385_value v : eval_hfexpr expr_385 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_385 v)).
Proof. change (eval_hfexpr expr_385 (closed_385 v) (closed_385 v) = Some (Gval (Fuint 1) (word_385 v))). apply closed_385_value. Qed.
Lemma source_386 : find_driver 386 generated_module_0_stmts_0 = Some expr_386.
Proof. vm_compute. reflexivity. Qed.
Transparent word_386.
Lemma closed_386_value v : eval_hfexpr expr_386 (closed_386 v) (closed_386 v) = Some (Gval (Fuint 7) (word_386 v)).
Proof. unfold word_386, closed_386, expr_386, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_386.
Lemma node_386_value v : eval_hfexpr expr_386 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_386 v)).
Proof. change (eval_hfexpr expr_386 (closed_386 v) (closed_386 v) = Some (Gval (Fuint 7) (word_386 v))). apply closed_386_value. Qed.
Lemma source_387 : find_driver 387 generated_module_0_stmts_0 = Some expr_387.
Proof. vm_compute. reflexivity. Qed.
Transparent word_387.
Lemma closed_387_value v : eval_hfexpr expr_387 (closed_387 v) (closed_387 v) = Some (Gval (Fuint 6) (word_387 v)).
Proof. unfold word_387, closed_387, expr_387, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_387.
Lemma node_387_value v : eval_hfexpr expr_387 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_387 v)).
Proof. change (eval_hfexpr expr_387 (closed_387 v) (closed_387 v) = Some (Gval (Fuint 6) (word_387 v))). apply closed_387_value. Qed.
Lemma source_388 : find_driver 388 generated_module_0_stmts_0 = Some expr_388.
Proof. vm_compute. reflexivity. Qed.
Transparent word_388.
Lemma closed_388_value v : eval_hfexpr expr_388 (closed_388 v) (closed_388 v) = Some (Gval (Fuint 1) (word_388 v)).
Proof. unfold word_388, closed_388, expr_388, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_388.
Lemma node_388_value v : eval_hfexpr expr_388 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_388 v)).
Proof. change (eval_hfexpr expr_388 (closed_388 v) (closed_388 v) = Some (Gval (Fuint 1) (word_388 v))). apply closed_388_value. Qed.
Lemma source_389 : find_driver 389 generated_module_0_stmts_0 = Some expr_389.
Proof. vm_compute. reflexivity. Qed.
Transparent word_389.
Lemma closed_389_value v : eval_hfexpr expr_389 (closed_389 v) (closed_389 v) = Some (Gval (Fuint 3) (word_389 v)).
Proof. unfold word_389, closed_389, expr_389, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_389.
Lemma node_389_value v : eval_hfexpr expr_389 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_389 v)).
Proof. change (eval_hfexpr expr_389 (closed_389 v) (closed_389 v) = Some (Gval (Fuint 3) (word_389 v))). apply closed_389_value. Qed.
Lemma source_390 : find_driver 390 generated_module_0_stmts_0 = Some expr_390.
Proof. vm_compute. reflexivity. Qed.
Transparent word_390.
Lemma closed_390_value v : eval_hfexpr expr_390 (closed_390 v) (closed_390 v) = Some (Gval (Fuint 1) (word_390 v)).
Proof. unfold word_390, closed_390, expr_390, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_390.
Lemma node_390_value v : eval_hfexpr expr_390 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_390 v)).
Proof. change (eval_hfexpr expr_390 (closed_390 v) (closed_390 v) = Some (Gval (Fuint 1) (word_390 v))). apply closed_390_value. Qed.
Lemma source_391 : find_driver 391 generated_module_0_stmts_0 = Some expr_391.
Proof. vm_compute. reflexivity. Qed.
Transparent word_391.
Lemma closed_391_value v : eval_hfexpr expr_391 (closed_391 v) (closed_391 v) = Some (Gval (Fuint 3) (word_391 v)).
Proof. unfold word_391, closed_391, expr_391, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_391.
Lemma node_391_value v : eval_hfexpr expr_391 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_391 v)).
Proof. change (eval_hfexpr expr_391 (closed_391 v) (closed_391 v) = Some (Gval (Fuint 3) (word_391 v))). apply closed_391_value. Qed.
Lemma source_392 : find_driver 392 generated_module_0_stmts_0 = Some expr_392.
Proof. vm_compute. reflexivity. Qed.
Transparent word_392.
Lemma closed_392_value v : eval_hfexpr expr_392 (closed_392 v) (closed_392 v) = Some (Gval (Fuint 3) (word_392 v)).
Proof. unfold word_392, closed_392, expr_392, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_392.
Lemma node_392_value v : eval_hfexpr expr_392 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_392 v)).
Proof. change (eval_hfexpr expr_392 (closed_392 v) (closed_392 v) = Some (Gval (Fuint 3) (word_392 v))). apply closed_392_value. Qed.
Lemma source_393 : find_driver 393 generated_module_0_stmts_0 = Some expr_393.
Proof. vm_compute. reflexivity. Qed.
Transparent word_393.
Lemma closed_393_value v : eval_hfexpr expr_393 (closed_393 v) (closed_393 v) = Some (Gval (Fuint 129) (word_393 v)).
Proof. unfold word_393, closed_393, expr_393, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_393.
Lemma node_393_value v : eval_hfexpr expr_393 (stable_env v) (stable_env v) = Some (Gval (Fuint 129) (word_393 v)).
Proof. change (eval_hfexpr expr_393 (closed_393 v) (closed_393 v) = Some (Gval (Fuint 129) (word_393 v))). apply closed_393_value. Qed.
Lemma source_394 : find_driver 394 generated_module_0_stmts_0 = Some expr_394.
Proof. vm_compute. reflexivity. Qed.
Transparent word_394.
Lemma closed_394_value v : eval_hfexpr expr_394 (closed_394 v) (closed_394 v) = Some (Gval (Fuint 6) (word_394 v)).
Proof. unfold word_394, closed_394, expr_394, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_394.
Lemma node_394_value v : eval_hfexpr expr_394 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_394 v)).
Proof. change (eval_hfexpr expr_394 (closed_394 v) (closed_394 v) = Some (Gval (Fuint 6) (word_394 v))). apply closed_394_value. Qed.
Lemma source_395 : find_driver 395 generated_module_0_stmts_0 = Some expr_395.
Proof. vm_compute. reflexivity. Qed.
Transparent word_395.
Lemma closed_395_value v : eval_hfexpr expr_395 (closed_395 v) (closed_395 v) = Some (Gval (Fuint 3) (word_395 v)).
Proof. unfold word_395, closed_395, expr_395, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_395.
Lemma node_395_value v : eval_hfexpr expr_395 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_395 v)).
Proof. change (eval_hfexpr expr_395 (closed_395 v) (closed_395 v) = Some (Gval (Fuint 3) (word_395 v))). apply closed_395_value. Qed.
Lemma source_396 : find_driver 396 generated_module_0_stmts_0 = Some expr_396.
Proof. vm_compute. reflexivity. Qed.
Transparent word_396.
Lemma closed_396_value v : eval_hfexpr expr_396 (closed_396 v) (closed_396 v) = Some (Gval (Fuint 129) (word_396 v)).
Proof. unfold word_396, closed_396, expr_396, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_396.
Lemma node_396_value v : eval_hfexpr expr_396 (stable_env v) (stable_env v) = Some (Gval (Fuint 129) (word_396 v)).
Proof. change (eval_hfexpr expr_396 (closed_396 v) (closed_396 v) = Some (Gval (Fuint 129) (word_396 v))). apply closed_396_value. Qed.
Lemma source_397 : find_driver 397 generated_module_0_stmts_0 = Some expr_397.
Proof. vm_compute. reflexivity. Qed.
Transparent word_397.
Lemma closed_397_value v : eval_hfexpr expr_397 (closed_397 v) (closed_397 v) = Some (Gval (Fuint 3) (word_397 v)).
Proof. unfold word_397, closed_397, expr_397, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_397.
Lemma node_397_value v : eval_hfexpr expr_397 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_397 v)).
Proof. change (eval_hfexpr expr_397 (closed_397 v) (closed_397 v) = Some (Gval (Fuint 3) (word_397 v))). apply closed_397_value. Qed.
Lemma source_398 : find_driver 398 generated_module_0_stmts_0 = Some expr_398.
Proof. vm_compute. reflexivity. Qed.
Transparent word_398.
Lemma closed_398_value v : eval_hfexpr expr_398 (closed_398 v) (closed_398 v) = Some (Gval (Fuint 6) (word_398 v)).
Proof. unfold word_398, closed_398, expr_398, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_398.
Lemma node_398_value v : eval_hfexpr expr_398 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_398 v)).
Proof. change (eval_hfexpr expr_398 (closed_398 v) (closed_398 v) = Some (Gval (Fuint 6) (word_398 v))). apply closed_398_value. Qed.
Lemma source_399 : find_driver 399 generated_module_0_stmts_0 = Some expr_399.
Proof. vm_compute. reflexivity. Qed.
Transparent word_399.
Lemma closed_399_value v : eval_hfexpr expr_399 (closed_399 v) (closed_399 v) = Some (Gval (Fuint 7) (word_399 v)).
Proof. unfold word_399, closed_399, expr_399, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_399.
Lemma node_399_value v : eval_hfexpr expr_399 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_399 v)).
Proof. change (eval_hfexpr expr_399 (closed_399 v) (closed_399 v) = Some (Gval (Fuint 7) (word_399 v))). apply closed_399_value. Qed.
Lemma source_400 : find_driver 400 generated_module_0_stmts_0 = Some expr_400.
Proof. vm_compute. reflexivity. Qed.
Transparent word_400.
Lemma closed_400_value v : eval_hfexpr expr_400 (closed_400 v) (closed_400 v) = Some (Gval (Fuint 3) (word_400 v)).
Proof. unfold word_400, closed_400, expr_400, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_400.
Lemma node_400_value v : eval_hfexpr expr_400 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_400 v)).
Proof. change (eval_hfexpr expr_400 (closed_400 v) (closed_400 v) = Some (Gval (Fuint 3) (word_400 v))). apply closed_400_value. Qed.
Lemma source_401 : find_driver 401 generated_module_0_stmts_0 = Some expr_401.
Proof. vm_compute. reflexivity. Qed.
Transparent word_401.
Lemma closed_401_value v : eval_hfexpr expr_401 (closed_401 v) (closed_401 v) = Some (Gval (Fuint 129) (word_401 v)).
Proof. unfold word_401, closed_401, expr_401, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_401.
Lemma node_401_value v : eval_hfexpr expr_401 (stable_env v) (stable_env v) = Some (Gval (Fuint 129) (word_401 v)).
Proof. change (eval_hfexpr expr_401 (closed_401 v) (closed_401 v) = Some (Gval (Fuint 129) (word_401 v))). apply closed_401_value. Qed.
Lemma source_402 : find_driver 402 generated_module_0_stmts_0 = Some expr_402.
Proof. vm_compute. reflexivity. Qed.
Transparent word_402.
Lemma closed_402_value v : eval_hfexpr expr_402 (closed_402 v) (closed_402 v) = Some (Gval (Fuint 3) (word_402 v)).
Proof. unfold word_402, closed_402, expr_402, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_402.
Lemma node_402_value v : eval_hfexpr expr_402 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_402 v)).
Proof. change (eval_hfexpr expr_402 (closed_402 v) (closed_402 v) = Some (Gval (Fuint 3) (word_402 v))). apply closed_402_value. Qed.
Lemma source_403 : find_driver 403 generated_module_0_stmts_0 = Some expr_403.
Proof. vm_compute. reflexivity. Qed.
Transparent word_403.
Lemma closed_403_value v : eval_hfexpr expr_403 (closed_403 v) (closed_403 v) = Some (Gval (Fuint 7) (word_403 v)).
Proof. unfold word_403, closed_403, expr_403, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_403.
Lemma node_403_value v : eval_hfexpr expr_403 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_403 v)).
Proof. change (eval_hfexpr expr_403 (closed_403 v) (closed_403 v) = Some (Gval (Fuint 7) (word_403 v))). apply closed_403_value. Qed.
Lemma source_404 : find_driver 404 generated_module_0_stmts_0 = Some expr_404.
Proof. vm_compute. reflexivity. Qed.
Transparent word_404.
Lemma closed_404_value v : eval_hfexpr expr_404 (closed_404 v) (closed_404 v) = Some (Gval (Fuint 129) (word_404 v)).
Proof. unfold word_404, closed_404, expr_404, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_404.
Lemma node_404_value v : eval_hfexpr expr_404 (stable_env v) (stable_env v) = Some (Gval (Fuint 129) (word_404 v)).
Proof. change (eval_hfexpr expr_404 (closed_404 v) (closed_404 v) = Some (Gval (Fuint 129) (word_404 v))). apply closed_404_value. Qed.
Lemma source_405 : find_driver 405 generated_module_0_stmts_0 = Some expr_405.
Proof. vm_compute. reflexivity. Qed.
Transparent word_405.
Lemma closed_405_value v : eval_hfexpr expr_405 (closed_405 v) (closed_405 v) = Some (Gval (Fuint 64) (word_405 v)).
Proof. unfold word_405, closed_405, expr_405, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_405.
Lemma node_405_value v : eval_hfexpr expr_405 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_405 v)).
Proof. change (eval_hfexpr expr_405 (closed_405 v) (closed_405 v) = Some (Gval (Fuint 64) (word_405 v))). apply closed_405_value. Qed.
Lemma source_406 : find_driver 406 generated_module_0_stmts_0 = Some expr_406.
Proof. vm_compute. reflexivity. Qed.
Transparent word_406.
Lemma closed_406_value v : eval_hfexpr expr_406 (closed_406 v) (closed_406 v) = Some (Gval (Fuint 65) (word_406 v)).
Proof. unfold word_406, closed_406, expr_406, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_406.
Lemma node_406_value v : eval_hfexpr expr_406 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_406 v)).
Proof. change (eval_hfexpr expr_406 (closed_406 v) (closed_406 v) = Some (Gval (Fuint 65) (word_406 v))). apply closed_406_value. Qed.
Lemma source_407 : find_driver 407 generated_module_0_stmts_0 = Some expr_407.
Proof. vm_compute. reflexivity. Qed.
Transparent word_407.
Lemma closed_407_value v : eval_hfexpr expr_407 (closed_407 v) (closed_407 v) = Some (Gval (Fuint 64) (word_407 v)).
Proof. unfold word_407, closed_407, expr_407, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_407.
Lemma node_407_value v : eval_hfexpr expr_407 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_407 v)).
Proof. change (eval_hfexpr expr_407 (closed_407 v) (closed_407 v) = Some (Gval (Fuint 64) (word_407 v))). apply closed_407_value. Qed.
Lemma source_408 : find_driver 408 generated_module_0_stmts_0 = Some expr_408.
Proof. vm_compute. reflexivity. Qed.
Transparent word_408.
Lemma closed_408_value v : eval_hfexpr expr_408 (closed_408 v) (closed_408 v) = Some (Gval (Fuint 64) (word_408 v)).
Proof. unfold word_408, closed_408, expr_408, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_408.
Lemma node_408_value v : eval_hfexpr expr_408 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_408 v)).
Proof. change (eval_hfexpr expr_408 (closed_408 v) (closed_408 v) = Some (Gval (Fuint 64) (word_408 v))). apply closed_408_value. Qed.
Lemma source_409 : find_driver 409 generated_module_0_stmts_0 = Some expr_409.
Proof. vm_compute. reflexivity. Qed.
Transparent word_409.
Lemma closed_409_value v : eval_hfexpr expr_409 (closed_409 v) (closed_409 v) = Some (Gval (Fuint 65) (word_409 v)).
Proof. unfold word_409, closed_409, expr_409, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_409.
Lemma node_409_value v : eval_hfexpr expr_409 (stable_env v) (stable_env v) = Some (Gval (Fuint 65) (word_409 v)).
Proof. change (eval_hfexpr expr_409 (closed_409 v) (closed_409 v) = Some (Gval (Fuint 65) (word_409 v))). apply closed_409_value. Qed.
Lemma source_410 : find_driver 410 generated_module_0_stmts_0 = Some expr_410.
Proof. vm_compute. reflexivity. Qed.
Transparent word_410.
Lemma closed_410_value v : eval_hfexpr expr_410 (closed_410 v) (closed_410 v) = Some (Gval (Fuint 64) (word_410 v)).
Proof. unfold word_410, closed_410, expr_410, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_410.
Lemma node_410_value v : eval_hfexpr expr_410 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_410 v)).
Proof. change (eval_hfexpr expr_410 (closed_410 v) (closed_410 v) = Some (Gval (Fuint 64) (word_410 v))). apply closed_410_value. Qed.
Lemma source_411 : find_driver 411 generated_module_0_stmts_0 = Some expr_411.
Proof. vm_compute. reflexivity. Qed.
Transparent word_411.
Lemma closed_411_value v : eval_hfexpr expr_411 (closed_411 v) (closed_411 v) = Some (Gval (Fuint 64) (word_411 v)).
Proof. unfold word_411, closed_411, expr_411, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_411.
Lemma node_411_value v : eval_hfexpr expr_411 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_411 v)).
Proof. change (eval_hfexpr expr_411 (closed_411 v) (closed_411 v) = Some (Gval (Fuint 64) (word_411 v))). apply closed_411_value. Qed.
Lemma source_412 : find_driver 412 generated_module_0_stmts_0 = Some expr_412.
Proof. vm_compute. reflexivity. Qed.
Transparent word_412.
Lemma closed_412_value v : eval_hfexpr expr_412 (closed_412 v) (closed_412 v) = Some (Gval (Fuint 64) (word_412 v)).
Proof. unfold word_412, closed_412, expr_412, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_412.
Lemma node_412_value v : eval_hfexpr expr_412 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_412 v)).
Proof. change (eval_hfexpr expr_412 (closed_412 v) (closed_412 v) = Some (Gval (Fuint 64) (word_412 v))). apply closed_412_value. Qed.
Lemma source_413 : find_driver 413 generated_module_0_stmts_0 = Some expr_413.
Proof. vm_compute. reflexivity. Qed.
Transparent word_413.
Lemma closed_413_value v : eval_hfexpr expr_413 (closed_413 v) (closed_413 v) = Some (Gval (Fuint 32) (word_413 v)).
Proof. unfold word_413, closed_413, expr_413, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_413.
Lemma node_413_value v : eval_hfexpr expr_413 (stable_env v) (stable_env v) = Some (Gval (Fuint 32) (word_413 v)).
Proof. change (eval_hfexpr expr_413 (closed_413 v) (closed_413 v) = Some (Gval (Fuint 32) (word_413 v))). apply closed_413_value. Qed.
Lemma source_414 : find_driver 414 generated_module_0_stmts_0 = Some expr_414.
Proof. vm_compute. reflexivity. Qed.
Transparent word_414.
Lemma closed_414_value v : eval_hfexpr expr_414 (closed_414 v) (closed_414 v) = Some (Gval (Fuint 1) (word_414 v)).
Proof. unfold word_414, closed_414, expr_414, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_414.
Lemma node_414_value v : eval_hfexpr expr_414 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_414 v)).
Proof. change (eval_hfexpr expr_414 (closed_414 v) (closed_414 v) = Some (Gval (Fuint 1) (word_414 v))). apply closed_414_value. Qed.
Lemma source_415 : find_driver 415 generated_module_0_stmts_0 = Some expr_415.
Proof. vm_compute. reflexivity. Qed.
Transparent word_415.
Lemma closed_415_value v : eval_hfexpr expr_415 (closed_415 v) (closed_415 v) = Some (Gval (Fuint 1) (word_415 v)).
Proof. unfold word_415, closed_415, expr_415, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_415.
Lemma node_415_value v : eval_hfexpr expr_415 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_415 v)).
Proof. change (eval_hfexpr expr_415 (closed_415 v) (closed_415 v) = Some (Gval (Fuint 1) (word_415 v))). apply closed_415_value. Qed.
Lemma source_416 : find_driver 416 generated_module_0_stmts_0 = Some expr_416.
Proof. vm_compute. reflexivity. Qed.
Transparent word_416.
Lemma closed_416_value v : eval_hfexpr expr_416 (closed_416 v) (closed_416 v) = Some (Gval (Fuint 32) (word_416 v)).
Proof. unfold word_416, closed_416, expr_416, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_416.
Lemma node_416_value v : eval_hfexpr expr_416 (stable_env v) (stable_env v) = Some (Gval (Fuint 32) (word_416 v)).
Proof. change (eval_hfexpr expr_416 (closed_416 v) (closed_416 v) = Some (Gval (Fuint 32) (word_416 v))). apply closed_416_value. Qed.
Lemma source_417 : find_driver 417 generated_module_0_stmts_0 = Some expr_417.
Proof. vm_compute. reflexivity. Qed.
Transparent word_417.
Lemma closed_417_value v : eval_hfexpr expr_417 (closed_417 v) (closed_417 v) = Some (Gval (Fuint 64) (word_417 v)).
Proof. unfold word_417, closed_417, expr_417, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_417.
Lemma node_417_value v : eval_hfexpr expr_417 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_417 v)).
Proof. change (eval_hfexpr expr_417 (closed_417 v) (closed_417 v) = Some (Gval (Fuint 64) (word_417 v))). apply closed_417_value. Qed.
Lemma source_418 : find_driver 418 generated_module_0_stmts_0 = Some expr_418.
Proof. vm_compute. reflexivity. Qed.
Transparent word_418.
Lemma closed_418_value v : eval_hfexpr expr_418 (closed_418 v) (closed_418 v) = Some (Gval (Fuint 64) (word_418 v)).
Proof. unfold word_418, closed_418, expr_418, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_418.
Lemma node_418_value v : eval_hfexpr expr_418 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_418 v)).
Proof. change (eval_hfexpr expr_418 (closed_418 v) (closed_418 v) = Some (Gval (Fuint 64) (word_418 v))). apply closed_418_value. Qed.
Lemma source_419 : find_driver 419 generated_module_0_stmts_0 = Some expr_419.
Proof. vm_compute. reflexivity. Qed.
Transparent word_419.
Lemma closed_419_value v : eval_hfexpr expr_419 (closed_419 v) (closed_419 v) = Some (Gval (Fuint 1) (word_419 v)).
Proof. unfold word_419, closed_419, expr_419, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_419.
Lemma node_419_value v : eval_hfexpr expr_419 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_419 v)).
Proof. change (eval_hfexpr expr_419 (closed_419 v) (closed_419 v) = Some (Gval (Fuint 1) (word_419 v))). apply closed_419_value. Qed.
Lemma source_421 : find_driver 421 generated_module_0_stmts_0 = Some expr_421.
Proof. vm_compute. reflexivity. Qed.
Transparent word_421.
Lemma closed_421_value v : eval_hfexpr expr_421 (closed_421 v) (closed_421 v) = Some (Gval (Fuint 1) (word_421 v)).
Proof. unfold word_421, closed_421, expr_421, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_421.
Lemma node_421_value v : eval_hfexpr expr_421 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_421 v)).
Proof. change (eval_hfexpr expr_421 (closed_421 v) (closed_421 v) = Some (Gval (Fuint 1) (word_421 v))). apply closed_421_value. Qed.
Lemma source_422 : find_driver 422 generated_module_0_stmts_0 = Some expr_422.
Proof. vm_compute. reflexivity. Qed.
Transparent word_422.
Lemma closed_422_value v : eval_hfexpr expr_422 (closed_422 v) (closed_422 v) = Some (Gval (Fuint 1) (word_422 v)).
Proof. unfold word_422, closed_422, expr_422, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_422.
Lemma node_422_value v : eval_hfexpr expr_422 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_422 v)).
Proof. change (eval_hfexpr expr_422 (closed_422 v) (closed_422 v) = Some (Gval (Fuint 1) (word_422 v))). apply closed_422_value. Qed.
Lemma source_423 : find_driver 423 generated_module_0_stmts_0 = Some expr_423.
Proof. vm_compute. reflexivity. Qed.
Transparent word_423.
Lemma closed_423_value v : eval_hfexpr expr_423 (closed_423 v) (closed_423 v) = Some (Gval (Fuint 1) (word_423 v)).
Proof. unfold word_423, closed_423, expr_423, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_423.
Lemma node_423_value v : eval_hfexpr expr_423 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_423 v)).
Proof. change (eval_hfexpr expr_423 (closed_423 v) (closed_423 v) = Some (Gval (Fuint 1) (word_423 v))). apply closed_423_value. Qed.
Lemma source_424 : find_driver 424 generated_module_0_stmts_0 = Some expr_424.
Proof. vm_compute. reflexivity. Qed.
Transparent word_424.
Lemma closed_424_value v : eval_hfexpr expr_424 (closed_424 v) (closed_424 v) = Some (Gval (Fuint 1) (word_424 v)).
Proof. unfold word_424, closed_424, expr_424, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_424.
Lemma node_424_value v : eval_hfexpr expr_424 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_424 v)).
Proof. change (eval_hfexpr expr_424 (closed_424 v) (closed_424 v) = Some (Gval (Fuint 1) (word_424 v))). apply closed_424_value. Qed.
Lemma source_425 : find_driver 425 generated_module_0_stmts_0 = Some expr_425.
Proof. vm_compute. reflexivity. Qed.
Transparent word_425.
Lemma closed_425_value v : eval_hfexpr expr_425 (closed_425 v) (closed_425 v) = Some (Gval (Fuint 64) (word_425 v)).
Proof. unfold word_425, closed_425, expr_425, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_425.
Lemma node_425_value v : eval_hfexpr expr_425 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_425 v)).
Proof. change (eval_hfexpr expr_425 (closed_425 v) (closed_425 v) = Some (Gval (Fuint 64) (word_425 v))). apply closed_425_value. Qed.
Lemma source_426 : find_driver 426 generated_module_0_stmts_0 = Some expr_426.
Proof. vm_compute. reflexivity. Qed.
Transparent word_426.
Lemma closed_426_value v : eval_hfexpr expr_426 (closed_426 v) (closed_426 v) = Some (Gval (Fuint 1) (word_426 v)).
Proof. unfold word_426, closed_426, expr_426, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_426.
Lemma node_426_value v : eval_hfexpr expr_426 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_426 v)).
Proof. change (eval_hfexpr expr_426 (closed_426 v) (closed_426 v) = Some (Gval (Fuint 1) (word_426 v))). apply closed_426_value. Qed.
Lemma source_427 : find_driver 427 generated_module_0_stmts_0 = Some expr_427.
Proof. vm_compute. reflexivity. Qed.
Transparent word_427.
Lemma closed_427_value v : eval_hfexpr expr_427 (closed_427 v) (closed_427 v) = Some (Gval (Fuint 1) (word_427 v)).
Proof. unfold word_427, closed_427, expr_427, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_427.
Lemma node_427_value v : eval_hfexpr expr_427 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_427 v)).
Proof. change (eval_hfexpr expr_427 (closed_427 v) (closed_427 v) = Some (Gval (Fuint 1) (word_427 v))). apply closed_427_value. Qed.
Lemma source_428 : find_driver 428 generated_module_0_stmts_0 = Some expr_428.
Proof. vm_compute. reflexivity. Qed.
Transparent word_428.
Lemma closed_428_value v : eval_hfexpr expr_428 (closed_428 v) (closed_428 v) = Some (Gval (Fuint 1) (word_428 v)).
Proof. unfold word_428, closed_428, expr_428, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_428.
Lemma node_428_value v : eval_hfexpr expr_428 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_428 v)).
Proof. change (eval_hfexpr expr_428 (closed_428 v) (closed_428 v) = Some (Gval (Fuint 1) (word_428 v))). apply closed_428_value. Qed.
Lemma source_429 : find_driver 429 generated_module_0_stmts_0 = Some expr_429.
Proof. vm_compute. reflexivity. Qed.
Transparent word_429.
Lemma closed_429_value v : eval_hfexpr expr_429 (closed_429 v) (closed_429 v) = Some (Gval (Fuint 1) (word_429 v)).
Proof. unfold word_429, closed_429, expr_429, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_429.
Lemma node_429_value v : eval_hfexpr expr_429 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_429 v)).
Proof. change (eval_hfexpr expr_429 (closed_429 v) (closed_429 v) = Some (Gval (Fuint 1) (word_429 v))). apply closed_429_value. Qed.
Lemma source_430 : find_driver 430 generated_module_0_stmts_0 = Some expr_430.
Proof. vm_compute. reflexivity. Qed.
Transparent word_430.
Lemma closed_430_value v : eval_hfexpr expr_430 (closed_430 v) (closed_430 v) = Some (Gval (Fuint 1) (word_430 v)).
Proof. unfold word_430, closed_430, expr_430, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_430.
Lemma node_430_value v : eval_hfexpr expr_430 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_430 v)).
Proof. change (eval_hfexpr expr_430 (closed_430 v) (closed_430 v) = Some (Gval (Fuint 1) (word_430 v))). apply closed_430_value. Qed.
Lemma source_431 : find_driver 431 generated_module_0_stmts_0 = Some expr_431.
Proof. vm_compute. reflexivity. Qed.
Transparent word_431.
Lemma closed_431_value v : eval_hfexpr expr_431 (closed_431 v) (closed_431 v) = Some (Gval (Fuint 1) (word_431 v)).
Proof. unfold word_431, closed_431, expr_431, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_431.
Lemma node_431_value v : eval_hfexpr expr_431 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_431 v)).
Proof. change (eval_hfexpr expr_431 (closed_431 v) (closed_431 v) = Some (Gval (Fuint 1) (word_431 v))). apply closed_431_value. Qed.
Lemma source_432 : find_driver 432 generated_module_0_stmts_0 = Some expr_432.
Proof. vm_compute. reflexivity. Qed.
Transparent word_432.
Lemma closed_432_value v : eval_hfexpr expr_432 (closed_432 v) (closed_432 v) = Some (Gval (Fuint 1) (word_432 v)).
Proof. unfold word_432, closed_432, expr_432, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_432.
Lemma node_432_value v : eval_hfexpr expr_432 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_432 v)).
Proof. change (eval_hfexpr expr_432 (closed_432 v) (closed_432 v) = Some (Gval (Fuint 1) (word_432 v))). apply closed_432_value. Qed.
Lemma source_433 : find_driver 433 generated_module_0_stmts_0 = Some expr_433.
Proof. vm_compute. reflexivity. Qed.
Transparent word_433.
Lemma closed_433_value v : eval_hfexpr expr_433 (closed_433 v) (closed_433 v) = Some (Gval (Fuint 1) (word_433 v)).
Proof. unfold word_433, closed_433, expr_433, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_433.
Lemma node_433_value v : eval_hfexpr expr_433 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_433 v)).
Proof. change (eval_hfexpr expr_433 (closed_433 v) (closed_433 v) = Some (Gval (Fuint 1) (word_433 v))). apply closed_433_value. Qed.
Lemma source_434 : find_driver 434 generated_module_0_stmts_0 = Some expr_434.
Proof. vm_compute. reflexivity. Qed.
Transparent word_434.
Lemma closed_434_value v : eval_hfexpr expr_434 (closed_434 v) (closed_434 v) = Some (Gval (Fuint 128) (word_434 v)).
Proof. unfold word_434, closed_434, expr_434, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_434.
Lemma node_434_value v : eval_hfexpr expr_434 (stable_env v) (stable_env v) = Some (Gval (Fuint 128) (word_434 v)).
Proof. change (eval_hfexpr expr_434 (closed_434 v) (closed_434 v) = Some (Gval (Fuint 128) (word_434 v))). apply closed_434_value. Qed.
Lemma source_435 : find_driver 435 generated_module_0_stmts_0 = Some expr_435.
Proof. vm_compute. reflexivity. Qed.
Transparent word_435.
Lemma closed_435_value v : eval_hfexpr expr_435 (closed_435 v) (closed_435 v) = Some (Gval (Fuint 129) (word_435 v)).
Proof. unfold word_435, closed_435, expr_435, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_435.
Lemma node_435_value v : eval_hfexpr expr_435 (stable_env v) (stable_env v) = Some (Gval (Fuint 129) (word_435 v)).
Proof. change (eval_hfexpr expr_435 (closed_435 v) (closed_435 v) = Some (Gval (Fuint 129) (word_435 v))). apply closed_435_value. Qed.
Lemma source_436 : find_driver 436 generated_module_0_stmts_0 = Some expr_436.
Proof. vm_compute. reflexivity. Qed.
Transparent word_436.
Lemma closed_436_value v : eval_hfexpr expr_436 (closed_436 v) (closed_436 v) = Some (Gval (Fuint 64) (word_436 v)).
Proof. unfold word_436, closed_436, expr_436, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_436.
Lemma node_436_value v : eval_hfexpr expr_436 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_436 v)).
Proof. change (eval_hfexpr expr_436 (closed_436 v) (closed_436 v) = Some (Gval (Fuint 64) (word_436 v))). apply closed_436_value. Qed.
Lemma source_437 : find_driver 437 generated_module_0_stmts_0 = Some expr_437.
Proof. vm_compute. reflexivity. Qed.
Transparent word_437.
Lemma closed_437_value v : eval_hfexpr expr_437 (closed_437 v) (closed_437 v) = Some (Gval (Fuint 1) (word_437 v)).
Proof. unfold word_437, closed_437, expr_437, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_437.
Lemma node_437_value v : eval_hfexpr expr_437 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_437 v)).
Proof. change (eval_hfexpr expr_437 (closed_437 v) (closed_437 v) = Some (Gval (Fuint 1) (word_437 v))). apply closed_437_value. Qed.
Lemma source_438 : find_driver 438 generated_module_0_stmts_0 = Some expr_438.
Proof. vm_compute. reflexivity. Qed.
Transparent word_438.
Lemma closed_438_value v : eval_hfexpr expr_438 (closed_438 v) (closed_438 v) = Some (Gval (Fuint 1) (word_438 v)).
Proof. unfold word_438, closed_438, expr_438, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_438.
Lemma node_438_value v : eval_hfexpr expr_438 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_438 v)).
Proof. change (eval_hfexpr expr_438 (closed_438 v) (closed_438 v) = Some (Gval (Fuint 1) (word_438 v))). apply closed_438_value. Qed.
Lemma source_439 : find_driver 439 generated_module_0_stmts_0 = Some expr_439.
Proof. vm_compute. reflexivity. Qed.
Transparent word_439.
Lemma closed_439_value v : eval_hfexpr expr_439 (closed_439 v) (closed_439 v) = Some (Gval (Fuint 1) (word_439 v)).
Proof. unfold word_439, closed_439, expr_439, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_439.
Lemma node_439_value v : eval_hfexpr expr_439 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_439 v)).
Proof. change (eval_hfexpr expr_439 (closed_439 v) (closed_439 v) = Some (Gval (Fuint 1) (word_439 v))). apply closed_439_value. Qed.
Lemma source_440 : find_driver 440 generated_module_0_stmts_0 = Some expr_440.
Proof. vm_compute. reflexivity. Qed.
Transparent word_440.
Lemma closed_440_value v : eval_hfexpr expr_440 (closed_440 v) (closed_440 v) = Some (Gval (Fuint 1) (word_440 v)).
Proof. unfold word_440, closed_440, expr_440, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_440.
Lemma node_440_value v : eval_hfexpr expr_440 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_440 v)).
Proof. change (eval_hfexpr expr_440 (closed_440 v) (closed_440 v) = Some (Gval (Fuint 1) (word_440 v))). apply closed_440_value. Qed.
Lemma source_441 : find_driver 441 generated_module_0_stmts_0 = Some expr_441.
Proof. vm_compute. reflexivity. Qed.
Transparent word_441.
Lemma closed_441_value v : eval_hfexpr expr_441 (closed_441 v) (closed_441 v) = Some (Gval (Fuint 1) (word_441 v)).
Proof. unfold word_441, closed_441, expr_441, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_441.
Lemma node_441_value v : eval_hfexpr expr_441 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_441 v)).
Proof. change (eval_hfexpr expr_441 (closed_441 v) (closed_441 v) = Some (Gval (Fuint 1) (word_441 v))). apply closed_441_value. Qed.
Lemma source_442 : find_driver 442 generated_module_0_stmts_0 = Some expr_442.
Proof. vm_compute. reflexivity. Qed.
Transparent word_442.
Lemma closed_442_value v : eval_hfexpr expr_442 (closed_442 v) (closed_442 v) = Some (Gval (Fuint 1) (word_442 v)).
Proof. unfold word_442, closed_442, expr_442, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_442.
Lemma node_442_value v : eval_hfexpr expr_442 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_442 v)).
Proof. change (eval_hfexpr expr_442 (closed_442 v) (closed_442 v) = Some (Gval (Fuint 1) (word_442 v))). apply closed_442_value. Qed.
Lemma source_443 : find_driver 443 generated_module_0_stmts_0 = Some expr_443.
Proof. vm_compute. reflexivity. Qed.
Transparent word_443.
Lemma closed_443_value v : eval_hfexpr expr_443 (closed_443 v) (closed_443 v) = Some (Gval (Fuint 1) (word_443 v)).
Proof. unfold word_443, closed_443, expr_443, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_443.
Lemma node_443_value v : eval_hfexpr expr_443 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_443 v)).
Proof. change (eval_hfexpr expr_443 (closed_443 v) (closed_443 v) = Some (Gval (Fuint 1) (word_443 v))). apply closed_443_value. Qed.
Lemma source_444 : find_driver 444 generated_module_0_stmts_0 = Some expr_444.
Proof. vm_compute. reflexivity. Qed.
Transparent word_444.
Lemma closed_444_value v : eval_hfexpr expr_444 (closed_444 v) (closed_444 v) = Some (Gval (Fuint 1) (word_444 v)).
Proof. unfold word_444, closed_444, expr_444, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_444.
Lemma node_444_value v : eval_hfexpr expr_444 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_444 v)).
Proof. change (eval_hfexpr expr_444 (closed_444 v) (closed_444 v) = Some (Gval (Fuint 1) (word_444 v))). apply closed_444_value. Qed.
Lemma source_448 : find_driver 448 generated_module_0_stmts_0 = Some expr_448.
Proof. vm_compute. reflexivity. Qed.
Transparent word_448.
Lemma closed_448_value v : eval_hfexpr expr_448 (closed_448 v) (closed_448 v) = Some (Gval (Fuint 1) (word_448 v)).
Proof. unfold word_448, closed_448, expr_448, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_448.
Lemma node_448_value v : eval_hfexpr expr_448 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_448 v)).
Proof. change (eval_hfexpr expr_448 (closed_448 v) (closed_448 v) = Some (Gval (Fuint 1) (word_448 v))). apply closed_448_value. Qed.
Lemma source_449 : find_driver 449 generated_module_0_stmts_0 = Some expr_449.
Proof. vm_compute. reflexivity. Qed.
Transparent word_449.
Lemma closed_449_value v : eval_hfexpr expr_449 (closed_449 v) (closed_449 v) = Some (Gval (Fuint 1) (word_449 v)).
Proof. unfold word_449, closed_449, expr_449, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_449.
Lemma node_449_value v : eval_hfexpr expr_449 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_449 v)).
Proof. change (eval_hfexpr expr_449 (closed_449 v) (closed_449 v) = Some (Gval (Fuint 1) (word_449 v))). apply closed_449_value. Qed.
Lemma source_450 : find_driver 450 generated_module_0_stmts_0 = Some expr_450.
Proof. vm_compute. reflexivity. Qed.
Transparent word_450.
Lemma closed_450_value v : eval_hfexpr expr_450 (closed_450 v) (closed_450 v) = Some (Gval (Fuint 1) (word_450 v)).
Proof. unfold word_450, closed_450, expr_450, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_450.
Lemma node_450_value v : eval_hfexpr expr_450 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_450 v)).
Proof. change (eval_hfexpr expr_450 (closed_450 v) (closed_450 v) = Some (Gval (Fuint 1) (word_450 v))). apply closed_450_value. Qed.
Lemma source_451 : find_driver 451 generated_module_0_stmts_0 = Some expr_451.
Proof. vm_compute. reflexivity. Qed.
Transparent word_451.
Lemma closed_451_value v : eval_hfexpr expr_451 (closed_451 v) (closed_451 v) = Some (Gval (Fuint 1) (word_451 v)).
Proof. unfold word_451, closed_451, expr_451, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_451.
Lemma node_451_value v : eval_hfexpr expr_451 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_451 v)).
Proof. change (eval_hfexpr expr_451 (closed_451 v) (closed_451 v) = Some (Gval (Fuint 1) (word_451 v))). apply closed_451_value. Qed.
Lemma source_452 : find_driver 452 generated_module_0_stmts_0 = Some expr_452.
Proof. vm_compute. reflexivity. Qed.
Transparent word_452.
Lemma closed_452_value v : eval_hfexpr expr_452 (closed_452 v) (closed_452 v) = Some (Gval (Fuint 1) (word_452 v)).
Proof. unfold word_452, closed_452, expr_452, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_452.
Lemma node_452_value v : eval_hfexpr expr_452 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_452 v)).
Proof. change (eval_hfexpr expr_452 (closed_452 v) (closed_452 v) = Some (Gval (Fuint 1) (word_452 v))). apply closed_452_value. Qed.
Lemma source_453 : find_driver 453 generated_module_0_stmts_0 = Some expr_453.
Proof. vm_compute. reflexivity. Qed.
Transparent word_453.
Lemma closed_453_value v : eval_hfexpr expr_453 (closed_453 v) (closed_453 v) = Some (Gval (Fuint 1) (word_453 v)).
Proof. unfold word_453, closed_453, expr_453, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_453.
Lemma node_453_value v : eval_hfexpr expr_453 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_453 v)).
Proof. change (eval_hfexpr expr_453 (closed_453 v) (closed_453 v) = Some (Gval (Fuint 1) (word_453 v))). apply closed_453_value. Qed.
Lemma source_454 : find_driver 454 generated_module_0_stmts_0 = Some expr_454.
Proof. vm_compute. reflexivity. Qed.
Transparent word_454.
Lemma closed_454_value v : eval_hfexpr expr_454 (closed_454 v) (closed_454 v) = Some (Gval (Fuint 1) (word_454 v)).
Proof. unfold word_454, closed_454, expr_454, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_454.
Lemma node_454_value v : eval_hfexpr expr_454 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_454 v)).
Proof. change (eval_hfexpr expr_454 (closed_454 v) (closed_454 v) = Some (Gval (Fuint 1) (word_454 v))). apply closed_454_value. Qed.
Lemma source_455 : find_driver 455 generated_module_0_stmts_0 = Some expr_455.
Proof. vm_compute. reflexivity. Qed.
Transparent word_455.
Lemma closed_455_value v : eval_hfexpr expr_455 (closed_455 v) (closed_455 v) = Some (Gval (Fuint 1) (word_455 v)).
Proof. unfold word_455, closed_455, expr_455, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_455.
Lemma node_455_value v : eval_hfexpr expr_455 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_455 v)).
Proof. change (eval_hfexpr expr_455 (closed_455 v) (closed_455 v) = Some (Gval (Fuint 1) (word_455 v))). apply closed_455_value. Qed.
Lemma source_456 : find_driver 456 generated_module_0_stmts_0 = Some expr_456.
Proof. vm_compute. reflexivity. Qed.
Transparent word_456.
Lemma closed_456_value v : eval_hfexpr expr_456 (closed_456 v) (closed_456 v) = Some (Gval (Fuint 1) (word_456 v)).
Proof. unfold word_456, closed_456, expr_456, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_456.
Lemma node_456_value v : eval_hfexpr expr_456 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_456 v)).
Proof. change (eval_hfexpr expr_456 (closed_456 v) (closed_456 v) = Some (Gval (Fuint 1) (word_456 v))). apply closed_456_value. Qed.
Lemma source_457 : find_driver 457 generated_module_0_stmts_0 = Some expr_457.
Proof. vm_compute. reflexivity. Qed.
Transparent word_457.
Lemma closed_457_value v : eval_hfexpr expr_457 (closed_457 v) (closed_457 v) = Some (Gval (Fuint 1) (word_457 v)).
Proof. unfold word_457, closed_457, expr_457, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_457.
Lemma node_457_value v : eval_hfexpr expr_457 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_457 v)).
Proof. change (eval_hfexpr expr_457 (closed_457 v) (closed_457 v) = Some (Gval (Fuint 1) (word_457 v))). apply closed_457_value. Qed.
Lemma source_458 : find_driver 458 generated_module_0_stmts_0 = Some expr_458.
Proof. vm_compute. reflexivity. Qed.
Transparent word_458.
Lemma closed_458_value v : eval_hfexpr expr_458 (closed_458 v) (closed_458 v) = Some (Gval (Fuint 1) (word_458 v)).
Proof. unfold word_458, closed_458, expr_458, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_458.
Lemma node_458_value v : eval_hfexpr expr_458 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_458 v)).
Proof. change (eval_hfexpr expr_458 (closed_458 v) (closed_458 v) = Some (Gval (Fuint 1) (word_458 v))). apply closed_458_value. Qed.
Lemma source_459 : find_driver 459 generated_module_0_stmts_0 = Some expr_459.
Proof. vm_compute. reflexivity. Qed.
Transparent word_459.
Lemma closed_459_value v : eval_hfexpr expr_459 (closed_459 v) (closed_459 v) = Some (Gval (Fuint 1) (word_459 v)).
Proof. unfold word_459, closed_459, expr_459, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_459.
Lemma node_459_value v : eval_hfexpr expr_459 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_459 v)).
Proof. change (eval_hfexpr expr_459 (closed_459 v) (closed_459 v) = Some (Gval (Fuint 1) (word_459 v))). apply closed_459_value. Qed.
Lemma source_460 : find_driver 460 generated_module_0_stmts_0 = Some expr_460.
Proof. vm_compute. reflexivity. Qed.
Transparent word_460.
Lemma closed_460_value v : eval_hfexpr expr_460 (closed_460 v) (closed_460 v) = Some (Gval (Fuint 3) (word_460 v)).
Proof. unfold word_460, closed_460, expr_460, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_460.
Lemma node_460_value v : eval_hfexpr expr_460 (stable_env v) (stable_env v) = Some (Gval (Fuint 3) (word_460 v)).
Proof. change (eval_hfexpr expr_460 (closed_460 v) (closed_460 v) = Some (Gval (Fuint 3) (word_460 v))). apply closed_460_value. Qed.
Lemma source_461 : find_driver 461 generated_module_0_stmts_0 = Some expr_461.
Proof. vm_compute. reflexivity. Qed.
Transparent word_461.
Lemma closed_461_value v : eval_hfexpr expr_461 (closed_461 v) (closed_461 v) = Some (Gval (Fuint 1) (word_461 v)).
Proof. unfold word_461, closed_461, expr_461, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_461.
Lemma node_461_value v : eval_hfexpr expr_461 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_461 v)).
Proof. change (eval_hfexpr expr_461 (closed_461 v) (closed_461 v) = Some (Gval (Fuint 1) (word_461 v))). apply closed_461_value. Qed.
Lemma source_462 : find_driver 462 generated_module_0_stmts_0 = Some expr_462.
Proof. vm_compute. reflexivity. Qed.
Transparent word_462.
Lemma closed_462_value v : eval_hfexpr expr_462 (closed_462 v) (closed_462 v) = Some (Gval (Fuint 1) (word_462 v)).
Proof. unfold word_462, closed_462, expr_462, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_462.
Lemma node_462_value v : eval_hfexpr expr_462 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_462 v)).
Proof. change (eval_hfexpr expr_462 (closed_462 v) (closed_462 v) = Some (Gval (Fuint 1) (word_462 v))). apply closed_462_value. Qed.
Lemma source_463 : find_driver 463 generated_module_0_stmts_0 = Some expr_463.
Proof. vm_compute. reflexivity. Qed.
Transparent word_463.
Lemma closed_463_value v : eval_hfexpr expr_463 (closed_463 v) (closed_463 v) = Some (Gval (Fuint 1) (word_463 v)).
Proof. unfold word_463, closed_463, expr_463, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_463.
Lemma node_463_value v : eval_hfexpr expr_463 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_463 v)).
Proof. change (eval_hfexpr expr_463 (closed_463 v) (closed_463 v) = Some (Gval (Fuint 1) (word_463 v))). apply closed_463_value. Qed.
Lemma source_464 : find_driver 464 generated_module_0_stmts_0 = Some expr_464.
Proof. vm_compute. reflexivity. Qed.
Transparent word_464.
Lemma closed_464_value v : eval_hfexpr expr_464 (closed_464 v) (closed_464 v) = Some (Gval (Fuint 1) (word_464 v)).
Proof. unfold word_464, closed_464, expr_464, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_464.
Lemma node_464_value v : eval_hfexpr expr_464 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_464 v)).
Proof. change (eval_hfexpr expr_464 (closed_464 v) (closed_464 v) = Some (Gval (Fuint 1) (word_464 v))). apply closed_464_value. Qed.
Lemma source_465 : find_driver 465 generated_module_0_stmts_0 = Some expr_465.
Proof. vm_compute. reflexivity. Qed.
Transparent word_465.
Lemma closed_465_value v : eval_hfexpr expr_465 (closed_465 v) (closed_465 v) = Some (Gval (Fuint 1) (word_465 v)).
Proof. unfold word_465, closed_465, expr_465, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_465.
Lemma node_465_value v : eval_hfexpr expr_465 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_465 v)).
Proof. change (eval_hfexpr expr_465 (closed_465 v) (closed_465 v) = Some (Gval (Fuint 1) (word_465 v))). apply closed_465_value. Qed.
Lemma source_466 : find_driver 466 generated_module_0_stmts_0 = Some expr_466.
Proof. vm_compute. reflexivity. Qed.
Transparent word_466.
Lemma closed_466_value v : eval_hfexpr expr_466 (closed_466 v) (closed_466 v) = Some (Gval (Fuint 7) (word_466 v)).
Proof. unfold word_466, closed_466, expr_466, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_466.
Lemma node_466_value v : eval_hfexpr expr_466 (stable_env v) (stable_env v) = Some (Gval (Fuint 7) (word_466 v)).
Proof. change (eval_hfexpr expr_466 (closed_466 v) (closed_466 v) = Some (Gval (Fuint 7) (word_466 v))). apply closed_466_value. Qed.
Lemma source_467 : find_driver 467 generated_module_0_stmts_0 = Some expr_467.
Proof. vm_compute. reflexivity. Qed.
Transparent word_467.
Lemma closed_467_value v : eval_hfexpr expr_467 (closed_467 v) (closed_467 v) = Some (Gval (Fuint 6) (word_467 v)).
Proof. unfold word_467, closed_467, expr_467, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_467.
Lemma node_467_value v : eval_hfexpr expr_467 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_467 v)).
Proof. change (eval_hfexpr expr_467 (closed_467 v) (closed_467 v) = Some (Gval (Fuint 6) (word_467 v))). apply closed_467_value. Qed.
Lemma source_468 : find_driver 468 generated_module_0_stmts_0 = Some expr_468.
Proof. vm_compute. reflexivity. Qed.
Transparent word_468.
Lemma closed_468_value v : eval_hfexpr expr_468 (closed_468 v) (closed_468 v) = Some (Gval (Fuint 6) (word_468 v)).
Proof. unfold word_468, closed_468, expr_468, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_468.
Lemma node_468_value v : eval_hfexpr expr_468 (stable_env v) (stable_env v) = Some (Gval (Fuint 6) (word_468 v)).
Proof. change (eval_hfexpr expr_468 (closed_468 v) (closed_468 v) = Some (Gval (Fuint 6) (word_468 v))). apply closed_468_value. Qed.
Lemma source_469 : find_driver 469 generated_module_0_stmts_0 = Some expr_469.
Proof. vm_compute. reflexivity. Qed.
Transparent word_469.
Lemma closed_469_value v : eval_hfexpr expr_469 (closed_469 v) (closed_469 v) = Some (Gval (Fuint 1) (word_469 v)).
Proof. unfold word_469, closed_469, expr_469, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_469.
Lemma node_469_value v : eval_hfexpr expr_469 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_469 v)).
Proof. change (eval_hfexpr expr_469 (closed_469 v) (closed_469 v) = Some (Gval (Fuint 1) (word_469 v))). apply closed_469_value. Qed.
Lemma source_470 : find_driver 470 generated_module_0_stmts_0 = Some expr_470.
Proof. vm_compute. reflexivity. Qed.
Transparent word_470.
Lemma closed_470_value v : eval_hfexpr expr_470 (closed_470 v) (closed_470 v) = Some (Gval (Fuint 1) (word_470 v)).
Proof. unfold word_470, closed_470, expr_470, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_470.
Lemma node_470_value v : eval_hfexpr expr_470 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_470 v)).
Proof. change (eval_hfexpr expr_470 (closed_470 v) (closed_470 v) = Some (Gval (Fuint 1) (word_470 v))). apply closed_470_value. Qed.
Lemma source_471 : find_driver 471 generated_module_0_stmts_0 = Some expr_471.
Proof. vm_compute. reflexivity. Qed.
Transparent word_471.
Lemma closed_471_value v : eval_hfexpr expr_471 (closed_471 v) (closed_471 v) = Some (Gval (Fuint 1) (word_471 v)).
Proof. unfold word_471, closed_471, expr_471, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_471.
Lemma node_471_value v : eval_hfexpr expr_471 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_471 v)).
Proof. change (eval_hfexpr expr_471 (closed_471 v) (closed_471 v) = Some (Gval (Fuint 1) (word_471 v))). apply closed_471_value. Qed.
Lemma source_472 : find_driver 472 generated_module_0_stmts_0 = Some expr_472.
Proof. vm_compute. reflexivity. Qed.
Transparent word_472.
Lemma closed_472_value v : eval_hfexpr expr_472 (closed_472 v) (closed_472 v) = Some (Gval (Fuint 1) (word_472 v)).
Proof. unfold word_472, closed_472, expr_472, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_472.
Lemma node_472_value v : eval_hfexpr expr_472 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_472 v)).
Proof. change (eval_hfexpr expr_472 (closed_472 v) (closed_472 v) = Some (Gval (Fuint 1) (word_472 v))). apply closed_472_value. Qed.
Lemma source_473 : find_driver 473 generated_module_0_stmts_0 = Some expr_473.
Proof. vm_compute. reflexivity. Qed.
Transparent word_473.
Lemma closed_473_value v : eval_hfexpr expr_473 (closed_473 v) (closed_473 v) = Some (Gval (Fuint 1) (word_473 v)).
Proof. unfold word_473, closed_473, expr_473, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_473.
Lemma node_473_value v : eval_hfexpr expr_473 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_473 v)).
Proof. change (eval_hfexpr expr_473 (closed_473 v) (closed_473 v) = Some (Gval (Fuint 1) (word_473 v))). apply closed_473_value. Qed.
Lemma source_8 : find_driver 8 generated_module_0_stmts_0 = Some expr_8.
Proof. vm_compute. reflexivity. Qed.
Transparent word_8.
Lemma closed_8_value v : eval_hfexpr expr_8 (closed_8 v) (closed_8 v) = Some (Gval (Fuint 1) (word_8 v)).
Proof. unfold word_8, closed_8, expr_8, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_8.
Lemma node_8_value v : eval_hfexpr expr_8 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_8 v)).
Proof. change (eval_hfexpr expr_8 (closed_8 v) (closed_8 v) = Some (Gval (Fuint 1) (word_8 v))). apply closed_8_value. Qed.
Lemma source_474 : find_driver 474 generated_module_0_stmts_0 = Some expr_474.
Proof. vm_compute. reflexivity. Qed.
Transparent word_474.
Lemma closed_474_value v : eval_hfexpr expr_474 (closed_474 v) (closed_474 v) = Some (Gval (Fuint 1) (word_474 v)).
Proof. unfold word_474, closed_474, expr_474, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_474.
Lemma node_474_value v : eval_hfexpr expr_474 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_474 v)).
Proof. change (eval_hfexpr expr_474 (closed_474 v) (closed_474 v) = Some (Gval (Fuint 1) (word_474 v))). apply closed_474_value. Qed.
Lemma source_477 : find_driver 477 generated_module_0_stmts_0 = Some expr_477.
Proof. vm_compute. reflexivity. Qed.
Transparent word_477.
Lemma closed_477_value v : eval_hfexpr expr_477 (closed_477 v) (closed_477 v) = Some (Gval (Fuint 1) (word_477 v)).
Proof. unfold word_477, closed_477, expr_477, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_477.
Lemma node_477_value v : eval_hfexpr expr_477 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_477 v)).
Proof. change (eval_hfexpr expr_477 (closed_477 v) (closed_477 v) = Some (Gval (Fuint 1) (word_477 v))). apply closed_477_value. Qed.
Lemma source_478 : find_driver 478 generated_module_0_stmts_0 = Some expr_478.
Proof. vm_compute. reflexivity. Qed.
Transparent word_478.
Lemma closed_478_value v : eval_hfexpr expr_478 (closed_478 v) (closed_478 v) = Some (Gval (Fuint 1) (word_478 v)).
Proof. unfold word_478, closed_478, expr_478, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_478.
Lemma node_478_value v : eval_hfexpr expr_478 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_478 v)).
Proof. change (eval_hfexpr expr_478 (closed_478 v) (closed_478 v) = Some (Gval (Fuint 1) (word_478 v))). apply closed_478_value. Qed.
Lemma source_479 : find_driver 479 generated_module_0_stmts_0 = Some expr_479.
Proof. vm_compute. reflexivity. Qed.
Transparent word_479.
Lemma closed_479_value v : eval_hfexpr expr_479 (closed_479 v) (closed_479 v) = Some (Gval (Fuint 1) (word_479 v)).
Proof. unfold word_479, closed_479, expr_479, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_479.
Lemma node_479_value v : eval_hfexpr expr_479 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_479 v)).
Proof. change (eval_hfexpr expr_479 (closed_479 v) (closed_479 v) = Some (Gval (Fuint 1) (word_479 v))). apply closed_479_value. Qed.
Lemma source_9 : find_driver 9 generated_module_0_stmts_0 = Some expr_9.
Proof. vm_compute. reflexivity. Qed.
Transparent word_9.
Lemma closed_9_value v : eval_hfexpr expr_9 (closed_9 v) (closed_9 v) = Some (Gval (Fuint 64) (word_9 v)).
Proof. unfold word_9, closed_9, expr_9, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_9.
Lemma node_9_value v : eval_hfexpr expr_9 (stable_env v) (stable_env v) = Some (Gval (Fuint 64) (word_9 v)).
Proof. change (eval_hfexpr expr_9 (closed_9 v) (closed_9 v) = Some (Gval (Fuint 64) (word_9 v))). apply closed_9_value. Qed.
Lemma source_480 : find_driver 480 generated_module_0_stmts_0 = Some expr_480.
Proof. vm_compute. reflexivity. Qed.
Transparent word_480.
Lemma closed_480_value v : eval_hfexpr expr_480 (closed_480 v) (closed_480 v) = Some (Gval (Fuint 1) (word_480 v)).
Proof. unfold word_480, closed_480, expr_480, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_480.
Lemma node_480_value v : eval_hfexpr expr_480 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_480 v)).
Proof. change (eval_hfexpr expr_480 (closed_480 v) (closed_480 v) = Some (Gval (Fuint 1) (word_480 v))). apply closed_480_value. Qed.
Lemma source_481 : find_driver 481 generated_module_0_stmts_0 = Some expr_481.
Proof. vm_compute. reflexivity. Qed.
Transparent word_481.
Lemma closed_481_value v : eval_hfexpr expr_481 (closed_481 v) (closed_481 v) = Some (Gval (Fuint 1) (word_481 v)).
Proof. unfold word_481, closed_481, expr_481, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_481.
Lemma node_481_value v : eval_hfexpr expr_481 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_481 v)).
Proof. change (eval_hfexpr expr_481 (closed_481 v) (closed_481 v) = Some (Gval (Fuint 1) (word_481 v))). apply closed_481_value. Qed.
Lemma source_482 : find_driver 482 generated_module_0_stmts_0 = Some expr_482.
Proof. vm_compute. reflexivity. Qed.
Transparent word_482.
Lemma closed_482_value v : eval_hfexpr expr_482 (closed_482 v) (closed_482 v) = Some (Gval (Fuint 1) (word_482 v)).
Proof. unfold word_482, closed_482, expr_482, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_482.
Lemma node_482_value v : eval_hfexpr expr_482 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_482 v)).
Proof. change (eval_hfexpr expr_482 (closed_482 v) (closed_482 v) = Some (Gval (Fuint 1) (word_482 v))). apply closed_482_value. Qed.
Lemma source_483 : find_driver 483 generated_module_0_stmts_0 = Some expr_483.
Proof. vm_compute. reflexivity. Qed.
Transparent word_483.
Lemma closed_483_value v : eval_hfexpr expr_483 (closed_483 v) (closed_483 v) = Some (Gval (Fuint 1) (word_483 v)).
Proof. unfold word_483, closed_483, expr_483, word_of_eval. cbn [eval_hfexpr eval_href eval_type_of_expr type_of_expr' eval_binop eval_unop extend_hvalue_as_type]. repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]. unfold eval_binop; cbn [eval_binop_basic eval_unop extend_hvalue_as_type]. rewrite ?refine_ground. repeat match goal with | |- context [if is_zero ?b then _ else _] => destruct (is_zero b) end; cbn [eval_type_of_expr type_of_expr' eval_type_of_ref type_of_val make_ftype_explicit extend_hvalue_as_type]; repeat first [rewrite VM.Lemmas.find_add_eq; [|reflexivity] | rewrite VM.Lemmas.find_add_neq; [|discriminate]]; cbn [type_of_val make_ftype_explicit extend_hvalue_as_type]; reflexivity. Qed.
Opaque word_483.
Lemma node_483_value v : eval_hfexpr expr_483 (stable_env v) (stable_env v) = Some (Gval (Fuint 1) (word_483 v)).
Proof. change (eval_hfexpr expr_483 (closed_483 v) (closed_483 v) = Some (Gval (Fuint 1) (word_483 v))). apply closed_483_value. Qed.
Print Assumptions node_14_value.
Print Assumptions node_483_value.

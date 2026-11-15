From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
 HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import EnvironmentFacts ScalarEvaluation.

(* Standalone scalar type preservation. The operator case proofs are adapted
   from the upstream development, but no admitted evaluator theorem or circuit
   typing hypothesis is used. Plain references are discharged by env_typed. *)
Inductive scalar_expression : @hfexpr VarOrder.T -> Prop :=
| ScalarConstant typ bits : scalar_expression (@Econst VarOrder.T typ bits)
| ScalarCast cast e : scalar_expression e -> scalar_expression (@Ecast VarOrder.T cast e)
| ScalarUnary op e : scalar_expression e -> scalar_expression (@Eprim_unop VarOrder.T op e)
| ScalarBinary op lhs rhs : scalar_expression lhs -> scalar_expression rhs ->
    scalar_expression (@Eprim_binop VarOrder.T op lhs rhs)
| ScalarMux guard yes no : scalar_expression guard -> scalar_expression yes -> scalar_expression no ->
    scalar_expression (@Emux VarOrder.T guard yes no)
| ScalarValidif guard body : scalar_expression guard -> scalar_expression body ->
    scalar_expression (@Evalidif VarOrder.T guard body)
| ScalarIdentifier id : scalar_expression (@Eref VarOrder.T (@Eid VarOrder.T id)).
Lemma scalar_expression_from_bool e (pure : scalar_exprb e) : scalar_expression e.
Proof.
  revert pure. induction e as [typ bits|cast e IH|op e IH|op lhs IHlhs rhs IHrhs|
    guard IHguard yes IHyes no IHno|guard IHguard body IHbody|reference]; intro pure.
  - constructor.
  - apply ScalarCast. exact (IH pure).
  - apply ScalarUnary. exact (IH pure).
  - move/andP: pure => [HL HR]. constructor; [exact (IHlhs HL)|exact (IHrhs HR)].
  - move/andP: pure => [/andP [HC HY] HN]. constructor;
      [exact (IHguard HC)|exact (IHyes HY)|exact (IHno HN)].
  - move/andP: pure => [HC HB]. constructor; [exact (IHguard HC)|exact (IHbody HB)].
  - destruct reference; try discriminate pure. constructor.
Qed.

Definition scalar_raw_typed result typ : bool :=
 match result, typ with
 | Some value, Some t => hvalue_is_type_correct value (make_ftype_explicit t) && ftype_is_concrete t
 | Some _, None => false
 | None, Some t => ftype_is_concrete t
 | None, None => true end.
Definition scalar_validif_value (guard body : option hvalue) (typ : option ftype) :=
 match guard with
 | Some (Gval (Fuint _) bits) => if is_zero bits then
     option_map Undefinedonpurpose (option_map make_ftype_explicit typ) else body
 | Some (Needtobedefined (Gtyp (Fuint _)))
 | Some (Uninitialized (Gtyp (Fuint _))) =>
     option_map Needtobedefined (option_map make_ftype_explicit typ)
 | Some (Undefinedonpurpose (Gtyp (Fuint _))) =>
     option_map Undefinedonpurpose (option_map make_ftype_explicit typ)
 | _ => None end.
Lemma scalar_validif_preserves_type guard body typ
 (typed : scalar_raw_typed body typ) : scalar_raw_typed (scalar_validif_value guard body typ) typ.
Proof.
  destruct typ as [t|], body as [v|]; cbn [scalar_raw_typed] in typed; try discriminate typed.
  all: destruct guard as [[[w|w|w|w| | | |] bits|elt array|fields|
     [[w|w|w|w| | | |]|elt n|fields]|
     [[w|w|w|w| | | |]|elt n|fields]|
     [[w|w|w|w| | | |]|elt n|fields]]|];
     cbn [scalar_validif_value option_map scalar_raw_typed hvalue_is_type_correct];
     try (destruct (is_zero bits));
     cbn [option_map scalar_raw_typed hvalue_is_type_correct];
     try exact typed;
     try reflexivity;
     try (exact (proj2 (elimT andP typed)));
     rewrite ?make_ftype_explicit_is_explicit_and_concrete ?eq_refl ?andTb;
     try exact typed;
     try (exact (proj2 (elimT andP typed))).
Qed.

Lemma scalar_identifier_type_correct env id (typed : env_typed env) :
 scalar_raw_typed (VM.find id env) (option_map type_of_val (VM.find id env)).
Proof.
 destruct (VM.find id env) as [value|] eqn:found;
   cbn [option_map scalar_raw_typed]; [|reflexivity].
 pose proof (typed id value found) as correct.
 pose proof (hvalue_is_type_correct_is_explicit correct) as explicit.
 rewrite -(ftype_is_explicit_and_concrete_implies_make_ftype_explicit_id explicit).
 rewrite correct andTb. exact (ftype_is_explicit_and_concrete_implies_concrete explicit).
Qed.

Lemma scalar_eval_type_correct sem_old sem_new e
 (environment : env_typed sem_new) (pure : scalar_exprb e) :
 match eval_hfexpr e sem_old sem_new, eval_type_of_expr e sem_new with
 | Some value, Some typ => hvalue_is_type_correct value typ
 | Some _, None => false
 | None, Some typ => ftype_is_explicit_and_concrete typ
 | None, None => true end.
Proof.
  pose proof (env_typed_evaluator_condition sem_new environment) as H.
  pose proof (scalar_expression_from_bool e pure) as derivation. clear pure.
  enough (match eval_hfexpr e sem_old sem_new, type_of_expr' (eval_type_of_ref^~ sem_new) e with
          | Some val, Some toe => hvalue_is_type_correct val (make_ftype_explicit toe) && ftype_is_concrete toe
          | Some _, None => false
          | None, Some toe => ftype_is_concrete toe (* should allow for out-of-bound array indices *)
          | None, _ => true
          end).
          unfold eval_type_of_expr.
          destruct (eval_hfexpr e sem_old sem_new) as [val|], (type_of_expr' (eval_type_of_ref^~ sem_new) e) as [toe|] ;
                try done ;
                unfold option_map.
          - move /andP : H0 => [H0 _] ; by exact H0.
          - by apply make_ftype_explicit_is_explicit_and_concrete.
  (* Now that we have proven the "enough" condition, we can continue with the simplified goal: *)
  induction derivation as [[w|w|w|w| | | |] bs|[] e body IHe|op e body IHe|
    op e1 e2 left_pure IHe1 right_pure IHe2|
    c e1 e2 guard_pure IHc yes_pure IHe1 no_pure IHe2|
    c e guard_pure IHc body_pure IHe|id] ;
        simpl ; try done.
  + (* Econst *)
    1,2: destruct (w < size bs) eqn: Hws ; first done.
    1,2: simpl ; rewrite ?size_zext ?size_sext eq_refl ?andbT subnKC // leqNgt Hws //.
  + (* Ecast *)
    1-4: destruct (eval_hfexpr e sem_old sem_new) as [[[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]]|],
                  (type_of_expr' (eval_type_of_ref^~ sem_new) e) as [[[wt|wt|wt|wt| | | |]| |]|] ;
            simpl ; simpl in IHe ;
            try (by move /andP : IHe => [IHe1 IHe2]) ;
            try done.
    1-4: by rewrite eq_refl IHe.
  + (* Eunop *)
    destruct (eval_hfexpr e sem_old sem_new) as [val|], (type_of_expr' (eval_type_of_ref^~ sem_new) e) as [toe|] ;
        try done ;
        last (by destruct op) ;
        last (by destruct op as [n|n|n| | | | | | |hi lo|n|n],
                         toe as [[wt|wt|wt|wt| | | |]| |] ; simpl ; try done ;
                 try (destruct (lo <= hi) ; simpl ; try done) ;
                 destruct (_ <= wt) ; simpl).
    unfold option_map in IHe.
    (*generalize (type_of_val_correct IHe) ; intro.*)
    destruct op as [n|n|n| | | | | | |hi lo|n|n] ; simpl.
    - (* Upad n *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
             by rewrite ?size_zext ?size_sext -maxnE IHe1 IHe2 ?eq_refl.
      * 1-15: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst ;
              by rewrite eq_refl.
    - (* Ushl n *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |];
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
             by rewrite size_cat size_zeros IHe1 IHe2 (addnC n) ?eq_refl.
      * 1-15: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst ;
              by rewrite eq_refl.
    - (* Ushr n *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 4,5: destruct wv ; simpl.
      * 1-7: move /andP : IHe => [/eqP IHe1 /eqP IHe2].
        1-7: rewrite ?size_drop ?IHe1 -IHe2 ?eq_refl //.
        1-2: rewrite maxnC /maxn ltnNge leq_subLR addn1 ltnS -ltnNge.
        1-2: rewrite subn1 /predn /minn.
        1-2: destruct (n < wv) ; by rewrite ?subSnn eq_refl.
      * 1-15: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst ;
              by rewrite eq_refl.
    - (* Ucvt *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
             by rewrite ?size_zext IHe1 IHe2 ?addn1 ?eq_refl.
      * 1-15: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst ;
              by rewrite eq_refl.
    - (* Uneg *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
             by rewrite size_negB ?size_zext ?size_sext IHe1 IHe2 addn1 ?eq_refl.
      * 1-15: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst ;
              by rewrite eq_refl.
    - (* Unot *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
             by rewrite size_invB IHe1 IHe2 ?eq_refl.
      * 1-15: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst ;
              by rewrite eq_refl.
    - (* Uandr, Uorr, Uxorr *)
      1-3: destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; done.
    - (* Uextr hi lo *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      1-50: destruct (lo <= hi) eqn: Hlohi ; try done.
      * 1-5: generalize (eqn_leq hi.+1 wv) ; intro.
        1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
                  rewrite IHe2 ; rewrite IHe2 in IHe1 H0.
        1-5: destruct (hi < _) ; try done ; simpl.
        1-5: rewrite andTb leqNgt in H0.
        1-5: rewrite size_drop size_take IHe1 ?/minn ;
             destruct (hi.+1 < _) ; first by rewrite ?eq_refl.
        1-5: simpl in H0 ; move /eqP : H0 => H0 ; by rewrite H0 ?eq_refl.
      * 1-5,10-14,19-23: generalize (eqn_leq hi.+1 wv) ; intro.
        1-15: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst wv.
        1-15: rewrite ?/minn ; destruct (hi < _) ; simpl ; rewrite ?eq_refl //.
        1-9: rewrite andTb leqNgt in H0.
        1,3,4,6,7,9: destruct (hi.+1 < _) ; first rewrite ?eq_refl //.
        7-9: rewrite ltnS ltn0 in H0.
        1-9: simpl in H0 ; move /eqP : H0 => H0 ; try by rewrite H0 ?eq_refl.
      * 1-12: move /andP : IHe => [_ /eqP IHe] ; by discriminate IHe.
    - (* Uhead n *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
             rewrite IHe2 ?(minnC n) ?/minn ?ltnNge ; rewrite IHe2 in IHe1.
        1-5: destruct (n <= _) eqn: Hn ; try done ; simpl.
        1-5: by rewrite size_drop IHe1 (subKn Hn) ?eq_refl.
      * 1-5,10-14,19-23: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst wv.
        1-15: rewrite ?(minnC n) ?/minn ?ltnNge.
        1-15: destruct (n <= _) eqn: Hn ; simpl ; by rewrite // eq_refl.
      * 1-12: move /andP : IHe => [_ /eqP IHe] ; by discriminate IHe.
    - (* Utail n *)
      destruct val as [[wv|wv|wv|wv| | | |]| | |[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]|[[wv|wv|wv|wv| | | |]| |]],
               toe as [[wt|wt|wt|wt| | | |]| |] ;
            simpl ; simpl in IHe ;
            try (move /andP : IHe => [IHe IHe']) ; try done.
      * 1-5: move /andP : IHe => [/eqP IHe1 /eqP IHe2] ;
             rewrite IHe2 ; rewrite IHe2 in IHe1.
        1-5: destruct (n <= _) ; try done ; simpl.
        1-5: rewrite size_take IHe1 ltn_subrL ;
             destruct n ; try done ; destruct wt ;
             by rewrite ?subn0 ?eq_refl.
      * 1-5,10-14,19-23: move /eqP : IHe => IHe ; injection IHe ; clear IHe ; intros ; subst wv.
        1-15: destruct (n <= _) eqn: Hn ; simpl ; by rewrite // eq_refl.
      * 1-12: move /andP : IHe => [_ /eqP IHe] ; by discriminate IHe.
  + (* Ebinop *)
    destruct (eval_hfexpr e1 sem_old sem_new) as [val1|], (type_of_expr' (eval_type_of_ref^~ sem_new) e1) as [toe1|] ;
        try done ;
        last (by destruct op) ;
        last (by destruct op, toe1 as [[]| |] ;
                 try done ;
                 destruct (type_of_expr' (eval_type_of_ref^~ sem_new) e2) as [[[]| |]|]).
    destruct (eval_hfexpr e2 sem_old sem_new) as [val2|], (type_of_expr' (eval_type_of_ref^~ sem_new) e2) as [toe2|] ;
        try done ;
        last (by destruct op, toe1 as [[]| |]) ;
        last (by destruct op, toe1 as [[]| |] ;
                 try done ;
                 destruct toe2 as [[]| |]).
    unfold eval_binop.
    apply refine_boolean_result_type_correct.
    apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1 IHe1'] ;
    apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2 IHe2'].
    destruct op ; simpl.
    - (* Badd, Bsub *)
      1,2: destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-416: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      1-416: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].
      1-416: by rewrite ?size_from_N ?size_from_Z ?eq_refl //.
    - (* Bmul *)
      destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-208: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      1-208: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].
      1-208: by rewrite ?size_from_N ?size_from_Z ?eq_refl //.
    - (* Bdiv *)
      destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-208: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      (*1-208: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].*)
      1-208: by rewrite ?size_from_N ?size_from_Z ?eq_refl //.
    - (* Brem *)
      destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-208: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      1-208: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].
      1-208: by rewrite ?size_from_N ?size_from_Z ?eq_refl //.
    - (* Bcomp *)
      destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl.
      1-13: by destruct b.
    - (* Bdshl *)
      destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-240: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      1-240: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].
      1-240: rewrite ?eq_refl ?andbT //.
      1-15: rewrite ?size_zext ?size_sext size_cat size_zeros (elimT eqP IHe1'') IHe1 subnKC //.
      1-15: rewrite (addnC _ (2^_)) -subn1 -addnBAC ?expn_gt0 // leq_add2r leq_subRL ?expn_gt0 // add1n.
      1-15: apply (leq_trans (to_nat_bounded b0)).
      1-15: by rewrite (elimT eqP IHe2'') IHe2.
    - (* Bdshr *)
      destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-240: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      (*1-240: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].*)
      1-240: rewrite ?size_zext ?size_sext ?size_drop ?eq_refl ?andbT //.
      1-15: rewrite subnKC // (elimT eqP IHe1'') IHe1 ; by apply leq_subr.
    - (* Band, Bor, Bxor *)
      1-3: destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-624: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      1-624: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].
      1-624: rewrite ?eq_refl ?andbT //.
      * 1-13: by rewrite size_andB (elimT eqP IHe1'') IHe1 (elimT eqP IHe2'') IHe2 eq_refl.
      * 1-13: by rewrite size_orB  (elimT eqP IHe1'') IHe1 (elimT eqP IHe2'') IHe2 eq_refl.
      * 1-13: by rewrite size_xorB (elimT eqP IHe1'') IHe1 (elimT eqP IHe2'') IHe2 eq_refl.
    - (* Βcat *)
      destruct val1 as [[wv1|wv1|wv1|wv1| | | |]| | |[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]|[[wv1|wv1|wv1|wv1| | | |]| |]],
                    toe1 as [[wt1|wt1|wt1|wt1| | | |]| |] ; try done ;
           destruct val2 as [[wv2|wv2|wv2|wv2| | | |]| | |[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]|[[wv2|wv2|wv2|wv2| | | |]| |]],
                    toe2 as [[wt2|wt2|wt2|wt2| | | |]| |] ; try done ;
            simpl ; simpl in IHe1 ; simpl in IHe2.
      1-208: first [apply (elimT andP) in IHe1 ; destruct IHe1 as [IHe1'' IHe1] ; apply (elimT eqP) in IHe1 ; rewrite IHe1
                   |apply (elimT eqP) in IHe1 ; injection IHe1 ; clear IHe1 ; intros ; subst wv1].
      1-208: first [apply (elimT andP) in IHe2 ; destruct IHe2 as [IHe2'' IHe2] ; apply (elimT eqP) in IHe2 ; rewrite IHe2
                   |apply (elimT eqP) in IHe2 ; injection IHe2 ; clear IHe2 ; intros ; subst wv2].
      1-208: rewrite ?eq_refl ?andbT //.
      1-13: by rewrite size_cat (elimT eqP IHe1'') IHe1 (elimT eqP IHe2'') IHe2 // addnC.
  + (* Emux *)
    unfold eval_type_of_expr.
    destruct (eval_hfexpr c sem_old sem_new) as [valc|], (type_of_expr' (eval_type_of_ref^~ sem_new) c) as [toc|] ;
        try done ;
        last (by destruct toc as [[wc|wc|wc|wc| | | |]| |] ; try done ;
                 destruct (type_of_expr' (eval_type_of_ref^~ sem_new) e1) as [t1|] ; try done ;
                 destruct (type_of_expr' (eval_type_of_ref^~ sem_new) e2) as [t2|] ; try done ;
                 apply ftype_mux_preserves_concrete ;
                         destruct (eval_hfexpr e1 sem_old sem_new) ;
                         try apply (elimT andP) in IHe1 ;
                         by apply IHe1).
    apply (elimT andP) in IHc ; destruct IHc as [IHc IHc'].
    destruct valc as [[wvc|wvc|wvc|wvc| | | |] bc| | |[[wvc|wvc|wvc|wvc| | | |]| |]|[[wvc|wvc|wvc|wvc| | | |]| |]|[[wvc|wvc|wvc|wvc| | | |]| |]],
             toc as [[wtc|wtc|wtc|wtc| | | |]| |] ; simpl ; simpl in IHc ;
          try (apply (elimT andP) in IHc ; destruct IHc as [IHc'' IHc]) ;
          try done.
    - (* valc is a Gval *)
      1-3: destruct (eval_hfexpr e1 sem_old sem_new) as [val1|], (type_of_expr' (eval_type_of_ref^~ sem_new) e1) as [toe1|] ;
           try (apply (elimT andP) in IHe1) ; try done ;
           destruct (eval_hfexpr e2 sem_old sem_new) as [val2|], (type_of_expr' (eval_type_of_ref^~ sem_new) e2) as [toe2|] ;
           try (apply (elimT andP) in IHe2) ; try done ;
           unfold option_map.
      1-27: destruct (is_zero bc) ;
              try done ;
              try (by apply ftype_mux_preserves_concrete ; try apply IHe1 ; apply IHe2).
      * 1,4,5,8,9,12: generalize (extend_hvalue_as_type_and_ftype_mux (proj1 IHe2)
                                        (make_ftype_explicit_is_explicit_and_concrete toe2)
                                        (make_ftype_explicit_is_explicit_and_concrete toe1)) ;
                      intro ;
                      rewrite (ftype_mux_and_make_ftype_explicit true (proj2 IHe2)) in H0 ;
                                        try by apply IHe1.
        1-6: generalize (ftype_mux_preserves_concrete true toe1 (proj2 IHe2)) ; intro.
        1-6: rewrite (ftype_mux_commutative _ toe1) ;
             destruct (extend_hvalue_as_type val2 (make_ftype_explicit toe1)) as [evtval|] ;
                last by apply H1.
        1-6: destruct (ftype_mux true toe2 toe1) as [toe12|] ; simpl in H0 ;
                last by apply H0.
        1-6: rewrite H0 andTb ; by apply H1.
      * 1-6: generalize (extend_hvalue_as_type_and_ftype_mux (proj1 IHe1)
                                        (make_ftype_explicit_is_explicit_and_concrete toe1)
                                        (make_ftype_explicit_is_explicit_and_concrete toe2)) ;
                      intro ;
                      rewrite (ftype_mux_and_make_ftype_explicit true (proj2 IHe1)) in H0 ;
                                        try by apply IHe2.
        1-6: generalize (ftype_mux_preserves_concrete true toe2 (proj2 IHe1)) ; intro.
        1-6: destruct (extend_hvalue_as_type val1 (make_ftype_explicit toe2)) as [evtval|] ;
                last by apply H1.
        1-6: destruct (ftype_mux true toe1 toe2) as [toe12|] ; simpl in H0 ;
                last by apply H0.
        1-6: rewrite H0 andTb ; by apply H1.
    - (* valc is Undefinedonpurpose etc. *)
      1-9: destruct (eval_hfexpr e1 sem_old sem_new) as [val1|], (type_of_expr' (eval_type_of_ref^~ sem_new) e1) as [toe1|] ;
           try (apply (elimT andP) in IHe1 ; destruct IHe1 as [_ IHe1]) ; try done ;
           destruct (eval_hfexpr e2 sem_old sem_new) as [val2|], (type_of_expr' (eval_type_of_ref^~ sem_new) e2) as [toe2|] ;
           try (apply (elimT andP) in IHe2 ; destruct IHe2 as [_ IHe2]) ; try done ;
           unfold option_map.
      1-36: rewrite (ftype_mux_and_make_ftype_explicit true IHe1 IHe2).
      1-36: generalize (ftype_mux_preserves_concrete true toe2 IHe1) ; intro.
      1-36: destruct (ftype_mux true toe1 toe2) as [toe12|] ; last done ; simpl.
      1-36: rewrite eq_refl H0 ?andbT.
      1-36: by apply make_ftype_explicit_is_explicit_and_concrete.
  + (* Evalidif: body type controls all concrete and unknown guard paths. *)
    change (scalar_raw_typed
      (scalar_validif_value (eval_hfexpr c sem_old sem_new) (eval_hfexpr e sem_old sem_new)
        (type_of_expr' (eval_type_of_ref^~ sem_new) e))
      (type_of_expr' (eval_type_of_ref^~ sem_new) e)).
    apply scalar_validif_preserves_type. exact IHe.
  + (* Eref (Eid id), with no aggregate/memory reference. *)
    change (scalar_raw_typed (VM.find id sem_new) (option_map type_of_val (VM.find id sem_new))).
    exact (scalar_identifier_type_correct sem_new id environment).
Qed.

Lemma scalar_eval_uint_size sem_old sem_new e actual_width expected_width bits
 (environment : env_typed sem_new) (pure : scalar_exprb e)
 (evaluates : eval_hfexpr e sem_old sem_new = Some (Gval (Fuint actual_width) bits))
 (has_type : eval_type_of_expr e sem_new = Some (Gtyp (Fuint expected_width))) :
 size bits = expected_width.
Proof.
 pose proof (scalar_eval_type_correct sem_old sem_new e environment pure) as typed.
 rewrite evaluates has_type in typed.
 exact (uint_value_typed_size actual_width expected_width bits typed).
Qed.
Print Assumptions scalar_eval_type_correct.
Print Assumptions scalar_eval_uint_size.

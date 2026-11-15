From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import ScalarEvaluation.
Fixpoint scalar_refs (e : @hfexpr VarOrder.T) : list VarOrder.T :=
 match e with
 | Econst _ _ => nil
 | Eref (Eid id) => cons id nil
 | Eref _ => nil
 | Ecast _ b | Eprim_unop _ b => scalar_refs b
 | Eprim_binop _ a b | Evalidif a b => List.app (scalar_refs a) (scalar_refs b)
 | Emux c a b => List.app (scalar_refs c) (List.app (scalar_refs a) (scalar_refs b))
 end.
Definition scalar_agree e (env1 env2 : VM.t hvalue) :=
 forall id, List.In id (scalar_refs e) -> VM.find id env1 = VM.find id env2.
Lemma scalar_type_raw_extensional e env1 env2 (pure : scalar_exprb e)
 (agree : scalar_agree e env1 env2) :
 type_of_expr' (eval_type_of_ref^~ env1) e = type_of_expr' (eval_type_of_ref^~ env2) e.
Proof.
 revert pure agree. induction e as [t bs|cast b IH|op b IH|op a IHa b IHb|
 c IHc a IHa b IHb|c IHc b IHb|r]; intros pure agree.
 - reflexivity.
 - destruct cast; cbn [type_of_expr']; rewrite (IH pure agree); reflexivity.
 - cbn [type_of_expr']; rewrite (IH pure agree); reflexivity.
 - move/andP: pure => [pa pb].
   have aa : scalar_agree a env1 env2 by intros id hi; apply agree; apply List.in_or_app; left.
   have ab : scalar_agree b env1 env2 by intros id hi; apply agree; apply List.in_or_app; right.
   cbn [type_of_expr']; rewrite (IHa pa aa) (IHb pb ab); reflexivity.
 - move/andP: pure => [/andP [pc pa] pb].
   have ac : scalar_agree c env1 env2 by intros id hi; apply agree; apply List.in_or_app; left.
   have aa : scalar_agree a env1 env2 by intros id hi; apply agree; apply List.in_or_app; right; apply List.in_or_app; left.
   have ab : scalar_agree b env1 env2 by intros id hi; apply agree; apply List.in_or_app; right; apply List.in_or_app; right.
   cbn [type_of_expr']; rewrite (IHc pc ac) (IHa pa aa) (IHb pb ab); reflexivity.
 - move/andP: pure => [pc pb].
   have ab : scalar_agree b env1 env2 by intros id hi; apply agree; apply List.in_or_app; right.
   cbn [type_of_expr']; exact (IHb pb ab).
 - destruct r as [id| | |]; try discriminate pure.
   cbn [type_of_expr' eval_type_of_ref]. rewrite (agree id (or_introl (Logic.eq_refl id))). reflexivity.
Qed.
Lemma scalar_type_extensional e env1 env2 (pure : scalar_exprb e)
 (agree : scalar_agree e env1 env2) :
 eval_type_of_expr e env1 = eval_type_of_expr e env2.
Proof. unfold eval_type_of_expr. rewrite (scalar_type_raw_extensional e env1 env2 pure agree). reflexivity. Qed.

Lemma scalar_eval_extensional e old1 old2 env1 env2 (pure : scalar_exprb e)
 (agree : scalar_agree e env1 env2) :
 eval_hfexpr e old1 env1 = eval_hfexpr e old2 env2.
Proof.
 revert pure agree. induction e as [t bs|cast b IH|op b IH|op a IHa b IHb|
 c IHc a IHa b IHb|c IHc b IHb|r]; intros pure agree.
 - reflexivity.
 - destruct cast; cbn [eval_hfexpr]; rewrite (IH pure agree); reflexivity.
 - cbn [eval_hfexpr]; rewrite (IH pure agree); reflexivity.
 - move/andP: pure => [pa pb].
   have aa : scalar_agree a env1 env2 by intros id hi; apply agree; apply List.in_or_app; left.
   have ab : scalar_agree b env1 env2 by intros id hi; apply agree; apply List.in_or_app; right.
   cbn [eval_hfexpr]; rewrite (IHa pa aa) (IHb pb ab); reflexivity.
 - move/andP: pure => [/andP [pc pa] pb].
   have ac : scalar_agree c env1 env2 by intros id hi; apply agree; apply List.in_or_app; left.
   have aa : scalar_agree a env1 env2 by intros id hi; apply agree; apply List.in_or_app; right; apply List.in_or_app; left.
   have ab : scalar_agree b env1 env2 by intros id hi; apply agree; apply List.in_or_app; right; apply List.in_or_app; right.
   cbn [eval_hfexpr]; rewrite (IHc pc ac) (IHa pa aa) (IHb pb ab).
   rewrite (scalar_type_extensional a env1 env2 pa aa) (scalar_type_extensional b env1 env2 pb ab). reflexivity.
 - move/andP: pure => [pc pb].
   have ab : scalar_agree b env1 env2 by intros id hi; apply agree; apply List.in_or_app; right.
   have ac : scalar_agree c env1 env2 by intros id hi; apply agree; apply List.in_or_app; left.
   cbn [eval_hfexpr]; rewrite (IHc pc ac) (IHb pb ab).
   rewrite (scalar_type_extensional b env1 env2 pb ab). reflexivity.
 - destruct r as [id| | |]; try discriminate pure.
   cbn [eval_hfexpr eval_href]. rewrite (agree id (or_introl (Logic.eq_refl id))). reflexivity.
Qed.
Print Assumptions scalar_eval_extensional.

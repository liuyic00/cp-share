From Coq Require Import ZArith Lia List.
Import ListNotations.
Open Scope Z_scope.
Module RestoringDivision.
Definition digit c d := if Z.leb d c then 1 else 0.
Definition restore c d := if Z.leb d c then c-d else c.
Lemma restore_correct c d (hc : 0 <= c) (hd : 0 < d) (bound : c < 2*d) :
  c = digit c d * d + restore c d /\
  0 <= restore c d < d /\ 0 <= digit c d <= 1.
Proof.
  unfold digit, restore; destruct (Z.leb d c) eqn:h;
    [apply Z.leb_le in h | apply Z.leb_gt in h]; repeat split; nia.
Qed.
Record Accumulator := mkAccumulator { quotient : Z; remainder : Z }.
Definition step s d b := mkAccumulator
  (2 * quotient s + digit (2 * remainder s + b) d)
  (restore (2 * remainder s + b) d).
Lemma step_correct s consumed d b (hd : 0 < d) (hb : 0 <= b <= 1)
  (identity : consumed = quotient s * d + remainder s)
  (bound : 0 <= remainder s < d) :
  2 * consumed + b = quotient (step s d b) * d + remainder (step s d b) /\
  0 <= remainder (step s d b) < d.
Proof.
  pose proof (restore_correct (2*remainder s+b) d ltac:(lia) hd ltac:(lia)) as [hi [hr hq]].
  cbn [step quotient remainder]; split; nia.
Qed.
Fixpoint value bits consumed := match bits with
  | [] => consumed | b::bs => value bs (2*consumed+b) end.
Fixpoint run bits s d := match bits with
  | [] => s | b::bs => run bs (step s d b) d end.
Lemma run_correct bits s consumed d (hd : 0 < d)
  (binary : Forall (fun b => 0 <= b <= 1) bits)
  (identity : consumed = quotient s*d + remainder s)
  (bound : 0 <= remainder s < d) :
  value bits consumed = quotient (run bits s d)*d + remainder (run bits s d) /\
  0 <= remainder (run bits s d) < d.
Proof.
  revert s consumed identity bound; induction binary; intros.
  - exact (conj identity bound).
  - cbn [value run]. destruct (step_correct s consumed d x hd H identity bound).
    apply IHbinary; assumption.
Qed.
Lemma quotient_remainder s consumed d (hd : 0 < d)
  (identity : consumed = quotient s*d + remainder s)
  (bound : 0 <= remainder s < d) :
  quotient s = consumed / d /\ remainder s = consumed mod d.
Proof.
  split.
  - apply Z.div_unique with (r := remainder s); [left; exact bound | nia].
  - apply Z.mod_unique with (q := quotient s); [left; exact bound | nia].
Qed.
Theorem divides bits d (hd : 0 < d)
  (binary : Forall (fun b => 0 <= b <= 1) bits) :
  quotient (run bits (mkAccumulator 0 0) d) = value bits 0 / d /\
  remainder (run bits (mkAccumulator 0 0) d) = value bits 0 mod d.
Proof.
  destruct (run_correct bits (mkAccumulator 0 0) 0 d hd binary ltac:(reflexivity) ltac:(cbn; lia)).
  apply quotient_remainder; assumption.
Qed.
End RestoringDivision.
Print Assumptions RestoringDivision.divides.

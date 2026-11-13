From Coq Require Import ZArith Lia.
From Proofs Require Import MulDivMulLow MulDivMulWord MulDivMulHigh MulDivMulSignedHigh.
From Generated Require Import MulDiv.
Import MulDiv.CIRCTBits MulDiv.nMulDiv MulDivControl.MulDivControl.
Open Scope Z_scope.
Module MulDivCheckedMulSpec.
Module L := MulDivMulLow.MulDivMulLow.
Module W := MulDivMulWord.MulDivMulWord.
Module U := MulDivMulHigh.MulDivMulHigh.
Module S := MulDivMulSignedHigh.MulDivMulSignedHigh.
Definition specification i := if word 4 (nio_5Freq_5Fbits_5Ffn i)=?0 then
  (if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then L.specification i else W.specification i)
  else if word 4 (nio_5Freq_5Fbits_5Ffn i)=?3 then U.specification i else S.specification i.
Definition total i : nat := if word 1 (nio_5Freq_5Fbits_5Fdw i)=?1 then 65%nat else 33%nat.
Definition Legal i := word 4 (nio_5Freq_5Fbits_5Ffn i)<4 /\
  (word 4 (nio_5Freq_5Fbits_5Ffn i)=0 \/ word 1 (nio_5Freq_5Fbits_5Fdw i)=1).
Local Opaque run observe.
Theorem accepted_result s pins (idle : word 3 (r0_nstate s)=0)
  (valid : word 1 (nio_5Freq_5Fvalid (pins O))=1) (legal : Legal (pins O))
  (live : MulDivTiming.MulDivTiming.active pins (total (pins O))) :
  nio_5Fresp_5Fbits_5Fdata (observe (run s pins (total (pins O))) (pins (total (pins O))))=specification (pins O).
Proof.
  destruct legal as [range width].
  pose proof (Words.word_bound 4 (nio_5Freq_5Fbits_5Ffn (pins O)) ltac:(lia)) as bound.
  change (0<=word 4 (nio_5Freq_5Fbits_5Ffn (pins O))<2^4) in bound.
  assert (cases : word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=0 \/ word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=1 \/
    word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=2 \/ word 4 (nio_5Freq_5Fbits_5Ffn (pins O))=3) by lia.
  destruct cases as [fn|[fn|[fn|fn]]].
  - unfold total in *; unfold specification; rewrite fn; cbn [Z.eqb].
    destruct (bit_cases (nio_5Freq_5Fbits_5Fdw (pins O))) as [dw|dw]; rewrite dw in *; cbn [Z.eqb Pos.eqb] in *.
    + exact (proj1 (proj2 (W.accepted_result s pins idle valid fn dw live))).
    + exact (proj1 (proj2 (L.accepted_result s pins idle valid fn dw live))).
  - assert (dw : word 1 (nio_5Freq_5Fbits_5Fdw (pins O))=1) by lia.
    unfold total in *; rewrite dw in *; unfold specification; rewrite fn; cbn [Z.eqb Pos.eqb] in *.
    exact (proj1 (proj2 (S.accepted_result s pins idle valid (or_introl fn) dw live))).
  - assert (dw : word 1 (nio_5Freq_5Fbits_5Fdw (pins O))=1) by lia.
    unfold total in *; rewrite dw in *; unfold specification; rewrite fn; cbn [Z.eqb Pos.eqb] in *.
    exact (proj1 (proj2 (S.accepted_result s pins idle valid (or_intror fn) dw live))).
  - assert (dw : word 1 (nio_5Freq_5Fbits_5Fdw (pins O))=1) by lia.
    unfold total in *; rewrite dw in *; unfold specification; rewrite fn; cbn [Z.eqb Pos.eqb] in *.
    exact (proj1 (proj2 (U.accepted_result s pins idle valid fn dw live))).
Qed.
Lemma specification_congruent i j
  (fn : word 4 (nio_5Freq_5Fbits_5Ffn i)=word 4 (nio_5Freq_5Fbits_5Ffn j))
  (dw : word 1 (nio_5Freq_5Fbits_5Fdw i)=word 1 (nio_5Freq_5Fbits_5Fdw j))
  (a : word 64 (nio_5Freq_5Fbits_5Fin1 i)=word 64 (nio_5Freq_5Fbits_5Fin1 j))
  (b : word 64 (nio_5Freq_5Fbits_5Fin2 i)=word 64 (nio_5Freq_5Fbits_5Fin2 j)) : specification i=specification j.
Proof.
  assert (bridge : Words.word=word) by reflexivity.
  assert (lowA : word 32 (nio_5Freq_5Fbits_5Fin1 i)=word 32 (nio_5Freq_5Fbits_5Fin1 j)).
  { rewrite <-(MulDivRefinement.MulDivRefinement.narrow 64 32 (nio_5Freq_5Fbits_5Fin1 i) ltac:(lia) ltac:(lia)),
      <-(MulDivRefinement.MulDivRefinement.narrow 64 32 (nio_5Freq_5Fbits_5Fin1 j) ltac:(lia) ltac:(lia)),a; reflexivity. }
  assert (lowB : word 32 (nio_5Freq_5Fbits_5Fin2 i)=word 32 (nio_5Freq_5Fbits_5Fin2 j)).
  { rewrite <-(MulDivRefinement.MulDivRefinement.narrow 64 32 (nio_5Freq_5Fbits_5Fin2 i) ltac:(lia) ltac:(lia)),
      <-(MulDivRefinement.MulDivRefinement.narrow 64 32 (nio_5Freq_5Fbits_5Fin2 j) ltac:(lia) ltac:(lia)),b; reflexivity. }
  unfold specification,L.specification,W.specification,U.specification,S.specification,
    MulDivMulSignedCapture.MulDivMulSignedCapture.multiplicand,SignedWords.signed.
  rewrite bridge,fn,dw,a,b,lowA,lowB; reflexivity.
Qed.
End MulDivCheckedMulSpec.
Print Assumptions MulDivCheckedMulSpec.accepted_result.

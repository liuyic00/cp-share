#!/usr/bin/env python3
from pathlib import Path
import re
H=Path(__file__).resolve().parent;raw=(H.parents[1]/'rocq/Generated/Radix2Divider.v').read_text()
s=['''From Coq Require Import ZArith Lia.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Representation LeafWords.
Local Open Scope Z_scope.
''']
for k,w in re.findall(r'Definition v(\d+) .*? := \(word (\d+)',raw):
 s += [f'Lemma reference_{k}_normalized s i : normalize {w} (Reference.v{k} s i) = Reference.v{k} s i.',f'Proof. unfold Reference.v{k}, Radix2Divider.CIRCTBits.word, normalize, modulus.', ' rewrite Z.mod_mod; [reflexivity|apply Z.pow_nonzero; lia]. Qed.']
 s += [f'Lemma reference_{k}_widen outer s i (larger : ({w} <= outer)%nat) : normalize outer (Reference.v{k} s i) = Reference.v{k} s i.',f'Proof. rewrite <- (reference_{k}_normalized s i). apply normalize_widen. exact larger. Qed.']
s+=['Print Assumptions reference_226_normalized.'];(H/'ReferenceNormalization.v').write_text('\n'.join(s)+'\n')

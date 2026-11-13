#!/usr/bin/env python3
"""Stage tracked legacy proof sources for fresh checking with the native toolchain.

Import namespaces change; two proof scripts avoid costly rewrite searches.
No theorem statement or definition changes. All proofs are checked afresh.
These are reference proofs, not native-model proofs: a checked refinement is
required before their properties can be used for a native circuit.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'verification' / 'rocq'
DEST = ROOT / 'verification' / 'rocq-bits' / 'Reference'
seen = set()

def stage(kind, name):
    key = kind, name
    if key in seen:
        return
    seen.add(key)
    text = (SOURCE / kind / f'{name}.v').read_text()
    for dep_kind, names in re.findall(r'From (Generated|Proofs) Require Import ([^.]+)\.', text):
        for dep in names.split():
            stage(dep_kind, dep)
    for old, new in [('Coq', 'Stdlib'), ('Generated', 'ReferenceGenerated'), ('Proofs', 'ReferenceProofs')]:
        text = text.replace(f'From {old} Require Import ', f'From {new} Require Import ')
    if name == 'ArrayRowSum':
        # Avoid unfolding the circuit while matching a proven window equation.
        # Restore transparency immediately after that lemma. The same window
        # equations are composed by congruence instead of a costly rewrite-at
        # search. The tracked reference sources remain untouched.
        windows = re.findall(r'Lemma window_value_\d+[^\n]*?\bv(\d+)', text)
        assert len(windows) == 33
        constants = 'BoothWindows.digit ' + ' '.join('v' + n for n in windows)
        start = text.index('Lemma window_sum_math ')
        end = text.index('Qed.', start) + len('Qed.')
        proof_start = text.index('Proof.', start)
        proof = '''Proof.
  unfold windowSum, BoothOperand.recoded65.
  let rec split_add unused :=
    lazymatch goal with
    | |- Z.add _ _ = Z.add _ _ => apply f_equal2; [split_add tt | split_add tt]
    | _ => idtac end in split_add tt.
  all: apply f_equal; apply f_equal.
  all: first [''' + ' | '.join(f'exact (window_value_{k} s i)' for k in range(33)) + '''].
Qed.'''
        text = (text[:start] + f'Local Opaque {constants}.\n' + text[start:proof_start] + proof
                + f'\nLocal Transparent {constants}.' + text[end:])
    if name == 'MulDivCheckedData':
        # Keep the normalized wire abstract during occurrence-specific rewrites.
        # The existing normalization hypothesis still proves its range property.
        needle = ('  rewrite <-normal at 1 2.\n'
                  '  apply MulDivCheckedSignedOperands.MulDivCheckedSignedOperands.extend_wire.')
        assert text.count(needle) == 1
        text = text.replace(needle, '''  set (x := v258 s i) in *; clearbody x.
  pose proof (MulDivCheckedSignedOperands.MulDivCheckedSignedOperands.extend_wire x) as result.
  rewrite normal in result; exact result.''')
    path = DEST / kind / f'{name}.v'
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text() != text:
        path.write_text(text)

for root in [
    'ArrayInvariant', 'RadixOutput', 'RadixTrace', 'RadixControl',
    'MulDivUnsigned', 'MulDivSigned', 'MulDivMulLow', 'MulDivMulHigh',
    'MulDivMulSignedHigh', 'MulDivMulWord', 'MulDivTiming', 'MulDivStall',
    'MulDivCheckedProjection', 'MulDivCheckedMonitorResult', 'MulDivCheckedAssertions',
]:
    stage('Proofs', root)
print(f'Staged {len(seen)} reference modules for fresh Rocq checking')

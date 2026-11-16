#!/usr/bin/env python3
"""Split unchanged firrtl2coq models from lemmas discharged by external proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
CIRCUITS = {
    'Radix2Divider': ('Divider', 'divider'),
    'ArrayMulDataModule8': ('SmallMultiplier', 'multiplier'),
}

def split_output(text, namespace, proof_prefix):
    """Keep the model prefix and lemma statements verbatim; replace only Admitted."""
    parts = re.split(r'(?=^Lemma generated_assert_\d+ :)', text, flags=re.M)
    if len(parts) < 2 or '(* Generated verification properties. *)' not in parts[0]:
        raise ValueError('Missing generated model/properties or assertion lemmas')
    model = parts[0]
    if re.search(r'\b(Admitted|admit|Axiom|Parameter)\b', model):
        raise ValueError('Unexpected axiom in model')
    # Repeat only the prelude: imports and notation scopes are local to a file.
    prelude = ''.join(line for line in model.splitlines(keepends=True)
                      if line.startswith(('From ', 'Local Open Scope ')))
    lemmas = prelude + f'From {namespace} Require Import Model.\nFrom {namespace} Require Proof.\n\n'
    for index, item in enumerate(parts[1:]):
        match = re.fullmatch(r'(Lemma generated_assert_(\d+) : .*?\.\n)Admitted\.(\s*)', item, re.S)
        if not match or int(match[2]) != index:
            raise ValueError('Unexpected generated obligation format')
        lemmas += match[1] + f'Proof. exact {namespace}.Proof.{proof_prefix}_obligation_{index}. Qed.' + match[3]
    return model, lemmas, len(parts) - 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--firrtl-root', type=Path, default=ROOT / 'artifacts/chisel3/firrtl')
    parser.add_argument('--tool', type=Path, default=ROOT.parent / 'tool/firrtl2coq')
    parser.add_argument('--check', action='store_true',
                        help='Run firrtl2coq again and compare every generated file without writing it')
    args = parser.parse_args()
    tool = args.tool.resolve()
    output = ROOT / 'verification/firrtl2coq/Generated'
    produced = {}
    with tempfile.TemporaryDirectory(prefix='firrtl2coq-models-') as temporary:
        for name in CIRCUITS:
            source = (args.firrtl_root / (name + '.lo.fir')).resolve(strict=True)
            raw = Path(temporary) / (name + '.v')
            subprocess.run([str(tool / 'src/ocaml/_build/default/bin/main.exe'),
                            str(source), str(raw)], check=True)
            text = raw.read_text()
            namespace, proof_prefix = CIRCUITS[name]
            model, lemmas, count = split_output(text, namespace, proof_prefix)
            record = {name: {
                'firrtl_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'model_sha256': hashlib.sha256(model.encode()).hexdigest(),
                'lemmas_sha256': hashlib.sha256(lemmas.encode()).hexdigest(),
                'raw_sha256': hashlib.sha256(text.encode()).hexdigest(),
                'obligations': count, 'proved': False,
            }}
            produced[output / name / 'Model.v'] = model
            produced[output / name / (name + '.v')] = lemmas
            produced[output / name / 'manifest.json'] = json.dumps(record, indent=2) + '\n'
    for target, text in produced.items():
        if args.check:
            if not target.is_file() or target.read_bytes() != text.encode():
                raise SystemExit('Fresh firrtl2coq export differs: ' + str(target))
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.is_file() or target.read_bytes() != text.encode():
                target.write_text(text)
    print('Fresh firrtl2coq models, lemma statements/proof calls and manifests match exactly.' if args.check else
          'Generated unchanged models and lemmas with external proof calls; compile lemmas to check proofs.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Export the two assertion-proof models without importing admitted obligations."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--firrtl-root', type=Path, default=ROOT / 'artifacts/chisel3/firrtl')
    p.add_argument('--tool', type=Path, default=ROOT.parent / 'tool/firrtl2coq')
    a = p.parse_args()
    tool = a.tool.resolve()
    out = ROOT / 'verification/firrtl2coq/Generated'
    out.mkdir(parents=True, exist_ok=True)
    records = {}
    for name in ['Radix2Divider', 'ArrayMulDataModule8']:
        source = (a.firrtl_root / (name + '.lo.fir')).resolve(strict=True)
        target = out / (name + '.v')
        subprocess.run([str(tool / 'src/ocaml/_build/default/bin/main.exe'), str(source), str(target)], check=True)
        text = target.read_text()
        parts = re.split(r'(?=^Lemma generated_assert_\d+ :)', text, flags=re.M)
        if len(parts) < 2:
            raise SystemExit('No generated assertion obligations: ' + name)
        goals = []
        for i, item in enumerate(parts[1:]):
            match = re.fullmatch(r'Lemma generated_assert_(\d+) : (.*?)\.\nAdmitted\.\s*', item, re.S)
            if not match or int(match[1]) != i:
                raise SystemExit('Unexpected generated obligation format: ' + name)
            goals.append(f'Definition obligation_{i} : Prop := {match[2]}.\n')
        # Preserve the exact generated propositions as definitions. They cannot
        # be used as axioms: proof files must inhabit these types themselves.
        target.write_text(parts[0] + '\n(* Unproved proposition types, not axioms. *)\n' + ''.join(goals))
        if re.search(r'\b(Admitted|Axiom|Parameter)\b', target.read_text()):
            raise SystemExit('Unexpected axiom in model: ' + name)
        records[name] = {'firrtl_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                         'model_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                         'obligations': len(goals), 'proved': False}
    (out / 'manifest.json').write_text(json.dumps(records, indent=2) + '\n')
    print('Generated model definitions and unproved obligation types; no hardware proof claimed.')

if __name__ == '__main__':
    main()

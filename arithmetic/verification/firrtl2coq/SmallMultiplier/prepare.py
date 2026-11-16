#!/usr/bin/env python3
"""Extract the unchanged model and property definitions for the compressor proofs."""
import argparse
import re
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--firrtl', type=Path, required=True)
p.add_argument('--tool', type=Path,
               default=REPO / 'tool/firrtl2coq/src/ocaml/_build/default/bin/main.exe')
a = p.parse_args()
with tempfile.TemporaryDirectory() as temp:
    output = Path(temp) / 'model.v'
    subprocess.run([str(a.tool.resolve()), str(a.firrtl.resolve()), str(output)], check=True)
    text = output.read_text()
    marker = '(* Generated verification properties. *)'
    if marker not in text:
        raise SystemExit('Unexpected generator output: verification boundary missing')
    # Preserve the full prefix verbatim; final lemmas are emitted by the central generator.
    model = re.split(r'(?=^Lemma generated_assert_\d+ :)', text, flags=re.M)[0]
    if 'Definition generated_top := 3.' not in model:
        raise SystemExit('Unexpected top module; review this helper before regenerating')
    target = HERE.parent / 'Generated/ArrayMulDataModule8/Model.v'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(model)

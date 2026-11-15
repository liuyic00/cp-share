#!/usr/bin/env python3
"""Extract unchanged module AST declarations for the compressor proof helpers."""
import argparse
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
    # This preserves every generated AST definition and removes only the
    # unrelated automatically admitted verification obligations.
    model = text.split(marker, 1)[0]
    if 'Definition generated_top := 3.' not in model:
        raise SystemExit('Unexpected top module; review this helper before regenerating')
    (HERE / 'Model.v').write_text(model)

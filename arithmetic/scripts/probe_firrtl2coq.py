#!/usr/bin/env python3
"""Reproduce current upstream blockers; this does not prove hardware assertions."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parent
TOOL = REPO / 'tool/firrtl2coq'
WORK = ROOT / 'build/firrtl2coq-legacy-probe'
REV = '58759b554890e0fc877c0a07c5093fec6d69b104'


def run(cmd, log, cwd=REPO):
    with (WORK / log).open('w') as stream:
        return subprocess.run(cmd, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT).returncode


def main():
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=TOOL, text=True).strip() != REV:
        raise SystemExit('This diagnostic is pinned to firrtl2coq ' + REV)
    if subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=TOOL):
        raise SystemExit('Diagnostic requires unmodified upstream sources.')
    WORK.mkdir(parents=True, exist_ok=True)
    opam = ['opam', 'exec', '--switch=firrtl2coq', '--']
    for cmd in [['coq_makefile', '-f', '_CoqProject', '-o', 'Makefile'], ['make', '-j4']]:
        if run(opam + cmd, 'library-' + cmd[0] + '.log', TOOL):
            raise SystemExit('Upstream Coq library failed; see ' + str(WORK))
    original = run(opam + ['dune', 'build'], 'original-build.log', TOOL / 'src/ocaml')
    # Explicit diagnostic overlay: synchronize only the two updated upstream
    # files that were not copied into dune's lib/ directory. No semantic patch.
    dest = WORK / 'ocaml'
    shutil.copytree(TOOL / 'src/ocaml', dest,
                    ignore=shutil.ignore_patterns('_build'), dirs_exist_ok=True)
    for name in ['transhiast_without_inline.ml', 'coqgen.ml']:
        shutil.copy2(dest / name, dest / 'lib' / name)
    if run(opam + ['dune', 'build'], 'overlay-build.log', dest):
        raise SystemExit('Diagnostic overlay failed to build.')
    coq = opam + ['coqc', '-Q', str(TOOL / 'lib/simplssrlib'), 'simplssrlib',
                 '-Q', str(TOOL / 'lib/nbits'), 'nbits', '-R', str(TOOL / 'src'), 'firrtl']
    results = {'upstream_revision': REV, 'original_build_exit': original,
               'overlay': ['lib/' + n for n in ['transhiast_without_inline.ml', 'coqgen.ml']],
               'hardware_assertions_proved': False, 'circuits': {}}
    for name in ['ArrayMulDataModule', 'Radix2Divider']:
        fir = ROOT / 'artifacts/chisel3/firrtl' / (name + '.lo.fir')
        out = WORK / (name + '.v')
        code = run([str(dest / '_build/default/bin/main.exe'), str(fir), str(out)], name + '.convert.log')
        item = {'firrtl_sha256': hashlib.sha256(fir.read_bytes()).hexdigest(), 'convert_exit': code}
        if code == 0:
            item['generated_obligations'] = out.read_text().count('Lemma generated_assert_')
            item['admitted'] = out.read_text().count('Admitted.')
            item['coq_exit'] = run(coq + [str(out)], name + '.coq.log')
        results['circuits'][name] = item
    diag = ROOT / 'verification/firrtl2coq/Diagnostics/RegisterIteration.v'
    # Compile in build/, keeping the diagnostics source directory clean.
    shutil.copy2(diag, WORK / diag.name)
    results['register_counterexample_exit'] = run(coq + [str(WORK / diag.name)], 'RegisterIteration.log')
    (WORK / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))
    if results['register_counterexample_exit']:
        raise SystemExit('Register diagnostic failed to compile.')

if __name__ == '__main__':
    main()

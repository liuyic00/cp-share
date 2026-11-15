#!/usr/bin/env python3
"""Reproduce vanilla csj regression results; this does not prove hardware assertions."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parent
TOOL = REPO / 'tool/firrtl2coq'
WORK = ROOT / 'build/firrtl2coq-csj'
REV = 'ced58a8125da4b044ca6c4b75b528040af88cf80'


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
    dest = TOOL / 'src/ocaml'
    if run(opam + ['dune', 'build'], 'vanilla-build.log', dest):
        raise SystemExit('Vanilla csj failed to build.')
    dune_tests = run(opam + ['dune', 'runtest'], 'dune-tests.log', dest)
    coq = opam + ['coqc', '-Q', str(TOOL / 'lib/simplssrlib'), 'simplssrlib',
                 '-Q', str(TOOL / 'lib/nbits'), 'nbits', '-R', str(TOOL / 'src'), 'firrtl']
    results = {'upstream_revision': REV, 'vanilla_build_exit': 0,
               'dune_tests_exit': dune_tests, 'overlay': [],
               'hardware_assertions_proved': False, 'circuits': {}}
    for name in ['ArrayMulDataModule', 'Radix2Divider']:
        for level in ['hi', 'lo']:
            key = name + level.capitalize()
            fir = ROOT / 'artifacts/chisel3/firrtl' / (name + '.' + level + '.fir')
            out = WORK / (key + '.v')
            code = run([str(dest / '_build/default/bin/main.exe'), str(fir), str(out)], key + '.convert.log')
            item = {'firrtl_sha256': hashlib.sha256(fir.read_bytes()).hexdigest(), 'convert_exit': code}
            if code == 0:
                item['generated_obligations'] = out.read_text().count('Lemma generated_assert_')
                item['admitted'] = out.read_text().count('Admitted.')
                item['coq_exit'] = run(coq + [str(out)], key + '.coq.log')
            results['circuits'][key] = item
    diag = ROOT / 'verification/firrtl2coq/Diagnostics/CSJRegisterIteration.v'
    # Compile in build/, keeping the diagnostics source directory clean.
    shutil.copy2(diag, WORK / diag.name)
    results['register_regression_exit'] = run(coq + [str(WORK / diag.name)], 'CSJRegisterIteration.log')
    (WORK / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))
    if results['register_regression_exit']:
        raise SystemExit('Register diagnostic failed to compile.')

if __name__ == '__main__':
    main()

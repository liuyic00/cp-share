#!/usr/bin/env python3
"""Export the unchanged nutshell-fv NutCore using its own Scala dependencies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SPOT = Path(os.environ["CIRCT_SPOT"]).resolve() if os.environ.get("CIRCT_SPOT") else None


def run(args, **kwargs):
    display = list(map(str, args))
    for index in range(1, len(display)):
        if display[index-1] in ('-cp', '-classpath', '--classpath'):
            display[index] = '<classpath>'
    print('+ ' + ' '.join(display), flush=True)
    return subprocess.run(list(map(str, args)), check=True, **kwargs)


def snapshot(source):
    result = {}
    for repo in (source, source / 'riscv-spec-core', source / 'difftest'):
        result[str(repo)] = {
            'commit': subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
            'status': subprocess.check_output(['git', '-C', str(repo), 'status', '--porcelain', '--untracked-files=all'], text=True),
            'diff': subprocess.check_output(['git', '-C', str(repo), 'diff', 'HEAD', '--binary']),
        }
    return result


def partition_and_check(output):
    """Split at declaration boundaries only; check every generated declaration."""
    text = (output / 'NutCore.lean').read_text()
    namespace = 'nNutCore'
    start = text.index(f'namespace {namespace}\n') + len(f'namespace {namespace}\n')
    end = text.rindex(f'end {namespace}')
    nodes = list(re.finditer(r'^@\[noinline\] def v\d+ ', text, re.M))
    bounds = [start] + [nodes[n].start() for n in range(1000, len(nodes), 1000)] + [end]
    chunks = [text[a:b] for a, b in zip(bounds, bounds[1:])]
    assert ''.join(chunks) == text[start:end]
    directory = ROOT / 'verification/lean' / 'Generated' / 'NutCore'
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.glob('Part*.lean'):
        stale.unlink()
    for n, chunk in enumerate(chunks):
        name = f'Part{n:03d}'
        header = text[:start - len(f'namespace {namespace}\n')] if n == 0 else f'import Generated.NutCore.Part{n-1:03d}\n'
        path = directory / f'{name}.lean'
        path.write_text(header + 'set_option linter.unusedVariables false\n' +
                        f'namespace {namespace}\n' + chunk + f'end {namespace}\n')
    facade = directory.parent / 'NutCore.lean'
    facade.write_text(f'import Generated.NutCore.Part{len(chunks)-1:03d}\n')
    run(['lake', 'build', 'Generated.NutCore'], cwd=ROOT / 'verification/lean')
    return len(chunks)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--mill', required=True, help='Mill launcher; MILL_VERSION is set to 0.11.7')
    parser.add_argument('--java', default='java')
    parser.add_argument('--firtool', required=True)
    parser.add_argument('--circt-opt', required=SPOT is None,
                        default=str(SPOT / 'deps/circt/bin/circt-opt') if SPOT else None)
    parser.add_argument('--plugin', required=SPOT is None,
                        default=str(SPOT / 'build/circt-spot/lib/CIRCTSpotPlugin.so') if SPOT else None)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--output', type=Path, default=ROOT / 'build')
    args = parser.parse_args()
    os.environ['ELAN_TOOLCHAIN'] = (ROOT / 'verification/lean' / 'lean-toolchain').read_text().strip()
    for name in ('mill', 'java', 'firtool', 'circt_opt', 'lean'):
        value = getattr(args, name)
        resolved = shutil.which(value)
        if resolved is None:
            raise SystemExit(f'Executable not found: {value}')
        setattr(args, name, str(Path(resolved).absolute()))
    args.plugin = str(Path(args.plugin).resolve())
    source, output = args.source.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / 'report.json').unlink(missing_ok=True)
    before = snapshot(source)
    if any(v['status'] for v in before.values()):
        raise SystemExit('Use a clean source checkout and initialized reference-model submodule.')
    env = dict(os.environ, MILL_VERSION='0.11.7')
    java = shutil.which(args.java) or str(Path(args.java).resolve())
    env['PATH'] = str(Path(java).parent) + os.pathsep + env.get('PATH', '')
    try:
        classpaths = {}
        for target in ('runClasspath', 'scalaCompilerClasspath'):
            result = run([args.mill, '--no-server', 'show', 'chiselModule.' + target],
                         cwd=source, env=env, text=True, stdout=subprocess.PIPE)
            # Mill 0.11 PathRef JSON encoding includes a hash before the path.
            refs = json.loads(result.stdout)
            paths = [ref.split(':', 3)[3] for ref in refs]
            classpaths[target] = os.pathsep.join(paths)
        classes = output / 'driver-classes'
        classes.mkdir(exist_ok=True)
        run([java, '-cp', classpaths['scalaCompilerClasspath'], 'scala.tools.nsc.Main',
             '-classpath', classpaths['runClasspath'], '-d', classes, HERE / 'Export.scala'],
            stdout=(output / 'compile.log').open('w'), stderr=subprocess.STDOUT)
        driver_cp = classpaths['runClasspath'] + os.pathsep + str(classes)
        run([sys.executable, HERE / 'check-adapter.py', '--output', output / 'adapter-test',
             '--java', java, '--classpath', driver_cp, '--firtool', args.firtool,
             '--circt-opt', args.circt_opt, '--plugin', args.plugin, '--lean', args.lean],
            stdout=(output / 'adapter-test.log').open('w'), stderr=subprocess.STDOUT)
        run([java, '-cp', driver_cp,
             'ExportNutShell', output], cwd=source,
            stdout=(output / 'elaborate.log').open('w'), stderr=subprocess.STDOUT)
        fir = (output / 'NutCore.prepared.fir').read_text()
        assert fir.startswith('FIRRTL version 1.2.0\n')
        # The adapter leaves only the typed, ground integer/clock subset shared
        # by FIRRTL 1.2 and 2.0; modern firtool rejects the old version header.
        assert not re.search(r'\b(?:validif\(|is invalid|Fixed|Interval|Analog)', fir)
        (output / 'NutCore.fir2.fir').write_text(fir.replace('FIRRTL version 1.2.0', 'FIRRTL version 2.0.0', 1))
        hw = output / 'NutCore.hw.mlir'
        run([args.firtool, output / 'NutCore.fir2.fir', '--ir-hw', '--disable-opt',
             '--lower-to-core', '--verification-flavor=immediate', '-o', hw])
        # Do not canonicalize: self-fed instruction-memory registers otherwise
        # fold to zero, which destroys arbitrary but stable program contents.
        run([args.circt_opt, hw, '--load-pass-plugin=' + args.plugin,
             '--mlir-print-op-on-diagnostic=false',
             '--pass-pipeline=builtin.module(strip-om,export-lean{output-file=' + str(output / 'NutCore.lean') + '})',
             '-o', output / 'NutCore.final.mlir'])
        raw = (output / 'NutCore.flat.fir').read_text()
        final = (output / 'NutCore.final.mlir').read_text()
        lean = (output / 'NutCore.lean').read_text()
        counts = {}
        for kind in ('assert', 'assume'):
            labels = re.findall(r'^\s*' + kind + r'\(.*?\) : (\w+)', raw, re.M)
            adapted = re.findall(r'^\s*' + kind + r'\(.*?\) : (\w+)', fir, re.M)
            lowered = re.findall(r'verif.clocked_' + kind + r' .*?label "' + kind + r'__(\w+)"', final)
            assert labels == adapted and set(labels) == set(lowered), (kind, labels, lowered)
            assert len(labels) == len(lowered)
            stem = 'assertion' if kind == 'assert' else 'assumption'
            checks = re.findall(r'^def ' + stem + r'Checks\d+ .*$', lean, re.M)
            assert sum(line.count('decide (') for line in checks) == len(labels)
            counts[kind] = len(labels)
        assert counts == {'assert': 48, 'assume': 4}, counts
        checker_assertions = re.findall(r'^\s*assert\(.*?\) : (backend_wbu_checker_\w+)', raw, re.M)
        assert len(checker_assertions) == 45, checker_assertions
        partitions = partition_and_check(output)
        report = {
            'source': {k: v['commit'] for k, v in before.items()},
            'properties': counts,
            'reference_checker_assertions': len(checker_assertions),
            'configuration': {'Formal': True, 'RVFI': True, 'base': 'FormalSettings ++ InOrderSettings'},
            'verification_statements': [line.strip() for line in raw.splitlines()
                                        if re.match(r'\s*(assert|assume)\(', line)],
            'registers': len(re.findall(r'= seq.firreg ', final)),
            'lean_partitions': partitions,
            'adapter_summary': (output / 'elaborate.log').read_text().split('Unused BoringUtils source annotations: ', 1)[1].strip(),
            'circt_opt_version': subprocess.check_output([args.circt_opt, '--version'], text=True).strip(),
            'plugin_sha256': hashlib.sha256(Path(args.plugin).read_bytes()).hexdigest(),
            'lean_version': subprocess.check_output([args.lean, '--version'], text=True).strip(),
            'firtool_version': subprocess.check_output([args.firtool, '--version'], text=True).strip(),
            'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
                       (output / 'NutCore.flat.fir', output / 'NutCore.prepared.fir', hw,
                        output / 'NutCore.final.mlir', output / 'NutCore.lean')},
            'scope': 'Generated definitions typechecked; CPU equivalence is NOT proved.',
        }
        if snapshot(source) != before:
            raise RuntimeError('Source checkout changed during export')
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=2))
    finally:
        if snapshot(source) != before:
            raise RuntimeError('Source checkout changed during export')


if __name__ == '__main__':
    main()

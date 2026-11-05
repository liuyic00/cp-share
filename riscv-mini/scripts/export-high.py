#!/usr/bin/env python3
"""Export hierarchical High FIRRTL using the unchanged upstream dependencies."""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
from export import HERE, ROOT, run, snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--mill', required=True)
    parser.add_argument('--java', default='java')
    parser.add_argument('--compare-low', type=Path, help='Require byte equality with an earlier CoreSoc.lo.fir')
    parser.add_argument('--output', type=Path, default=ROOT / 'build' / 'high-export')
    args = parser.parse_args()
    source, output = args.source.resolve(), args.output.resolve()
    before = snapshot(source)
    if any(v['status'] for v in before.values()):
        raise SystemExit('Use a clean source checkout and reference submodule.')
    java = shutil.which(args.java)
    mill = shutil.which(args.mill)
    if not java or not mill:
        raise SystemExit('Java 17 and a Mill launcher are required.')
    env = dict(os.environ, MILL_VERSION='0.11.12')
    env['PATH'] = str(Path(java).parent) + os.pathsep + env.get('PATH', '')
    build = ROOT / 'build' / 'high'
    build.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)
    try:
        cp = {}
        for target in ('runClasspath', 'scalaCompilerClasspath'):
            result = run([mill, '--no-server', 'show', 'chiselModule.' + target],
                         cwd=source, env=env, text=True, stdout=subprocess.PIPE)
            cp[target] = os.pathsep.join(ref.split(':', 3)[3] for ref in json.loads(result.stdout))
        classes = build / 'classes'
        classes.mkdir(exist_ok=True)
        run([java, '-cp', cp['scalaCompilerClasspath'], 'scala.tools.nsc.Main',
             '-classpath', cp['runClasspath'], '-d', classes, HERE / 'ExportHigh.scala'])
        run([java, '-cp', cp['runClasspath'] + os.pathsep + str(classes),
             'ExportRiscvMiniHigh', build], cwd=source)
        shutil.copyfile(build / 'CoreSoc.hi.fir', output / 'CoreSoc.hi.fir')
        # Preserve compiler metadata alongside the standalone wired circuit.
        annotations = json.loads((build / 'CoreSoc.anno.json').read_text())
        annotations = [a for a in annotations if a['class'] not in (
            'firrtl.stage.FirrtlFileAnnotation', 'firrtl.EmitCircuitAnnotation')]
        (output / 'CoreSoc.anno.json').write_text(json.dumps(annotations, indent=2) + '\n')
        circuit = (output / 'CoreSoc.hi.fir').read_text()
        counts = {kind: len(re.findall(r'^\s*' + kind + r'\(', circuit, re.M))
                  for kind in ('assert', 'assume')}
        if counts != {'assert': 45, 'assume': 1}:
            raise RuntimeError(f'Unexpected property counts: {counts}')
        recheck = build / 'recheck'
        run([java, '-cp', cp['runClasspath'], 'firrtl.stage.FirrtlMain',
             '-i', output / 'CoreSoc.hi.fir', '-faf', output / 'CoreSoc.anno.json',
             '-X', 'low', '--target-dir', recheck])
        low = (recheck / 'CoreSoc.lo.fir').read_bytes()
        if args.compare_low and low != args.compare_low.read_bytes():
            raise RuntimeError('High-to-low output differs from the supplied previous Low FIRRTL')
        report = {
            'source': {Path(k).name: v['commit'] for k, v in before.items()},
            'entry': 'new mini.CoreSoc(new mini.Core(mini.MiniConfig().core))',
            'properties': counts,
            'modules': re.findall(r'^  module (\w+)', circuit, re.M),
            'regenerated_low_sha256': hashlib.sha256(low).hexdigest(),
            'compared_previous_low': args.compare_low is not None,
            'compiler': 'Chisel 3.6.0 / FIRRTL 1.6.0, -X high',
            'sha256': {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                       for f in (output / 'CoreSoc.hi.fir', output / 'CoreSoc.anno.json')},
        }
        (output / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    finally:
        if snapshot(source) != before:
            raise RuntimeError('Upstream source checkout changed during export')


if __name__ == '__main__':
    main()

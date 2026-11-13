#!/usr/bin/env python3
"""Partition hierarchical generated Lean at declaration boundaries.

Namespaces are closed/reopened across imports; definitions are not rewritten.
Only marker-owned partition files may be replaced.
"""
import argparse
import re
from pathlib import Path

MARKER = '-- Generated partitions of export-lean-hierarchical.\n'


def split(source: Path, limit: int = 500) -> None:
    text = source.read_text()
    if MARKER in text:
        return
    stack = []
    boundaries = [(0, ())]
    count = 0
    offset = 0
    declaration_start = None
    has_private = False
    for line in text.splitlines(keepends=True):
        if line.startswith('set_option ') and line.rstrip().endswith(' in'):
            if declaration_start is None:
                declaration_start = offset
        if line.startswith('private '):
            has_private = True
        if re.match(r'^(?:@\[[^]]+\] )?(?:def|theorem|structure) ', line):
            if count >= limit and not has_private:
                boundaries.append((declaration_start if declaration_start is not None else offset, tuple(stack)))
                count = 0
            count += 1
            declaration_start = None
        if match := re.fullmatch(r'namespace (\w+)\n', line):
            stack.append(match[1])
            has_private = False
        elif match := re.fullmatch(r'end (\w+)\n', line):
            if not stack or stack.pop() != match[1]:
                raise ValueError('unbalanced generated namespace')
        offset += len(line)
    if stack:
        raise ValueError('unclosed generated namespace')
    directory = source.with_suffix('')
    old = list(directory.glob('Part*.lean')) if directory.exists() else []
    for file in old:
        if MARKER not in file.read_text():
            raise ValueError(f'refusing to replace unrecognized file: {file}')
    if len(boundaries) == 1:
        for file in old:
            file.unlink()
        return
    boundaries.append((len(text), ()))
    directory.mkdir(exist_ok=True)
    module = '.'.join(source.with_suffix('').parts[-2:])
    chunks = []
    for index, ((start, opened), (end, remaining)) in enumerate(zip(boundaries, boundaries[1:])):
        chunk = text[start:end]
        chunks.append(chunk)
        prefix = '' if index == 0 else f'import {module}.Part{index-1:03d}\n'
        prefix += MARKER
        if index:
            prefix += 'set_option linter.unusedVariables false\nset_option maxRecDepth 16384\n'
        prefix += ''.join(f'namespace {name}\n' for name in opened)
        suffix = ''.join(f'end {name}\n' for name in reversed(remaining))
        (directory / f'Part{index:03d}.lean').write_text(prefix + chunk + suffix)
    assert ''.join(chunks) == text
    for file in old:
        if int(file.stem[4:]) >= len(chunks):
            file.unlink()
    source.write_text(f'import {module}.Part{len(chunks)-1:03d}\n' + MARKER)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('source', type=Path)
    parser.add_argument('--limit', type=int, default=500)
    args = parser.parse_args()
    if args.limit <= 0:
        parser.error('--limit must be positive')
    split(args.source, args.limit)

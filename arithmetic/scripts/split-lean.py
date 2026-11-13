#!/usr/bin/env python3
"""Partition a large generated namespace without changing any definitions.

Lean retains command environments while compiling a file. Keeping thousands of
node definitions per module bounds that chain; later parts import earlier ones.
Small circuits remain single files so their models are easy to inspect.
"""
import re
import sys
from pathlib import Path

source = Path(sys.argv[1])
text = source.read_text()
nodes = list(re.finditer(r"^@\[noinline\] def v\d+ ", text, re.MULTILINE))
marker = "-- Generated partition of circt-spot export-lean output.\n"
parts = source.with_suffix("")
if len(nodes) <= 3000:
    if marker not in text and parts.is_dir():
        for old in parts.glob("Part*.lean"):
            if marker not in old.read_text():
                raise SystemExit(f"refusing to replace unrecognized file: {old}")
        for old in parts.glob("Part*.lean"):
            old.unlink()
        if not any(parts.iterdir()):
            parts.rmdir()
    sys.exit(0)
namespace_matches = re.findall(r"^namespace (\w+)$", text, re.MULTILINE)
if len(namespace_matches) != 1:
    raise SystemExit("expected one generated namespace")
namespace = namespace_matches[0]
start = text.index(f"namespace {namespace}\n") + len(f"namespace {namespace}\n")
end = text.rindex(f"end {namespace}")
if text[end + len(f"end {namespace}"):].strip():
    raise SystemExit("unexpected text after namespace")
header = text[:start - len(f"namespace {namespace}\n")]
bounds = [start] + [nodes[n].start() for n in range(3000, len(nodes), 3000)] + [end]
chunks = [text[a:b] for a, b in zip(bounds, bounds[1:])]
if "".join(chunks) != text[start:end]:
    raise SystemExit("partition changed the generated definitions")
parts.mkdir(exist_ok=True)
# This directory is owned by this generator; refuse to delete unknown files.
for old in parts.glob("Part*.lean"):
    if marker not in old.read_text():
        raise SystemExit(f"refusing to replace unrecognized file: {old}")
for old in parts.glob("Part*.lean"):
    old.unlink()
module = ".".join(source.with_suffix("").parts[-2:])
for n, chunk in enumerate(chunks):
    imports = header if n == 0 else f"import {module}.Part{n - 1:03d}\n"
    content = imports + marker + "set_option linter.unusedVariables false\n"
    content += f"namespace {namespace}\n" + chunk + f"end {namespace}\n"
    (parts / f"Part{n:03d}.lean").write_text(content)
source.write_text(f"import {module}.Part{len(chunks) - 1:03d}\n" + marker)

# Divider interpreter bridge (in progress)

These certificates use the original `firrtl2coq` deep embedding and its bitvector
expression evaluator. They do not replace the FIRRTL execution model with the
older arithmetic model, and do not assume equivalence of the two models.

`build.sh` regenerates the AST in `../Generated/Radix2Divider/Model.v` and local certificate sources, then checks them
with the `firrtl2coq` opam switch. Prerequisites are the built tool Coq libraries,
its extracted OCaml executable, the `ArithmeticCommon` helper libraries, and the
older `verification/rocq/Generated/Radix2Divider.vo`. The source FIRRTL is the
tracked `artifacts/chisel3/firrtl/Radix2Divider.lo.fir`. Width metadata is extracted
by a temporary Coq computation; a previous diagnostic log is not required.

The Python generators are outside the trusted proof boundary: each generated
certificate is checked by Coq. `match_nodes.py` only proposes correspondences;
its JSON output is not an equivalence proof.

Current layers:

- `Stable.v`: source-expression membership and local original-evaluator results
  for all 458 combinational nodes and output drivers.
- `Representation.v`: encoded leaf sizes and projections to the older model.
- `Typing.v`: sizes of all 458 local results and typing of the complete 484-entry
  symbolic environment, using independently proved scalar type preservation.
- `Slices.v`, `Reductions.v`, and `ReferenceNodes.v`: checked mathematical
  correspondences for slice chains, 30 reduction nodes, and the initial state
  comparison.
- `Certificates.v`: all 455 original `Snode` locations, register exclusion, and
  dependency ranks (maximum rank 25).
- `Frames.v`: symbolic lookup values, input frames, register locations, and
  output connection locations.

This is not yet the complete divider assertion proof. Remaining work includes
interpreter convergence, full state-transition/observation correspondence, and
transfer of the older model's reachable-state assertion theorem to the actual
`firrtl2coq` generated obligations. No final assertion theorem should be inferred
from the local certificates alone.

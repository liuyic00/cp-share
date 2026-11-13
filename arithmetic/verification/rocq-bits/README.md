# Native Rocq bitvector arithmetic models

This is the new `export-rocq-bits` backend, targeting Rocq 9.3.0 and
Stdlib 9.2.0. Ports, registers and nodes use the standard library's `bits n`
type and native `Zmod` operations. Widths are checked by Rocq; input/state
records cannot contain out-of-range integers. This is independent of the
legacy `export-rocq` pass, whose generated output remains unchanged.

The standard library stores bitvectors efficiently as bounded integers, but
the model interface and operations use its typed API, not the legacy raw-Z
records and repeated modulo expressions. Explicit unsigned/signed projections
are used for comparisons and numeric specifications. Zero-divisor results
remain arbitrary input choices; the library's deterministic zero-divisor
defaults do not replace CIRCT semantics.

Versions were selected from the official releases on 2026-11-06:
[Rocq 9.3.0](https://github.com/rocq-prover/rocq/releases/tag/V9.3.0),
[Stdlib 9.2.0](https://github.com/rocq-prover/stdlib/releases/tag/V9.2.0).

From `arithmetic/` (model regeneration is documented in `README.md`):

```sh
opam exec --switch=rocq-bits -- make -C verification/rocq-bits check
```

The committed proof certificates are compiled directly. Reference staging uses
`../../scripts/stage-rocq-bits-reference.py` automatically from the Makefile.

## Proof coverage

All twelve arithmetic instances have the circuit-level contracts listed in
[`../rocq/README.md`](../rocq/README.md). Proofs quantify over arbitrary typed
inputs and states; the full post-reset assertion theorems permit arbitrary
subsequent pins. Finite test cases are exporter regression tests, not substitutes
for these circuit proofs. Processor and temporal LTL examples are outside this
arithmetic task.

Paths in the following table are relative to `Proofs/`.

| Circuit / contract | Native proof entry points | Scope |
| --- | --- | --- |
| Adder | `Adder.v`: `result_correct`, `assertions_hold` | 8-bit operands, arbitrary inputs/state |
| Six carry-save instances | `C22.v`, `C32.v`, `C53.v`, `CSA2_2.v`, `CSA3_2.v`, `CSA5_3.v`: `assertions_hold` | Every generated conservation assertion |
| MultiCycleMac arithmetic/control | `MultiCycleMac.v`: `completes_after_two`, `no_early_output`, `reset_idle`, `stall_stable`, `arithmetic_to_Z` | Accepted operands, exactly two further edges, arbitrary later operand pins |
| MAC assertions | `MacInvariant.v`: `assertions_after_reset` | All eight generated assertions after one reset edge |
| Array signed product | `ArrayContract.v`: `two_edges`, `valid_product_after_two_edges`, `output_hold` | Signed 65-bit operands, independent capture/transfer enables; `two_edges` has no reset hypothesis |
| Array assertions | `ArrayInvariant.v`: `all_assertions_after_reset` | All 3481 assertions, arbitrary post-reset trace |
| Radix arithmetic/latency | `RadixOutput.v`: `accepted_result`, `after_reset_result` | Signed/unsigned, quotient/remainder, full/word, zero divisor; 4–67 total edges |
| Radix stall/assertions | `RadixControl.v`: `stall_stable`; `RadixTrace.v`: `all_assertions_after_reset` | Backpressure and all eleven assertions |
| Unsigned DIV/REM | `MulDivUnsigned.v`: `accepted_result`, `after_reset_result` | Full/word, zero divisor included, 66 total edges |
| Signed DIV/REM | `MulDivSigned.v`: `accepted_result_exact`, `after_reset_result` | Full/word, sign/overflow/zero cases, exact 66–68 total edges |
| Multiplication modes | `MulDivMulLow.v`, `MulDivMulHigh.v`, `MulDivMulSignedHigh.v`, `MulDivMulWord.v`: `accepted_result`, `after_reset_result` | MUL/MULHU/MULH/MULHSU: 65 edges; MULW: 33; data/tag/valid |
| MulDiv control | `MulDivTiming.v`: `accepted_completes`, `after_reset_completes`; `MulDivStall.v`: `stall_stable`, `stall_run_stable` | Same reset/cancellation/backpressure conditions as the reference contracts |
| Checked/core equivalence | `MulDivCheckedProjection.v`: `step_projects`, `observe_projects`, `run_projects`, `trace_projects` | Direct native-model equality, arbitrary states and traces |
| Checked monitor-cycle result | `MulDivCheckedMonitorResult.v`: `signed_result_at_monitor_cycle` | Exact source-monitor latency and correct signed DIV/REM data/tag/valid |
| Checked assertions | `MulDivCheckedAssertions.v`: `all_assertions_after_reset` | All eleven assertions, arbitrary post-reset request/reset/kill/ready pins |

Total-edge counts include acceptance. The proofs cover the emitted parameter
instances, not every Scala width or Rocket configuration. The exporter itself
is tested software, not a formally verified compiler pass.

## How the proofs connect to the generated model

Adder, carry-save and MAC proofs operate directly on native `bits` models.
The byte-wide CSA proofs use checked one-bit column equations, slice
reconstruction, concatenation and overflow bounds. `Unsigned.v`,
`BitDecomposition.v` and `BitFacts.v` provide proved library facts, not axioms.

For the array and divider instances, checked refinement shares the existing
mathematical and invariant proofs while preserving the new representation:

1. `stage-rocq-bits-reference.py` stages the required tracked sources from
   `../rocq` under ignored `Reference/`, using distinct logical namespaces.
   They are compiled afresh with Rocq 9.3; Coq 8.16 object files are never loaded.
   Two proof-script adaptations avoid expensive rewrite searches in
   `ArrayRowSum.window_sum_math` and `MulDivCheckedData.expected_format`.
   Their statements and all model definitions stay unchanged. The old tracked
   sources are not edited.
2. Native records map to reference records by `Zmod.unsigned`. Every proposed
   node equality is proved. The array has 59,798 such equations. Its 1000-node
   proof files partition certificates only; they do not partition or alter the
   generated circuit or its execution semantics.
3. `ArrayRefinementStep.v` and the three `*Refinement.v` divider files prove
   that the mapping commutes with each actual generated `step` and every
   `run`. Output and assertion-list equalities connect the actual generated
   `observe` and `asserts` predicates. The large array record uses a proved
   reversible list encoding to keep the state-equality proof manageable.
4. Contract files conclude properties of native `run`/`step`/`observe`, or the
   native `asserts` predicate. Divider contracts retain the reference theorem
   statements using local numeric views of native fields. Only mathematical
   specifications, request predicates and latency formulas are shared.
   Native/reference model equivalence is proved, never assumed.

`MulDivCheckedProjection.v` additionally proves direct native checked/core
projection using 161 structural cuts. Hashes only propose node matches;
Rocq proves each equality and the complete step/output/trace statements.

The proof generators are untrusted. `make check` rebuilds source dependencies
and independently checks the compiled models and proof modules with the Rocq
kernel. The entry points print their assumptions; none requires an additional
axiom or an admitted result. `Reference/` is a build artifact, not a second
committed copy of the old proof suite.

Both model-reproduction checks above use temporary output directories. The
native models reproduce byte for byte; the old Coq models and Lean declarations
also reproduce unchanged with the plugin containing both passes.

# Rocq arithmetic circuit models and proofs

The `singlefile.RocqEmit` Chisel entry elaborates the same twelve arithmetic
circuits and runs the same HW lowering pipeline as `singlefile.LeanEmit`, ending
with the circt-spot `export-rocq` pass. No NutShell or riscv-mini model is included.

```sh
# From arithmetic/: see ../../README.md for model regeneration.
# With the pinned Coq tools on PATH:
cd verification/rocq
make -j4 check
```

Verified toolchain: OCaml 4.14.2, Coq 8.16.0, MathComp ssreflect 2.2.0.
Generated `.v` files are committed separately from `Proofs/`; proof development
must not edit generated definitions. `coqchk` checks compiled proof terms.

Each integer port/register denotes its residue modulo 2^width. Every generated
read and operation normalizes that residue, representing the same finite-word
domain as Lean's BitVec. Inputs and initial registers remain arbitrary; reset
is a theorem hypothesis, not an initial-state value chosen by the exporter.
`step`, `observe`, `run`, `asserts` and `assumes` have the same cycle convention
as the Lean model. Division by zero has an explicit arbitrary input per
operation, as in the Lean exporter. Immediate enabled checks are preserved.
Temporal LTL properties are currently rejected, not silently approximated.

## Property coverage

The proof target is the existing Lean arithmetic inventory in the repository
README, including all source assertions and the same arithmetic, latency,
reset and backpressure statements. Generated code alone is not a proof.

- Adder: result and universal assertion.
- CSA2_2, CSA3_2, CSA5_3, C22, C32, C53: all conservation assertions.
- MultiCycleMac: accepted result/latency, no early output, stall/reset,
  mathematical arithmetic, and all eight assertions after reset.
- ArrayMulDataModule: all 3481 assertions and signed product across the two
  independently enabled pipeline edges.
- Radix2Divider: all eleven assertions, signed/unsigned arithmetic including
  zero divisor, bounded completion, reset and backpressure.
- MulDiv and MulDivChecked: all thirteen legal operation modes with their
  arithmetic and completion bounds, metadata/backpressure, and all eleven
  checked assertions on arbitrary post-reset traces.

The Lean proof files remain the reference specifications. The following entry
points cover their circuit-level contracts; internal helper lemmas are organized
differently in the two languages. Paths below are relative to `Proofs/`.

| Lean contract | Rocq entry point | Scope and hypotheses |
| --- | --- | --- |
| Adder result/assertion | `Adder.v`: `result_correct`, `assertions_hold` | All inputs and states, 8-bit operands |
| CarrySave assertions | `C22.v`, `C32.v`, `C53.v`, `CSA2_2.v`, `CSA3_2.v`, `CSA5_3.v`: `assertions_hold` | All generated checks; one-bit and 8-bit instances |
| MAC result, latency, no early output, reset | `MultiCycleMac.v`: `completes_after_two`, `no_early_output`, `reset_idle`, `arithmetic_to_Z` | Accepted operands; reset low during the transaction; later operands arbitrary |
| MAC stall and eight assertions | `MacInvariant.v`: `stall_stable`, `assertions_after_reset` | Same backpressure/reset gates; arbitrary post-reset trace |
| Array signed product and pipeline | `ArrayRowSum.v`: `two_edges`; `ArrayInvariant.v`: `valid_product_after_two_edges` | Signed 65-bit operands; independently enabled capture and transfer edges |
| Array 3481 assertions | `ArrayInvariant.v`: `all_assertions_after_reset` | Arbitrary initial registers, one reset edge, arbitrary later inputs |
| Radix result and completion | `RadixOutput.v`: `accepted_result`, `after_reset_result` | All signed/unsigned, quotient/remainder and word controls; zero divisor included; 4–67 total edges, reset low |
| Radix stall and eleven assertions | `RadixControl.v`: `stall_stable`; `RadixTrace.v`: `all_assertions_after_reset` | Same source enable gates; arbitrary post-reset trace |
| MulDiv unsigned DIV/REM, full/word | `MulDivUnsigned.v`: `accepted_result`, `after_reset_result` | Four modes, zero divisor included; 66 total edges; reset/kill low |
| MulDiv signed DIV/REM, full/word | `MulDivSigned.v`: `accepted_result_exact`, `after_reset_result` | Four modes; sign, zero divisor and overflow cases; exact 66–68 total edges |
| MUL, MULHU, MULH/MULHSU, MULW | `MulDivMulLow.v`, `MulDivMulHigh.v`, `MulDivMulSignedHigh.v`, `MulDivMulWord.v`: `accepted_result`, `after_reset_result` | Five modes; data/tag/valid; 65 total edges, or 33 for MULW; reset/kill low |
| MulDiv completion and stall | `MulDivTiming.v`: `accepted_completes`, `after_reset_completes`; `MulDivStall.v`: `stall_stable`, `stall_run_stable` | Legal requests; later request pins arbitrary; same cancellation/reset assumptions |
| Checked/core equivalence | `MulDivCheckedProjection.v`: `step_projects`, `observe_projects`, `run_projects`, `trace_projects` | All states and traces, no reset assumption |
| Checked signed result at monitor cycle | `MulDivCheckedMonitorResult.v`: `signed_result_at_monitor_cycle` | Exact source-monitor latency, correct data/tag/valid; reset/kill low for 68 edges |
| Checked eleven assertions | `MulDivCheckedAssertions.v`: `all_assertions_after_reset` | Exactly generated `asserts`; arbitrary post-reset request/reset/kill/ready pins |

Total-edge counts include the acceptance edge. Thus 65 total edges correspond
to Lean's 64 further edges, and 67 total edges to 66 further edges. None of these
entry-point theorems assumes its arithmetic result or generated assertions. These
proofs cover the emitted parameter instances, not every possible Scala width
or Rocket configuration. The exporters themselves are tested software, not
formally proved compiler passes.

## Current checked progress

All eleven MulDivChecked generated assertions now have one unconditional
post-reset theorem, `MulDivCheckedAssertions.all_assertions_after_reset`.
The theorem permits arbitrary subsequent request, reset, cancellation and
response-ready pins.

- All twelve generated models compile under Coq 8.16.0.
- `Proofs/Adder.v`: both Lean result and assertion statements.
- `Proofs/C22.v`, `C32.v`, `C53.v`, `CSA2_2.v`, `CSA3_2.v`, `CSA5_3.v`:
  every exported conservation assertion, for all inputs. Eight-bit proofs use
  checked one-bit column identities and an exact eight-bit decomposition.
- `Proofs/MultiCycleMac.v` and `MacInvariant.v`: all matching Lean contracts,
  including backpressure, exact accepted-input result/latency, reset, no early
  output, mathematical arithmetic without overflow, and all eight assertions
  on every post-reset cycle with arbitrary subsequent inputs and resets.
- `Proofs/ArrayRowSum.v` and `ArrayInvariant.v`: the full signed 65-by-65-bit
  result across two independently enabled edges, the valid-result flag when
  both edges are outside reset, and all 3481 assertions after reset. The
  assertion proof allows arbitrary subsequent inputs and resets. Its invariant connects
  the actual first-stage boundary sum and output to their validity monitors.
- `Proofs/ArrayCompressors.v`: all 3479 local compressor assertions of the
  actual generated array, for arbitrary states and inputs. Seven shared cut
  templates prove the bit arithmetic; every connection to the actual DAG and
  the ordered assertion list is checked by Coq.
- `Proofs/ArrayHold.v` and `ArrayStall.v`: actual output stability whenever the
  second stage is disabled, and the exported stall assertion after any edge.
  `all_except_product_after_edge` checks 3480 of the 3481 assertions, explicitly
  excluding only the pipeline-product assertion at index 3479.
- `Proofs/ArrayOutput.v`: all 130 final compressor columns conserve their
  weighted inputs. The actual output equals the three physical register rows
  modulo 2^130, and an enabled second-stage edge captures the corresponding
  incoming rows.
- `Proofs/ArrayTree*.v`: 2364 actual inter-stage compressor identities, 130
  column balances, and their weighted sum connect the 2278 first-stage
  register bits and 31 constant bits to the captured output rows.
  `tree_output_capture` connects that boundary sum to the actual output on an
  enabled second-stage edge. `ArrayTreeCapture.v` checks first-stage capture
  and hold, and the resulting two-enabled-edge datapath formula. This formula
  is connected to the corrected Booth rows by `ArrayPacking.v` below.
- `Proofs/BoothPadding.v`: the three sign-padding formats, delayed correction
  placement, and cancellation of the fixed offsets modulo 2^130.
- `Proofs/ArrayPacking*.v`: reconstruct all 34 actual captured groups (33
  Booth row groups plus the last correction), check regrouping across all 130
  columns, and connect the two-edge output to the corrected sum of the actual
  33 row/correction node pairs. The discarded final padding bit is accounted
  for explicitly modulo 2^130.
- `Proofs/ArraySelector*.v`, `ArrayWideSelector*.v`, and `ArrayBoothOperands.v`:
  all 33 actual row/correction pairs, including the special first and final
  windows, have the required signed radix-four digit products.
  `BoothWindows.v` and `BoothOperand.v` reconstruct the signed 65-bit operand
  from these overlapping windows; `ArrayRowSum.v` completes the product.
- `Proofs/ArrayContract.v`: the actual product monitor captures the signed
  65-by-65-bit specification and transfers it on independently enabled edges;
  reset clears its validity flags. `ArrayInvariant.v` proves agreement of the
  datapath and monitor whenever the result is marked known after reset.
- `Proofs/BitPacking.v`: exact reconstruction of an arbitrary-width word
  from its positionally weighted low bits.
- `Proofs/BoothRecoding.v`: the matching generic radix-4 recoding, signed
  product, sign extension and corrected 66-bit selector lemmas, now connected
  to the actual array rows and pipeline.
  `SignedWords.v` and `BoothWide.v` additionally prove signed widening before
  the Booth correction, including the minimum signed operand boundary.
- `Proofs/RadixControl.v`: actual divider reset, acceptance, initialization,
  compute/finish transitions and modular counter increment, plus trace
  decomposition and output stability under backpressure.
- `Proofs/RadixTemporal.v`: compute finishes after exactly the remaining
  counter iterations; an accepted request reaches valid output between edges
  4 and 67 (at most 66 further edges after acceptance), matching Lean. Only
  reset absence is required; later data, input valid and output ready are
  unrestricted.
- `Proofs/RadixDatapath.v`: the actual compute update implements a restoring
  division step and preserves captured operands/controls. The selected quotient
  bit and truncated subtraction satisfy the integer remainder identity under
  the restoring bound, including candidates with bit 64 set.
- `Proofs/RadixBalance.v`: exact packed-register splitting and shift arithmetic;
  each actual compute edge preserves the candidate bound and the integer
  balance of the shifted dividend, accumulated quotient and packed register.
- `Proofs/RadixExecution.v`: all compute prefixes preserve the exact counter,
  captured operands and output metadata. Through the final compute edge, the
  actual run preserves the remainder bound and packed arithmetic balance with
  an existential accumulated quotient bounded by the number of processed bits.
- `Proofs/RadixCapture.v`: actual request acceptance captures the doubled
  dividend magnitude and divisor magnitude; the captured divide-by-zero flag
  is equivalent to a zero divisor magnitude, including signed boundary values.
- `Proofs/RadixSetup.v`: busy cycles and both setup cycles preserve captured
  operands and metadata. With the zero-divisor flag, the actual setup circuit
  initializes the counter to zero and loads the captured 65-bit dividend.
- `Proofs/RadixZero.v`: with a captured zero divisor, every actual compute
  step is a 129-bit left shift with a low one; every compute prefix matches
  the corresponding recurrence and preserves the zero divisor.
- `Proofs/RadixZeroResult.v`: the recurrence has a closed form; after 64 actual
  compute edges from zero setup, valid is asserted, the quotient wire is all
  ones, and the remainder wire is the captured doubled dividend divided by
  two.
- `Proofs/RadixZeroAccepted.v`: from an actual idle acceptance with zero
  divisor, after 67 edges the generated valid wire is one, the quotient wire
  is all ones, and the remainder wire is the original dividend magnitude.
  Captured operands and output metadata are preserved. This matches Lean
  `accepted_zero_magnitudes`, with no restrictions on later data/ready pins.
- `Proofs/RadixShift.v`: the actual shift initialization fits within 128 bits
  without truncation and establishes dividend alignment for the remaining
  compute iterations.
- `Proofs/RadixSkipArithmetic.v`: actual encoder output ranges and the exact
  captured skip formula `min(63, 64 + divisorIndex - dividendIndex)`. The
  generic power-bound argument is connected to operand leading bits below.
- `Proofs/LeadingBits.v` and `RadixLeadingLeaves.v`: the four-bit priority
  encoder and binary merge rule satisfy leading-bit power bounds. All 32
  actual four-bit leaves (divisor and dividend) match that encoder. Their
  node-connection certificates are included; regular tree connections are
  provided below.
- `Proofs/RadixLeadingMerge.v` and `RadixLeadingTree.v`: exact chunk splitting
  and all 29 regular binary merge nodes preserve the leading-bit meaning.
  The connection certificates are included.
- `Proofs/RadixLeading.v`: both complete actual encoder outputs, including
  the special divisor root and 65-bit dividend top-bit selection, satisfy
  the operand leading-bit bounds.
- `Proofs/RadixInitialization.v`: the actual nonzero-divisor setup establishes
  the restoring candidate bound using those encoders, skip selection and shift
  loading. This discharges the candidate-bound initialization obligation.
- `Proofs/RadixResult.v`: given the same initial candidate bound and dividend
  alignment as Lean, the actual compute run yields mathematical quotient and
  remainder on generated wires `v40` and `v402`, with output valid at the
  final counter edge.
- `Proofs/RadixSetupResult.v` and `RadixAccepted.v`: the nonzero-divisor
  accepted-request magnitude theorem is connected end to end. Within edges
  4 through 67, actual valid, quotient and remainder wires agree with division
  of the original operand magnitudes, and captured metadata is preserved.
- `Proofs/RadixFormat.v` and `RadixMetadata.v`: the actual output circuit
  implements sign restoration, quotient/remainder selection and low-32-bit
  sign extension. Acceptance captures the corresponding request controls,
  and captured-state equality preserves them.
- `Proofs/RadixOutput.v`: complete accepted-request and reset-to-request
  output contracts, matching Lean for every divisor, signed/unsigned control,
  quotient/remainder selection and word formatting, within edges 4 through 67.
  Arbitrary later pins and output readiness are allowed.
- `Proofs/RadixArithmeticChecks.v`: all five actual arithmetic checks follow
  from correct zero/nonzero magnitude results, including the widened product
  identity. They are inactive outside finish or during reset.
- `Proofs/RadixHistoryChecks.v`: all six actual history-based assertions
  hold after every edge and throughout arbitrary later traces, including
  resets and backpressure.
- `Proofs/RadixFinishInvariant.v` and `RadixComputeInvariant.v`: a correct
  finish state entails every assertion after an edge and stays correct while
  held. The compute continuation invariant survives each nonfinal step and
  yields magnitude correctness on the last step.
- `Proofs/RadixSetupInvariant.v` and `RadixTrace.v`: capture and both setup
  paths establish the compute invariant; state induction proves all 11
  exported assertions on every cycle after reset, with arbitrary subsequent
  resets, requests, controls and response readiness. This completes the
  Radix2Divider proof scope corresponding to Lean.
- `Proofs/MulDivControl.v`: actual MulDiv reset, multiply/divide state
  transitions, input/output-negation states, done-valid, compute counters,
  busy kill cancellation and captured request metadata preservation. All
  MulDiv arithmetic responses and checked monitor contracts are completed below.
- `Proofs/MulDivTiming.v`: actual generated runs complete multiplication
  within 64 edges from its compute state, division including output sign
  correction within 66 edges, and division from input sign correction within
  67 edges. The initial counter must be in the corresponding valid range;
  reset and kill stay low, while later request pins and response readiness
  are unrestricted. Request acceptance initializes a valid compute state
  and count; `accepted_completes` and `after_reset_completes` prove response
  validity within 68 edges including acceptance (67 further edges), matching
  the Lean completion contract. Division arithmetic is connected below.
- `Proofs/MulDivStall.v`: the generated completed state retains response
  validity, data and tag under backpressure, matching Lean `stall_stable`.
  An induction extends this to any finite number of stalled cycles with
  arbitrary request pins, provided reset, kill and response ready stay low.
- `Proofs/MulDivDivision.v`: exact generated division-edge datapath and
  divisor preservation, plus the 65-bit subtraction-sign comparison under
  the restoring bound. This uses the actual 130-bit remainder register;
  the final division results are connected below.
- `Proofs/MulDivRefinement.v`: the low 129 bits of the actual MulDiv
  division edge equal the verified Radix restoring step under its candidate
  bound and normalized unsigned divisor. Extraction and subtraction lemmas
  connect the 130-bit generated register to that shared datapath.
- `Proofs/MulDivSimulation.v`: arbitrary-length division prefixes preserve
  state and counter; up to the final compute edge, the actual packed register
  equals iteration of the shared restoring step and the divisor stays fixed.
  The restoring bound is maintained inductively, with reset and kill low
  and arbitrary other inputs. Request initialization and accepted arithmetic
  results are connected by the later division proofs.
- `Proofs/MulDivResult.v`: accumulation of quotient bits establishes the
  integer balance invariant; the actual register slices equal quotient and
  remainder for an aligned compute segment. `compute_64_result` specializes
  this to 64 edges from count 1 with packed dividend `2*a` and nonzero divisor.
  These compute-stage contracts are used by the complete division proofs below.
- `Proofs/MulDivInitialization.v`: the actual count-0 division edge shifts
  the captured magnitude to `2*a` and advances to count 1. For nonzero
  divisors, `full_magnitude_result` connects this initialization to all 65
  compute edges and proves the final quotient/remainder register slices.
  Request decoding/capture, formatting and zero division are connected below.
- `Proofs/MulDivUnsignedCapture.v`: DIVU/REMU decoding and operand capture
  for both full-width and word modes, including zero extension and request
  metadata. With a nonzero effective divisor, the actual accepted request
  yields correct quotient/remainder register slices after 66 edges including
  acceptance. The following control and formatting proofs connect these
  register results to the response; the zero-divisor path is proved below.
- `Proofs/MulDivMetadata.v`: division preserves captured width, tag and
  result selection; unsigned division retains a clear output-negation flag.
  After 65 compute edges, state 7 and the requested quotient/remainder
  selection are established. The accepted-request control theorem covers
  both widths and all divisors, including zero, at edge 66. Response data
  formatting is connected in `MulDivFormat.v` and `MulDivUnsigned.v`.
- `Proofs/MulDivFormat.v` and `MulDivUnsigned.v`: actual response formatting
  preserves full-width results and sign-extends the low 32 bits in word mode.
  `accepted_result` and `after_reset_result` prove response validity, specified
  data and the original tag at edge 66 for all DIVU/REMU and DIVUW/REMUW
  operands, including zero effective divisors. This completes the unsigned
  division response contract corresponding to Lean.
- `Proofs/MulDivZero.v`: under the reachable zero-divisor bound, each actual
  division edge shifts the packed value and appends one. `zero_execution`
  proves the exact value `a * 2^n + (2^n - 1)` throughout all 65 compute
  edges while preserving the zero divisor. `zero_magnitudes` decodes all-ones
  quotient and unchanged dividend remainder; `MulDivUnsigned.v` connects
  these values to the actual accepted-request response.
- `Proofs/MulDivSignedOutput.v`: the actual output-negation edge negates
  the selected quotient/remainder, clears the output selector, enters the
  completed state and preserves request metadata. Optional correction yields
  the correctly formatted response and original tag.
- `Proofs/MulDivSignedExecution.v`: the first division edge suppresses
  quotient negation on zero divisors while preserving remainder sign;
  subsequent edges preserve the effective sign and request metadata.
  `finish65` proves the exact finish/negation state and result selection
  after 65 magnitude-compute edges for all divisors. Arithmetic and output
  correction are composed in `MulDivSignedCore.v`.
- `Proofs/MulDivSignedCore.v`: combines all-divisor magnitude arithmetic,
  effective sign and optional output correction. From a magnitude-prepared
  state, the actual run produces valid, correctly formatted data and the
  original tag after exactly 65 or 66 edges, according to the correction flag.
  This includes zero-divisor quotient/remainder behavior. `MulDivSigned.v`
  connects signed requests to this prepared-state contract.
- `Proofs/MulDivSignedInputEdge.v`: the generated input-negation state
  converts the captured dividend to its 64-bit magnitude, conditionally
  negates the 65-bit divisor and preserves request metadata/output sign.
  The proof uses the actual register slices; the following bit and capture
  lemmas connect it to signed request preparation.
- `Proofs/MulDivSignedBits.v`: the captured 65-bit sign extension preserves
  the operand's low bits/sign, and conditional negation yields its 64-bit
  magnitude, including the minimum signed value. `prepared_edge` connects
  this arithmetic to the generated input-negation edge and establishes the
  compute state, count, magnitudes and metadata required by the core proof.
  Signed capture and optional preparation are connected below.
- `Proofs/MulDivSignedOperands.v`: full-width input selection and 32-bit
  sign extension agree with the signed operand specification. The selected
  input sign equals the resulting 64-bit sign, and the generated high/low
  concatenation equals that operand without truncation. These lemmas support
  the signed request-capture proof for both widths.
- `Proofs/MulDivSignedCapture.v`: generated DIV/REM decoding and request
  capture for both widths. The captured operands equal the signed operand
  specification (with a 65-bit sign-extended divisor), state selects optional
  input negation, and count, output sign, selector, width and tag are correct.
  Optional preparation and the core response are composed below.
- `Proofs/MulDivSignedPreparation.v`: signed request capture followed by
  zero or one input-negation edge establishes the magnitude-compute contract
  for both widths and every operand. The `run_prepared` theorem connects
  that state and shifted input stream to the original generated execution.
  The final accepted-response composition is provided in `MulDivSigned.v`.
- `Proofs/MulDivSigned.v`: `accepted_result_exact` and `after_reset_result`
  compose request capture, optional input negation, all-divisor arithmetic
  and output correction into the actual generated run. All DIV/REM and
  DIVW/REMW inputs produce the specified valid response and original tag
  after exactly the request-dependent 66–68 edges, including zero divisors
  and signed-overflow bit patterns. This completes the signed division
  response contract corresponding to Lean.
- `Proofs/MulDivMultiply.v`: the generated multiplication edge updates the
  physical register exactly as specified, injects the output sign at count
  62, and preserves the divisor, output sign and request metadata. Removing
  the separate physical sign slot preserves all product bits (`packed_edge`).
  The arithmetic invariants and accepted-response contracts are composed
  in the multiplication modules below.
- `Proofs/MulDivMultiplyBalance.v`: reconstructs the complete 66-bit partial
  product from the physical update and proves that an unsigned compute edge
  is the ordinary shift/add recurrence. The arithmetic lemmas establish its
  exact discarded-bit balance, accumulator bound, 128-bit result bound and
  induction step for the consumed multiplier bits. `compute_prefix` proves
  that the generated control stays in the multiply state and increments the
  count until the last iteration. `MulDivMultiplyRun.v` connects this recurrence
  to the full unsigned compute loop; `MulDivMultiplyCapture.v` connects MULHU
  request capture.
- `Proofs/MulDivMultiplyRun.v`: `unsigned_execution` proves the consumed-bit
  balance over every prefix of the actual generated unsigned multiply loop,
  preserving the divisor, sign and 128-bit bound. `unsigned_product` proves
  that 64 compute edges produce the full 128-bit product for all 64-bit
  operands. Its premises describe a prepared multiply state; request capture
  is connected below, and `MulDivMulHigh.v` completes the MULHU response.
- `Proofs/MulDivMultiplyCapture.v`: proves MULHU decoding and capture of the
  operands, count, sign, selector, width and tag. `accepted_product` connects
  capture to all 64 compute edges: after 65 edges including acceptance, the
  generated packed register equals the full unsigned product for every pair
  of 64-bit operands. The external valid/data/tag response is completed below.
- `Proofs/MulDivMultiplyMetadata.v`: preserves multiplication request metadata
  through the compute loop and proves that the last iteration enters state 6
  and selects the requested result half. MULHU reaches this state after 65
  edges including acceptance, with its captured width, selector and tag.
- `Proofs/MulDivMulHigh.v`: `accepted_result` and `after_reset_result` prove
  the complete MULHU response for every pair of 64-bit operands: valid is
  asserted after 65 edges, data is the upper 64 bits of the unsigned product,
  and the original request tag is returned. Later request pins and response
  ready are arbitrary; reset and kill stay low during the transaction.
- `Proofs/MulDivMultiplySigned.v`: connects the generated replicated sign bit,
  divisor sign extension and accumulator sign extension to signed integer
  arithmetic. `signed_raw_exact` proves that the actual 66-bit partial sum
  equals coefficient times divisor plus accumulator, without overflow for
  coefficients -1, 0 and 1 under the loop's strict operand bounds. The
  arithmetic right-shift bound is preserved. The following modules connect
  this to hardware updates, execution prefixes and final responses.
- `Proofs/MulDivMultiplySignedStep.v`: connects the signed partial sum to
  the actual generated register update. `signed_step_balance` proves the
  exact signed shift/add balance including the discarded low bit, and
  `accumulator_range` preserves the strict signed accumulator bounds across
  that same hardware edge. Signed concatenation and arithmetic right shift
  are proved over integers; no bit-vector correctness axioms are introduced.
  `MulDivMultiplySignedRun.v` and `MulDivMultiplySignedProduct.v` compose
  all 64 edges; response contracts are completed below.
- `Proofs/MulDivMultiplySignedRun.v`: proves the signed multiplication balance
  over every prefix through iteration 63 of the generated circuit, preserving
  the signed divisor and accumulator range. The sign slot stays zero until
  the final iteration's injection point. `prefix_decode` recovers the original
  multiplier's high bit and consumed low bits from that balance, preparing
  the final signed-weight step completed in `MulDivMultiplySignedProduct.v`.
  Final response composition is completed below.
- `Proofs/MulDivMultiplySignedProduct.v`: proves the sign injection at the
  final iteration and the exact product after all 64 generated compute edges.
  `product_from_packed` starts from a prepared state containing the unsigned
  multiplier and a signed 65-bit multiplicand. With the injected flag zero
  or equal to the multiplier high bit, the result is respectively the
  unsigned-weight or signed-weight integer product. Signed-high request
  capture and responses, as well as low and word modes, are connected below.
- `Proofs/MulDivMulSignedCapture.v`: proves MULH/MULHSU decoding, full-width
  operand capture, multiplicand sign extension and final sign selection.
  `accepted_product` proves that after 65 edges including acceptance, the
  actual packed register contains the exact signed-by-signed (MULH) or
  signed-by-unsigned (MULHSU) product, for every operand pair. External
  response valid/data/tag composition is completed in `MulDivMulSignedHigh.v`.
- `Proofs/MulDivMulSignedHigh.v`: completes MULH and MULHSU for all full-width
  inputs. `accepted_result` and `after_reset_result` prove the response after
  exactly 65 edges including acceptance: valid is asserted, data is the high
  64 bits of the signed-by-signed or signed-by-unsigned product, and the
  original request tag is returned.
- `Proofs/MulDivMulLowProduct.v`: proves that sign injection does not affect
  the low 64 bits of a compute edge, including coefficient -2. Combined
  with the first 63 iterations, the actual 64-edge execution produces the
  low product for every initial output-sign flag and signed multiplicand.
- `Proofs/MulDivMulLowCapture.v`: proves full-width MUL request decoding,
  signed multiplicand capture, output-sign selection, and the accepted
  low-half product for all operand bit patterns.
- `Proofs/MulDivMulLow.v`: `accepted_result` and `after_reset_result` complete
  full-width MUL: exactly 65 edges including acceptance produce a valid
  response containing the low 64 product bits and original request tag.
  Together with the high-half proofs, all four full-width multiplication
  modes are complete.
- `Proofs/MulDivMulWordBalance.v`: generalizes the signed prefix invariant to
  a nonzero initial count and proves MULW's 32-edge compute loop starting
  at count 32. `word_slice` proves that packed bits 63:32 equal the low
  32 bits of the multiplicand times the multiplier's low 32 bits, with no
  restriction on the output-sign flag. Request capture, completion and
  output sign extension are composed below.
- `Proofs/MulDivMulWordCapture.v`: proves MULW request decoding, count-32
  initialization and signed low-32-bit operand capture; `accepted_slice`
  connects the request to the actual generated result bits after 33 edges.
- `Proofs/MulDivMulWord.v`: `accepted_result` and `after_reset_result` prove
  the complete MULW response after exactly 33 edges including acceptance:
  valid is asserted, data is the sign-extended low 32-bit product, and the
  original request tag is preserved. This completes all five multiplication
  modes and all thirteen legal MulDiv arithmetic modes. The checked-model
  projection and post-reset monitor assertions are proved below.
- `Proofs/MulDivCheckedProjection.v`: proves each core combinational node,
  each core state update and every external output of MulDivChecked equal
  to the corresponding MulDiv projection. `run_projects` and `trace_projects`
  extend this to arbitrary input/reset traces and arbitrary initial monitor
  registers. This connects all existing core arithmetic response proofs to
  the instrumented circuit; the eleven monitor assertions still need their
  own post-reset invariants.
- `Proofs/MulDivCheckedHistory.v`: proves captured monitor request fields,
  their preservation without a new request, reset clearing of control flags,
  accepted-request age initialization and legal-request pending activation.
  It also proves that quotient/remainder witnesses are recorded before
  output negation and remain stable otherwise. These establish the monitor
  history used by the post-reset assertion invariants.
- `Proofs/MulDivCheckedStall.v`: proves exported checks 8, 9 and 10 on every
  observation after any initial edge, without requiring that edge to reset.
  A recorded stalled response remains valid with unchanged data and tag.
  The proof connects the actual monitor flag and recorded values to the core
  backpressure theorem through the checked-model projection. Arbitrary later
  resets, cancellation, requests and response readiness are allowed. The
  tag proof below brings the total to four of eleven checked assertions.
- `Proofs/MulDivActive.v` and `MulDivCheckedControl.v`: prove that every
  post-reset pending monitor request occupies a valid core execution phase,
  with the multiplication count below 64 and division count at most 64.
  The invariant handles acceptance, cancellation and response handshakes,
  and implies that an outstanding request cannot be overwritten by later
  request pins. This supplies the control invariant for the
  monitor assertions; it does not assume their conclusions.
- `Proofs/MulDivCheckedMetadata.v`: proves exported response-tag check 2 at
  every observation after reset. Pending requests retain matching core and
  monitor tag/width fields, and their captured operation and width always
  describe one of the thirteen legal modes. Arbitrary subsequent inputs,
  resets and cancellation are covered. All eleven monitor assertions
  are complete in the aggregate theorem below.
- `Proofs/MulDivCheckedTimingChecks.v`: connects the two exported timing
  checks directly to an age bound and exact response-valid condition. Proves
  their disabled cases (no pending request, reset, cancellation), their truth
  immediately after a reset edge, and the generated multiplication latency
  of 64 or 32 further edges. The running age/control invariants needed for
  all post-reset observations are supplied separately by operation class.
- `Proofs/MulDivCheckedAge.v`: proves the generated age register increments
  while a request is pending and not responding, holds during a completed
  response, and preserves captured width/function without acceptance.
- `Proofs/MulDivCheckedMulTiming.v`: proves both exported timing checks at
  every post-reset observation with a captured multiplication operation.
  The inductive invariant relates monitor age to the actual core counter,
  including the word-mode offset, the last iteration, and response stalls.
  Arbitrary later inputs, reset and kill are covered.
- `Proofs/MulDivCheckedUnsignedTiming.v`: proves both exported timing checks
  on all post-reset traces for DIVU/REMU, including word mode and zero
  divisors. The captured unsigned operation has latency 65; the core count
  equals monitor age during division, with no input/output negation phase.
  Completion stalls preserve age.
- `Proofs/MulDivCheckedLatency.v`: proves the generated division latency is
  exactly 65 plus its two one-bit input/output-negation costs (65–67), is
  independent of current input pins, and remains stable while a request is
  pending. The proof uses the actual generated monitor nodes.
- `Proofs/MulDivCheckedSignedTiming.v`: proves that the signed timing phase
  conditions imply both generated timing checks. This is a conditional
  theorem; the unconditional trace result is provided by the trace module
  below.
- `Proofs/MulDivCheckedSignedTimingEdges.v`: proves preservation of signed
  timing phases from iteration count 1 onward, through the last divide
  iteration, optional output negation and response stalls. This uses actual
  generated state/age transitions and the core negative-flag theorem.
  The initialization and capture lemmas below establish its starting phase.
- `Proofs/MulDivCheckedSignedOperands.v`: connects the generated monitor's
  signed operands, sign bits and divisor magnitude to the existing core
  signed-division definitions, for full-width and word requests. Proves its
  output-negation cost equals the core's effective negative flag, including
  the quotient-specific zero-divisor correction. These bridge lemmas supply
  the arithmetic facts needed to initialize the signed timing invariant.
- `Proofs/MulDivCheckedSignedTimingInit.v`: proves the input-negation edge
  establishes the magnitude-prepared phase and the first divide iteration
  establishes the later-iteration invariant, including zero-divisor sign
  correction. Captured operand/function stability is proved from generated
  registers. The capture and trace modules below complete the induction.
- `Proofs/MulDivCheckedSignedTimingCapture.v`: proves signed request capture
  establishes either the input-negation or magnitude-prepared phase, with
  matching captured operands, extra cycle count and raw output sign.
- `Proofs/MulDivCheckedSignedTimingTrace.v`: combines capture and all phase
  transitions into both timing assertions at every post-reset observation
  for signed DIV/REM, including word mode, zero divisors and overflow.
- `Proofs/MulDivCheckedTiming.v`: proves generated assertions 0 and 1 for
  every post-reset trace across all thirteen legal modes. Subsequent request
  pins, resets, cancellation and response backpressure are arbitrary.
- `Proofs/MulDivCheckedDivisionChecks.v`: proves all four generated division
  arithmetic checks from correct quotient/remainder witnesses. Covers zero
  divisors, the widened 129-bit identity and strict remainder bounds without
  assuming arithmetic truncation is harmless. The trace module below
  establishes witness correctness.
- `Proofs/MulDivCheckedWitness.v`: proves the monitor's selected saved/raw
  quotient and remainder exactly match the generated assertion nodes, that
  output-negation captures the pre-negation pair, and that response stalls
  preserve the selected pair.
- `Proofs/MulDivCheckedMagnitude.v`: proves the captured magnitude parameters
  remain stable and establishes the future-iteration correctness invariant
  from the initialized core. Each actual divide edge preserves it; the last
  edge yields correct quotient/remainder registers, including zero divisors.
- `Proofs/MulDivCheckedWitnessCorrect.v`: connects correct core registers to
  selected monitor witnesses, preserves witness correctness through output
  negation and response stalls, and derives the four arithmetic assertions.
  The combined post-reset induction is completed in the trace module below.
- `Proofs/MulDivCheckedMagnitudeInit.v`: establishes the magnitude-computation
  invariant from signed prepared states and unsigned request capture.
- `Proofs/MulDivCheckedDivisionTrace.v`: proves correct quotient/remainder
  witnesses on arbitrary post-reset division traces, including cancellation,
  input/output negation, iteration-zero correction and response stalls.
- `Proofs/MulDivCheckedDivisionAssertions.v`: proves exported checks 4–7 at
  every post-reset observation using the trace invariant and actual generated
  enable gates. Together with timing, tag and stall checks, all eleven
  assertions are complete in the aggregate theorem below.
- `Proofs/MulDivCheckedData.v`: connects the generated response-data check
  to actual output equality, including inactive gates and word-result sign
  extension in the generated expected-value expression.
- `Proofs/MulDivCheckedDivisionOutput.v`: proves a division completion result
  relation implies the actual output equals the monitor expectation, and
  proves the output-negation edge establishes the negated result relation.
  The trace module below establishes this relation on all division traces;
  the multiplication data bridge is completed below.
- `Proofs/MulDivCheckedDivisionSign.v`: derives the last-iteration and
  output-negation sign facts from the proved signed/unsigned timing traces.
- `Proofs/MulDivCheckedDivisionOutputControl.v`: proves the core quotient/
  remainder selector matches the captured function and preserves completed
  result relations under response backpressure.
- `Proofs/MulDivCheckedDivisionOutputTrace.v`: proves response-data assertion
  3 for every post-reset observation in all division modes, using capture,
  final-iteration, output-negation and stall transitions. The multiplication
  cases of assertion 3 are completed below.
- `Proofs/MulDivCheckedMulSpec.v`: unifies the five legal multiplication
  modes under one accepted-result specification and proves it depends only
  on normalized function, width and operand inputs.
- `Proofs/MulDivCheckedMulFuture.v`: establishes future output correctness
  on request capture and preserves it through actual multiplier iterations;
  the final iteration yields the captured request's specified data. The
  generated-product bridge and trace induction are completed below.
- `Proofs/MulDivCheckedMulTrace.v`: proves completed multiplier outputs equal
  the captured request specification on every post-reset trace. Covers legal
  capture, iterative computation, cancellation/reset and response stalls.
- `Proofs/MulDivCheckedProductBits.v`: proves 128-bit sign-extension and high
  product extraction identities and the MULW low-word product equivalence.
  These arithmetic lemmas support the generated-product bridge below.
- `Proofs/MulDivCheckedMulBridge.v`: proves the generated expected product
  expression equals the independently proved specification for MUL, MULW,
  MULH, MULHSU and MULHU, including signed extension and high-half extraction.
- `Proofs/MulDivCheckedMulOutput.v`: proves response-data assertion 3 in every
  multiplication mode on arbitrary post-reset traces.
- `Proofs/MulDivCheckedAssertions.v`: combines timing, tag, data, division
  arithmetic and stall results into `all_assertions_after_reset`, proving
  exactly the generated `asserts` predicate (all eleven checks).
- `Proofs/MulDivCheckedMonitorResult.v`: proves the captured signed-division
  monitor latency equals the core's exact edge count, then projects the core
  data/tag/valid theorem onto the instrumented circuit at that exact cycle.
- `Proofs/RestoringDivision.v`: unbounded integer restoring division over any
  finite binary sequence, with quotient/remainder uniqueness. Connecting the
  full divider initialization, iterations and signed outputs is complete.
  All thirteen legal MulDiv arithmetic modes are now complete. MulDivChecked
  post-reset assertions are proved by `MulDivCheckedAssertions`.

## Snapshot notes

The proof certificates above were migrated from the private source repository.
Proof generators and exporter regression scripts are not included here.
Use `make check` in this directory for compilation and kernel checking, and
see `../../README.md` for the adapted model regeneration command. The retained
`models.json` records the original export audit; `../../manifest.json` records
this migrated snapshot. Historical generator names above describe provenance,
not runnable commands in this package.

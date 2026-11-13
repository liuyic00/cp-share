Hierarchical arithmetic models and proofs
========================================

This independent Lean 4.24.0 project contains arithmetic circuits only. It
neither imports flat Lean proofs nor proves equivalence with flat models.
From arithmetic/, compile all models and proofs::

    cd verification/lean-hierarchical
    lake build

Model regeneration is documented in ../../README.md. It invokes the adapted
singlefile.HierarchicalLeanEmit entry, writes HW IR under
artifacts/mlir/lean-hierarchical and models under this project's Generated/.
It does not modify Proofs/. Generated ArrayMul files are split into imports to
bound elaboration depth. The committed models and proof certificates suffice
for lake build without Scala, firtool or the CIRCT plugin.

Conversion and composition
--------------------------

``export-lean-hierarchical`` preserves module definitions and instance states.
Exporter-side dependency analysis treats registers as old-state sources and
assigns one shared phase partition to each module, considering every instance.
Greedy compatible merges reduce phases until no compatible pair can merge;
this is not a claim of a globally minimum partition. Per-tick memo structures
share intermediate results without adding persistent registers. The generated
API includes eval, step, run, evaluation contracts, and assertion/assumption
composition lemmas. Large states and computation blocks are grouped without
flattening child instance state.

``Proofs/Composition.lean`` supplies instance trajectory and assumption
composition. Exporter scheduling regressions from the original project are
not included in this arithmetic snapshot.
ArrayMul composes 1499 compressor instances using reusable compressor contracts.
Assertions retain their enables and instance paths. Environment assumptions
must be premises of composition; they are not silently promoted to theorems.

Arithmetic proof entry points
-----------------------------

* Adder: ``Proofs/Adder.lean`` (result_correct, assertions_hold).
* C22, C32, C53 and CSA2_2/CSA3_2/CSA5_3:
  ``Proofs/CSA2_2.lean``, ``Proofs/CSA3_2.lean``, ``Proofs/CSA5_3.lean``
  and ``Proofs/ArrayCompressors.lean``.
* MultiCycleMac: ``Proofs/MultiCycleMac.lean`` (accepted_result and pipeline
  invariants), with protocol and natural-number refinements in companion files.
* ArrayMulDataModule: ``Proofs/ArrayArithmeticContract.lean``
  (two_edges_product) proves the 130-bit signed product after the two enabled
  register transfers; ``Proofs/ArrayAssertions.lean`` proves assertions after
  reset, including child assertions and pipeline holding behavior.
* Radix2Divider: ``Proofs/RadixOutput.lean`` (accepted_result,
  after_reset_result) and ``Proofs/RadixReachability.lean``
  (asserts_after_reset).
* MulDiv: ``Proofs/MulDivArithmeticContract.lean`` (arithmetic_accepted,
  arithmetic_after_reset), covering legal multiplication, high products,
  signed/unsigned division and remainder, full/word modes and zero divisors.
* MulDivChecked: ``Proofs/MulDivCheckedArithmetic.lean`` supplies the final
  arithmetic contracts; ``Proofs/MulDivCheckedReachability.lean`` proves all
  eleven assertions after reset for arbitrary subsequent input traces.
  The checked datapath reuses the independently generated new MulDiv core
  contract through a state projection; neither side is a legacy model.

Completion contracts require reset and cancellation to remain inactive during
the stated latency window. Reachable assertion contracts instead allow arbitrary
subsequent reset, cancellation and response backpressure. Initial data registers
may be arbitrary where the contract starts with a reset edge. Exact hypotheses,
word formatting, overflow behavior and latency bounds are stated in Lean.

Validation and trust
--------------------

``lake build`` checks every Generated and Proofs module. Bit-vector
obligations use bv_decide; the reported dependencies include Lean.ofReduceBool
and Lean.trustCompiler, in addition to standard Lean axioms. No sorry, admit,
or user-declared axiom is used as a proof substitute. This is not a claim of
exporter correctness for all possible source programs or of kernel-only SAT
certificate checking. Unsupported clocks/reset forms and temporal operations
are rejected by the exporter; see its diagnostic regression tests.

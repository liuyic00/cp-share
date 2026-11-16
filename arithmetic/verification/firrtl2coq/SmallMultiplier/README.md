# XiangShan 8-bit multiplier: original firrtl2coq assertions

`Proof.v` proves all five exact propositions in the generated
`SmallMultiplier.ArrayMulDataModule8` file: one assertion for each of the three
compressor module types (at every instance), and the two top-level assertions.
All five theorems and `multiplier_all_obligations` have compiled with Coq 8.16.0.
The full dependency closure of 140 files compiles under the current per-circuit
layout. Before this directory reorganization, a forced rebuild and independent
`coqchk` run had both passed. The latest layout validation compiled all
necessary dependencies but did not repeat `coqchk`. A complete checker run
writes `arithmetic/build/firrtl2coq-multiplier-proof/result.json` only after
independent checking succeeds.

The proof quantifies arbitrary symbolic power-on register values, executes the
original interpreter's reset-high cycle, and covers every subsequent finite
number of cycles with arbitrary legal inputs. Observation `k` uses input
`S k`, before the next ordinary edge. Inputs are known, correctly sized bit
vectors, as specified by the tool's generated legal-trace predicate. The proof
does not require capture enables to remain high and covers disabled/holding
cycles and subsequent resets.

The retained hierarchical FIRRTL AST and original bit-vector/cycle interpreter
remain the model. Integer identities are connected to that model by proved
lemmas; no alternative transition function or assumed equivalence is used.
`Print Assumptions multiplier_all_obligations` reports only the upstream
`ftype_eqn_eq` and `ffield_eqn_eq` type-equality axioms. There are no new axioms,
`Admitted`, or imported admitted generated obligations. Tool fixes are recorded in the firrtl2coq submodule; circuit proofs and
reproduction scripts are recorded in the parent repository.

## Reproduce

Use the `firrtl2coq` opam switch (Coq 8.16.0, MathComp 1.15). Run from the worktree
root. Build the modified tool first if its sources changed:

```sh
(cd tool/firrtl2coq && opam exec --switch=firrtl2coq -- coq_makefile -f _CoqProject -o Makefile && opam exec --switch=firrtl2coq -- make -j1)
(cd tool/firrtl2coq/src/ocaml && opam exec --switch=firrtl2coq -- dune build && opam exec --switch=firrtl2coq -- dune runtest)
python3 arithmetic/scripts/generate_firrtl2coq_models.py
python3 arithmetic/scripts/check_firrtl2coq_multiplier.py --jobs 2 --force
```

The retained 8-bit Low FIRRTL is available in this `ai-dev` worktree;
the commands above use its default repository-local path.

Tool-generated Coq lives under `../Generated/ArrayMulDataModule8/`:
`Model.v` is the verbatim model/properties prefix, and `ArrayMulDataModule8.v`
retains the original five lemma statements, replacing each `Admitted.` with
`Proof. exact SmallMultiplier.Proof.multiplier_obligation_i. Qed.`.
Both Coq files are reviewable sources; only the generation manifest is ignored.
The complex proofs remain here and import only `Model`, avoiding circular dependencies.

The checker audits the dependency closure for admitted proofs and compiles the final
`SmallMultiplier.ArrayMulDataModule8` module. Use `--compile-only` to skip an additional
`coqchk`; otherwise it independently checks that final module too. `--force` recompiles
the full closure. The result records compilation and independent checking separately.
Generation (`proved: false` in the manifest) does not claim that these proofs compile.

## Proof structure

- `GlobalConvergence.v` and `ObservationBridge.v` connect all 2262 stable values
  to the original 2256 combinational iterations, including nested instances.
- `GlobalCommit.v`, `CycleBridge.v`, and `RuntimeWords.v` establish all 56
  register updates and their widths across the original full circuit cycle.
- `PipelineEquations.v`, `CaptureNumbers.v`, and `ColumnUpdate.v` establish
  capture/hold equations for the 52 column registers and reconstruct the five
  partial-product rows, whose weighted sum is the signed product modulo 65536.
- `ControlEquations.v`, `ExpectedProduct.v`, and `PipelineInvariant.v` establish
  the expected-result/valid/previous-result/holding updates and prove reset
  establishment and single-step preservation of both top-level invariants.
- `RuntimeSeed.v`, `RuntimeInputs.v`, `RuntimeState.v`, and `RuntimeReset.v`
  connect arbitrary power-on registers, legal inputs, and the actual reset/run
  interpreter to the invariants for any step count.
- `RuntimeObservation.v` and `GeneratedObservation.v` connect the invariants
  to the exact generated observation predicate. `ChildAssertions.v` and
  `TopAssertions.v` discharge the original local assertions; `Proof.v` closes
  the five generated obligations for all relevant instances.

The `prepare_*.py` and `*_certificate.py` scripts regenerate their corresponding
proof certificates. These emit Coq proof terms/tactics, not trusted results;
each output is checked by Coq. Unused intermediate proofs and their scripts,
including the old component-only `check.py`, are preserved in
[the exploration archive](../Archive/README.md). `CaptureAST.v` remains here
because three current generators read its capture table. Use the full
verification script above for the complete arbitrary-step theorem.

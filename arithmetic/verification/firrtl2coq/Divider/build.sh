#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd -- "$here/../../../.." && pwd)
cd "$repo"
python3 "$here/prepare.py"
python3 "$here/match_nodes.py"
python3 "$here/prepare_slices.py"
python3 "$here/prepare_typing.py"
python3 "$here/prepare_certificates.py"
python3 "$here/prepare_reductions.py"
python3 "$here/prepare_frames.py"
python3 "$here/prepare_mux_shapes.py"
python3 "$here/prepare_concats.py"
python3 "$here/prepare_log2.py"
python3 "$here/prepare_scalar_ops.py"
python3 "$here/prepare_slice_ops.py"
python3 "$here/prepare_leaf_words.py"
python3 "$here/prepare_reference_normalization.py"
python3 "$here/prepare_controls.py"
python3 "$here/prepare_convergence.py"
python3 "$here/prepare_initialization.py"
python3 "$here/prepare_commit.py"
coq_args=(-Q tool/firrtl2coq/lib/simplssrlib simplssrlib
 -Q tool/firrtl2coq/lib/nbits nbits -R tool/firrtl2coq/src firrtl
 -Q arithmetic/verification/firrtl2coq/Common ArithmeticCommon
 -Q arithmetic/verification/firrtl2coq/Divider Divider
 -Q arithmetic/verification/firrtl2coq/Generated/Radix2Divider Divider
 -Q arithmetic/verification/rocq/Generated Generated)
opam exec --switch=firrtl2coq -- coqc "${coq_args[@]}" "$here/../Generated/Radix2Divider/Model.v"
for part in Stable Representation ReferenceNodes Typing Slices Reductions Muxes MuxShapes Concats Log2 ScalarOps SliceOps LeafWords ControlStart ControlSpecial Log2Bounds ReferenceNormalization Controls Certificates Frames SingleModule NodeProgress Convergence Initialization Commit Bridge; do
 opam exec --switch=firrtl2coq -- coqc "${coq_args[@]}" "$here/$part.v"
done

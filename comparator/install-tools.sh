#!/usr/bin/env bash
set -euo pipefail
R4_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${COMPARATOR_TOOLS:?Set COMPARATOR_TOOLS to a fresh tool directory}"
test "$(uname -s)" = Linux
mkdir -p "$COMPARATOR_TOOLS/bin"
export PATH="$HOME/.elan/bin:$PATH"
read -r R4_CMP R4_EXPORT R4_LANDRUN < <(python3 - "$R4_ROOT/comparator/pins.json" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]));print(p['comparator_commit'],p['lean4export_commit'],p['landrun_commit'])
PY
)
git clone --quiet https://github.com/zouuup/landrun.git "$COMPARATOR_TOOLS/landrun"
git -C "$COMPARATOR_TOOLS/landrun" checkout --quiet --detach "$R4_LANDRUN"
(cd "$COMPARATOR_TOOLS/landrun" && go build -trimpath -o "$COMPARATOR_TOOLS/bin/landrun" ./cmd/landrun)
git clone --quiet https://github.com/leanprover/comparator.git "$COMPARATOR_TOOLS/comparator"
git -C "$COMPARATOR_TOOLS/comparator" checkout --quiet --detach "$R4_CMP"
(cd "$COMPARATOR_TOOLS/comparator" && lake build comparator)
git clone --quiet https://github.com/leanprover/lean4export.git "$COMPARATOR_TOOLS/lean4export"
git -C "$COMPARATOR_TOOLS/lean4export" checkout --quiet --detach "$R4_EXPORT"
cp "$R4_ROOT/lean/lean-toolchain" "$COMPARATOR_TOOLS/lean4export/lean-toolchain"
(cd "$COMPARATOR_TOOLS/lean4export" && lake build lean4export)
# The checking job compiles the trusted challenge before restoring proof build products.
# Never compile the submitted R4 solution outside Comparator's sandbox in this job.

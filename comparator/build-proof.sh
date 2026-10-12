#!/usr/bin/env bash
# Cache a partial build at the 300 minute boundary; rerun the SAME commit to resume.
set -euo pipefail
mkdir -p ../build-receipt
set +e
timeout --kill-after=120 300m lake build R4Initial.FinalTheorem R4Initial.StatementSanity FCSolution \
  2>&1 | tee ../build-receipt/build.log
R4_PIPE=("${PIPESTATUS[@]}")
set -e
R4_CODE=${R4_PIPE[0]}
test "${R4_PIPE[1]}" -eq 0
if [[ "$R4_CODE" -eq 0 ]]; then
  printf 'ready=true\n' >> "$GITHUB_OUTPUT"
  printf 'PASS\n' > ../build-receipt/status.txt
elif [[ "$R4_CODE" -eq 124 || "$R4_CODE" -eq 137 ]]; then
  printf 'ready=false\n' >> "$GITHUB_OUTPUT"
  printf 'INCOMPLETE: rerun same commit to resume cached build\n' > ../build-receipt/status.txt
else
  printf 'FAIL: exit=%s\n' "$R4_CODE" > ../build-receipt/status.txt
  exit "$R4_CODE"
fi

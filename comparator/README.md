# R4 proposed FC target verification

The FC-target verification described here passed on public `main` on 12 October 2026
([run 38223600783](https://github.com/KitaKen1/smooth-isometric-embeddings-r4/actions/runs/38223600783)),
after passing in a private verification repository. Its records are in
`ComparatorLog20261012/38223600783-attempt1/`. No R4 Formal Conjectures PR has been created.

The target is `SmoothIsometricEmbeddingR4.smooth_isometric_embedding_R4`. The complete proposed
FC-style file is in `FClikelean/SmoothIsometricEmbeddingR4.lean`; that folder also contains
the statement guide.
`render-target.py` copies its definitions and generates two trusted files:
`lean/FCTargetDefinitions.lean` contains the definitions with seven pinned Mathlib imports,
and `lean/Challenge.lean` imports those definitions and retains the theorem's intended `sorry`
hole. The FC import, module/public declarations and review metadata are removed;
`answer(True)` is written as `True`. FC's default elaborator marks this term with a
review annotation. The normalization and its pinned official source are recorded in `pins.json`.
`lean/FCSolution.lean` imports the same independently elaborated definitions and
`R4Initial.FinalTheorem`, retains the same statement/name, and fills the hole with
the forward implication supplied by `R4Embedding.closedOrientableSurfaceEmbedding.{0}`
and the trivial reverse implication to `True`. Sharing the independently compiled target
definitions prevents solution imports from changing their elaborated declaration information.

This extraction is explicit: **Challenge.lean is not a byte-for-byte copy of an upstream FC file.**
The full draft is preserved and hashed, and the generated files are checked against it. The FC
file is not submitted, so `fc_target_commit` and `fc_pr` are null rather than invented identifiers.

The upstream FC base `8b3ec608d55559e384ad359b3c83f1c2112df448` uses Lean 4.33.1 / Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. R4 uses Lean 4.34.1 / Mathlib `d13f23b…`.
The current draft's compatibility with a real FC checkout remains pending. Do not describe
this candidate as an accepted FC theorem, a validated upstream FC checkout, or an exact
upstream-target Comparator run. Different version numbers alone do not establish a compilation failure or require porting the
whole external proof. First build the proposed statement and definitions in a real FC checkout.
If incompatibilities are found, determine the smallest changes needed, keep the submitted and
external target definitions aligned, and then freeze the submitted FC head/path for the final
exact-target comparison. FC permits longer proofs to be hosted externally using formal_proof.

## Fixed inputs

`pins.json` fixes the original verified proof source, proposed draft hash, toolchain, Mathlib and
three tool revisions. `check-inputs.py` checks all 2,511 original release inputs, including all
2,494 proof/dependency modules. Original proof files are unchanged. The publication lakefile
only adds the three review libraries; its unchanged original is `proof-source-lakefile.toml`.

```bash
python3 comparator/render-target.py --check
python3 comparator/check-inputs.py --receipt-dir input-receipt
```

For an existing compiled R4 workspace, the local preflight is:

```bash
python3 comparator/local-precheck.py \
  --proof-workspace /absolute/path/to/r4/lean \
  --receipt-dir /absolute/path/to/local-verification/fc-local-precheck
```

It separately elaborates Challenge and FCSolution, compares the theorem and reachable
declarations using the pinned Comparator's equality/traversal rules, and audits the solution's
axioms. Its success status is `LOCAL_PRECHECK_PASS`, **not** `PASS` for a Linux Comparator run.

## Private CI first, then public main CI

First run `.github/workflows/comparator.yml` in a private verification repository. Check the
complete FC target, permitted axioms and kernel acceptance; repair setup or target issues there.
Freeze the successful proof and verification configuration, publish them to public `main`, and
rerun this same workflow in the public repository. Private success alone is not public-run evidence.

The workflow is manual (`workflow_dispatch`), with read-only repository
permissions and three substantive jobs:

1. Build the complete proof and FCSolution on a separate runner. Save the complete or partial
   build under the exact tested commit; if the 300-minute build window expires, rerun the same
   commit to resume. An incomplete round fails the final gate rather than appearing verified.
2. On a fresh checker runner, compile the trusted extracted challenge and definitions, install pinned tools,
   restore proof products, restore the separately compiled challenge, and run Comparator through
   landrun under an unprivileged systemd service. AF_UNIX is restricted. The checking job does
   not compile the R4 solution outside the sandbox before Comparator acceptance.
3. Independently replay the whole original R4 environment using `leanchecker --fresh`.

Comparator success additionally requires exact success lines and exact axiom lines for the FC
named wrapper and the original R4 theorem. Failed receipts are also uploaded. All artifact
retention is 90 days. The final gate requires all three jobs to succeed. This workflow has
checked the FC target in the private verification repository and on public `main`.
Runner preparation and swap helpers live in `comparator/prepare-runner.sh` and
`comparator/add-swap.sh`; no separate root `ci/` folder is needed.

To build and inspect the original R4 proof locally, from the repository root:

```bash
cd lean
lake exe cache get
lake build R4Initial.FinalTheorem R4Initial.StatementSanity
lake env lean Verify.lean
LEAN_BIN=$(dirname "$(elan which lean)")
lake env "$LEAN_BIN/leanchecker" --fresh R4Initial.FinalTheorem
```

## Preserve a completed public run

Only after public `main` CI succeeds, archive the completed attempt using its actual IDs:

```bash
python3 comparator/archive-run.py \
  --repo KitaKen1/smooth-isometric-embeddings-r4 \
  --run RUN_ID --attempt ATTEMPT --expected-commit TESTED_COMMIT \
  --public-success-only \
  --output ComparatorLogYYYYMMDD/RUN_ID-attemptATTEMPT
```

Authentication uses `GH_TOKEN` or the existing Git credential helper; credentials are not saved.
The archive preserves original artifact ZIPs, all extracted receipts, original complete workflow
log ZIP, complete job logs, API metadata, artifact IDs/digests/expiry, and `SHA256SUMS`.
The downloaded ZIP digest must equal the GitHub artifact digest. A successful run must contain
`status.txt: PASS`, both Comparator success messages, target axiom lines, and the tested commit.
Existing archive directories are not overwritten. `--public-success-only` rejects a private,
failed or non-main run before writing evidence. Keep private and failed-run troubleshooting
archives in the separate local verification workspace, outside the initial publication candidate.

Keep three identities separate: original proof commit, tested CI commit, and the later archive
commit. The last cannot be embedded as its own commit hash; record it in the README/PR after
committing the archive. Local hashes are file identities, not signed GitHub attestations.

The local publication workspace retains historical R4 private-run records and FC preflight
records outside this repository candidate, under `local-verification/`. The historical run
concerns the original R4 Mathlib-only target. `ComparatorLog20261012/` holds the
records of the successful public FC-target run; they were assembled from the artifact ZIPs
and the workflow log archive of that run.

Official references: [Comparator at the pinned revision](https://github.com/leanprover/comparator/blob/ca04cfc72b550331658ec314bf47685281bfd4bf/README.md),
[FC contribution guidance](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md).

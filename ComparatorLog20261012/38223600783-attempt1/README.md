# Lean Comparator records: run 38223600783, attempt 1

The verification on public `main` completed successfully on 12 October 2026.
This folder keeps the original artifacts of that run and GitHub's API records in Git,
so that readers can inspect them after the Actions retention period ends.
The records refer to the tested commit below. The later commit that adds this
folder changes documentation and records only.

| Item | Recorded value |
|---|---|
| Repository | `KitaKen1/smooth-isometric-embeddings-r4` |
| Workflow | `R4 proposed FC target verification` |
| Run / attempt | `38223600783` / `1` |
| Branch / event | `main` / `workflow_dispatch` |
| Tested commit | `b8ddbd009791591c817d5b18cb4eb6dd30039853` |
| Target | `SmoothIsometricEmbeddingR4.smooth_isometric_embedding_R4` |
| Jobs | `build`, `comparator`, `replay`, `verification_status`: all `success` |
| Receipt status | `PASS` in all three receipts |
| Artifacts | `build-38223600783-1`, `comparator-38223600783-1`, `replay-38223600783-1` |
| GitHub artifact expiry | `2027-01-10T08:26:46Z` |

Original online records:
[run](https://github.com/KitaKen1/smooth-isometric-embeddings-r4/actions/runs/38223600783),
[tested source](https://github.com/KitaKen1/smooth-isometric-embeddings-r4/tree/b8ddbd009791591c817d5b18cb4eb6dd30039853).

## What is saved

| File or directory | Contents |
|---|---|
| [artifacts/](artifacts/) | The three original artifact ZIPs, byte for byte |
| [receipt/](receipt/) | Every member of the three ZIPs, extracted without alteration |
| [github/attempt.json](github/attempt.json) | GitHub API response for the run attempt |
| [github/jobs.json](github/jobs.json) | The four jobs and the conclusion of each of their steps |
| [github/artifacts.json](github/artifacts.json) | Artifact identities, sizes, expiry and the digests reported by GitHub |
| [github/repository.json](github/repository.json) | GitHub API response for the repository |
| [provenance.json](provenance.json) | Index written during archival: run, commits, artifact digests |
| [SHA256SUMS](SHA256SUMS) | Checksums of every other file in this folder, including this guide |

The complete workflow logs are not in this folder; GitHub serves them only to signed-in users.
The receipts contain the complete output of the build (`build.log`), of Comparator
(`comparator.log`) and of the axiom audit (`axioms.log`), and the report of the kernel replay
(`time.log`). The API responses are saved as retrieved, without credentials. This guide,
`provenance.json` and `SHA256SUMS` were generated locally during archival.

## How to check the result

1. Read [attempt.json](github/attempt.json) and [jobs.json](github/jobs.json). Match the run ID,
   the attempt, `head_sha`, the branch `main` and the `success` conclusions of the run, of the
   four jobs and of the step `Compare target, audit all target axioms, replay built-in kernel`.
2. Read [comparator.json](receipt/comparator-38223600783-1/comparator.json). The target is
   `SmoothIsometricEmbeddingR4.smooth_isometric_embedding_R4`, the challenge module is
   `Challenge` and the solution module is `FCSolution`. The permitted axioms are `propext`,
   `Classical.choice` and `Quot.sound`.
3. Read [input-check.json](receipt/comparator-38223600783-1/input-check.json) and
   [pins.json](receipt/comparator-38223600783-1/pins.json). The input check passed for the
   tested commit: the 2,511 files of the proof release have their recorded hashes.
   [Challenge.lean](receipt/comparator-38223600783-1/Challenge.lean),
   [FCTargetDefinitions.lean](receipt/comparator-38223600783-1/FCTargetDefinitions.lean) and
   [FCSolution.lean](receipt/comparator-38223600783-1/FCSolution.lean) are the files that
   were compared.
4. Read [comparator.log](receipt/comparator-38223600783-1/comparator.log). Its final output is
   `Lean default kernel accepts the solution`, `Your solution is okay!` and
   `Finished with result: success`.
   [status.txt](receipt/comparator-38223600783-1/status.txt) is `PASS`.
   [axioms.log](receipt/comparator-38223600783-1/axioms.log) reports
   `[propext, Classical.choice, Quot.sound]` for the target and for
   `R4Embedding.closedOrientableSurfaceEmbedding`.
5. Read [time.log](receipt/replay-38223600783-1/time.log). The kernel-only replay
   `leanchecker --fresh R4Initial.FinalTheorem` ended with `Exit status: 0`.
6. Inspect [comparator.yml](receipt/comparator-38223600783-1/comparator.yml) and the
   [launcher at the tested commit](https://github.com/KitaKen1/smooth-isometric-embeddings-r4/blob/b8ddbd009791591c817d5b18cb4eb6dd30039853/comparator/run-check.sh).
   A nonzero exit of Comparator or of the log pipeline fails the job. In
   [the pinned Comparator source](https://github.com/leanprover/comparator/blob/ca04cfc72b550331658ec314bf47685281bfd4bf/Main.lean),
   the comparison and the axiom check must pass before the kernel replay, and
   `Your solution is okay!` is printed only after all three.

These checks verify the affirmative answer (`answer(True)`, written as `True` in the
challenge) with the three standard axioms. The run used the built-in Lean kernel; no external
kernel was configured.

## Check the hashes

From a clone of this repository:

```bash
cd ComparatorLog20261012/38223600783-attempt1
shasum -a 256 -c SHA256SUMS
```

On Linux, `sha256sum -c SHA256SUMS` is an alternative. Every entry should report `OK`.
The checksums of the three ZIPs in `artifacts/` equal the `digest` values in
[artifacts.json](github/artifacts.json):

```text
build-38223600783-1          sha256:6bd31bf86431549696f87d32ef0a6b316bf60757b656a963ff4375853efa86bf
comparator-38223600783-1     sha256:fa251b98a5f1c8b56a6d8c480535fe63c9d14eb8e230878a55094eec05f96cdb
replay-38223600783-1         sha256:bd99113650bc64d8c86572bf1e965c9ca9064d8fbd1d96f445a3f0102afc53ba
```

The checksums of the downloaded ZIPs were compared with these digests before this folder was
committed.

## Limits

The saved API responses are unsigned snapshots. The hashes establish byte identity with the
digests recorded by GitHub and detect later changes of this folder; they are not a
cryptographic attestation of the execution. Readers can inspect the original GitHub record
while it is available, and can rerun the verification from the tested source as described in
[comparator/README.md](../../comparator/README.md).

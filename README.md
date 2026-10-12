# Lean proof of smooth isometric embeddings into four-space

The smooth isometric embedding problem for closed orientable surfaces asks for the following.

> (Conjecture) **Smooth isometric embeddings in four-space.** Every closed orientable smooth
> surface with any smooth Riemannian metric admits a smooth isometric embedding
> into Euclidean four-space.

This repository provides a Lean proof giving an affirmative answer to this conjecture.

This repository makes the following contributions:

1. **A Lean formalization of the conjecture statement in the style of Formal Conjectures.**
   [FClikelean/](FClikelean/) contains the definitions, theorem statement, external
   proof-link placeholder.
2. **The complete Lean 4 proof.**
   [R4Initial/FinalTheorem.lean](lean/stage07/R4Initial/FinalTheorem.lean) connects
   the initial-embedding construction to the analytic construction. Its complete
   pinned source dependencies are in [lean/](lean/).

## Formal Conjectures like targets

### FClikelean

The final theorem statement follows the Formal Conjectures format and is in
[FClikelean/SmoothIsometricEmbeddingR4.lean](FClikelean/SmoothIsometricEmbeddingR4.lean).

### Comparator target

The verification target is in [Challenge.lean](lean/Challenge.lean), and the proof is in
[FCSolution.lean](lean/FCSolution.lean).
Lean Comparator uses the challenge as the reference and checks that the proof establishes
the same statement with matching definitions and permitted axioms.

## Mathematical explanation (AI generated)

Write $\gamma(F)=F^*\delta_4$ for the metric induced by a map into $\mathbb R^4$.
The construction uses exact primitive realization, boundary propagation and uniform
spherical and metric preparation. The key geometric step is to preserve injectivity
while realizing each metric correction.

**1. Start with a short embedding.** A closed connected orientable smooth surface
is diffeomorphic to the boundary of a handlebody in $\mathbb R^3$. Inverse stereographic
projection gives an embedding into $S^3\subset\mathbb R^4$. Spherical preparation
perturbs it within a small $C^1$ neighborhood, retaining the embedding and making
its spherical second fundamental form vanish at the finitely many boundary crossings used below.
After scaling, obtain an embedding $F^0$ with $\gamma^0=\gamma(F^0)<g$.

**2. Prepare a finite sequence of metric corrections.** Uniform metric preparation
decomposes the positive deficit into smooth rank-one tensors supported on coordinate disks:

```math
\gamma^j=\gamma^0+\sum_{i=1}^j a_i^2\,dx_i\otimes dx_i,
\qquad \gamma^K=g.
```

The phases and sufficiently small increments are chosen so that
$`\mathrm{Hess}_{\gamma^{j-1}}x_j(\partial_{y_j},\partial_{y_j})>0`$
on each disk closure. Uniformity over the spherical preparation family allows the
phases and boundary curves to be fixed before the final initial map is chosen.
The prepared map satisfies the normal and boundary-crossing conditions needed for
the primitive construction.

**3. Realize one correction exactly.** For the current map $F$, set
$`P_p=\mathrm{span}(F_y(p),F_{yy}(p))^\perp`$ and $v=\pi_PF_x$.
Choose a periodic velocity loop $V$ in $P$ with mean $v$ and
$|V|^2=|v|^2+a^2$. Replacing the projected velocity $v$ by $V(p,x/z)$
adds the desired $`a^2\,dx\otimes dx`$ term at leading order. The exact realization
theorem supplies smooth maps $f_z$ satisfying

```math
f_z^*\delta_4=\gamma(F)+a^2\,dx\otimes dx,
\qquad df_z-dF=W_z+R_z,
```

where $W_z$ takes values in $P$, $f_z\to F$ in $C^0$, and
$`\|R_z\|_{C^0}\to0`$ as $z\downarrow0$. Outside the disk the maps converge in $C^2$.
The fixed metric identity bounds $df_z$ uniformly.

**4. Preserve injectivity.** The positive phase Hessian gives
$`\Gamma^x_{yy}=-\mathrm{Hess}_{\gamma(F)}x(\partial_y,\partial_y)\ne0`$.
The Gauss decomposition of $F_{yy}$ then shows that $P_p$ is complementary to
$dF_p(T_pM)$. In local coordinates choose a linear map $L_p:\mathbb R^4\to\mathbb R^2$
that kills $P_p$ and satisfies $L_p dF_p=\mathrm{id}$. Continuity of the transverse
planes, boundedness of $W_z$ and smallness of $R_z$ keep the derivative of $L_p f_z$
uniformly close to the identity on a sufficiently small coordinate ball.
The mean-value estimate gives a positive lower Lipschitz bound there, hence local
injectivity. Outside the disk, $C^1$ convergence gives the same local conclusion.
A finite cover gives a neighborhood of the diagonal in $M\times M$
on which pairs are separated. Away from that neighborhood, compactness and
injectivity of $F$ give a positive separation margin; the $C^0$ closeness of $f_z$
preserves it. Thus the exact map $f_z$ is an embedding for small enough $z$.

**5. Complete the finite induction.** Boundary propagation retains the preferred
normal, nonzero second fundamental form and conditions needed for later corrections
on these same exact maps. At each stage choose $z$ small enough for both this
propagation and embedding preservation. After $K$ steps,
$(F^K)^*\delta_4=\gamma^K=g$, and $F^K$ is a smooth embedding.
For a disconnected surface, apply the construction to its finitely many components
and translate their compact images to make them disjoint.

The [manuscript](PDF/smooth-isometric-embeddings-r4.pdf) gives the detailed analytic
hypotheses and estimates.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.34.1` | Complete R4 proof, pinned source dependencies, FC-target definitions, Challenge and FCSolution |
| [FClikelean/](FClikelean/) | FC reference base `v4.33.1`; compilation pending | FC-style statement and definitions |
| [comparator/](comparator/) | Checks the proof with `v4.34.1` | Input pins, comparison scripts, runner preparation and verification guide |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Private/public Comparator verification workflow candidate |
| [PDF/](PDF/) | — | Manuscript, editable TeX and existing timestamp evidence |

The final entry point is [FinalTheorem.lean](lean/stage07/R4Initial/FinalTheorem.lean).
The release contains 2,494 proof and dependency modules, largely pinned upstream libraries.
[THIRD_PARTY.md](THIRD_PARTY.md) records their sources and licenses.
[PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) identifies this assembled candidate.

## Verification

### Lean execution results

`#print axioms` for the final theorem reports only three axioms:
`[propext, Classical.choice, Quot.sound]` ([Verify.lean](lean/Verify.lean)).

### Lean Comparator check

The original private CI checked the proof against its
[challenge](lean/comparator/Challenge.lean) and accepted it using the same three axioms.

- **Within 90 days:** Check the CI results and artifacts ([see appendix](#certification-within-90-days-ci-results)).
- **After 90 days:** Check the archived logs and artifacts, to be added after public CI succeeds ([see appendix](#certification-after-90-days-archive)).

## Sources

- [Manuscript](PDF/smooth-isometric-embeddings-r4.pdf) and
  [TeX source](PDF/smooth-isometric-embeddings-r4.tex), public draft 1, 9 October 2026.
- [FC-style statement and its mathematical references](FClikelean/SmoothIsometricEmbeddingR4.lean).
- [Third-party formalization sources](THIRD_PARTY.md), including the analytic construction,
  differential geometry and surface classification.
- [Formal Conjectures contribution guide](https://github.com/google-deepmind/formal-conjectures/blob/8b3ec608d55559e384ad359b3c83f1c2112df448/CONTRIBUTING.md), at the recorded reference base.
- [Lean Comparator](https://github.com/leanprover/comparator/tree/ca04cfc72b550331658ec314bf47685281bfd4bf), at the pinned revision.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

## Appendix: timeline (AI generated)

| Date | Contributor | Contribution |
|---|---|---|
| Around 1950 | Chern | Proposed smooth isometric immersion of surfaces into four-space as a conjecture ([Gromov, footnote 6](https://www.ihes.fr/~gromov/wp-content/uploads/2018/08/nash-copy-Oct9.pdf#page=4)). |
| September 2026 | [OpenAI](https://github.com/openai/math/blob/main/overview.tex) | Proved that every closed Riemannian surface admits a smooth isometric immersion into four-space. |
| October 2026 | This repo | Extends OpenAI's construction to smooth isometric embeddings of closed orientable surfaces, with a [Lean proof](lean/FCSolution.lean). |

## Appendix: Verification by Lean Comparator on GitHub CI runner

Lean Comparator checks the theorem statement and dependent definitions against the challenge,
audits permitted axioms and verifies kernel acceptance.

GitHub CI runs checks in a fresh environment and records their results;
pinned inputs support reproducibility.

Lean Comparator and GitHub CI enable the following:

- **Verification in a web browser (within 90 days):** see [CI results](#certification-within-90-days-ci-results).
- **Verification from an archive (after 90 days):** see [archived records](#certification-after-90-days-archive).
- **Regenerate and verify the results yourself:** see [how to run the checks on your own CI runner](#reproduce-the-verification).

### Certification Within 90 days: CI results

Readers who want to inspect the verification results can check the Comparator execution
and axiom audit in the CI logs within 90 days. In particular,
`#print axioms R4Embedding.closedOrientableSurfaceEmbedding` reports the three axioms:

```text
'R4Embedding.closedOrientableSurfaceEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The [original private R4 CI run](https://github.com/KitaKen1/r4-verify-sandbox/actions/runs/38134361617)
passed; its logs and artifacts can be inspected on GitHub.
The [FC-target private CI run](https://github.com/KitaKen1/r4-verify-sandbox/actions/runs/38195392399)
also passed. The public main CI is pending.

### Certification After 90 days: archive

After the [90-day retention period](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/download-workflow-artifacts)
for CI logs and artifacts expires, readers can inspect the same results in the archive.
Archived CI run records, logs, artifacts and checksums also allow file integrity checks.
The archive link is pending public CI success.

### Reproduce the verification

To run the verification yourself, clone the repository, push it to a GitHub repository
you control, and run the [verification workflow](.github/workflows/comparator.yml) from
**Actions → Run workflow**. Your CI runner executes the same checks; compare the Comparator
result and three-axiom output with the recorded results.
Setup and commands are in [comparator/README.md](comparator/README.md).


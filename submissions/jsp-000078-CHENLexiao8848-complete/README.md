# JSP-000078: complete historical-route Lean formalization

This submission requests **Justin Sun Prize consideration for a completed independent formalization** of Gyárfás's finite-graph theorem and its historical structural proof. It preserves [PR #517](https://github.com/TheJustinSunPrize/awards/pull/517) and [PR #581](https://github.com/TheJustinSunPrize/awards/pull/581) as earlier immutable records; neither is closed, overwritten, or modified by this package.

## Completed result

For every finite simple graph G with exactly k distinct odd simple-cycle lengths, **χ(G)≤2k+2**. For every natural k, the complete graph on 2k+2 vertices attains the bound. The package also proves **Gyárfás's structural Theorem 1**: a vertex-2-connected graph with exactly k≥1 odd cycle lengths and minimum degree at least 2k+1 is complete on exactly 2k+2 vertices.

| Result | Declaration in namespace JSP000078 |
| --- | --- |
| Exact-k chromatic bound | `chromaticNumber_le_of_card_oddCycleLengths_eq` |
| Proper finite coloring | `colorable_of_card_oddCycleLengths_le` |
| Structural Theorem 1 | `gyarfas_structural_theorem` |
| Full structural proposition | `historicalGyarfasStructuralTheorem` |
| Universal sharpness | `oddCycleLengths_bound_sharp` |
| Zero case | `isBipartite_iff_oddCycleLengths_eq_empty` |

Main now derives its coloring from the proved historical structural theorem through vertex-count induction and universe transport. Its 151-module local dependency closure excludes the earlier DFS proof modules. All eight historical lemmas, including the previously incomplete Lemma 6 and singleton endpoint case, are integrated. No structural, path-family, counting, or coloring conclusion remains as a premise of the final numerical theorem.

## What is new since #581

The mathematical library has **49 new modules, six modified modules, and 103 unchanged modules** relative to #581. It contains 158 Lean files, plus the separate Audit.lean entry point (159 total). New work includes the full Lemma 6, longest-outside-path and endpoint reduction, singleton fan contradiction, complete structural theorem, independent bipartite base, separator coloring, and historical structural-to-coloring integration.

The completed finite numerical theorem and historical route are the claimed scope. The 2021 consecutive-length strengthening, arbitrary infinite-graph extension, and separate full equality/block classification are not additional exports of this package. Related submissions #130 and #458 cover a broader arbitrary-graph/equality statement using existing finite work; the precise contribution comparison is in [COMPARISON.md](COMPARISON.md).

## Verification and release

The frozen source rebuild passes **1,667 Lake jobs**. Standalone numerical/structural type checks, axiom audits, source scans, and full mathematical-module replay are documented in [VERIFICATION.md](VERIFICATION.md). These are reproducible submitter-side checks through the standard Lean kernel, not an official award or an independently implemented checker attestation.

Run from this directory with elan installed:

```bash
lake exe cache get
python3 verify.py
```

Lean: `leanprover/lean4:v4.34.0`. Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`, with all transitive revisions locked. No source-paper PDFs, dependency caches, or prebuilt project artifacts are distributed.

Release archive and immutable tag: [jsp000078-complete-20260917](https://github.com/CHENLexiao8848/awards/releases/tag/jsp000078-complete-20260917). The release carries source and evidence archives plus SHA-256 checksums. See [CLAIMS.md](CLAIMS.md), [STATEMENT.md](STATEMENT.md), [PROOF.md](PROOF.md), [SOURCE_RECONSTRUCTION.md](SOURCE_RECONSTRUCTION.md), and [PROVENANCE.md](PROVENANCE.md).

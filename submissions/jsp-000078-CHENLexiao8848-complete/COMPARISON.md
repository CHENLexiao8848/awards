> Historical snapshot: this document originally described the finite package at e5fff3632957cbd00dec7029b5756a256c263d93. The current full-scope revision supersedes its finite-only exclusions; see [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) and [README.md](README.md). Earlier claims and verification results remain dated evidence, not results for the new revision.

# Contribution comparison

## Records inspected

- [#130](https://github.com/TheJustinSunPrize/awards/pull/130): MaxwellLaw, pinned `524c5971113fb0405e90534e5709093de7b43f3f`. It declares reuse of 35 finite proof modules from plby/lean-proofs commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- [#458](https://github.com/TheJustinSunPrize/awards/pull/458): randyxian08, pinned `3aeab0ca401764f2738230427142ba74ba79bc89`. It also reuses the finite proof and documents its relation to #130.
- Own #517 and #581, pinned in CLAIMS.md.

This comparison inspected published descriptions, theorem source, build/axiom/replay evidence, and principal finite structural modules. It is not a fresh independent compilation of the competing packages or an adverse soundness finding. Existing complete proof evidence is acknowledged.

## Scope and implementation

| Topic | #130 / #458 | Completed submission here |
| --- | --- | --- |
| Finite upper bound | Existing finite proof, including a DFS-based upper bound | Independent historical structural proof followed by coloring induction |
| Finite structural theorem | Present in incorporated finite source | Independently developed and now fully integrated, with all endpoint cases |
| Arbitrary infinite vertex types | Compactness extension present | Finite types only; no infinite extension claimed |
| Full equality iff a complete subgraph occurs | Present | Universal sharpness examples proved; the separate full iff is outside scope |
| Source-boundary repairs | Some corrected endpoint/orientation arguments are already present | Explicit source reconstruction, one-hub rigidity, shared-edge and singleton completions |
| Reuse | Finite mathematical modules deliberately reused with attribution | Mathematical modules independently developed in the user's project; no copied modules from those submissions |
| Toolchain | Lean/Mathlib 4.33.0 in inspected revisions | Lean/Mathlib 4.34.0 |

The completed claim is not that no earlier proof exists. It is that this package now supplies its own entire finite structural-to-coloring route and specific standalone interfaces whose merit and attribution should be assessed directly. File counts, model usage, or byte differences alone are not originality criteria.

## Specific comparison anchors

The earlier finite source's `Structural.gyarfas_structural` already proves a complete structural theorem; its `DFSUpper.NormalTree` and associated coloring lemmas already contain the general DFS idea. `Structural/BoundaryApplication.differentNeighborhoodNoChordBoundary` explicitly retains the endpoint-cardinality orientation. These themes are not claimed absent from previous work.

The present `odd_cycle_length_eq_of_outside_hub` exports single-hub rigidity with 2k selected neighbors and no global degree/independence/maximality assumptions. `two_large_endpoint_attachment_sets_impossible` similarly removes global hypotheses from a reusable boundary statement. The historical-to-coloring route now also handles separators and the no-odd-cycle base independently of the initial DFS theorem. These exact interfaces and proof decompositions are the requested comparison targets.

## Verifiable increment over own #581

The final mathematical library has 49 added modules, six modified modules, and 103 unchanged modules relative to #581. New modules close Lemma 6, shared/singleton fan cases, longest outside path endpoint contradictions, and structural/coloring integration. Main's import closure contains 151 local modules and excludes `Coloring`, `DepthFirst`, `Parity`, and `OddCycles`, the old DFS route. The exact delta and hashes are in evidence/contribution-delta.json and evidence/source-manifest.json.

The new submission has a distinct branch and directory. No file or public statement in #517 or #581 is overwritten. The official assessment may consider overlap, reuse boundaries, independent contribution, and priority separately from mathematical correctness.

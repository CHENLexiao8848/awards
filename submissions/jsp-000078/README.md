# JSP-000078: sharp odd-cycle-length chromatic bound

This submission provides a Lean 4 proof of the exact numerical theorem associated with JSP-000078: for every finite simple graph G, if k counts its distinct odd simple-cycle lengths, then its chromatic number is at most 2k+2. The bound is attained for every natural k by the complete graph on 2k+2 vertices.

This is a request for formalization intake and independent verification. It does not claim official verification, award eligibility, or an award.

## Main results

- `JSP000078.chromaticNumber_le_of_card_oddCycleLengths_eq`: exact-k form.
- `JSP000078.chromaticNumber_le_two_mul_oddCycleLengths_card_add_two`: direct cardinality form.
- `JSP000078.oddCycleLengths_bound_sharp`: matching example for every k.
- `JSP000078.isBipartite_iff_oddCycleLengths_eq_empty`: k=0 characterization.
- `JSP000078.card_oddCycleLengths_ge_of_chromaticNumber_eq`: modern lower bound.

The numerical proof uses an independently verified depth-first coloring argument. Additional files reproduce the two-disjoint-links construction and Gyárfás's published Lemma 1. The rest of his stronger structural proof is not included in this frozen submission. That limitation leaves no missing premise in the numerical theorem.

## Reproduce

Run from this directory with elan installed:

```bash
lake exe cache get
lake build
lake env lean JSP000078/Main.lean
lake env lean JSP000078/AxiomAudit.lean
lake env lean Audit.lean
```

Lean is pinned to `leanprover/lean4:v4.34.0`; Mathlib is pinned by `lake-manifest.json` to `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0). No project build products or paper PDFs are distributed.

See [STATEMENT.md](STATEMENT.md), [PROOF.md](PROOF.md), [PROVENANCE.md](PROVENANCE.md), and [VERIFICATION.md](VERIFICATION.md). The [source manifest](evidence/source-manifest.json) records SHA-256 hashes and byte counts for the frozen Lean sources.

# JSP-000078: structural formalization and prize consideration

This submission requests **Justin Sun Prize consideration for original formalization contributions** to JSP-000078: a complete verified finite-graph chromatic bound and universal sharpness, seven historical structural lemmas, and independently derived reusable rigidity and exceptional-case results. It is a new, separately reviewable submission that preserves [PR #517](https://github.com/TheJustinSunPrize/awards/pull/517).

The specific originality and priority claims are set out in [CLAIMS.md](CLAIMS.md), with an evidence-based [comparison to related work](COMPARISON.md). The submitter requests substantive assessment of these contributions and an attribution/priority determination from the immutable record.

## Verified contributions

| Contribution | Exported Lean declaration |
| --- | --- |
| Exact finite bound: k distinct odd cycle lengths imply χ(G)≤2k+2 | `JSP000078.chromaticNumber_le_of_card_oddCycleLengths_eq` |
| Bound attained for every natural k | `JSP000078.oddCycleLengths_bound_sharp` |
| Historical Lemmas 1, 2, 3, 4, 5, 7, 8 | Seven `GyarfasLemma*.lean` modules, mapped in STATEMENT.md |
| One-hub rigidity: 2k selected neighbors on an odd cycle force length 2k+1 for k≥2 | `JSP000078.odd_cycle_length_eq_of_outside_hub` |
| Two large endpoint attachment sets are impossible under the k-length bound | `JSP000078.two_large_endpoint_attachment_sets_impossible` |
| Shared-endpoint-edge boundary, including k=1 | `JSP000078.shared_endpoint_edge_exception` |

The last three are precise reusable results with their own hypotheses, not completion flags or assumed certificates. Definitions and full signatures are checked in `Audit.lean`.

## What changed since PR #517

The mathematical library grows from 24 to 109 Lean files: 85 added modules and two updated entry/audit files, with 22 existing modules unchanged. A separate `Audit.lean` brings the submitted Lean file count to 110. The earlier PR supplied the numerical bound, universal sharpness, and historical Lemma 1. This submission adds Lemmas 2, 3, 4, 5, 7, and 8, including all their imported geometric/counting proofs. These counts describe the reproducible change, not a proposed scoring formula.

The snapshot rebuild passes 1,622 Lake jobs. Exact-type/axiom checks and standard Lean kernel replay evidence are in [VERIFICATION.md](VERIFICATION.md). The same Lean kernel is used; no official independent-checker attestation is implied.

## Scope

The exact finite numerical theorem and universal sharpness are complete. The full source-context statements of the seven listed lemmas are proved. The general one-chord equal-neighbor case of historical Lemma 6 and final assembly of Gyárfás's stronger global structural theorem remain outside this frozen snapshot; the shared-endpoint-edge subcase is proved. This scope is stated explicitly so that completed contributions can be assessed on their actual merits.

Mathematical discovery is credited to Gyárfás (1992); the 2021 Gao-Huo-Ma strengthening is supplementary. Formalization assistance and licenses are in [PROVENANCE.md](PROVENANCE.md).

## Reproduce

```bash
lake exe cache get
python3 verify.py
```

Lean: `leanprover/lean4:v4.34.0`. Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0), pinned with transitive dependencies. No `.lake` cache, prebuilt project artifacts, source-paper PDFs, or private information is distributed.

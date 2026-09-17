# Provenance and attribution

## Mathematical result

The numerical theorem is the Bollobás-Erdős conjecture proved by András Gyárfás in 1992. The supplementary Gao-Huo-Ma paper strengthens the cycle-length distribution in 2021. This submission claims Lean formalization of an existing result, not a new mathematical discovery or authorship of those published theorems.

## Formalization

Recipient identifier pending confirmation: RECIPIENT-JSP-000078-A. The submitting GitHub account supplied the task and authorized public submission. No recipient confirmation, committee endorsement, award, or payment entitlement is asserted.

The formalization was developed with substantial OpenAI Codex / GPT-6-based AI assistance, including mathematical reconstruction, Lean source drafting, compiler repair, documentation, and separate AI review passes. An earlier unverified draft in the user's adjacent project was copied, repaired, and compiled. The independent DFS proof was reconstructed and verified during that workflow. The historical two-link and Lemma 1 modules were added during subsequent work. AI review passes are not independent official human verification or independent kernel implementations.

This submission freezes the checked import closure at preparation time. Concurrent exploratory historical-proof work is excluded; the source manifest identifies exactly what is submitted.

## Related prior submission

During intake preparation, the existing [PR #130](https://github.com/TheJustinSunPrize/awards/pull/130) was found. It presents an extension of an existing finite formalization to arbitrary vertex types and a stronger equality characterization. This package is an additional independently developed finite numerical proof and limited historical-proof reconstruction. It does not claim priority, novelty over that submission, coverage of arbitrary infinite graphs, or the stronger equality characterization. None of PR #130's proof modules was copied into this package. Maintainers should assess overlap and contribution scope.

## Third-party material and licensing

The source papers were inspected locally but their PDFs and extracted text are not redistributed. Bibliographic links and original summaries are provided in STATEMENT.md. Mathlib and other dependencies are referenced by pinned revisions and retain their original licenses; their source and build caches are not included.

First-party Lean source and audit scripts in this directory are provided under the accompanying MIT license. First-party submission prose is provided under CC BY 4.0, consistent with the host repository's content license. Mathematical attribution remains with the original sources.

> Historical snapshot: this document originally described the finite package at e5fff3632957cbd00dec7029b5756a256c263d93. The current full-scope revision supersedes its finite-only exclusions; see [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) and [README.md](README.md). Earlier claims and verification results remain dated evidence, not results for the new revision.

# Provenance and attribution

## Mathematical authorship

The original finite numerical theorem and structural result are due to András Gyárfás (1992), resolving the Bollobás-Erdős question and Gallai's stronger formulation. The consecutive-length strengthening is due to Gao, Huo, and Ma (2021). This submission seeks recognition for formalization and its specific independent proof contributions; mathematical discovery attribution is preserved.

## Development and assistance

The submitting GitHub account CHENLexiao8848 supplied the task, source materials, and authorization to publish and request prize consideration. Pending recipient confirmation, the record uses RECIPIENT-JSP-000078-A. No identity confirmation, committee decision, award, or payment is asserted.

Development used substantial OpenAI Codex / GPT-6-based AI assistance for mathematical reconstruction, Lean source drafting, compiler repair, and documentation. Separate AI review passes examined source fidelity, hypotheses, dependency cycles, and axiom lists. These are not independent human referee or official prize-verifier attestations.

The initial numerical core reused an unverified draft discovered in another project of the same user and then repaired and compiled it. The historical infrastructure and final structural/coloring route were subsequently developed in the user's proof workspace. No mathematical module was copied from the packages in #130 or #458. The final Main dependency closure does not use the initial DFS proof.

This package freezes the final source in a separate checkout and rebuilds/replays it. The original working project and prior submission checkouts remain intact. #517 and #581 preserve the earlier public history; this submission records the newly completed work at its own commit and release.

## Licensing

First-party Lean source and verification scripts in this directory are MIT-licensed under LICENSE. First-party documentation is CC BY 4.0. Lean, Mathlib, and other dependencies retain their original licenses and are referenced by exact revisions, not redistributed as caches. The kernel-replay command runs the official LeanChecker source in the pinned Lean distribution; no competing submission's replay driver is copied.

The source-paper PDFs and extracted text, private correspondence, account credentials, identity documents, payment details, and personal filesystem paths are excluded. Public mathematical references and original explanations provide source correspondence.

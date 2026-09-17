# Full-scope verification, 2026-09-17

The public verify.py entry completed successfully on the final proof sources: source-manifest checks and forbidden-construct scan; default build and retained alternative build; original Main/Sharpness/AxiomAudit/Audit; new FullScopeAudit; and full namespace kernel replay. All commands exited zero.

- New final theorem: JSP000078.erdos_58, with arbitrary Type u vertices, finite odd-cycle-length set, ncard at most k, upper bound and equality iff.
- FullScopeAudit.lean elaborates the exact source statement, an infinite natural-number domain, the k=0 iff, an empty vertex domain, and fewer-than-k lengths.
- Eight new audit declarations have exactly propext, Classical.choice and Quot.sound in their transitive axiom lists. Original18+8 audit inventories also passed.
- The official pinned Lean kernel replayed all **160 mathematical modules** (and the namespace root/audit module). verify.py compares the reported replay names against the full mathematical-module list and rejects omissions. The namespace invocation avoids repeatedly enumerating the entire search path for every module.
- The original frozen baseline rebuilt successfully (1667 Lake jobs); new full integration and public entry build succeeded. Original first-party mathematical modules were unchanged. Shared pinned Mathlib/dependency caches were reused; local proof modules were compiled from source.

Logs are evidence/reproduction-build.log, reproduction-alternative.log, reproduction-main.log, reproduction-sharpness.log, reproduction-axioms-full.log, reproduction-audit.log, reproduction-full-scope.log and reproduction-replay-full.log. The manifest full-scope-artifacts.json supplies IDs, SHA-256 and byte counts. Empty output logs correspond to successful quiet Lean checks, not missing execution; verify.py stops on nonzero exit.

An initial per-module-list replay was interrupted during performance investigation. Its exploratory batch logs are excluded from current acceptance evidence; the subsequent full-namespace run above completed and is the acceptance record. A separate native bundled-checker replay of General also exited0. The public helper still uses the supplied official LeanChecker.lean, with the same Lean kernel and imported dependency trust.

Source files and Git published bytes are normalized to LF; source-manifest.json binds the exact bytes. .gitattributes enforces LF for fresh clones. This addresses platform-dependent line ending mismatches without changing mathematical content.

Separate agent source/statement review reported no semantic scope gap. All review/verification here is submitter-side or AI-assisted; it is not independent human verification, an organizer attestation, a fresh replay of Mathlib or a second kernel implementation. Earlier release evidence remains dated historical evidence.


# JSP-000078: complete original theorem

The final theorem is **JSP000078.erdos_58** in [General.lean](JSP000078/General.lean). For any simple graph on an arbitrary vertex type, finitely many odd simple-cycle lengths with cardinality at most k imply a chromatic bound of 2k+2, with equality if and only if the graph contains K_(2k+2). The statement includes k=0, empty and disconnected graphs, and infinite vertex types without countability or local-finiteness assumptions.

## Proof and attribution

The finite bound remains derived from this project's complete historical Gyárfás structural proof. [FiniteEquality.lean](JSP000078/FiniteEquality.lean) adds the strict 2k+1-color bound when the extremal clique is absent. General.lean applies that result and compactness twice to obtain the full original statement.

Compactness is attributed reuse from MaxwellLaw's #130, based on Mathlib's Rado selection lemma. The standard cycle definitions and final statement are credited to The Formal Conjectures Authors. The existing first-party historical proof is retained. [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) identifies exact versions, licenses and contribution boundaries.

Earlier #130/#458 already supply complete arbitrary-graph formalizations. This package requests assessment of its concrete historical implementation, structural interfaces and added finite strict-coloring/bridge work, not first mathematical discovery or first formalization. OpenAI Codex assistance is disclosed.

## Reproduce

Lean 4.34.0; Mathlib 5ed2965256430c3649e86755f9576b54eca72435, with transitive revisions locked. From this directory:

```bash
lake exe cache get
python3 verify.py
```

The verifier checks source hashes and forbidden constructs, builds the full default target and retained alternatives, checks original/new signatures and axioms, and replays all 160 mathematical modules. [FullScopeAudit.lean](FullScopeAudit.lean) checks the exact arbitrary-universe statement and boundary interfaces. It trusts imported pinned Mathlib; it is not a from-source rebuild of all dependencies or a second checker implementation.

Current-run evidence is in reproduction logs and [FULL_SCOPE_VERIFICATION.md](FULL_SCOPE_VERIFICATION.md). Submitter-run checks and separate agent review do not establish organizer approval, independent human verification or an award.

## History and submission

The previous finite package remains at e5fff3632957cbd00dec7029b5756a256c263d93 and in the [original release](https://github.com/CHENLexiao8848/awards/releases/tag/jsp000078-complete-20260917). Earlier #517/#581 and historical contribution records are preserved. New equality and arbitrary-graph results are not backdated.

Existing awards PR #649 is revised to catalog text and external references only. The proof is preserved on a separate public named branch; the catalog commit is not the proof version.

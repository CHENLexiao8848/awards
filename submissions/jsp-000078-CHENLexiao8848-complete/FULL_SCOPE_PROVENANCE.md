# Full original scope: sources and contribution boundaries

This revision extends the previously published finite historical-route package at e5fff3632957cbd00dec7029b5756a256c263d93. The old commit, release jsp000078-complete-20260917 and PRs #517/#581 remain historical records. The full original theorem is first claimed by this package only in this new revision; it is not backdated.

## New proof work

- FiniteEquality.lean derives a 2*k+1-coloring from the absence of K_(2*k+2), using this project's already proved Gyárfás structural theorem, vertex deletion and separator recoloring. It includes k=0, fewer than k lengths and arbitrary finite vertex universes.
- General.lean connects the finite Finset representation to the standard set of odd simple-cycle lengths, transports induced cycles, and applies compactness twice to prove the full upper bound and equality iff on arbitrary vertex types.
- FullScopeAudit.lean checks the exact original signature and edge-case interfaces. No old first-party mathematical module was replaced or imported from an external complete proof.

## Reused sources

Compactness.lean is adapted from [MaxwellLaw's fixed source](https://github.com/MaxwellLaw/awards/blob/524c5971113fb0405e90534e5709093de7b43f3f/submissions/jsp-000078-MaxwellLaw/Jsp000078/Compactness.lean). Changes are the namespace and local provenance reference. Copyright 2026 MaxwellLaw; Apache-2.0; Codex assistance disclosed by that source. Its proof uses Mathlib's Rado selection lemma, formalized by Bhavik Mehta. The compactness argument is attributed reuse, not a new contribution claimed here.

CycleLengths.lean is copied from the [same fixed package](https://github.com/MaxwellLaw/awards/blob/524c5971113fb0405e90534e5709093de7b43f3f/submissions/jsp-000078-MaxwellLaw/Jsp000078/CycleLengths.lean), retaining Copyright 2026 The Formal Conjectures Authors and Apache-2.0. It supplies the standard simple-cycle-length definitions absent from this pinned Mathlib version. General.lean's final statement follows the [Formal Conjectures Erdős 58 statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/58.lean), whose authors and Apache-2.0 notice are credited. LICENSE-APACHE-2.0 contains the applicable license text. Existing first-party source remains under the package's MIT license; documentation remains CC BY 4.0.

The mathematical result is due to András Gyárfás (1992), following the Bollobás–Erdős problem. Earlier complete arbitrary-graph formalizations include #130 and #458. This revision makes no global-first formalization or original mathematical discovery claim. The review request concerns the concrete historical implementation and the added finite strict-coloring/bridge work, with attributed reuse disclosed. Source differences alone are not proof of independent provenance.

Substantial OpenAI Codex assistance was used. Separate agent checks and submitter-side compilation/replay do not constitute independent human review, organizer acceptance, award eligibility or a right to payment.


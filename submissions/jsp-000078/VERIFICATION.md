# Local reproduction evidence

This document records submitter-side checks of a frozen proof package. It is not an official verification attestation and does not claim independent-checker certification, an isolated offline run, award eligibility, or a payment decision.

## Frozen scope

The package contains the full import closure of JSP000078.Main, universal sharpness, and the checked historical two-link and Gyárfás Lemma 1 modules, plus an audit entry point. Experimental later historical lemmas from the ongoing development workspace are excluded. There are 25 Lean source files including the two root entry points. The exact sources are listed with SHA-256 and byte counts in [source-manifest.json](evidence/source-manifest.json).

## Toolchain and environment

- Lean 4.34.0, compiler commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b.
- Mathlib v4.34.0, commit 5ed2965256430c3649e86755f9576b54eca72435.
- Local architecture: arm64 macOS. No architecture-dependent computation is used in the proofs.
- Project build products were rebuilt in the submission directory. Pinned Mathlib/dependency caches were reused. Network access was not disabled, and dependencies were not rebuilt from source for this run. These limits are disclosed rather than recorded as successful offline verification.

## Checks

From this directory:

```bash
lake build
lake env lean JSP000078/Main.lean
lake env lean Audit.lean
```

All three commands exited 0. The frozen package build completed successfully with 1,237 jobs. The Main check was silent. Audit checked exact statement types and printed axiom dependencies for the exact-k theorem, universal sharpness, historical linking, and the published Lemma 1; every list contains only propext, Classical.choice, and Quot.sound. See [build output](evidence/lake-build.log), [Main check](evidence/main-check.log), and [types and axioms](evidence/axioms-and-types.log).

No task-created mathematical axiom, proof placeholder, unsafe bypass, or native-decide computation was found. The [placeholder scan](evidence/placeholder-scan.txt) covers all submitted Lean sources. Official repository validate, links, data build, and data check commands passed, and all 22 repository unit tests passed under Python 3.12.

## Specification review

The exact membership theorem counts distinct odd lengths of arbitrary simple cycles, with chords permitted. The exact-k chromatic theorem has only a finite simple graph and its cardinality equality as premises. Empty and disconnected graphs and k=0 are covered. The [statement comparison](STATEMENT.md) explains why the theorem is the original numerical result, separately from the stronger structural theorem and consecutive-length results.

The numerical proof is complete. Full reproduction of the stronger published structural proof remains outside this submission; the verified historical progress included here stops after Lemma 1. The original mathematical result is credited to Gyárfás. AI assistance and the limits of AI review are disclosed in [PROVENANCE.md](PROVENANCE.md).

## Official review still required

The maintainers must determine statement fidelity and verification sufficiency. No official two-checker audit or permanent DOI archive has been issued for this submission. The PR and pinned GitHub source revision provide intake evidence; they must not be described as an announced award or a completed formal verification record under the prize's schema. Existing award, candidate, recipient, and problem eligibility records are unchanged.

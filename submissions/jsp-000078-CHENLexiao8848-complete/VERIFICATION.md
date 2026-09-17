> Historical snapshot: this document originally described the finite package at e5fff3632957cbd00dec7029b5756a256c263d93. The current full-scope revision supersedes its finite-only exclusions; see [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) and [README.md](README.md). Earlier claims and verification results remain dated evidence, not results for the new revision.

# Frozen final verification

## Scope and exact source

The frozen package contains 158 project Lean files and one separate Audit.lean entry point: **159 Lean source files**. Of these, **156 mathematical modules** are replayed by the official Lean checker; JSP000078.lean, JSP000078/AxiomAudit.lean, and Audit.lean contain import/audit commands. The source manifest includes every Lean file, the verification script, and exact toolchain/configuration files.

All project modules were rebuilt in a separate submission directory from the frozen source. No project build products were copied from the development tree. Pinned upstream Mathlib/dependency caches were reused; this is not an offline source rebuild of all dependencies.

## Toolchain

- Lean 4.34.0, compiler commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b.
- Mathlib v4.34.0, commit 5ed2965256430c3649e86755f9576b54eca72435.
- Local platform: arm64 macOS. No architecture-dependent computation is used in the mathematical proof.
- Exact transitive dependencies: lake-manifest.json.

## Build and audits

The frozen full build completed successfully with **1,667 jobs**. The retained alternative DFS modules were also built separately (1,019 target jobs) but are not dependencies of Main.

The standalone Main, Sharpness, AxiomAudit, and Audit commands exited zero. The built exact final numerical theorem quantifies over arbitrary finite vertex types and has only the cycle-length cardinality hypothesis. The structural theorem has exactly the expected k≥1, vertex-2-connectivity, minimum-degree, and distinct-length assumptions.

The full AxiomAudit has **18 standard-only lists**. The extra Audit checks eight key final/dependency results, including the formerly missing Lemma 6 and the actual structural-to-coloring reduction. Every list is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Actual evidence: [build](evidence/lake-build.log), [alternative modules](evidence/alternative-modules.log), [Main](evidence/main-check.log), [sharpness](evidence/sharpness-check.log), [full axioms](evidence/axioms-full.log), and [explicit types and axioms](evidence/axioms-and-types.log).

## Kernel replay

The replay runs the official `LeanChecker.lean` supplied with the pinned Lean toolchain. It reloads module declarations, sends them to the Lean kernel, and compares generated constructors/recursors. It is run with two workers and bounded module batches to avoid excessive resource contention. No competing submission's checker code is reused.

The full mathematical-module inventory, each command, exit code, and duration are preserved in [kernel-replay.log](evidence/kernel-replay.log) and [kernel-replay-results.json](evidence/kernel-replay-results.json). The source inventory fixes exactly which final modules were replayed; the older #581 replay is not substituted.

**All 156 final mathematical modules passed kernel replay**, in 13 batches with exit code zero. This includes the completed historical structural and coloring modules, not only the earlier partial snapshot.

This is the same Lean kernel used for compilation, not a separately implemented checker or a complete fresh replay of Mathlib. It is reproducible supporting evidence, not official prize verification.

## Source integrity and dependence

[placeholder-scan.txt](evidence/placeholder-scan.txt) scans all 159 Lean files for sorry/admit, mathematical axiom declarations, unsafe declarations, native-decide/reduction shortcuts, external implementations, and kernel-check disabling. No matches were found. The Python scanner contains those words as search strings and is not imported by the proof. Positive detection probes verified the scanner detects representative forbidden constructs.

Main's recursive local import closure contains **151 modules** and excludes the old `Coloring`, `DepthFirst`, `Parity`, and `OddCycles` files. It imports the proved historical structure, historical coloring implication, and finite-model transport. Both conditional premises are supplied explicitly by proved results. Main does not import Sharpness. The closure list is in [main-local-dependencies.txt](evidence/main-local-dependencies.txt).

Source and evidence files have SHA-256 and byte counts in [source-manifest.json](evidence/source-manifest.json) and [artifacts.json](evidence/artifacts.json). The release provides a fixed source archive and independent checksum list at a tag pinned to the submitted commit.

## Reproduce

```bash
lake exe cache get
python3 verify.py
```

The script verifies hashes, scans source, runs the complete build and standalone checks, verifies axiom inventories, and replays every mathematical module using the pinned toolchain. Reproduction logs use separate filenames so original evidence remains intact. The toolchain's source component is required for the official LeanChecker invocation.

## Acceptance and limits

The finite numerical theorem, universal sharpness, all eight historical lemmas, full structural Theorem 1, and historical structural-to-coloring route are complete. No required mathematical proof dependency remains. Source corrections and local equivalent arguments are disclosed. The arbitrary infinite-graph extension, separate full equality/block classification, and 2021 consecutive-length strengthening are outside the claimed exports.

Official verification, assessment of independent contribution/priority, recipient confirmation, and an award decision remain for authorized reviewers. Existing prize records are not changed. The release and PR provide fixed public evidence rather than asserting a committee outcome.

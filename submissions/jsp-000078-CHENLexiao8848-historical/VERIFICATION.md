# Verification evidence for the structural submission

## Frozen package

The mathematical import closure contains 109 Lean files. A separate Audit.lean makes 110 submitted Lean source files. A dated frozen-source list, the final source/configuration manifest, and the contribution delta from #517 are under evidence/. The submission is independent of the live working directory; subsequent development does not change the frozen files.

## Toolchain

- Lean 4.34.0, compiler commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b.
- Mathlib v4.34.0, commit 5ed2965256430c3649e86755f9576b54eca72435, with locked transitive dependencies.
- Local platform: arm64 macOS.
- All submitted project modules were rebuilt in the separate submission directory. Upstream dependency caches were reused; this was not an offline rebuild of every dependency.

## Build and theorem audit

`lake build` completed successfully with **1,622 jobs**, including GyarfasLemmaEight and all imports. The saved [build log](evidence/lake-build.log) contains the actual compiler output.

`lake env lean Audit.lean` exited 0. The [type and axiom log](evidence/axioms-and-types.log) checks the numerical result, universal sharpness, incident-chord and path-family statements, arbitrary-neighbor endpoint theorem, independent-complement theorem, shared-attachment theorem, outside-hub rigidity, two-large-attachment obstruction, Lemma 8 wrapper, and shared-edge exception.

Each of the twelve audited final/structural axiom lists is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No project mathematical premise encodes an unproved claimed conclusion. In particular, the source-context Prop definitions have actual theorem proofs when listed as completed exports. The general Lemma 6 proposition remains explicitly unproved and is not used by a completed theorem.

## Source and bypass audit

The [source scan](evidence/placeholder-scan.txt) covers all 110 Lean files for proof placeholders, custom mathematical axioms, unsafe declarations, native-decide or reduction-oracle shortcuts, external implementations, and kernel-check disabling. All checks report no matches. The scanning script contains the patterns as data; it is not imported by Lean.

The standard `leanchecker` from the pinned official Lean distribution is used to replay the mathematical modules. It sends declarations to Lean's kernel again and checks constructors/recursors against the generated forms. No custom checker implementation is introduced into the proof. Actual replay commands/results are in [kernel-replay.log](evidence/kernel-replay.log) and [kernel-replay-results.json](evidence/kernel-replay-results.json).

**All 107 mathematical proof modules passed replay**, in 36 bounded batches, each with exit code 0. The two library/audit-only import modules contain no mathematical declarations and are checked by the ordinary build. Standalone Main and Audit checks also exited 0.

This is a second pass through the **same Lean kernel**, not a separately implemented independent checker. Imported Mathlib dependencies are trusted at their pinned versions; no official offline-verification or referee attestation is represented as completed.

## Reproduction

After `lake exe cache get`, run `python3 verify.py`. It checks source hashes and forbidden proof constructs, rebuilds, checks Main and Audit, validates all twelve axiom lists, and replays all mathematical modules in bounded batches through the standard Lean checker. Reproduction logs use separate filenames so the captured submission run remains preserved.

## Mathematical coverage

The finite numerical bound, universal sharpness, seven listed historical lemmas, and standalone rigidity/boundary results are proved. The general Lemma 6 and the stronger global structural assembly remain outside this snapshot. STATEMENT.md describes all hypotheses; CLAIMS.md requests prize consideration for the actual verified contributions without treating local tests as an award decision.

## External review

The public evidence archive is the immutable submission commit in the contributor fork. Evidence files have IDs, SHA-256 hashes, and byte counts in artifacts.json. Formal prize verification, assessment of originality/priority, and recipient confirmation remain decisions for the maintainers and committees. No existing catalog, candidate, recipient, or award status is modified by this submission.

# JSP-000562 — verification evidence review, 2026-09-26

This report reviews the existing verification of [PR #745](https://github.com/TheJustinSunPrize/awards/pull/745). No Lean build, axiom command or kernel replay was rerun for this report. The selected proof commit remains **`ea6e7fc0a5893edd13335acc4e1ebd00cd261782`** in `CHENLexiao8848/awards`, branch `codex/four-lean-proofs-20260917`, package `proofs/chen-lexiao-four-20260917/proof`.

## Evidence integrity

All 61 fixed package files were checked against their immutable Git blob IDs. Recomputed SHA256 values matched all **18 input records, 41 command logs and 60 checksum entries**. Before/after input hashes agree. The [published report](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/report.json) has SHA256:

```text
649e83ca5bb9de632d9141328820813bc800cac889d9a2955e7f235136617a06
```

The [checksum manifest](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/SHA256SUMS) and [fixed verifier](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verify.py) allow these checks to be repeated. Hash agreement establishes consistency of published source and submitter-provided transcripts; it does not independently establish execution of the historical commands.

## Recorded execution

The existing local run lasted from **2026-09-17T09:48:38.370887Z to 09:55:31.777885Z** and reports `passed`, script exit 0. It records Lean 4.34.0 on Apple arm64, Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. All nine dependency revisions and clean tracked-file states before and after match the [fixed lock file](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/lake-manifest.json).

| Check | Recorded result |
|---|---|
| [Project clean](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/clean.log) | `lake clean pinnacleLean`, exit 0. |
| [Build](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/build.log) | `lake build`, exit 0, 2,055 jobs; explicitly Built `Problems.JSP000562` and `Problems.JSP000562Audit`. |
| [Public audit](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/axioms.log) | `lake env lean -DwarningAsError=true Audit.lean`, exit 0. |
| [Module replay](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/kernel-replay.log) | `lake env leanchecker --verbose Problems`, exit 0; names both JSP-000562 modules. |

The shared package contains four problems and eight local modules. The clean build covers the local modules while retaining dependency caches. Replay uses the same Lean kernel and imported pinned dependencies, not an independently implemented checker or a fresh replay of all Mathlib.

## JSP-000562 axiom boundary

The [public audit file](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Audit.lean) and saved axiom log cover these **five** JSP-000562 targets:

```text
JSP000562.fourthDensity_is_density
JSP000562.density_fourth_13
JSP000562.density_fourth_17
JSP000562.density_fourth_19
JSP000562.jsp000562
```

Each has exactly `[propext, Classical.choice, Quot.sound]`. The separately built [JSP-000562 audit module](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000562Audit.lean) additionally prints `JSP000562.isFourthPrimeFactor_iff_primeFactors` and `JSP000562.fourthDensity_strict_valley`, with the same three axioms in the build log. Thus there are **seven distinct JSP-000562 declarations** across these two audits. The report's total of 11 public-audit targets includes six targets for other problems.

The [fixed proof](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000562.lean) proves actual counting-function densities for every prime and rejects unimodality using the exact strict valley at 13, 17 and 19. The `Nat.primeFactors` bridge concerns nonzero integers, matching the counted domain `(0,N]`. The final theorem discharges the intermediate density-existence premise. This is a negative witness at **k = 4**, not a classification of every k.

## CI distinction and limits

The three successful GitHub runs at the selected SHA are [Build data](https://github.com/CHENLexiao8848/awards/actions/runs/35227014559), [Data consistency](https://github.com/CHENLexiao8848/awards/actions/runs/35227014547), and [Validate](https://github.com/CHENLexiao8848/awards/actions/runs/35227014940). Their fixed workflow files perform catalog/repository checks; **none runs Lean or the proof verifier**. They must not be presented as proof-build CI. The proof evidence reviewed here is the historical local clean run.

No mismatch requiring a new build was found. This report establishes neither independent human mathematical review, authorship priority, eligibility nor an award decision. Documentation may be updated separately while the proof SHA above remains the exact verification target.

# Four JSP Lean formalizations

This package contains complete Lean proofs of the precisely stated catalog targets
for **JSP-000633, JSP-000562, JSP-000690, and JSP-000301**. It is submitted and
organized by **CHEN LEXIAO** ([CHENLexiao8848](https://github.com/CHENLexiao8848)),
with substantial AI assistance through Codex in implementation, verification, and
documentation. Mathematical authorship, prior formalization, and the present
submission contribution are distinguished in [CONTRIBUTIONS.md](CONTRIBUTIONS.md).

## Exact statements and proof endpoints

| Problem | Statement proved here | Final declarations | Present implementation contribution |
| --- | --- | --- | --- |
| JSP-000633 / Erdős 772 | For every finite set `A` of natural numbers whose ordered two-term representation counts are at most `k`, there is a Sidon `B ⊆ A` with `|A|² ≤ (4 + 24k)|B|³`. Diagonal representations and repeated Sidon summands are included. This yields a positive constant times `|A|^(2/3)`, exceeds every fixed multiple of `sqrt(|A|)` eventually, and yields the fixed exponent `1/2 + 1/12`. | `JSP000633.finite_bound`, `sidon_subset_two_thirds`, `answer_sqrt`, `answer_positive_power` | Full finite sampling, separate three- and four-element collision counts, deletion, and asymptotic bridges. The explicit cubic coefficient improves on the **specified** earlier implementation's `4096(k+1)^3`; no globally optimal constant is claimed. |
| JSP-000562 / Erdős 690 | The genuine natural densities for the fourth smallest **distinct** prime factor exist for every prime and are not unimodal. Exact values at `13`, `17`, and `19` form a strict valley. | `JSP000562.fourthDensity_is_density`, `density_fourth_13`, `density_fourth_17`, `density_fourth_19`, `jsp000562` | A finite inclusion-exclusion proof through actual divisibility counts and their limits. This is a targeted `k = 4` implementation; prior registered work has broader scope. |
| JSP-000690 / Erdős 834 | There is a weakly three-color-critical, three-uniform hypergraph with 9 vertices, 22 edges, and minimum degree exactly 7; every proper subhypergraph obtained by deleting vertices and/or edges is two-colorable. | `JSP000690.solution` | Explicit color certificates, kernel-checked finite enumeration, and a general reduction from edge deletion to arbitrary proper subhypergraphs. |
| JSP-000301 / Erdős 365 (catalog yes/no scope) | The consecutive positive integers `12167` and `12168` are both powerful and neither is a square, disproving the universal square claim. | `JSP000301.conjecture_false`; witness theorem `exists_consecutive_powerful_not_square` | A direct arithmetic Lean proof, with source and reproducible checks. This does not establish the separate infinite-family counting question. |

The 11 declarations in `Audit.lean` are the explicit public axiom-audit boundary.
All eight local modules under `Problems/` are built and kernel-replayed, including
the auxiliary audit module. The theorem statements and custom definitions remain
available for semantic review; successful compilation alone does not settle
whether a mathematical interpretation matches a prize rule.

## Reproduce

Required tools: Python 3.10 or later, Git, and
[elan](https://github.com/leanprover/elan). Run in this directory:

```sh
lake exe cache get
python3 verify.py
```

`lean-toolchain` pins **Lean 4.34.0**. `lakefile.toml` and `lake-manifest.json` pin
mathlib to **`5ed2965256430c3649e86755f9576b54eca72435`** and record every dependency
revision. Do not run `lake update` when reproducing this release. Dependency
caches are a build convenience, are excluded from the package, and are not proof
evidence. `verify.py` checks the installed dependency commits and tracked-file
cleanliness before and after verification.

The verification script:

1. Hashes every published source, audit, configuration, and documentation input,
   checks the exact toolchain/dependency pins, and scans Lean source for proof
   escapes after removing nested comments and string literals.
2. Runs `lake clean pinnacleLean` followed by `lake build`, forcing a fresh build
   of this package's modules without deleting dependency caches.
3. Runs `lake env lean -DwarningAsError=true Audit.lean` and checks the exact set
   of 11 declarations and each declaration's transitive axiom dependencies
   against `{propext, Classical.choice, Quot.sound}`.
4. Runs `lake env leanchecker --verbose Problems` and requires one replay entry
   for each of the eight local modules.
5. Confirms that all input hashes and dependency states remained unchanged,
   then writes command exit codes, log hashes, source hashes, and the result to
   `verification/report.json` and `verification/SHA256SUMS`.

Every command transcript is saved under `verification/`. Transcripts explicitly
identify sanitization of checkout, home, and temporary absolute paths, and ANSI
color codes. Sanitization does not alter theorem names, dependency names, command
arguments, diagnostics, or exit codes. Logs never establish publication priority
by themselves; use the immutable public commit and GitHub's public timeline.

`leanchecker` replays proof terms using **Lean's kernel**. This is an additional
kernel replay, not two independent proof checkers and not independent human peer
review. The `report.json` result must say `passed` to claim that this verification
run succeeded. A nonzero command status or audit mismatch makes the script fail.

## Proof routes and sources

- **633:** Define Bernoulli weights on a finite powerset and prove total weight
  and expectation identities. Count three-element and four-element collisions
  separately, then delete one point per forbidden set. For a maximum Sidon
  subset of size `m` in an `n`-element set, the alteration inequality at sampling
  rate `2m/n` yields `n² ≤ (4 + 24k)m³`; real-power estimates supply both requested
  asymptotic conclusions. The mathematical method is the Alon–Erdős random
  sampling and deletion method cited by [Erdős Problem 772](https://www.erdosproblems.com/772).
- **562:** Expand finite prime-divisibility patterns as signed sums of
  divisibility indicators. The exact count of multiples of `d` in `(0,N]` is
  `N / d`; its normalized limit is `1/d`. This proves the genuine natural
  densities, rather than assuming independence. The exact values are
  `31/5005`, `206/36465`, and `1308/230945`, with the middle one strictly smaller
  than both neighbors. Mathematical source: Stijn Cambie,
  [Resolution of Erdős' problems about unimodularity](https://arxiv.org/abs/2501.10333).
- **690:** Encode the 22 edges of Ruiliang Li's construction, numbered `0,...,8`.
  Prove the degree sequence, reject all 512 binary colorings, exhibit a
  three-coloring and a binary certificate for every edge deletion. Monotonicity
  and the absence of isolated vertices give arbitrary proper-subhypergraph
  criticality. The edge data are from Ruiliang Li,
  [On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7](https://arxiv.org/abs/2512.24850).
  This is weak vertex coloring, not transversal criticality.
- **301:** Use `12167 = 23³` and `12168 = 2³ · 3² · 13²`. Prime divisibility of
  powers and products proves powerfulness for every prime divisor. Both numbers
  lie strictly between `110²` and `111²`, which rules out every possible square.
  The catalog cites [the 1976 paper](https://doi.org/10.1080/00150517.1976.12430562).

## Prior work and licensing

These are submissions for contribution review, not claims that these four
problems had no prior Lean formalization. See [CONTRIBUTIONS.md](CONTRIBUTIONS.md)
for fixed comparisons and earlier public records. No mathematical firstness,
first formalization, award eligibility, independent review, or optimality is
asserted without supporting public evidence.

Original package contributions are provided under [Apache-2.0](LICENSE). See
[NOTICE](NOTICE) for attribution. Cited papers, external developments, and Lean/
mathlib dependencies retain their own authorship and licenses; no raw third-party
proof snapshots, downloaded papers, screenshots, or private logs are distributed.

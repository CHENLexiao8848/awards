# JSP-000562: mathematical statement, contribution and verification supplement

Prepared 2026-09-26 for [PR #745](https://github.com/TheJustinSunPrize/awards/pull/745), concerning JSP-000562 / [Erdős Problem 690](https://www.erdosproblems.com/690).

This document describes the unchanged proof at `ea6e7fc0a5893edd13335acc4e1ebd00cd261782` in `CHENLexiao8848/awards`, branch `codex/four-lean-proofs-20260917`, package `proofs/chen-lexiao-four-20260917/proof`. It is a later review document, not a replacement proof version. The existing same-directory `review-supplement.md` concerns JSP-000633 and remains separate.

## Mathematical sources and review status

1. **Original question and classical method.** P. Erdős, *Some unconventional problems in number theory*, Astérisque **61** (1979), **73–82**, [original scan](https://www.numdam.org/article/AST_1979__61__73_0.pdf), **printed p.75**. Erdős asks whether the density distribution for the prime factor at a fixed position is unimodal and explicitly notes that the densities are computable by inclusion-exclusion. This submission claims neither that method nor the problem as a new discovery.
2. **Known counterexample and solution.** Stijn Cambie, *Resolution of Erdős' problems about unimodularity*, Journal of Number Theory **280** (March 2026), **271–277**, [DOI](https://doi.org/10.1016/j.jnt.2025.08.014). Precise publicly accessible locations are **§3, Theorem 5 and Claim 6, p.4**, and **Appendix A, p.5**, in [arXiv:2501.10333v1](https://arxiv.org/pdf/2501.10333v1). These are **preprint page numbers**, not journal page numbers. The appendix already contains the same exact fourth-prime-factor densities at 13, 17 and 19 and their strict valley. The formalization is of this known mathematical counterexample.
3. **Newer, broader literature.** Shouqiao Wang and Davide Crapis, *A Complete Answer to Erdős Problem 690*, [arXiv:2605.08542v1](https://arxiv.org/html/2605.08542v1), submitted 2026-05-08, **§1, Theorem 1.1 and Corollary 1.2**, state non-unimodality for every `k≥4` and the complete classification when combined with Cambie's positive cases. This later preprint is disclosed as prior literature; its full argument and computational certificates have not been independently verified in this submission review, and no Lean formalization of that general result is claimed here.

The selected Lean statement and the argument below are proposed for maintainer mathematical and statement-correspondence review. No approved challenge statement, independent human referee approval, accepted candidate status or prize decision is asserted.

## Exact statement and scope

In [the fixed source](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000562.lean), `HasNaturalDensity P d` is

\[
 \lim_{N\to\infty}\frac{|\{n\in\mathbb N:0<n\le N,\ P(n)\}|}{N}=d.
\]

Thus this is the ordinary natural density of an actual set of positive integers. It is not a logarithmic density, a finite numerical sample, or a probability model assumed to have the required limit. The ratio at `N=0` does not affect the limit at infinity.

`IsFourthPrimeFactor p n` means that `p` is prime, divides `n`, and exactly three distinct primes less than `p` divide `n`. At [line 37](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000562.lean#L37), `isFourthPrimeFactor_iff_primeFactors` proves for `n≠0` that this is equivalent to membership in `Nat.primeFactors n` with exactly three smaller members. The counted interval excludes zero, so this premise covers every counted integer. Exponents of prime factors do not change this predicate; any number of further prime factors greater than `p` is allowed. The predicate does not mean that the integer has exactly four prime factors in total.

The explicitly defined function `fourthDensity : ℕ → ℝ` has the proved density property for **every prime `p`**, including small primes for which the fourth-factor event is empty. Its values away from prime arguments are irrelevant to the statement. `PrimeUnimodal d` asks for a natural cutoff `m` such that prime-indexed values are nondecreasing to the left of `m` and nonincreasing to its right. Allowing any natural cutoff is at least as permissive as requiring a prime mode: every prime mode supplies a natural cutoff. Refuting every natural cutoff therefore refutes the ordinary prime-indexed unimodality assertion.

The final [theorem at line 231](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000562.lean#L231) is

```lean
theorem jsp000562 : ¬ PrimeUnimodal fourthDensity :=
  fourth_density_not_unimodal fourthDensity fourthDensity_is_density
```

The intermediate theorem `fourth_density_not_unimodal` permits an arbitrary assignment of actual densities; its density premise is fully discharged by `fourthDensity_is_density` in this final declaration. No density-existence premise remains unproved.

**Quantifier boundary.** The source formalizes one specified parameter, `k=4`. That is a complete negative witness to the assertion that the distribution is unimodal for every fixed position `k`. It does not formalize an arbitrary-`k` density function, the positive cases `k=1,2,3`, Cambie's entire range `4≤k≤20`, or the newer claimed classification for all `k≥4`. If the approved challenge requires a per-parameter classification rather than a negative witness to the universal question, this fixed proof does not cover that larger statement; documentation cannot supply the missing theorems. The separate divisor-distribution problem addressed elsewhere in the cited papers is also outside this submission.

## Complete mathematical argument corresponding to this implementation

Let `I_d(n)` be 1 when `d` divides `n` and 0 otherwise. A finite certificate is a list of pairs `(a,d)` with integer coefficient `a`. It represents the function

\[
 F_T(n)=\sum_{(a,d)\in T}aI_d(n).
\]

Appending certificates adds their functions, negating all coefficients negates the function, and replacing every denominator `d` by `lcm(p,d)` multiplies the function by `I_p(n)`. The last fact follows from `lcm(p,d)∣n` if and only if both `p∣n` and `d∣n`; the source proves these identities in `evalTerms_append`, `evalTerms_negate` and `evalTerms_restrict`.

For a list of primes `P`, let `E(P,r)(n)` indicate that exactly `r` entries of `P` divide `n`. Initialize `E([],0)=1` and `E([],r+1)=0`. The exact identities

\[
\begin{aligned}
 E(p::P,0)&=(1-I_p)E(P,0),\\
 E(p::P,r+1)&=(1-I_p)E(P,r+1)+I_pE(P,r)
\end{aligned}
\]

follow by separating the cases `p∣n` and `p∤n`. `exactlyTerms` implements these identities with certificate operations, and `eval_exactlyTerms` proves the represented function equals the indicator for every `n`. Its general list statement counts entries; using the duplicate-free list of primes below `p` makes this the number of distinct smaller prime divisors.

Take that complete list `P={q prime:q<p}` and multiply the certificate for `E(P,3)` by `I_p`. This represents exactly `IsFourthPrimeFactor p`, so no condition on larger prime factors is imposed.

For each positive `d`, the exact number of its multiples in `(0,N]` is `⌊N/d⌋`. Therefore

\[
\frac1N\sum_{0<n\le N}F_T(n)
 =\sum_{(a,d)\in T}a\frac{\lfloor N/d\rfloor}{N}
 \longrightarrow\sum_{(a,d)\in T}\frac a d.
\]

The bound `0≤N/d−⌊N/d⌋<1` proves each scalar limit, and only finite sums are involved. The source's `tendsto_div_count`, `sum_evalTerms` and `tendsto_evalTerms` establish this conclusion; `hasNaturalDensity_of_terms` transfers it to the represented set. Every denominator generated from positive primes and the initial denominator 1 is positive. The generic Lean lemmas also support `d=0` using Lean's zero-division convention, which is not needed for these prime certificates. This argument proves density existence; it does not assume divisibility events are independent.

For a checkable rational description of the same finite expansion, let `P` be the primes below `p`. Then

\[
 d_4(p)=\sum_{\substack{U\subseteq P\\|U|\ge3}}
 \frac{(-1)^{|U|-3}\binom{|U|}{3}}{p\prod_{q\in U}q}.
\]

Indeed, summing the disjoint indicators `\prod_{q\in S}I_q\prod_{q\in P\setminus S}(1-I_q)` over the 3-element sets `S` and expanding gives the coefficient `(-1)^{|U|-3}\binom{|U|}{3}` of each product indexed by `U`. Distinct primes give `lcm=p\prod_{q\in U}q`, so the density calculation above yields this sum. Equivalently, grouping the same rational expansion gives

\[
 d_4(p)=\frac{[X^3]\prod_{q\in P}(q-1+X)}{p\prod_{q\in P}q}.
\]

This polynomial expression is an explanatory arithmetic cross-check of the finite expansion, not an additional imported assumption or an assertion that a polynomial-coefficient theorem is declared in this Lean source.

| `p` | Complete smaller-prime list | Coefficient `[X³]` | Denominator `p∏q` | Exact density |
| --- | --- | ---: | ---: | --- |
| 13 | 2, 3, 5, 7, 11 | 186 | 30030 | `31/5005` |
| 17 | 2, 3, 5, 7, 11, 13 | 2884 | 510510 | `206/36465` |
| 19 | 2, 3, 5, 7, 11, 13, 17 | 54936 | 9699690 | `1308/230945` |

The three Lean density theorems establish these exact rational values by the general density theorem and `decide +kernel`; they use no floating-point approximation or `native_decide`. The strict differences are

\[
 d_4(13)-d_4(17)=\frac{139}{255255}>0,
 \qquad d_4(19)-d_4(17)=\frac{2}{138567}>0.
\]

If a proposed cutoff satisfies `17≤m`, its nondecreasing left side would require `d₄(13)≤d₄(17)`. Otherwise `m≤17`, and its nonincreasing right side would require `d₄(19)≤d₄(17)`. Each is contradicted by the displayed strict inequality. This proves non-unimodality on the entire prime-indexed sequence, even though three exact values suffice to refute every possible mode.

## Earlier Lean work and attributable implementation

[Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16) registers the earlier [plby repository implementation at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean). Its header attributes the informal mathematics to Stijn Cambie, lists Codex and GPT-5.6 Sol as formal authors, and retains Joseph Tooby-Smith's 2026 copyright and an OpenAI Codex author line. These existing credits and its Apache-2.0 notice must not be assigned to this submitter.

| Aspect | Earlier pinned implementation | This selected proof |
| --- | --- | --- |
| Actual density | [`kthPrimeFactorSet_hasDensity`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L594) proves it for every positive `k` and prime `p`, using a proved CRT counting model and exact coefficients. | `fourthDensity_is_density` proves it for every prime at `k=4`, using signed indicators, LCM restrictions and exact floor-count limits. |
| Non-unimodality witness | [`valley_certificates`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2047) already includes the same `k=4` triple 13, 17, 19 and other certificates. | Reimplements that known triple and its strict-valley contradiction. |
| Final scope | [`erdos_690`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2162) includes all density formulas, unimodality for `k=1,2,3`, and non-unimodality for `k=4,…,20`. | A complete `k=4` negative witness, with smaller scope. |
| What is being submitted | Prior formalization and its authorship remain prior work. | The local generic indicator-certificate operations, exact count-to-limit bridge, prime-factor interface, rational certificates and focused audits, for assessment as an alternative implementation. |

The earlier development proves its CRT/counting facts; it must not be characterized as merely assuming an independence model or omitting genuine natural density. Both developments use standard exact finite counting. This submission claims no new mathematical counterexample, new inclusion-exclusion method, expanded range of `k`, first formalization, measured performance advantage or priority over that record. The fixed source imports Mathlib rather than the cited plby modules, which establishes a local implementation boundary; it is not evidence that this work was developed without knowledge of the prior result or proof route.

CHEN LEXIAO (@CHENLexiao8848) selected and directed the project, requested formal proof and verification, organized the submission and authorized publication. The Lean implementation, verification tooling and documentation were developed with substantial Codex assistance. The [fixed contribution record](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/CONTRIBUTIONS.md) and [NOTICE](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/NOTICE) make this division explicit. Repository ownership and upload dates are not offered as evidence of personal discovery or manual authorship of every proof term. The [publication commit](https://github.com/CHENLexiao8848/awards/commit/ea6e7fc0a5893edd13335acc4e1ebd00cd261782) and [source](https://github.com/CHENLexiao8848/awards/tree/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof) identify the actual submitted implementation; mathematical priority remains with the cited sources. No independent human verifier is named.

## Fixed verification evidence and its limits

The [existing report](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/report.json) records a submitter-run local verification on **2026-09-17**, with `lake clean pinnacleLean`, `lake build`, public declaration audit and same-kernel replay. The [build log](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/build.log) has 2,055 completed jobs, including actual `Built` entries for `Problems.JSP000562` and `Problems.JSP000562Audit`. The 2026-09-26 review checked the fixed Git blobs, input/log hashes, locked dependency revisions, target outputs and replay coverage. It did **not** execute a new Lean build. The three successful GitHub workflow runs for this SHA check repository catalog/data, not the Lean proof.

The [public audit log](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verification/axioms.log) prints these five JSP-000562 targets, each with exactly `[propext, Classical.choice, Quot.sound]`:

- `JSP000562.fourthDensity_is_density`
- `JSP000562.density_fourth_13`
- `JSP000562.density_fourth_17`
- `JSP000562.density_fourth_19`
- `JSP000562.jsp000562`

The [separately built focused audit](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000562Audit.lean) adds `JSP000562.isFourthPrimeFactor_iff_primeFactors` and `JSP000562.fourthDensity_strict_valley`; the build transcript prints the same three standard axioms for both. Thus there are **seven distinct relevant audited declarations**, of which five are in the shared public audit. The shared package has eleven public targets and eight local modules across four problems; those totals are not seven additional JSP-000562 results. Replay includes both JSP-000562 modules and uses Lean's own kernel, not a second independent checker.

The [companion evidence review](JSP-000562-verification-review-20260926.md) records the 61 Git-blob matches, 18 input hashes, 41 command logs, 60 checksum entries, nine locked dependency states and their limits. Historical evidence consistency is not independent observation of the past commands. These documents do not certify mathematical acceptance or award eligibility.

## Reproduction

The selected [toolchain](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/lean-toolchain) is `leanprover/lean4:v4.34.0`; [the lockfile](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/lake-manifest.json) pins Mathlib `5ed2965256430c3649e86755f9576b54eca72435` and the other dependencies. In a clean checkout, the fixed [README](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/README.md) and [verifier](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/verify.py) give:

```sh
git clone --branch codex/four-lean-proofs-20260917 https://github.com/CHENLexiao8848/awards.git
cd awards
git checkout --detach ea6e7fc0a5893edd13335acc4e1ebd00cd261782
cd proofs/chen-lexiao-four-20260917/proof
lake exe cache get
python3 verify.py
```

The full verifier runs all four problems in this shared package. For the focused declaration audit after a build, run `lake env lean -DwarningAsError=true Problems/JSP000562Audit.lean`; its seven `#print axioms` commands identify the precise relevant boundary. No dependency update is required.

## Remaining review questions

The principal questions are whether the approved challenge accepts this complete negative witness as its required scope, and whether this smaller alternative implementation has sufficient attributable originality or value under the prize rules, given the earlier broader formalization. No document-only change can establish priority or add a general-`k` proof. The submission requests an assessment of its actual local implementation contribution, with these limitations visible; it does not declare itself eligible or request displacement of earlier contributors.

# JSP-000633 / PR #744: bounded substantive prior comparison

Reviewed 2026-09-27. Scope is only the selected JSP-000633 implementation and the two fixed complete comparators below. Existing local source/evidence was reused; the comparator source files were read again at their immutable revisions. No Lean execution, GitHub mutation, priority ruling or new literature survey was performed.

## Finding

The coefficient `4 + 24k` is a real strengthening of a proved finite inequality under the same hypotheses, not a documentation-only change. It is substantially smaller than the specified plby coefficient `4096(k+1)^3`. However, #454 already has the same `k^(-1/3) n^(2/3)` scale: against that comparator the defensible increment is an explicit constant improvement and removal of the displayed additive rounding loss. Neither the exponent `2/3`, the affirmative answers, the treatment of repeated summands, nor the three-/four-point alteration method is new relative to these sources. Mathematical novelty, firstness and prize eligibility are not established by this comparison.

## Fixed source map

| Implementation | Definitions and finite bound | Full original conclusions |
| --- | --- | --- |
| Submitted `ea6e7fc0a5893edd13335acc4e1ebd00cd261782` | [Main L26](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000633.lean#L26): `representations` L26, `BoundedRepresentations` L30, `IsSidon` L34; [`finite_bound` L289–315](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000633.lean#L289). | [`sidon_subset_two_thirds` L317, `answer_sqrt` L351 and `answer_positive_power` L358](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000633.lean#L317). The final two are uniform thresholds over all admissible finite sets. |
| plby `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` | [Erdos772 L56–93](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L56): labelled representation count, strong Sidon, capped `H`; [`exists_sidon_finset_cubic` L829–832](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L829). | [`H_cubic_lower_bound` L928 and `H_real_rpow_lower_bound` L940](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L928); [`erdos_772` L1040–1046](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L1040) already combines both original conclusions. |
| #454, CollinYuanjieRen `32403814a463c9c1643c81409a0f76f5707bcbcd` | [Definitions L22–35](https://github.com/CollinYuanjieRen/awards/blob/32403814a463c9c1643c81409a0f76f5707bcbcd/submissions/jsp-000633-cyr/Erdos772Sidon/Definitions.lean#L22): `rep`, `RepBounded`, `IsSidon`, capped `H`; [`exists_sidon_subset`, Alteration L7](https://github.com/CollinYuanjieRen/awards/blob/32403814a463c9c1643c81409a0f76f5707bcbcd/submissions/jsp-000633-cyr/Erdos772Sidon/Alteration.lean#L7). | [Bounds L48](https://github.com/CollinYuanjieRen/awards/blob/32403814a463c9c1643c81409a0f76f5707bcbcd/submissions/jsp-000633-cyr/Erdos772Sidon/Bounds.lean#L48): `H_lower`; `tendsto_H_div_sqrt` L76 and `eventually_rpow_lt_H` L114 already answer both questions. |

## Same conventions; no advantage from silently changing the problem

All three finite-set hypotheses count ordered pairs in `A × A`, including `(a,a)`. All three conclusions include repeated summands. The submitted and #454 predicates have the identical unordered-pair disjunction; plby's equality of two-element finsets is equivalent to that disjunction, including the singleton/diagonal cases. This is a source-level semantic comparison, not a newly Lean-proved cross-library equivalence theorem.

The original paper's distinct-summand convention must remain distinguished. If `r_<(t)` counts `a<b` and `d_A(t)` counts diagonal pairs, then `R_A(t)=2r_<(t)+d_A(t)` with `d_A(t)∈{0,1}`. Thus distinct unordered multiplicity at most `K` implies the selected ordered hypothesis with `k=2K+1`, not unchanged `k=K`. A weak distinct-summand Sidon set need not be strong Sidon: `{0,1,2}` has `0+2=1+1`. The submitted complete adaptation already counts the three-element obstructions; no new literature work is required to retain that explanation.

The submitted bound and plby's finite-set bound include all natural `k` and the empty set. #454's asymptotic conclusions state `k≥1`, the original range. Extending a statement to `k=0` is not a meaningful additional solution here: only the empty set satisfies that ordered bound. For `k=1`, sets of size at least two are inadmissible, and both prior capped extremal definitions assign the vacuous guarantee `H_1(n)=n`.

## Exact quantitative comparison

Put `n=|A|` and let `m` be a guaranteed strong-Sidon subset size.

* Submitted: `n² ≤ (4+24k)m³`, hence `m ≥ (4+24k)^(-1/3)n^(2/3)`.
* plby's displayed theorem: `n² ≤ 4096(k+1)³m³`, hence `m ≥ n^(2/3)/(16(k+1))`. The new coefficient is strictly smaller for every natural `k`; it improves the displayed dependence from order `k^(-1)` to `k^(-1/3)` as `k` varies. That latter scale was already present in #454.
* #454 `H_lower` supplies `s` with `n²<6k(s+1)³` and `s≤2H_k(n)`. For `k≥1`, this gives `H_k(n)>(48k)^(-1/3)n^(2/3)-1/2`. The new leading coefficient is larger because `4+24k<48k`, and the new expression has no subtractive half. The ratio of these two leading coefficients is `(48k/(4+24k))^(1/3)`, tending to `2^(1/3)`, rather than an improvement in the exponent or the order in `k`.

The `48k` expression is an elementary real-valued consequence derived from #454's precise integer theorem, not a separately named declaration there. Its stronger rounded form also uses `exists_s` (Bounds L19) and `ceil(s/2)` from the alteration theorem. Do not claim a strictly larger integer guarantee for every `(k,n)`; rounding and small/vacuous instances can coincide.

## Where the additional implementation work actually lies

The submitted [`card_F3_le` L31 / `card_F4_le` L37](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000633Counting.lean#L31) bound forbidden supports by `kn` and `kn²`; `avoids_imp_sidon` L96 links avoidance to strong Sidon. This treatment is already conceptually present in plby's `card_badTriples_le` L196, `card_badQuads_le` L222 and `isSidon_of_edgeFree` L332. It must not be advertised as a newly discovered missing diagonal case.

The concrete change is the finite real-weight argument ([main `sampleWeight_sum` L92, `sampleWeight_containing` L110, `sampleWeight_card` L161, `alteration` L206 and `alteration_three_four` L232](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000633.lean#L92)), followed by maximum-subset optimization. For a largest Sidon subset of size `m`, it establishes `pn−knp³−kn²p⁴≤m` for every `p∈[0,1]`. [`polynomial_of_alteration`, Algebra L9–37](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/Problems/JSP000633Algebra.lean#L9) splits `n≤2m` and `n>2m`; the second substitutes `p=2m/n`, yielding `n²≤24km³`, while the first yields `n²≤4m³`.

By comparison, [plby `exists_large_edgeFree` L572](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L572) averages the zero class of `q`-colorings (selection probability `1/q`), and [L669–767](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean#L669) chooses `q=4(k+1)cubeCeil(n)` with coarse estimates. #454 instead averages fixed-cardinality subsets subject to `6ks³≤n²` and deletes first coordinates of bad tuples. These are different implementations of the same established alteration idea, not unrelated new mathematical methods.

## Remaining limits and usable claim

The local package does not define `H_k(n)` or export a Lean bridge to either prior `H`; its threshold statements give the mathematical correspondence, already explained in the published supplement. An explicit cross-library bridge would be additional formal work, not evidence already contained at `ea6e7fc…`. This audit has not established optimality among all lemmas, possible retunings, other revisions or the mathematical literature. It also does not establish independent provenance of every proof term or first publication of the stronger constant. Saved build/axiom evidence remains the earlier reviewed evidence, not a new execution.

Safe concise contribution statement:

> At the selected commit, the development proves the explicit finite inequality `|A|² ≤ (4+24k)|B|³` under the same ordered-pair hypothesis and repeated-summand Sidon convention as the two cited complete formalizations. This strengthens plby's specified `4096(k+1)³` coefficient and improves the real lower bound derived from #454's `H_lower`; #454 already achieves the same `k^(-1/3)n^(2/3)` scale. The concrete implementation contribution is a finite real-weight alteration proof with maximum-subset optimization. Both prior complete proofs, the established alteration method and Alon–Erdős's mathematics remain credited; no firstness, optimality or award entitlement is asserted.

## Contribution, provenance and validation record

| Review item | Finding |
| --- | --- |
| Material role | `polynomial_of_alteration` and the finite real-weight expectation proof are used by `finite_bound`; the stronger quantitative inequality is then used by all three asymptotic/threshold targets. This is more than an interface wrapper. |
| Reuse and attribution | The mathematical alteration method is established Alon–Erdős mathematics; both complete prior implementations are credited above. The submitted local files import Mathlib and their local helpers, rather than either comparator module. Absence of such imports does not demonstrate independent origin of every proof term. |
| Account contribution evidence | The fixed [CONTRIBUTIONS.md](https://github.com/CHENLexiao8848/awards/blob/ea6e7fc0a5893edd13335acc4e1ebd00cd261782/proofs/chen-lexiao-four-20260917/proof/CONTRIBUTIONS.md) records project direction and substantial Codex assistance. The public path history exposes the bulk publication commit, not an incremental development trail. This supports a project-submitted implementation claim, but does not independently establish personal authorship, exact division of work or first publication of the refinement. Those remain unestablished here. |
| Validation reused | The selected proof SHA remains `ea6e7fc0a5893edd13335acc4e1ebd00cd261782`. The [earlier reviewed evidence](https://github.com/CHENLexiao8848/awards/blob/2db7e80f9dbb5e56bf34b682051bf842a4b031f6/proofs/chen-lexiao-four-20260917/review-supplement.md) matched 18 input hashes, 41 log hashes and 60 SHA256SUMS entries. Its recorded build and all four target audits passed; axioms are `propext`, `Classical.choice`, `Quot.sound`. No build was rerun for this documentation-only audit. |
| Repair and remaining qualification issue | No missing proof step or narrow source defect was identified in the reviewed target chain. No proof or dependency was changed. Original contribution attribution, mathematical review and priority require maintainer assessment; a new document cannot settle them. |
| Most useful next evidence | Preserve any existing, publishable development record that specifically shows how the real-weight proof and the `p=2m/n` optimization were developed, while retaining the acknowledged references. Do not create retrospective history or infer authorship from commit metadata. |

This report is a later documentation artifact about the original proof SHA; its eventual publication commit must not be described as a newly verified proof version.

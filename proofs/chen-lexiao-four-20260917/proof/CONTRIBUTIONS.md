# Contribution and priority record

**Submitter and organizer:** CHEN LEXIAO
([CHENLexiao8848](https://github.com/CHENLexiao8848)).
The project was organized and submitted under this account, with substantial AI
assistance through Codex for the Lean implementation, proof development,
verification, and documentation. The submitter selected the targets, requested
complete formal proofs and verification, and authorized public submission. This
does not attribute every proof term or the underlying mathematical discoveries
to the submitter personally.

The intended review request is attribution of the actual additional formal work,
assessment of its value, and determination by the maintainers of the applicable
award/candidate process. This document does not change award status, eligibility,
review signatures, or an earlier contributor's priority.

## JSP-000633: a quantitative refinement with both catalog conclusions

Earlier work was registered in
[issue #19](https://github.com/TheJustinSunPrize/awards/issues/19), including
[the fixed implementation at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos772.lean).
That implementation already proves both asymptotic conclusions, and its
`exists_sidon_finset_cubic` uses coefficient `4096(k+1)^3`.

The present `JSP000633.finite_bound` gives coefficient **`4 + 24k`** in the
same-shaped inequality `|A|² ≤ C(k)|B|³`, under the same convention of bounded
**ordered** pair counts including diagonal pairs. The Sidon predicate also
includes repeated summands. Smaller `C(k)` gives a stronger explicit guaranteed
size, so this is a concrete improvement relative to that fixed implementation.
This is not a claim of a new asymptotic exponent, a first formalization, or the
best known mathematical constant.

The implementation contains the finite probability argument, counting of
three-element and four-element forbidden configurations, deletion argument,
maximum-subset optimization, and real-power limits needed for both final
threshold statements. The mathematical method and its attribution remain with
Alon–Erdős and the sources listed at [Erdős Problem 772](https://www.erdosproblems.com/772).

## JSP-000562: a focused inclusion-exclusion implementation

[Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16) registers an
[earlier fixed Lean implementation](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean).
Its formalization credits Codex/GPT-5.6 Sol, and the mathematics is attributed to
Stijn Cambie. That development has broader scope: unimodality for `k = 1,2,3`
and non-unimodality for `k = 4,...,20`.

The present contribution is a targeted `k = 4` route through finite signed
divisibility-indicator sums and actual counting limits. It defines densities
for every prime, proves the exact densities at 13, 17, and 19, and uses their
strict valley to disprove unimodality. It does not claim to extend the prior
range of `k`, nor to be the first Lean proof. This route is presented for review
as an alternative, compact proof structure; no unmeasured speed or line-count
advantage is claimed.

## JSP-000690: explicit finite certificates and full subgraph criticality

Earlier public submissions include
[PR #21](https://github.com/TheJustinSunPrize/awards/pull/21),
[PR #35](https://github.com/TheJustinSunPrize/awards/pull/35), and
[PR #39](https://github.com/TheJustinSunPrize/awards/pull/39). The
[fixed PR #35 result](https://github.com/superpilot69/awards/blob/5e762a0fbb6cc3a45426c9528d8d3dab15f4e75e/submissions/jsp-000690/JSP690/Result.lean)
already includes arbitrary proper-subhypergraph criticality, so that property
must not be advertised here as absent from prior formalizations.

The present implementation supplies its own explicit edge-deletion coloring
certificates, checks all finite claims with Lean's kernel, and proves the full
arbitrary proper-subhypergraph statement through monotonicity and absence of
isolated vertices. The 9-vertex, 22-edge mathematical construction belongs to
Ruiliang Li, whose paper is cited in the Lean source and README.

## JSP-000301: a direct implementation of the known counterexample

Earlier public submissions include
[PR #13](https://github.com/TheJustinSunPrize/awards/pull/13) and
[PR #17](https://github.com/TheJustinSunPrize/awards/pull/17); the latter links
[a fixed proof](https://github.com/Redchar1992/jsp-000301-lean/blob/94c99f824c0deb2f0a163ba1b07ad95c7995100d/JSP301/Proof.lean).
The present implementation gives direct prime-divisibility and bounding-square
arguments for the same known pair, `12167`, `12168`, together with a reproducible
environment and checks. It is not a new mathematical counterexample or a first
Lean formalization. The complete covered claim is the catalog's yes/no question,
not the distinct question about counting infinitely many pairs.

## Evidence and public priority

The verification script hashes the actual release inputs and records every
command's exit status. Immutable public commits and pull-request timestamps can
establish when this specific implementation was published. Local timestamps,
file creation times, and a catalog's historical `Lean proof: No` label cannot
establish priority over the earlier public records above.

The strongest quantified incremental claim in this package is the coefficient
comparison for JSP-000633 against the explicitly linked fixed implementation.
Independent semantic review of that comparison and the complete final statements
is requested. Build and replay both use Lean's kernel; neither is an independent
human review, a separate proof-assistant implementation, or an award decision.

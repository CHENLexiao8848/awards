# Contribution, originality, and priority claims

## Requested decision

The submitter affirmatively seeks Justin Sun Prize consideration for the formalization contributions in this package. Please assess the independent implementation, the exact reusable structural results, and the verified reconstruction/repair of source proof steps as substantive contributions in their own right. The existence of another proof of the same numerical inequality should trigger a contribution comparison, rather than replace that comparison.

The claims concern the submitted formalization and proof architecture. Gyárfás's published mathematical discovery remains fully credited.

## Claim A: independently developed formal proof architecture

The finite chromatic theorem is proved by a stack-based depth-first induction with an explicit boundary invariant and decreasing measure. The new historical library independently realizes paths and cycles in Mathlib and discharges the actual source-context statements of Lemmas 1, 2, 3, 4, 5, 7, and 8. The implementation was developed in the submitter's project and is not a renaming or copied extension of the proof modules submitted in PR #130.

The originality claim is made for this concrete implementation and its documented decomposition. Related work contains a DFS proof and a full structural theorem, so the general DFS idea and the original Gyárfás theorem are not presented as newly discovered here.

## Claim B: explicit standalone rigidity and boundary contributions

The following verified statements are put forward for originality and contribution assessment, with complete hypotheses available in the cited source files:

1. **Outside-hub rigidity.** For k≥2, an outside vertex with 2k selected neighbors on an odd simple cycle, in a graph having exactly k distinct odd cycle lengths, forces that cycle's length to be 2k+1. No longest-cycle, minimum-degree, independent-complement, or connectivity premise is needed. See `HubRigidity.lean`.
2. **Two-endpoint attachment obstruction.** A nonempty simple path outside an odd cycle, with at least 2k selected attachments at each endpoint and only k distinct odd cycle lengths, is impossible. This statement does not need longestness, connectivity, degree bounds, or inequality of the attachment sets. See `GyarfasLemmaEight.lean`.
3. **Weakened common-attachment criterion.** With 2k attachments at the first endpoint, the other endpoint needs to share only one selected attachment to force k+1 distinct odd lengths. See `GyarfasLemmaSeven.lean`.
4. **Shared-edge exception.** The case in which both apparent endpoint chords are the same endpoint edge is separately proved, including its k=1 connectivity boundary. See `SharedEdgeException.lean`.

These are claims to assess specific formally proved contributions. The inspected related package is compared in COMPARISON.md; the review was not an exhaustive search of all mathematical literature. A global first-discovery assertion would require a broader priority finding than this evidence establishes.

## Claim C: source reconstruction with checked repairs

The package makes intermediate edge counts and inherited hypotheses explicit, replacing potentially invalid source shorthand by checked constructions. The complementary attachment cycles have lengths u+t+2 and u+(N−t)+2. The distinct-neighbor exception retains the source's larger-second-neighborhood orientation and uses a rigidity argument that never counts a repeated-endpoint closed walk as a simple cycle. These contributions are auditable in SOURCE_RECONSTRUCTION.md.

Some related work also repairs source boundary arguments; the claim is for this implementation and its precise standalone exports, not exclusive ownership of every correction.

## Priority requested from the immutable record

- PR #130 was opened on 2026-09-16 at 15:50:58 UTC. Its chronology and disclosed prior finite proof are acknowledged as facts.
- The submitter's PR #517 was opened on 2026-09-17 at 06:18:35 UTC and pins commit `d172a837ba1bd1849b9dc9f8e6c6ad088085fcfb`. That is the public record requested for the numerical proof, universal sharpness, and historical Lemma 1 disclosed there.
- This new PR records the additional structural implementation at its own immutable commit and submission timestamp. New modules are not backdated to #517.

The submitter requests preservation and recognition of priority **to the extent supported by those records and the specific contribution comparison**, and reserves the claim to appropriate formalization credit and prize consideration. This document makes no blanket waiver of priority, originality, attribution, or eligibility. It does not assert an earlier timestamp than the documented prior submissions or a prize decision that has not been issued.

The earlier PR remains open and unchanged by this submission. Please evaluate both records together for attribution while reviewing the new evidence separately.

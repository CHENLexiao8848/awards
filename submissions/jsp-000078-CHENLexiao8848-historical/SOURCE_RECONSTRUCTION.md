# Checked reconstruction of compressed source arguments

The project reconstructs the published proof using explicit Mathlib paths, cycle supports, parity, and finite-set counting. The points below distinguish verified replacements from historical shorthand. These are contribution evidence, not claims that all other formalizations failed to address them.

## Exact complementary attachment edge count (Lemma 4)

Let N be the odd base-cycle length, t the chosen arc length, and u the outside-route length. Each mixed cycle includes two attachment edges. The actual lengths are

```text
u + t + 2
u + (N - t) + 2
```

Their attachment contributions sum to N+4. If the attachment path itself has length t+2, expressing the second mixed cycle by subtraction from that path requires the offset +4, rather than the +2 appearing in the printed intermediate formula. The formalization avoids ambiguous subtraction and constructs both cycles with the displayed exact lengths. The longest-cycle separation argument and final q+ceil(p/2) lower bound remain unchanged. See AttachmentCycles, EndpointCycleData, EndpointCount, and GyarfasLemmaFour.

## Retained orientation and simple-cycle witnesses (Lemma 8)

The main proof chooses A so that its cycle-neighborhood is no larger than B's. An isolated reading that keeps 2k A-neighbors but allows only one arbitrary B-neighbor is too weak. HistoricalDistinctEndpointException retains the source-context inequality and derives the required second-neighborhood count.

The Case 2 shorthand also admits a self-pair if interpreted literally as a family indexed over every marked point; that closed walk is not a simple cycle. This implementation replaces the fragile count with checked one-hub near-saturation rigidity for k≥2 and a separate k=1 argument. No repeated-vertex closed walk enters oddCycleLengths.

The rigidity proof rebases a finite marked set at a least even gap, proves the gap is two from parity exhaustion, fills the remaining odd and even positions by closure, and derives circumference 2k+1. Two large endpoint attachment sets then either overlap, triggering the stronger shared-attachment result, or their disjoint union exceeds the cycle order. See HubRigidity, DistinctAttachmentsLarge, DistinctAttachmentsOne, and GyarfasLemmaEight.

The inspected related submission also explicitly retains the endpoint orientation and repairs Lemma 8 using a different mixed-cycle argument. The contribution claim is the present standalone rigidity theorem, stronger hypothesis interface, and independent formal implementation.

## Shared endpoint chord (part of Lemma 6)

If the apparent chords at both path endpoints are the edge AB itself, they are a single edge, so a two-distinct-interior-chord classification does not automatically cover that case. SharedEdgeException provides a separate proof. For k≥2, triangle length three and the actual longer connector families give the additional odd length. For k=1, the argument separates path parity and uses the verified outside-cycle lemma in the even-path case.

The general two-chord branch of Lemma 6 remains open in the frozen snapshot. The completed shared-edge theorem is not represented as completion of that general branch.

## Fan path construction (Lemma 3)

The source's terse orientation/count step is replaced by explicit families in three rectangles of spoke positions, with separate treatment of the single-chord exception. Each member is a simple path and the length map is injective. Bipartiteness provides common parity only after distinct lengths and path simplicity are established. The resulting quantified endpoint theorem is the source statement.

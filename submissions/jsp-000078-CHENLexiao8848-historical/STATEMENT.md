# Mathematical statements and source correspondence

The primary source is András Gyárfás, *Graphs with k odd cycle lengths*, Discrete Mathematics 103 (1992), 41–48, [DOI](https://doi.org/10.1016/0012-365X%2892%2990037-G). The supplementary source is Gao, Huo, and Ma, [arXiv:2012.10624v2](https://arxiv.org/abs/2012.10624v2), *A strengthening on odd cycles in graphs of given chromatic number*. Both local source PDFs were read during development; no paper copies are distributed.

## Exact numerical theorem

For every finite simple undirected graph G and natural k, if G has exactly k distinct odd simple-cycle lengths, then χ(G)≤2k+2. The bound is attained for every k by a complete graph on 2k+2 vertices.

```lean
JSP000078.chromaticNumber_le_of_card_oddCycleLengths_eq
    {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : (JSP000078.oddCycleLengths G).card = k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ)
```

The membership theorem identifies the length set exactly:

```lean
n ∈ JSP000078.oddCycleLengths G ↔
  Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n
```

Fintype covers arbitrary finite sizes; SimpleGraph is symmetric and irreflexive. Cycles may have chords. A repeated-vertex closed walk cannot qualify as IsCycle. Finset cardinality counts each length once, not cycle occurrences. There is no connectedness or positive-k premise. Empty and disconnected graphs are included, and k=0 is equivalent to bipartiteness. Mathlib's chromatic number is in ℕ∞ and the finite natural bound is coerced to it; the proof first supplies proper finite colorability.

The source uses the conventional finite simple graph setting without a separate global sentence declaring it. The finite scope is explicit here. The independent DFS proof establishes exactly the original numerical conjecture stated on printed page 41, not the full stronger statement of the numbered Theorem 1.

## Historical source exports

All names below are in namespace JSP000078. Full elaborated types are in the audit log.

| Source | Proved export | Scope |
| --- | --- | --- |
| Lemma 1, pp.42–43 | `outside_odd_cycle_length_lt_longest` | An outside odd cycle is shorter than a longest odd cycle in a vertex-2-connected graph |
| Lemma 2, p.43 | `historicalIncidentChordLemmaTwo` | An exact cycle with 2k−1 proper incident chords is bipartite or has at least k distinct odd lengths |
| Lemma 3, p.44 | `historicalBipartiteFanPathLengths` | Every distinct endpoint pair in the bipartite fan has k+1 simple paths of different lengths and common parity |
| Lemma 4, pp.44–45 | `odd_lengths_of_endpoint_neighbor_sets` | Arbitrary selected neighbor vertices yield q+ceil(p/2) odd lengths; nonempty cycle attachments and the ordinary geometric support conditions are explicit |
| Lemma 5, pp.45–46 | `historicalIndependentComplement` | The source degree and odd-length assumptions with an independent outside set force completeness and exact order 2k+2 |
| Lemma 7, p.47 | `odd_lengths_of_common_endpoint_neighbors` | The common-neighbor lower bound, via a stronger shared-single-attachment theorem |
| Lemma 8, pp.47–48 | `historicalDistinctEndpointException` | Full inherited source context, including the larger second endpoint neighborhood, discharged by the two-large-attachment theorem |

The lemma numbers are source correspondences, not a claim that every intermediate line is copied literally. Equivalent or repaired arguments are documented in SOURCE_RECONSTRUCTION.md. None of the seven export statements is assumed as a field in its own proof.

## Additional structural results

`odd_cycle_length_eq_of_outside_hub` assumes a simple odd cycle C, a vertex v outside it, a selected set X of 2k neighbors of v on C, exactly k odd lengths in G, and k≥2. It concludes C.length=2k+1, with no longest-cycle or independent-complement premise.

`two_large_endpoint_attachment_sets_impossible` assumes a simple odd cycle and a simple path of positive length with support outside it, selected endpoint attachment sets of sizes 2k and at least 2k, and exactly k≥1 odd lengths. It proves False. Its source wrapper retains the inherited context of Lemma 8.

`shared_endpoint_edge_exception` proves the shared-AB-edge configuration impossible with the source longest-cycle/vertex-2-connectivity hypotheses, exactly k≥1 odd lengths, a path of length at least two, and 2k−1 selected common attachments.

## Remaining global assembly

The general equal-neighbor one-chord configuration of Lemma 6 is still an unproved proposition in HistoricalExceptionsSpec; only its shared-AB-edge subcase is proved in this snapshot. The strongest global structural theorem and its block/equality consequences are not exported here. These are remaining work, not hidden premises of Main or the seven completed historical lemmas.

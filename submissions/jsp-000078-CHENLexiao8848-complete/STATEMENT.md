> Historical snapshot: this document originally described the finite package at e5fff3632957cbd00dec7029b5756a256c263d93. The current full-scope revision supersedes its finite-only exclusions; see [FULL_SCOPE_PROVENANCE.md](FULL_SCOPE_PROVENANCE.md) and [README.md](README.md). Earlier claims and verification results remain dated evidence, not results for the new revision.

# Exact theorem and source correspondence

Primary source: András Gyárfás, *Graphs with k odd cycle lengths*, Discrete Mathematics 103 (1992), 41–48, [DOI](https://doi.org/10.1016/0012-365X%2892%2990037-G). Supplement: Gao, Huo, and Ma, *A strengthening on odd cycles in graphs of given chromatic number*, [arXiv:2012.10624v2](https://arxiv.org/abs/2012.10624v2). Both supplied PDFs were read during development.

## Numerical theorem

For every finite simple undirected graph G, if exactly k distinct odd simple-cycle lengths occur, then χ(G)≤2k+2. This is the original Bollobás-Erdős conjecture stated and resolved on printed page 41 of Gyárfás's paper.

```lean
theorem JSP000078.chromaticNumber_le_of_card_oddCycleLengths_eq
    {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : (JSP000078.oddCycleLengths G).card = k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ)
```

This displays the signature of the proved source declaration; the proof is in Main.lean. The numerical theorem has no connectedness, nonempty-vertex, minimum-degree, decidable-adjacency, or positive-k premise. Empty and disconnected graphs are included. Mathlib's chromatic number is in ℕ∞; the finite natural upper bound is coerced to that type. Proper finite colorability is proved first.

## Distinct odd lengths

```lean
n ∈ JSP000078.oddCycleLengths G ↔
  Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n
```

The set stores lengths, not occurrences or vertex sets. Even lengths are excluded. Mathlib Walk.IsCycle excludes repeated internal vertices and lengths below three; cycles need not be induced and may have chords. The finite-range representation loses no cycle length because the length bound by vertex cardinality is proved. Arbitrary finite vertex types and every k are quantified, rather than a finite computational range.

For k=0, emptiness is equivalent to bipartiteness. For every k, `oddCycleLengths_bound_sharp` constructs a complete graph on 2k+2 vertices with exactly k odd lengths and chromatic number 2k+2.

## Structural Theorem 1

Gyárfás's actual numbered Theorem 1 is stronger: if k≥1, the graph is 2-connected, all degrees are at least 2k+1, and exactly k odd lengths occur, then G is K_(2k+2).

```lean
JSP000078.gyarfas_structural_theorem
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (hG : JSP000078.TwoVertexConnected G)
    (hdegree : ∀ v : V, 2 * k + 1 ≤ G.degree v)
    (hK : (JSP000078.oddCycleLengths G).card = k) :
    G = ⊤ ∧ Fintype.card V = 2 * k + 2
```

TwoVertexConnected states order at least three, connectedness, and connectedness after any single-vertex deletion. Equality to the complete graph on the existing vertex type plus exact order encodes the complete-graph conclusion without choosing a labeling. DecidableRel is a computational instance that classical reasoning supplies, not an additional graph-theoretic hypothesis.

## Historical lemma map

| Source | Completed export in namespace JSP000078 |
| --- | --- |
| Lemma 1, pp.42–43 | `outside_odd_cycle_length_lt_longest` |
| Lemma 2, p.43 | `historicalIncidentChordLemmaTwo` |
| Lemma 3, p.44 | `historicalBipartiteFanPathLengths` |
| Lemma 4, pp.44–45 | `odd_lengths_of_endpoint_neighbor_sets` |
| Lemma 5, pp.45–46 | `historicalIndependentComplement` |
| Lemma 6, pp.46–47 | `historicalEqualEndpointChordException` |
| Lemma 7, p.47 | `odd_lengths_of_common_endpoint_neighbors` |
| Lemma 8, pp.47–48 | `historicalDistinctEndpointException` |
| Structural Theorem 1, p.41 | `historicalGyarfasStructuralTheorem` |
| Numerical coloring consequence | `colorable_of_card_oddCycleLengths_le` |

The exact source-context hypotheses are retained in the wrappers. Some reusable intermediate theorems have weaker hypotheses; stronger results discharge the source wrappers. Corrected source shorthand and equivalent local constructions are disclosed in SOURCE_RECONSTRUCTION.md. No unresolved source proposition is assumed in the final theorem.

## Supplement and scope

Gao-Huo-Ma Theorem 1.1 restates the numerical result as chromatic number r+1 forcing at least floor(r/2) distinct odd lengths. The project proves this arithmetic restatement. Their consecutive-length strengthenings supply context and are not assumed in the proof.

The source uses conventional finite simple graph arguments without a global finite/simple declaration; the formalization makes that scope explicit. It does not claim the arbitrary infinite-graph extension or separate full equality/block-exception classification as additional exports. The requested finite numerical result and historical structural route have no remaining proof dependency.

# Statement fidelity

## Original problem and sources

Official entry: [JSP-000078](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000078), How does the number of distinct odd cycle lengths constrain a graph's chromatic number?

Primary: András Gyárfás, *Graphs with k odd cycle lengths*, Discrete Mathematics 103 (1992), 41-48, [DOI](https://doi.org/10.1016/0012-365X%2892%2990037-G). Printed page 41 defines L(G) as the set of odd cycle lengths and states the Bollobás-Erdős conjecture |L(G)|=k implies χ(G)≤2k+2, sharp at K_(2k+2). Gyárfás proves the stronger Theorem 1: 2-connectivity, minimum degree at least 2k+1, and exactly k≥1 odd lengths imply G is complete on 2k+2 vertices. His unnumbered corollary gives the numerical bound and a stronger block exception.

Supplement: Jun Gao, Qingyi Huo, Jie Ma, *A strengthening on odd cycles in graphs of given chromatic number*, [arXiv:2012.10624v2](https://arxiv.org/abs/2012.10624v2). Theorem 1.1 restates the numerical result: chromatic number r+1 forces at least floor(r/2) distinct odd lengths. Theorems 1.2 and 1.3 strengthen their distribution to consecutive lengths. They are not substituted for the target or assumed by any Lean proof.

Both supplied papers were read. Neither contains an explicit global finite/simple convention sentence; their ordinary finite undirected simple-graph setting is reflected explicitly below. No infinite-graph extension is claimed.

## Exact Lean statement

```lean
namespace JSP000078
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
theorem chromaticNumber_le_of_card_oddCycleLengths_eq (k : ℕ)
    (hk : (oddCycleLengths G).card = k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ)
end JSP000078
```

This is the signature of the proved declaration in [Main.lean](JSP000078/Main.lean). Mathlib's chromatic number is in ℕ∞; the natural upper bound is coerced to that type. The proof supplies a proper finite coloring.

The membership theorem in [Basic.lean](JSP000078/Basic.lean) is exactly:

```lean
n ∈ oddCycleLengths G ↔
  Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n
```

- Each length is counted once, regardless of the number of cycles realizing it.
- Oddness excludes even lengths. Walk.IsCycle excludes repeated-vertex closed walks and lengths below three.
- Chords are permitted; cycles are not required to be induced.
- SimpleGraph supplies symmetric irreflexive adjacency.
- Fintype permits arbitrary finite size, not a fixed computational range.
- There is no connectedness, nonempty-vertex, minimum-degree, or positive-k premise. Empty and disconnected graphs and k=0 are included.
- The finite range loses no witness because cycle_length_le_card is proved.
- The at-most-k theorem is additional; it does not replace the exact-k statement.

The modern form follows by natural-number arithmetic. Complete-graph sharpness is proved for every k in [Sharpness.lean](JSP000078/Sharpness.lean). The stronger block/minimum-degree classification and consecutive-length strengthening are outside this submission's claimed theorem.

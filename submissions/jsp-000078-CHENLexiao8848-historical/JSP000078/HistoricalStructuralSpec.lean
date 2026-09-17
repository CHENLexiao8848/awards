import JSP000078.HistoricalSpec
import JSP000078.LongestOddCycle
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The structural target and its independent-complement subcase

These proposition definitions state the remaining historical conclusions,
without introducing any premise asserting them. The complete graph conclusion
is represented by equality to the complete graph on the existing vertex type
and the exact number of vertices.
-/

namespace JSP000078

open SimpleGraph

/-- Gyárfás Lemma 5: under the source minimum-degree and length-count
hypotheses, an independent complement of a longest odd cycle forces a clique. -/
def HistoricalIndependentComplement : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (c : V) (C : G.Walk c c),
    1 ≤ k → TwoVertexConnected G →
    (∀ v : V, 2 * k + 1 ≤ G.degree v) →
    (oddCycleLengths G).card = k → IsLongestOddCycle C →
    (∀ x y : V, x ∉ C.support → y ∉ C.support → ¬G.Adj x y) →
    G = ⊤ ∧ Fintype.card V = 2 * k + 2

/-- The numbered Theorem 1 in Gyárfás (1992), expressed independently of
vertex labels. It is stronger than the already-proved numerical JSP theorem. -/
def HistoricalGyarfasStructuralTheorem : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    1 ≤ k → TwoVertexConnected G →
    (∀ v : V, 2 * k + 1 ≤ G.degree v) →
    (oddCycleLengths G).card = k → G = ⊤ ∧ Fintype.card V = 2 * k + 2

end JSP000078

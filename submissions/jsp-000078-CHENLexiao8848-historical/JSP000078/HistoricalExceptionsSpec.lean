import JSP000078.HistoricalStructuralSpec

/-!
# The remaining exceptional configurations in the historical proof

The source's Lemma 8 uses inherited endpoint-neighbor and degree hypotheses.
They are retained here; a weaker standalone reading is false.
-/

namespace JSP000078

open SimpleGraph

/-- Cycle neighbors of a specified endpoint, represented without counting occurrences. -/
noncomputable def cycleNeighborVertices {V : Type*} [Fintype V]
    (G : SimpleGraph V) {c : V} (C : G.Walk c c) (a : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ v ∈ C.support ∧ G.Adj a v

/-- Proper outside-path neighbors exclude the initial edge of the path. -/
noncomputable def pathChordVertices {V : Type*} [Fintype V]
    (G : SimpleGraph V) {a b : V} (P : G.Walk a b) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ v ∈ P.support ∧ v ≠ P.getVert 1 ∧ G.Adj a v

/-- The distinct-neighbor exceptional configuration, retaining the actual
source context and the orientation selecting the smaller cycle-neighbor set. -/
def HistoricalDistinctEndpointException : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (c a b : V) (C : G.Walk c c) (P : G.Walk a b),
    1 ≤ k → TwoVertexConnected G →
    (∀ v : V, 2 * k + 1 ≤ G.degree v) →
    (oddCycleLengths G).card = k → IsLongestOddCycle C → P.IsPath → a ≠ b →
    Disjoint {v | v ∈ P.support} {v | v ∈ C.support} →
    (∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length) →
    (cycleNeighborVertices G C a).card = 2 * k →
    (cycleNeighborVertices G C a).card ≤ (cycleNeighborVertices G C b).card →
    (∃ v ∈ cycleNeighborVertices G C b, v ∉ cycleNeighborVertices G C a) →
    (pathChordVertices G P).card = 0 →
    k + 1 ≤ (oddCycleLengths G).card

/-- The equal-neighbor one-chord exception, including the possibility
that the two endpoint chords are the same edge between the endpoints. -/
def HistoricalEqualEndpointChordException : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (c a b : V) (C : G.Walk c c) (P : G.Walk a b),
    1 ≤ k → TwoVertexConnected G →
    (∀ v : V, 2 * k + 1 ≤ G.degree v) →
    (oddCycleLengths G).card = k → IsLongestOddCycle C → P.IsPath → a ≠ b →
    Disjoint {v | v ∈ P.support} {v | v ∈ C.support} →
    (∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length) →
    cycleNeighborVertices G C a = cycleNeighborVertices G C b →
    (cycleNeighborVertices G C a).card = 2 * k - 1 →
    (pathChordVertices G P).card = 1 →
    (pathChordVertices G P.reverse).card = 1 →
    k + 1 ≤ (oddCycleLengths G).card

end JSP000078

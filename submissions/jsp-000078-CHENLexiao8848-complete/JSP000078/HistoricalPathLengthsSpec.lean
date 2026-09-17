import JSP000078.HistoricalCountingSpec

/-!
# The next historical dependency: bipartite fan path lengths

The definition records Gyárfás Lemma 3, printed page 44. GyarfasLemmaThree
proves it by constructing fixed-endpoint simple paths and counting their lengths.
-/

namespace JSP000078

open SimpleGraph

/-- A bipartite cycle with `2*k-1` incident proper chords has `k+1` paths
between any two distinct vertices, all of one parity and different lengths. -/
def HistoricalBipartiteFanPathLengths : Prop :=
  ∀ {V : Type} [Fintype V] (H : SimpleGraph V) (F : CycleWithIncidentChords H)
    (k : ℕ), 1 ≤ k → F.indices.card = 2 * k - 1 → H.IsBipartite →
    ∀ x y : V, x ≠ y →
      ∃ P : Fin (k + 1) → H.Walk x y,
        (∀ i, (P i).IsPath) ∧
        Function.Injective (fun i ↦ (P i).length) ∧
        ∀ i j, (P i).length % 2 = (P j).length % 2

end JSP000078

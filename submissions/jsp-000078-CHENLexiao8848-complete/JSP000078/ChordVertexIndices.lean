import JSP000078.HistoricalExceptionsSpec
import JSP000078.EndpointConfigurationBridge

/-!
# Extracting proper chord indices from neighbor sets

The historical exceptional configurations count neighbor vertices. These
bridges expose the underlying support and adjacency conditions and turn
a nonempty proper-chord set at either endpoint into a numerical position
along the original walk.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

@[simp]
theorem mem_cycleNeighborVertices {c a v : V} {C : G.Walk c c} :
    v ∈ cycleNeighborVertices G C a ↔ v ∈ C.support ∧ G.Adj a v := by
  classical
  simp only [cycleNeighborVertices, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem mem_pathChordVertices {a b v : V} {P : G.Walk a b} :
    v ∈ pathChordVertices G P ↔
      v ∈ P.support ∧ v ≠ P.getVert 1 ∧ G.Adj a v := by
  classical
  simp only [pathChordVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A nonempty proper chord-vertex set at the initial endpoint supplies
an index at least two. Simplicity of the walk is not required. -/
theorem exists_path_proper_chord_index {a b : V} (P : G.Walk a b)
    (hchord : (pathChordVertices G P).Nonempty) :
    ∃ i : ℕ, 2 ≤ i ∧ i ≤ P.length ∧ G.Adj a (P.getVert i) := by
  obtain ⟨D, hDcard, hD⟩ := exists_path_chord_indices P (pathChordVertices G P)
    (fun _ hv ↦ mem_pathChordVertices.mp hv)
  have hDne : D.Nonempty := Finset.card_pos.mp (by
    rw [hDcard]
    exact Finset.card_pos.mpr hchord)
  obtain ⟨i, hi⟩ := hDne
  exact ⟨i, hD i hi⟩

/-- A proper chord from the final endpoint has an original-path index
at least two edges before the end. The index may be zero, allowing the
chord to be the edge between the two endpoints. -/
theorem exists_path_reverse_proper_chord_index {a b : V} (P : G.Walk a b)
    (hchord : (pathChordVertices G P.reverse).Nonempty) :
    ∃ j : ℕ, j + 2 ≤ P.length ∧ G.Adj b (P.getVert j) := by
  obtain ⟨i, hi, hiL, hAdj⟩ := exists_path_proper_chord_index P.reverse hchord
  have hiLen : i ≤ P.length := by simpa only [Walk.length_reverse] using hiL
  refine ⟨P.length - i, by omega, ?_⟩
  simpa only [Walk.getVert_reverse] using hAdj

end JSP000078

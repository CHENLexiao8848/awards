import JSP000078.HistoricalStructuralSpec
import JSP000078.OutsideNeighborSaturation
import JSP000078.SpanningCycleChords
import JSP000078.TwoOutsideVerticesCycle

/-!
# Gyárfás's independent-complement lemma

The published parity exhaustion forces every selected outside-neighbor set
to fill the odd cycle. A second outside vertex would extend it by two, so
the graph has exactly one vertex outside and minimum degree makes it complete.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- With the source's degree and odd-length bounds, a longest odd cycle
cannot span the graph. Its proper chords would give k shorter odd lengths. -/
theorem exists_vertex_outside_longest_odd_cycle
    (k : ℕ) (hk : 1 ≤ k) (hdeg : ∀ v : V, 2 * k + 1 ≤ G.degree v)
    (hK : (oddCycleLengths G).card = k) {c : V} {C : G.Walk c c}
    (hC : IsLongestOddCycle C) : ∃ v : V, v ∉ C.support := by
  classical
  by_contra h
  have hspan : ∀ v : V, v ∈ C.support := by simpa only [not_exists, not_not] using h
  obtain ⟨J, hJcard, hJ⟩ := exists_spanning_cycle_chord_indices hC.1 hspan
  have hchords : 2 * k - 1 ≤ J.card := by have := hdeg c; omega
  have hshort := odd_cycle_many_chords_shorter_lengths hC.1 hC.2.1 k hk J hchords hJ
  let L := (oddCycleLengths G).filter fun n ↦ n < C.length
  have hNmem : C.length ∈ oddCycleLengths G :=
    (mem_oddCycleLengths G).mpr ⟨hC.2.1, c, C, hC.1, rfl⟩
  have hNnot : C.length ∉ L := by simp [L]
  have hsub : insert C.length L ⊆ oddCycleLengths G :=
    Finset.insert_subset hNmem (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hNnot, hK] at hc
  change k ≤ L.card at hshort
  omega

/-- Gyárfás (1992), Lemma 5, printed pages 45-46. The conclusion uses
the existing vertex type and gives both completeness and its exact order. -/
theorem complete_of_independent_outside_longest_odd_cycle
    (k : ℕ) (hk : 1 ≤ k) (hdeg : ∀ v : V, 2 * k + 1 ≤ G.degree v)
    (hK : (oddCycleLengths G).card = k) {c : V} {C : G.Walk c c}
    (hC : IsLongestOddCycle C)
    (hInd : ∀ x y : V, x ∉ C.support → y ∉ C.support → ¬G.Adj x y) :
    G = ⊤ ∧ Fintype.card V = 2 * k + 2 := by
  classical
  obtain ⟨v, hv⟩ := exists_vertex_outside_longest_odd_cycle k hk hdeg hK hC
  obtain ⟨hvAdj, hN⟩ := outside_vertex_saturated_of_degree hC.1 hC.2.1 hv k hK (hdeg v) hInd
  have hcover : ∀ w : V, w ∈ C.support ∨ w = v := by
    intro w
    by_cases hw : w ∈ C.support
    · exact Or.inl hw
    apply Or.inr
    by_contra hwv
    have hwv' : w ≠ v := hwv
    obtain ⟨hwAdj, _⟩ := outside_vertex_saturated_of_degree hC.1 hC.2.1 hw k hK (hdeg w) hInd
    obtain ⟨D, hD, hDL⟩ := exists_cycle_through_two_outside_universal_vertices
      hC.1 hv hw hwv'.symm hvAdj hwAdj
    have hDO : Odd D.length := by rw [hDL]; exact hC.2.1.add_even even_two
    have hmax := hC.2.2 c D hD hDO
    omega
  have hcard : Fintype.card V = 2 * k + 2 := by
    have := card_vertex_eq_cycle_length_add_one hC.1 hv hcover
    omega
  refine ⟨graph_eq_top_of_card_sub_one_le_degree ?_, hcard⟩
  intro w
  rw [hcard]
  have := hdeg w
  omega

/-- The exact source-context Lemma 5 proposition. The proof actually
needs no extra connectivity once its cycle, degree, and independence data hold. -/
theorem historicalIndependentComplement : HistoricalIndependentComplement := by
  intro V _ G _ k c C hk _ hdeg hK hC hInd
  exact complete_of_independent_outside_longest_odd_cycle k hk hdeg hK hC hInd

end JSP000078

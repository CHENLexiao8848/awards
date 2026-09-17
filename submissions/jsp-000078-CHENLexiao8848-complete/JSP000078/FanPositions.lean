import JSP000078.HistoricalCountingSpec

/-! # Neighbor positions on a cycle with incident chords -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

/-- Include the two cycle neighbors along with the selected proper chords. -/
noncomputable def CycleWithIncidentChords.spokePositions (F : CycleWithIncidentChords H) :
    Finset ℕ := by
  classical
  exact insert 1 (insert (F.cycle.length - 1) (F.indices.image Fin.val))

theorem CycleWithIncidentChords.mem_spokePositions (F : CycleWithIncidentChords H) {i : ℕ} :
    i ∈ F.spokePositions ↔ i = 1 ∨ i = F.cycle.length - 1 ∨
      ∃ j ∈ F.indices, j.val = i := by
  classical
  simp [spokePositions, Finset.mem_image]

/-- All spokes have positions strictly between zero and the cycle length. -/
theorem CycleWithIncidentChords.spokePosition_bounds (F : CycleWithIncidentChords H)
    {i : ℕ} (hi : i ∈ F.spokePositions) : 1 ≤ i ∧ i < F.cycle.length := by
  have hlen := F.isCycle.three_le_length
  rcases F.mem_spokePositions.mp hi with rfl | rfl | ⟨j, hj, rfl⟩
  · omega
  · omega
  · obtain ⟨h2, hend⟩ := F.proper_indices j hj
    omega

/-- The base is adjacent to the vertex at every spoke position. -/
theorem CycleWithIncidentChords.spokePosition_adj (F : CycleWithIncidentChords H)
    {i : ℕ} (hi : i ∈ F.spokePositions) : H.Adj F.base (F.cycle.getVert i) := by
  rcases F.mem_spokePositions.mp hi with rfl | rfl | ⟨j, hj, rfl⟩
  · exact F.cycle.adj_snd F.isCycle.not_nil
  · exact (F.cycle.adj_penultimate F.isCycle.not_nil).symm
  · exact F.chord_adj j hj

/-- Proper diagonals are distinct from both rim neighbors, so two positions are added. -/
theorem CycleWithIncidentChords.card_spokePositions (F : CycleWithIncidentChords H) :
    F.spokePositions.card = F.indices.card + 2 := by
  classical
  have hlen := F.isCycle.three_le_length
  have hfirst : 1 ∉ F.indices.image Fin.val := by
    rintro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    have := (F.proper_indices j hj).1
    omega
  have hlast : F.cycle.length - 1 ∉ F.indices.image Fin.val := by
    rintro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    have := (F.proper_indices j hj).2
    omega
  have hne : 1 ≠ F.cycle.length - 1 := by omega
  simp [spokePositions, Finset.card_insert_of_notMem, hfirst, hlast, hne,
    Finset.card_image_of_injective _ Fin.val_injective]

end JSP000078

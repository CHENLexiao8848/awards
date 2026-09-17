import JSP000078.FanRegions
import JSP000078.FanRectanglePaths

/-!
# Realizing the rectangle length sets by simple paths

Every length in one of the three finite rectangles is realized by a
simple path between the two prescribed cycle positions.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

/-- Each left-right rectangle length is realized by a simple path. -/
theorem CycleWithIncidentChords.exists_path_of_mem_lengthsLR
    (F : CycleWithIncidentChords H) {r s n : ℕ}
    (hrs : r < s) (hn : n ∈ F.lengthsLR r s) :
    ∃ p : H.Walk (F.cycle.getVert r) (F.cycle.getVert s), p.IsPath ∧ p.length = n := by
  classical
  obtain ⟨⟨i, j⟩, hij, hlen⟩ := Finset.mem_image.mp hn
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  obtain ⟨hiS, hir⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjS, hsj⟩ := Finset.mem_filter.mp hj
  obtain ⟨p, hp, hplen⟩ := exists_fan_path_LR F.isCycle
    (F.spokePosition_bounds hiS).1 hir hrs hsj (F.spokePosition_bounds hjS).2
    (F.spokePosition_adj hiS) (F.spokePosition_adj hjS)
  exact ⟨p, hp, hplen.trans hlen⟩

/-- Each left-middle rectangle length is realized by a simple path. -/
theorem CycleWithIncidentChords.exists_path_of_mem_lengthsLM
    (F : CycleWithIncidentChords H) {r s n : ℕ}
    (hs : s < F.cycle.length) (hn : n ∈ F.lengthsLM r s) :
    ∃ p : H.Walk (F.cycle.getVert r) (F.cycle.getVert s), p.IsPath ∧ p.length = n := by
  classical
  obtain ⟨⟨i, j⟩, hij, hlen⟩ := Finset.mem_image.mp hn
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  obtain ⟨hiS, hir⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjS, hrj, hjs⟩ := Finset.mem_filter.mp hj
  obtain ⟨p, hp, hplen⟩ := exists_fan_path_LM F.isCycle
    (F.spokePosition_bounds hiS).1 hir hrj hjs hs
    (F.spokePosition_adj hiS) (F.spokePosition_adj hjS)
  exact ⟨p, hp, hplen.trans hlen⟩

/-- Each middle-right rectangle length is realized by a simple path. -/
theorem CycleWithIncidentChords.exists_path_of_mem_lengthsMR
    (F : CycleWithIncidentChords H) {r s n : ℕ}
    (hr : 1 ≤ r) (hn : n ∈ F.lengthsMR r s) :
    ∃ p : H.Walk (F.cycle.getVert r) (F.cycle.getVert s), p.IsPath ∧ p.length = n := by
  classical
  obtain ⟨⟨i, j⟩, hij, hlen⟩ := Finset.mem_image.mp hn
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  obtain ⟨hiS, hri, his⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjS, hsj⟩ := Finset.mem_filter.mp hj
  obtain ⟨p, hp, hplen⟩ := exists_fan_path_MR F.isCycle
    hr hri his hsj (F.spokePosition_bounds hjS).2
    (F.spokePosition_adj hiS) (F.spokePosition_adj hjS)
  exact ⟨p, hp, hplen.trans hlen⟩

/-- The union of lengths realized by the three two-spoke rectangles. -/
noncomputable def CycleWithIncidentChords.rectangleLengths
    (F : CycleWithIncidentChords H) (r s : ℕ) : Finset ℕ :=
  F.lengthsLR r s ∪ F.lengthsLM r s ∪ F.lengthsMR r s

theorem CycleWithIncidentChords.lengthsLR_subset_rectangleLengths
    (F : CycleWithIncidentChords H) (r s : ℕ) :
    F.lengthsLR r s ⊆ F.rectangleLengths r s := by
  intro n hn
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hn)

theorem CycleWithIncidentChords.lengthsLM_subset_rectangleLengths
    (F : CycleWithIncidentChords H) (r s : ℕ) :
    F.lengthsLM r s ⊆ F.rectangleLengths r s := by
  intro n hn
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hn)

theorem CycleWithIncidentChords.lengthsMR_subset_rectangleLengths
    (F : CycleWithIncidentChords H) (r s : ℕ) :
    F.lengthsMR r s ⊆ F.rectangleLengths r s := by
  intro n hn
  exact Finset.mem_union_right _ hn

/-- Every rectangle length is realized by a simple path between the
prescribed internal endpoints. -/
theorem CycleWithIncidentChords.exists_path_of_mem_rectangleLengths
    (F : CycleWithIncidentChords H) {r s n : ℕ}
    (hr : 1 ≤ r) (hrs : r < s) (hs : s < F.cycle.length)
    (hn : n ∈ F.rectangleLengths r s) :
    ∃ p : H.Walk (F.cycle.getVert r) (F.cycle.getVert s), p.IsPath ∧ p.length = n := by
  rcases Finset.mem_union.mp hn with hn | hn
  · rcases Finset.mem_union.mp hn with hn | hn
    · exact F.exists_path_of_mem_lengthsLR hrs hn
    · exact F.exists_path_of_mem_lengthsLM hs hn
  · exact F.exists_path_of_mem_lengthsMR hr hn

end JSP000078

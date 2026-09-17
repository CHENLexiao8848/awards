import JSP000078.FanRectangleBounds
import JSP000078.FanRectangleRealization
import JSP000078.FanSmallCase
import JSP000078.TriplePathCounting

/-! # Different path lengths between two nonbase cycle positions -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

/-- The three rectangle families, plus the one-chord exception, give k+1
different simple path lengths between any increasing internal positions. -/
theorem CycleWithIncidentChords.exists_paths_between_positions
    (F : CycleWithIncidentChords H) (k : ℕ) (hk : 1 ≤ k)
    (hcard : F.indices.card = 2 * k - 1) {r s : ℕ}
    (hr : 1 ≤ r) (hrs : r < s) (hs : s < F.cycle.length) :
    ∃ P : Fin (k + 1) → H.Walk (F.cycle.getVert r) (F.cycle.getVert s),
      (∀ i, (P i).IsPath) ∧ Function.Injective (fun i ↦ (P i).length) := by
  classical
  by_cases hcase : 2 ≤ k ∨ F.middlePositions r s = ∅
  · have htotal : (F.leftPositions r).card + (F.middlePositions r s).card +
        (F.rightPositions s).card = 2 * k + 1 := by
      rw [F.card_positions_sum hrs, F.card_spokePositions, hcard]
      omega
    have hLR : (F.leftPositions r).card + (F.rightPositions s).card - 1 ≤
        (F.rectangleLengths r s).card :=
      (F.card_lengthsLR_lower hr hs).trans
        (Finset.card_le_card (F.lengthsLR_subset_rectangleLengths r s))
    have hLM : (F.middlePositions r s).Nonempty →
        (F.leftPositions r).card + (F.middlePositions r s).card - 1 ≤
          (F.rectangleLengths r s).card := fun hm ↦
      (F.card_lengthsLM_lower hr hm).trans
        (Finset.card_le_card (F.lengthsLM_subset_rectangleLengths r s))
    have hMR : (F.middlePositions r s).Nonempty →
        (F.middlePositions r s).card + (F.rightPositions s).card - 1 ≤
          (F.rectangleLengths r s).card := fun hm ↦
      (F.card_lengthsMR_lower hs hm).trans
        (Finset.card_le_card (F.lengthsMR_subset_rectangleLengths r s))
    obtain ⟨P, hP, hInj, _⟩ := exists_paths_of_three_region_bounds
      (F.rectangleLengths r s) (F.leftPositions r) (F.middlePositions r s)
      (F.rightPositions s) k hk hcase (F.leftPositions_nonempty hr)
      (F.rightPositions_nonempty hs) htotal hLR hLM hMR
      (fun n hn ↦ F.exists_path_of_mem_rectangleLengths hr hrs hs hn)
    exact ⟨P, hP, hInj⟩
  · have hkOne : k = 1 := by omega
    subst k
    have hm : (F.middlePositions r s).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (fun h ↦ hcase (Or.inr h))
    obtain ⟨t, ht⟩ := hm
    obtain ⟨htS, hrt, hts⟩ := Finset.mem_filter.mp ht
    exact exists_two_fan_paths_of_internal_spoke F.isCycle hr hrt hts hs
      (F.spokePosition_adj htS)

end JSP000078

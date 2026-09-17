import JSP000078.FanRegions
import JSP000078.RectangleCounting

/-! # Lower bounds on the three rectangle length sets -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

theorem CycleWithIncidentChords.card_lengthsLR_lower (F : CycleWithIncidentChords H)
    {r s : ℕ} (hr : 1 ≤ r) (hs : s < F.cycle.length) :
    (F.leftPositions r).card + (F.rightPositions s).card - 1 ≤ (F.lengthsLR r s).card := by
  apply card_add_card_sub_one_le_card_rectangle_sum _ _
    (F.leftPositions_nonempty hr) (F.rightPositions_nonempty hs)
    (fun i ↦ r - i) (fun j ↦ j - s) 2
  · intro i hi j hj heq
    have hi' : i ≤ r := (Finset.mem_filter.mp hi).2
    have hj' : j ≤ r := (Finset.mem_filter.mp hj).2
    change r - i = r - j at heq
    omega
  · intro i hi j hj heq
    have hi' : s ≤ i := (Finset.mem_filter.mp hi).2
    have hj' : s ≤ j := (Finset.mem_filter.mp hj).2
    change i - s = j - s at heq
    omega

theorem CycleWithIncidentChords.card_lengthsLM_lower (F : CycleWithIncidentChords H)
    {r s : ℕ} (hr : 1 ≤ r) (hm : (F.middlePositions r s).Nonempty) :
    (F.leftPositions r).card + (F.middlePositions r s).card - 1 ≤ (F.lengthsLM r s).card := by
  apply card_add_card_sub_one_le_card_rectangle_sum _ _
    (F.leftPositions_nonempty hr) hm (fun i ↦ r - i) (fun j ↦ s - j) 2
  · intro i hi j hj heq
    have hi' : i ≤ r := (Finset.mem_filter.mp hi).2
    have hj' : j ≤ r := (Finset.mem_filter.mp hj).2
    change r - i = r - j at heq
    omega
  · intro i hi j hj heq
    have hi' : i < s := (Finset.mem_filter.mp hi).2.2
    have hj' : j < s := (Finset.mem_filter.mp hj).2.2
    change s - i = s - j at heq
    omega

theorem CycleWithIncidentChords.card_lengthsMR_lower (F : CycleWithIncidentChords H)
    {r s : ℕ} (hs : s < F.cycle.length) (hm : (F.middlePositions r s).Nonempty) :
    (F.middlePositions r s).card + (F.rightPositions s).card - 1 ≤ (F.lengthsMR r s).card := by
  apply card_add_card_sub_one_le_card_rectangle_sum _ _
    hm (F.rightPositions_nonempty hs) (fun i ↦ i - r) (fun j ↦ j - s) 2
  · intro i hi j hj heq
    have hi' : r < i := (Finset.mem_filter.mp hi).2.1
    have hj' : r < j := (Finset.mem_filter.mp hj).2.1
    change i - r = j - r at heq
    omega
  · intro i hi j hj heq
    have hi' : s ≤ i := (Finset.mem_filter.mp hi).2
    have hj' : s ≤ j := (Finset.mem_filter.mp hj).2
    change i - s = j - s at heq
    omega

end JSP000078

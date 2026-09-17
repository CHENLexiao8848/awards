import JSP000078.CyclicDistanceSets
import JSP000078.NearParityExhaustion

/-! # Finite distance data for a near-saturated outside hub -/

namespace JSP000078

/-- Individual odd-cycle lengths from a hub with an even number of
selected neighbors on an odd cycle. All cardinal conclusions must be proved. -/
structure HubDistanceData where
  circumference : ℕ
  parameter : ℕ
  marks : Finset ℕ
  lengths : Finset ℕ
  circumference_odd : Odd circumference
  parameter_pos : 1 ≤ parameter
  mark_bounds : ∀ x ∈ marks, x < circumference
  mark_card : marks.card = 2 * parameter
  length_card : lengths.card = parameter
  circumference_mem : circumference ∈ lengths
  odd_cycle : ∀ a ∈ marks, ∀ d ∈ properDistances marks circumference a,
    Odd d → d + 2 ∈ lengths
  even_cycle : ∀ a ∈ marks, ∀ d ∈ properDistances marks circumference a,
    Even d → circumference - d + 2 ∈ lengths

theorem HubDistanceData.parity_exhaustion (H : HubDistanceData) {a : ℕ} (ha : a ∈ H.marks) :
    let D := properDistances H.marks H.circumference a
    (((D.filter Odd).card = H.parameter ∧ (D.filter Even).card = H.parameter - 1) ∨
      ((D.filter Odd).card = H.parameter - 1 ∧ (D.filter Even).card = H.parameter)) ∧
    ((D.filter Odd).card = H.parameter → (D.filter Odd).image (fun d ↦ d + 2) = H.lengths) ∧
    ((D.filter Even).card = H.parameter →
      (D.filter Even).image (fun d ↦ H.circumference - d + 2) = H.lengths) := by
  apply near_spoke_parity_exhaustion _ _ _ _ H.parameter_pos
  · rw [properDistances_card H.marks H.mark_bounds ha, H.mark_card]
  · exact H.length_card
  · exact properDistances_bounds H.marks H.mark_bounds ha
  · exact H.odd_cycle a ha
  · exact H.even_cycle a ha

end JSP000078

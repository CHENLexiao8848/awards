import JSP000078.HubDistanceData
import JSP000078.CyclicDistanceRebase
import JSP000078.CyclicGapExistence

/-!
# Rebasing hub distances at an even gap

Cyclic translation preserves all individual length witnesses. An even
number of marks on an odd circumference has an even successive gap, so
the origin may be placed just before a positive even least marked distance.
-/

namespace JSP000078

/-- Rebase all hub marks at one selected mark, preserving every proper
distance set and hence both odd-cycle witness families. -/
def HubDistanceData.rebase (H : HubDistanceData) (a : ℕ) (ha : a ∈ H.marks) :
    HubDistanceData where
  circumference := H.circumference
  parameter := H.parameter
  marks := H.marks.image (cyclicDistance H.circumference a)
  lengths := H.lengths
  circumference_odd := H.circumference_odd
  parameter_pos := H.parameter_pos
  mark_bounds := image_cyclicDistance_bounds H.marks H.mark_bounds ha
  mark_card := by rw [card_image_cyclicDistance H.marks H.mark_bounds ha, H.mark_card]
  length_card := H.length_card
  circumference_mem := H.circumference_mem
  odd_cycle := by
    intro b hb d hd hdo
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    rw [properDistances_rebase H.marks H.mark_bounds ha hx] at hd
    exact H.odd_cycle x hx d hd hdo
  even_cycle := by
    intro b hb d hd hde
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    rw [properDistances_rebase H.marks H.mark_bounds ha hx] at hd
    exact H.even_cycle x hx d hd hde

@[simp] theorem HubDistanceData.rebase_circumference (H : HubDistanceData) (a : ℕ)
    (ha : a ∈ H.marks) : (H.rebase a ha).circumference = H.circumference := rfl

@[simp] theorem HubDistanceData.rebase_parameter (H : HubDistanceData) (a : ℕ)
    (ha : a ∈ H.marks) : (H.rebase a ha).parameter = H.parameter := rfl

@[simp] theorem HubDistanceData.rebase_lengths (H : HubDistanceData) (a : ℕ)
    (ha : a ∈ H.marks) : (H.rebase a ha).lengths = H.lengths := rfl

theorem HubDistanceData.zero_mem_rebase_marks (H : HubDistanceData) (a : ℕ)
    (ha : a ∈ H.marks) : 0 ∈ (H.rebase a ha).marks :=
  zero_mem_image_cyclicDistance H.marks H.mark_bounds ha

theorem HubDistanceData.rebase_marks_card (H : HubDistanceData) (a : ℕ)
    (ha : a ∈ H.marks) : (H.rebase a ha).marks.card = H.marks.card :=
  card_image_cyclicDistance H.marks H.mark_bounds ha

/-- If zero is already marked, rebase at the start of an even successive
gap to make that gap the least positive marked position. -/
theorem HubDistanceData.exists_rebase_even_min_gap_of_zero (H : HubDistanceData)
    (hzero : 0 ∈ H.marks) :
    ∃ (a : ℕ) (ha : a ∈ H.marks) (g : ℕ),
      0 ∈ (H.rebase a ha).marks ∧ 1 ≤ g ∧ Even g ∧ g ∈ (H.rebase a ha).marks ∧
      ∀ x ∈ (H.rebase a ha).marks, x ≠ 0 → g ≤ x := by
  have hcard : Even H.marks.card := by rw [H.mark_card]; exact even_two_mul H.parameter
  rcases exists_even_cyclic_gap H.marks H.circumference H.circumference_odd
      H.mark_bounds hzero hcard with ⟨a, ha, b, hb, hab, heven, hnone⟩ | ⟨a, ha, hpos, heven, hmax⟩
  · refine ⟨a, ha, b - a, H.zero_mem_rebase_marks a ha, by omega, heven, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨b, hb, cyclicDistance_eq_sub (H.mark_bounds b hb) hab.le⟩
    · intro x hx hxne
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have haN := H.mark_bounds a ha
      have hbN := H.mark_bounds b hb
      have hzN := H.mark_bounds z hz
      by_cases haz : a ≤ z
      · rw [cyclicDistance_eq_sub hzN haz] at hxne ⊢
        have hn := hnone z hz
        omega
      · rw [cyclicDistance_eq_wrap haN (by omega : z < a)]
        omega
  · have haN := H.mark_bounds a ha
    have haPos : 0 < a := by
      by_contra h
      have haZero : a = 0 := by omega
      have hNE : ¬Even H.circumference := Nat.not_even_iff_odd.mpr H.circumference_odd
      exact hNE (by simpa only [haZero, Nat.sub_zero] using heven)
    refine ⟨a, ha, H.circumference - a, H.zero_mem_rebase_marks a ha, hpos, heven, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨0, hzero, by
        simpa only [Nat.add_zero] using cyclicDistance_eq_wrap haN haPos⟩
    · intro x hx hxne
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hza := hmax z hz
      by_cases hzeq : z = a
      · subst z
        have hd := cyclicDistance_eq_sub haN (le_refl a)
        simp only [Nat.sub_self] at hd
        exact (hxne hd).elim
      · rw [cyclicDistance_eq_wrap haN (by omega : z < a)]
        omega

/-- Every hub distance configuration can be normalized so zero is marked
and the least positive mark is even, without changing the circumference,
parameter, or available length set. -/
theorem HubDistanceData.exists_rebase_even_min_gap (H : HubDistanceData) :
    ∃ (Y : HubDistanceData) (g : ℕ),
      Y.circumference = H.circumference ∧ Y.parameter = H.parameter ∧ Y.lengths = H.lengths ∧
      0 ∈ Y.marks ∧ 1 ≤ g ∧ Even g ∧ g ∈ Y.marks ∧
      ∀ x ∈ Y.marks, x ≠ 0 → g ≤ x := by
  have hne : H.marks.Nonempty := Finset.card_pos.mp (by have := H.mark_card; have := H.parameter_pos; omega)
  obtain ⟨a, ha⟩ := hne
  let H₀ := H.rebase a ha
  obtain ⟨b, hb, g, hzero, hpos, heven, hg, hmin⟩ :=
    H₀.exists_rebase_even_min_gap_of_zero (H.zero_mem_rebase_marks a ha)
  exact ⟨H₀.rebase b hb, g, rfl, rfl, rfl, hzero, hpos, heven, hg, hmin⟩

end JSP000078

import JSP000078.HubDistanceData
import JSP000078.EvenGapForcesTwo

/-! # An even minimum marked gap in a hub has length two -/

namespace JSP000078

theorem HubDistanceData.even_minimum_gap_two (H : HubDistanceData)
    (hzero : 0 ∈ H.marks) {a : ℕ} (ha : a ∈ H.marks) (hapos : 1 ≤ a)
    (he : Even a) (hmin : ∀ x ∈ H.marks, x ≠ 0 → a ≤ x) :
    a = 2 ∧
      ((H.marks.erase 0).filter Odd).card = H.parameter - 1 ∧
      ((properDistances H.marks H.circumference a).filter Odd).card = H.parameter := by
  let S := H.marks.erase 0
  have haS : a ∈ S := Finset.mem_erase.mpr ⟨by omega, ha⟩
  have hminS : ∀ x ∈ S, a ≤ x := fun x hx ↦
    hmin x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.mp hx).1
  have hboundS : ∀ x ∈ S, x < H.circumference := fun x hx ↦
    H.mark_bounds x (Finset.mem_of_mem_erase hx)
  have hzeroD := properDistances_zero H.marks H.mark_bounds
  have hshift := properDistances_eq_shiftAfterMinimum H.marks H.mark_bounds hzero ha hapos hmin
  have hzeroEx := H.parity_exhaustion hzero
  have haEx := H.parity_exhaustion ha
  have hSclasses : (S.filter Odd).card = H.parameter - 1 ∨ (S.filter Odd).card = H.parameter := by
    rw [hzeroD] at hzeroEx
    rcases hzeroEx.1 with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  have hTclasses : ((shiftAfterMinimum S H.circumference a).filter Odd).card = H.parameter - 1 ∨
      ((shiftAfterMinimum S H.circumference a).filter Odd).card = H.parameter := by
    rw [hshift] at haEx
    rcases haEx.1 with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  have hrec := odd_card_shiftAfterMinimum_of_even S H.circumference a H.circumference_odd
    haS hminS hboundS he
  have hhigh : ((properDistances H.marks H.circumference a).filter Odd).card = H.parameter := by
    rw [hshift]
    change ((shiftAfterMinimum S H.circumference a).filter Odd).card = H.parameter
    have := H.parameter_pos
    omega
  have hpred : H.circumference - 2 ∈ properDistances H.marks H.circumference a := by
    have himage := haEx.2.1 hhigh
    have hN : H.circumference ∈
        ((properDistances H.marks H.circumference a).filter Odd).image (fun d ↦ d + 2) :=
      himage.symm ▸ H.circumference_mem
    obtain ⟨d, hd, hdN⟩ := Finset.mem_image.mp hN
    have heq : d = H.circumference - 2 := by omega
    exact heq ▸ (Finset.mem_filter.mp hd).1
  have hresult := even_gap_forces_two S H.circumference a H.parameter H.parameter_pos
    H.circumference_odd haS hapos hminS hboundS he hSclasses hTclasses (hshift ▸ hpred)
  exact ⟨hresult.2.2, hresult.1, hhigh⟩

end JSP000078

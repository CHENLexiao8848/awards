import JSP000078.HubDistanceRebase
import JSP000078.HubEvenMinimum
import JSP000078.NormalizedHubRigidity
import JSP000078.OutsideHubData

/-! # Rigidity of an even marked neighbor set on an odd cycle -/

namespace JSP000078

open SimpleGraph

/-- For k≥2, 2k selected neighbors of one outside hub and only k odd
cycle lengths force the odd cycle to have exactly 2k+1 vertices. -/
theorem HubDistanceData.circumference_eq_two_mul_add_one (H : HubDistanceData)
    (hk : 2 ≤ H.parameter) : H.circumference = 2 * H.parameter + 1 := by
  obtain ⟨Y, g, hN, hkY, _, hzero, hgpos, hgEven, hg, hmin⟩ := H.exists_rebase_even_min_gap
  obtain ⟨hgTwo, hlow, hhigh⟩ := Y.even_minimum_gap_two hzero hg hgpos hgEven hmin
  have htwo : 2 ∈ Y.marks := hgTwo ▸ hg
  have hone : 1 ∉ Y.marks := by
    intro h
    have := hmin 1 h (by decide)
    omega
  have hlow' : ((properDistances Y.marks Y.circumference 0).filter Odd).card = Y.parameter - 1 := by
    rw [properDistances_zero Y.marks Y.mark_bounds]
    exact hlow
  have hhigh' : ((properDistances Y.marks Y.circumference 2).filter Odd).card = Y.parameter := by
    simpa only [hgTwo] using hhigh
  have hmarks := Y.normalized_marks_eq_range_erase (by omega) hzero htwo hone hlow' hhigh'
  have hNpos : 1 < Y.circumference := by have := Y.mark_bounds 2 htwo; omega
  have hcard := congrArg Finset.card hmarks
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hNpos), Finset.card_range, Y.mark_card] at hcard
  omega

theorem odd_cycle_length_eq_of_outside_hub {V : Type*} [Fintype V]
    {G : SimpleGraph V} {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hv : v ∉ C.support)
    (X : Finset V) (k : ℕ) (hk : 2 ≤ k) (hcard : X.card = 2 * k)
    (hK : (oddCycleLengths G).card = k)
    (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj v x) : C.length = 2 * k + 1 := by
  classical
  let H := outsideHubData hC hCO hv X k (by omega) hcard hK hX
  exact H.circumference_eq_two_mul_add_one hk

end JSP000078

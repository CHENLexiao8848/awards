import JSP000078.HubDistanceData
import JSP000078.NormalizedOddGapClosure
import Mathlib.Data.Finset.Max

/-!
# Rigidity after normalizing an even marked gap to zero and two

At the two ends of the gap, complementary parity classes exhaust the
available lengths. These identities force all positions except one to be marked.
-/

namespace JSP000078

namespace HubDistanceData

/-- At zero, proper odd distances are precisely the odd marked positions. -/
theorem odd_distances_zero (H : HubDistanceData) :
    (properDistances H.marks H.circumference 0).filter Odd = H.marks.filter Odd := by
  rw [properDistances_zero H.marks H.mark_bounds, Finset.filter_erase]
  apply Finset.erase_eq_of_notMem
  simp

/-- At zero, proper even distances are precisely the positive even marks. -/
theorem even_distances_zero (H : HubDistanceData) :
    (properDistances H.marks H.circumference 0).filter Even =
      H.marks.filter fun e ↦ 0 < e ∧ Even e := by
  rw [properDistances_zero H.marks H.mark_bounds]
  ext e
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨heZero, heX⟩, heEven⟩
    exact ⟨heX, by omega, heEven⟩
  · rintro ⟨heX, hePos, heEven⟩
    exact ⟨⟨by omega, heX⟩, heEven⟩

/-- The odd-cycle image at position two consists of the odd marks themselves
and the circumference, when zero and two are marked but one is absent. -/
theorem odd_image_at_two (H : HubDistanceData)
    (hzero : 0 ∈ H.marks) (htwo : 2 ∈ H.marks) (hone : 1 ∉ H.marks) :
    ((properDistances H.marks H.circumference 2).filter Odd).image (fun d ↦ d + 2) =
      insert H.circumference (H.marks.filter Odd) := by
  classical
  have htwoN := H.mark_bounds 2 htwo
  have hNmod := Nat.odd_iff.mp H.circumference_odd
  ext n
  constructor
  · intro hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hdD, hdOdd⟩ := Finset.mem_filter.mp hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hdD
    obtain ⟨hxTwo, hxX⟩ := Finset.mem_erase.mp hx
    have hxN := H.mark_bounds x hxX
    by_cases hxZero : x = 0
    · subst x
      apply Finset.mem_insert.mpr
      left
      rw [cyclicDistance_eq_wrap htwoN (by decide)]
      omega
    · have hxOne : x ≠ 1 := fun h ↦ hone (h ▸ hxX)
      have hxGe : 2 ≤ x := by omega
      rw [cyclicDistance_eq_sub hxN hxGe] at hdOdd ⊢
      apply Finset.mem_insert.mpr
      right
      have hxOdd : Odd x := by
        have hdmod := Nat.odd_iff.mp hdOdd
        rw [Nat.odd_iff]
        omega
      have heq : x - 2 + 2 = x := by omega
      rw [heq]
      exact Finset.mem_filter.mpr ⟨hxX, hxOdd⟩
  · intro hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · apply Finset.mem_image.mpr
      refine ⟨H.circumference - 2, Finset.mem_filter.mpr ⟨?_, ?_⟩, by omega⟩
      · apply Finset.mem_image.mpr
        refine ⟨0, Finset.mem_erase.mpr ⟨by decide, hzero⟩, ?_⟩
        rw [cyclicDistance_eq_wrap htwoN (by decide)]
        omega
      · rw [Nat.odd_iff]
        omega
    · obtain ⟨hnX, hnOdd⟩ := Finset.mem_filter.mp hn
      have hnN := H.mark_bounds n hnX
      have hnmod := Nat.odd_iff.mp hnOdd
      have hnOne : n ≠ 1 := fun h ↦ hone (h ▸ hnX)
      have hnGe : 3 ≤ n := by omega
      apply Finset.mem_image.mpr
      refine ⟨n - 2, Finset.mem_filter.mpr ⟨?_, ?_⟩, by omega⟩
      · apply Finset.mem_image.mpr
        exact ⟨n, Finset.mem_erase.mpr ⟨by omega, hnX⟩, cyclicDistance_eq_sub hnN (by omega)⟩
      · rw [Nat.odd_iff]
        omega

/-- If the first three even positions are marked but one and three are
absent, rebasing at four produces two extra odd distances. -/
theorem odd_count_at_four_lower (H : HubDistanceData)
    (hzero : 0 ∈ H.marks) (htwo : 2 ∈ H.marks) (hfour : 4 ∈ H.marks)
    (hone : 1 ∉ H.marks) (hthree : 3 ∉ H.marks) :
    (H.marks.filter Odd).card + 2 ≤
      ((properDistances H.marks H.circumference 4).filter Odd).card := by
  classical
  let O := H.marks.filter Odd
  let M := O.image fun d ↦ d - 4
  have hfourN := H.mark_bounds 4 hfour
  have hNmod := Nat.odd_iff.mp H.circumference_odd
  have hOge : ∀ d ∈ O, 5 ≤ d := by
    intro d hd
    obtain ⟨hdX, hdOdd⟩ := Finset.mem_filter.mp hd
    have hdmod := Nat.odd_iff.mp hdOdd
    have hdOne : d ≠ 1 := fun h ↦ hone (h ▸ hdX)
    have hdThree : d ≠ 3 := fun h ↦ hthree (h ▸ hdX)
    omega
  have hMcard : M.card = O.card := Finset.card_image_of_injOn (by
    intro d hd e he heq
    have hdGe := hOge d hd
    have heGe := hOge e he
    change d - 4 = e - 4 at heq
    omega)
  have hwrap₀not : H.circumference - 4 ∉ M := by
    intro hmem
    obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.mp hmem
    have hdN := H.mark_bounds d (Finset.mem_filter.mp hd).1
    have hdGe := hOge d hd
    omega
  have hwrap₂not : H.circumference - 2 ∉ insert (H.circumference - 4) M := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem
    · omega
    · obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.mp hmem
      have hdN := H.mark_bounds d (Finset.mem_filter.mp hd).1
      have hdGe := hOge d hd
      omega
  have hsub : insert (H.circumference - 2) (insert (H.circumference - 4) M) ⊆
      (properDistances H.marks H.circumference 4).filter Odd := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨2, Finset.mem_erase.mpr ⟨by decide, htwo⟩, ?_⟩, ?_⟩
      · rw [cyclicDistance_eq_wrap hfourN (by decide)]
        omega
      · rw [Nat.odd_iff]
        omega
    · rcases Finset.mem_insert.mp hn with rfl | hn
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨0, Finset.mem_erase.mpr ⟨by decide, hzero⟩, ?_⟩, ?_⟩
        · rw [cyclicDistance_eq_wrap hfourN (by decide)]
          omega
        · rw [Nat.odd_iff]
          omega
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
        have hdGe := hOge d hd
        obtain ⟨hdX, hdOdd⟩ := Finset.mem_filter.mp hd
        have hdN := H.mark_bounds d hdX
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨d, Finset.mem_erase.mpr ⟨by omega, hdX⟩,
          cyclicDistance_eq_sub hdN (by omega)⟩, ?_⟩
        have hdmod := Nat.odd_iff.mp hdOdd
        rw [Nat.odd_iff]
        omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hwrap₂not, Finset.card_insert_of_notMem hwrap₀not, hMcard] at hcard
  change O.card + 2 ≤ _
  omega

/-- A normalized even gap with low odd count at zero and high odd count
at two forces all positions except one to be marked. -/
theorem normalized_marks_eq_range_erase (H : HubDistanceData)
    (hk : 2 ≤ H.parameter)
    (hzero : 0 ∈ H.marks) (htwo : 2 ∈ H.marks) (hone : 1 ∉ H.marks)
    (hlow : ((properDistances H.marks H.circumference 0).filter Odd).card = H.parameter - 1)
    (hhigh : ((properDistances H.marks H.circumference 2).filter Odd).card = H.parameter) :
    H.marks = (Finset.range H.circumference).erase 1 := by
  classical
  let O := H.marks.filter Odd
  have hOcard : O.card = H.parameter - 1 := by
    simpa only [H.odd_distances_zero] using hlow
  have hO : O.Nonempty := Finset.card_pos.mp (by omega)
  have hK : H.lengths = insert H.circumference O := by
    have hsat := (H.parity_exhaustion htwo).2.1 hhigh
    rw [H.odd_image_at_two hzero htwo hone] at hsat
    exact hsat.symm
  have hEvenCard : ((properDistances H.marks H.circumference 0).filter Even).card = H.parameter := by
    rcases (H.parity_exhaustion hzero).1 with h | h
    · omega
    · exact h.2
  have hreflect : (H.marks.filter fun e ↦ 0 < e ∧ Even e).image
      (fun e ↦ H.circumference - e + 2) = insert H.circumference O := by
    have h := (H.parity_exhaustion hzero).2.2 hEvenCard
    rw [H.even_distances_zero, hK] at h
    exact h
  have hclosed : ∀ d ∈ O, d + 2 ∈ O ∨ d + 2 = H.circumference := by
    intro d hd
    obtain ⟨hdX, hdOdd⟩ := Finset.mem_filter.mp hd
    have hdZero : d ≠ 0 := by
      have hdmod := Nat.odd_iff.mp hdOdd
      omega
    have hdD : d ∈ properDistances H.marks H.circumference 0 := by
      rw [properDistances_zero H.marks H.mark_bounds]
      exact Finset.mem_erase.mpr ⟨hdZero, hdX⟩
    have hmem := H.odd_cycle 0 hzero d hdD hdOdd
    rw [hK] at hmem
    exact (Finset.mem_insert.mp hmem).symm
  let m := O.max' hO
  have hmO : m ∈ O := O.max'_mem hO
  have hmN := H.mark_bounds m (Finset.mem_filter.mp hmO).1
  have hmplus : m + 2 = H.circumference := by
    rcases hclosed m hmO with hnext | hterm
    · have hmax : m + 2 ≤ m := O.le_max' _ hnext
      omega
    · exact hterm
  have hmthree : 3 ≤ m := by
    have hmod := Nat.odd_iff.mp (Finset.mem_filter.mp hmO).2
    have hmOne : m ≠ 1 := fun h ↦ hone (h ▸ (Finset.mem_filter.mp hmO).1)
    omega
  have hNfive : 5 ≤ H.circumference := by omega
  have hfour : 4 ∈ H.marks := by
    have hmImage : m ∈ (H.marks.filter fun e ↦ 0 < e ∧ Even e).image
        (fun e ↦ H.circumference - e + 2) := by
      rw [hreflect]
      exact Finset.mem_insert_of_mem hmO
    obtain ⟨e, he, hem⟩ := Finset.mem_image.mp hmImage
    have heX := (Finset.mem_filter.mp he).1
    have heN := H.mark_bounds e heX
    have heFour : e = 4 := by omega
    exact heFour ▸ heX
  have hthree : 3 ∈ H.marks := by
    by_contra hnot
    have hcount := H.odd_count_at_four_lower hzero htwo hfour hone hnot
    have hupper : ((properDistances H.marks H.circumference 4).filter Odd).card ≤ H.parameter := by
      rcases (H.parity_exhaustion hfour).1 with h | h <;> omega
    change O.card + 2 ≤ _ at hcount
    omega
  exact normalized_odd_gap_closure_eq_range_erase H.marks H.circumference
    H.circumference_odd hNfive H.mark_bounds hzero hone hthree hclosed hreflect

end HubDistanceData

end JSP000078

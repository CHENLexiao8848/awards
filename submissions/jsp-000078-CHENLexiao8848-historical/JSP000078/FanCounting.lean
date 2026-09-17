import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.NatAbs

namespace JSP000078

open scoped Pointwise

/-- Taking absolute values identifies at most two integers at each value. -/
theorem card_le_two_mul_card_natAbs (S : Finset ℤ) :
    S.card ≤ 2 * (S.image Int.natAbs).card := by
  let T := S.image Int.natAbs
  have hsub : S ⊆ T.image (fun n : ℕ => (n : ℤ)) ∪
      T.image (fun n : ℕ => -(n : ℤ)) := by
    intro z hz
    have habs : z.natAbs ∈ T := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    rcases Int.natAbs_eq_iff.mp (rfl : z.natAbs = z.natAbs) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z.natAbs, habs, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z.natAbs, habs, h.symm⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hp := Finset.card_image_le (s := T) (f := fun n : ℕ => (n : ℤ))
  have hn := Finset.card_image_le (s := T) (f := fun n : ℕ => -(n : ℤ))
  change S.card ≤ 2 * T.card
  omega

/-- Two nonempty finite integer sets produce at least half their combined
cardinality minus one distinct absolute differences. -/
theorem card_add_card_le_two_mul_card_abs_sub_add_one
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card ≤ 2 * ((A - B).image Int.natAbs).card + 1 := by
  have hdiff : A.card + B.card - 1 ≤ (A - B).card := by
    simpa only [sub_eq_add_neg, Finset.card_neg] using
      cauchy_davenport_add_of_linearOrder_isCancelAdd hA
        (Finset.neg_nonempty_iff.mpr hB)
  have habs := card_le_two_mul_card_natAbs (A - B)
  omega

/-- A convenient threshold form of the absolute-difference estimate. -/
theorem le_card_abs_sub_of_two_mul_add_one_le
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty)
    (k : ℕ) (hk : 2 * k + 1 ≤ A.card + B.card) :
    k ≤ ((A - B).image Int.natAbs).card := by
  have hcard := card_add_card_le_two_mul_card_abs_sub_add_one A B hA hB
  omega

/-- Distinct absolute differences between even and odd members of a finite
integer set. These count lengths, rather than the pairs realizing them. -/
def oddAbsDifferences (S : Finset ℤ) : Finset ℕ :=
  ((S.filter Even - S.filter Odd).image Int.natAbs)

theorem mem_oddAbsDifferences_iff (S : Finset ℤ) (n : ℕ) :
    n ∈ oddAbsDifferences S ↔
      ∃ a ∈ S, ∃ b ∈ S, Even a ∧ Odd b ∧ (a - b).natAbs = n := by
  simp only [oddAbsDifferences, Finset.mem_image, Finset.mem_sub,
    Finset.mem_filter]
  constructor
  · rintro ⟨z, ⟨a, ⟨ha, hea⟩, b, ⟨hb, hob⟩, rfl⟩, hn⟩
    exact ⟨a, ha, b, hb, hea, hob, hn⟩
  · rintro ⟨a, ha, b, hb, hea, hob, hn⟩
    exact ⟨a - b, ⟨a, ⟨ha, hea⟩, b, ⟨hb, hob⟩, rfl⟩, hn⟩

theorem odd_of_mem_oddAbsDifferences {S : Finset ℤ} {n : ℕ}
    (hn : n ∈ oddAbsDifferences S) : Odd n := by
  obtain ⟨a, _, b, _, hea, hob, rfl⟩ := (mem_oddAbsDifferences_iff S n).mp hn
  exact (hea.sub_odd hob).natAbs

/-- The arithmetic counting step of the odd fan argument: at least `2k + 1`
integer positions, including both parities, determine at least `k` distinct
odd absolute differences. -/
theorem le_card_oddAbsDifferences
    (S : Finset ℤ) (hEven : (S.filter Even).Nonempty)
    (hOdd : (S.filter Odd).Nonempty)
    (k : ℕ) (hk : 2 * k + 1 ≤ S.card) :
    k ≤ (oddAbsDifferences S).card := by
  have hpartition : (S.filter Even).card + (S.filter Odd).card = S.card := by
    simpa only [Int.not_even_iff_odd] using S.card_filter_add_card_filter_not Even
  apply le_card_abs_sub_of_two_mul_add_one_le _ _ hEven hOdd k
  omega

/-- Distinct odd distances between natural-number positions. -/
def oddNatDifferences (S : Finset ℕ) : Finset ℕ :=
  oddAbsDifferences (S.image fun n : ℕ => (n : ℤ))

theorem odd_of_mem_oddNatDifferences {S : Finset ℕ} {n : ℕ}
    (hn : n ∈ oddNatDifferences S) : Odd n :=
  odd_of_mem_oddAbsDifferences hn

/-- Natural positions witnessing a difference can always be put in increasing
order; the parity of the two endpoints need not be specified separately. -/
theorem mem_oddNatDifferences_iff (S : Finset ℕ) (n : ℕ) :
    n ∈ oddNatDifferences S ↔
      ∃ i ∈ S, ∃ j ∈ S, i < j ∧ Odd (j - i) ∧ j - i = n := by
  constructor
  · intro hn
    have hnOdd := odd_of_mem_oddNatDifferences hn
    obtain ⟨a, ha, b, hb, _, _, hab⟩ :=
      (mem_oddAbsDifferences_iff _ n).mp hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have hnmod := Nat.odd_iff.mp hnOdd
    rcases le_total i j with hij | hji
    · rw [Int.natAbs_natCast_sub_natCast_of_le hij] at hab
      exact ⟨i, hi, j, hj, by omega, hab ▸ hnOdd, hab⟩
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hji] at hab
      exact ⟨j, hj, i, hi, by omega, hab ▸ hnOdd, hab⟩
  · rintro ⟨i, hi, j, hj, hij, hOdd, hn⟩
    apply (mem_oddAbsDifferences_iff _ n).mpr
    have himem : (i : ℤ) ∈ S.image (fun n : ℕ => (n : ℤ)) :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hjmem : (j : ℤ) ∈ S.image (fun n : ℕ => (n : ℤ)) :=
      Finset.mem_image.mpr ⟨j, hj, rfl⟩
    rcases Nat.even_or_odd i with hiEven | hiOdd
    · have hjOdd : Odd j := (Nat.odd_sub hij.le).mp hOdd |>.mpr hiEven
      refine ⟨i, himem, j, hjmem, ?_, ?_, ?_⟩
      · simpa only [Int.even_coe_nat] using hiEven
      · simpa only [Int.odd_coe_nat] using hjOdd
      · simpa only [Int.natAbs_natCast_sub_natCast_of_le hij.le] using hn
    · have hjEven : Even j := (Nat.odd_sub' hij.le).mp hOdd |>.mp hiOdd
      refine ⟨j, hjmem, i, himem, ?_, ?_, ?_⟩
      · simpa only [Int.even_coe_nat] using hjEven
      · simpa only [Int.odd_coe_nat] using hiOdd
      · simpa only [Int.natAbs_natCast_sub_natCast_of_ge hij.le] using hn

/-- The counting estimate in the natural-position form used to build fan
cycles from ordered pairs of incident edges. -/
theorem le_card_oddNatDifferences
    (S : Finset ℕ) (hEven : (S.filter Even).Nonempty)
    (hOdd : (S.filter Odd).Nonempty)
    (k : ℕ) (hk : 2 * k + 1 ≤ S.card) :
    k ≤ (oddNatDifferences S).card := by
  apply le_card_oddAbsDifferences
  · obtain ⟨i, hi⟩ := hEven
    refine ⟨i, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩
    · simpa only [Int.even_coe_nat] using (Finset.mem_filter.mp hi).2
  · obtain ⟨i, hi⟩ := hOdd
    refine ⟨i, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩
    · simpa only [Int.odd_coe_nat] using (Finset.mem_filter.mp hi).2
  · simpa only [Finset.card_image_of_injective S Nat.cast_injective] using hk

end JSP000078

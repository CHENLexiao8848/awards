import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Parity counts after passing a consecutive marked vertex

If `a` is the least positive marked distance from one base, changing the
base to that marked vertex subtracts `a` from all other distances and adds
the wrap distance `N - a` back to the old base. The two parity recurrences
below use these explicit finite sets.
-/

namespace JSP000078

/-- Proper marked distances after changing the base to the least distance `a`. -/
def shiftAfterMinimum (S : Finset ℕ) (N a : ℕ) : Finset ℕ :=
  insert (N - a) ((S.erase a).image fun x ↦ x - a)

private theorem shifted_odd_image_card (S : Finset ℕ) (a : ℕ)
    (hmin : ∀ x ∈ S, a ≤ x) :
    (((S.erase a).image fun x ↦ x - a).filter Odd).card =
      ((S.erase a).filter fun x ↦ Odd (x - a)).card := by
  rw [Finset.filter_image]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxS : x ∈ S := Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1
  have hyS : y ∈ S := Finset.mem_of_mem_erase (Finset.mem_filter.mp hy).1
  have hxMin := hmin x hxS
  have hyMin := hmin y hyS
  change x - a = y - a at hxy
  omega

/-- An even marked gap increases the number of odd proper distances by one. -/
theorem odd_card_shiftAfterMinimum_of_even (S : Finset ℕ) (N a : ℕ)
    (hN : Odd N) (ha : a ∈ S) (hmin : ∀ x ∈ S, a ≤ x)
    (hbound : ∀ x ∈ S, x < N) (hea : Even a) :
    ((shiftAfterMinimum S N a).filter Odd).card = (S.filter Odd).card + 1 := by
  classical
  have haN := hbound a ha
  have hNmod := Nat.odd_iff.mp hN
  have hamod := Nat.even_iff.mp hea
  have hwrap : Odd (N - a) := by rw [Nat.odd_iff]; omega
  have hnot : N - a ∉ ((S.erase a).image fun x ↦ x - a).filter Odd := by
    intro hmem
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hmem).1
    have hxN := hbound x (Finset.mem_of_mem_erase hx)
    have hxMin := hmin x (Finset.mem_of_mem_erase hx)
    omega
  have hfilter : (S.erase a).filter (fun x ↦ Odd (x - a)) = S.filter Odd := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hx⟩, hxOdd⟩
      have hxMin := hmin x hx
      have hxmod := Nat.odd_iff.mp hxOdd
      exact ⟨hx, by rw [Nat.odd_iff]; omega⟩
    · rintro ⟨hx, hxOdd⟩
      have hxMin := hmin x hx
      have hxmod := Nat.odd_iff.mp hxOdd
      refine ⟨⟨by omega, hx⟩, ?_⟩
      rw [Nat.odd_iff]
      omega
  simp only [shiftAfterMinimum, Finset.filter_insert, hwrap, ite_true,
    Finset.card_insert_of_notMem hnot]
  rw [shifted_odd_image_card S a hmin, hfilter]

/-- An odd marked gap complements the odd proper-distance count within
the original number of proper marked distances. -/
theorem odd_card_shiftAfterMinimum_of_odd (S : Finset ℕ) (N a : ℕ)
    (hN : Odd N) (ha : a ∈ S) (hmin : ∀ x ∈ S, a ≤ x)
    (hbound : ∀ x ∈ S, x < N) (hoa : Odd a) :
    ((shiftAfterMinimum S N a).filter Odd).card + (S.filter Odd).card = S.card := by
  classical
  have haN := hbound a ha
  have hNmod := Nat.odd_iff.mp hN
  have hamod := Nat.odd_iff.mp hoa
  have hwrap : ¬Odd (N - a) := by
    rw [Nat.odd_iff]
    omega
  have hfilter : (S.erase a).filter (fun x ↦ Odd (x - a)) = S.filter fun x ↦ ¬Odd x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hx⟩, hxOdd⟩
      have hxMin := hmin x hx
      have hxmod := Nat.odd_iff.mp hxOdd
      refine ⟨hx, ?_⟩
      rw [Nat.odd_iff]
      omega
    · rintro ⟨hx, hxNot⟩
      have hxMin := hmin x hx
      have hxmod : x % 2 ≠ 1 := by simpa only [Nat.odd_iff] using hxNot
      refine ⟨⟨by omega, hx⟩, ?_⟩
      rw [Nat.odd_iff]
      omega
  simp only [shiftAfterMinimum, Finset.filter_insert, hwrap, ite_false]
  rw [shifted_odd_image_card S a hmin, hfilter]
  have hsum := S.card_filter_add_card_filter_not Odd
  omega

/-- The odd-gap recurrence in the `2k - 1` proper-distance form used for
`2k` marked cycle vertices. -/
theorem odd_card_shiftAfterMinimum_add_of_card (S : Finset ℕ) (N a k : ℕ)
    (hN : Odd N) (ha : a ∈ S) (hmin : ∀ x ∈ S, a ≤ x)
    (hbound : ∀ x ∈ S, x < N) (hoa : Odd a) (hcard : S.card = 2 * k - 1) :
    ((shiftAfterMinimum S N a).filter Odd).card + (S.filter Odd).card = 2 * k - 1 := by
  rw [odd_card_shiftAfterMinimum_of_odd S N a hN ha hmin hbound hoa, hcard]

end JSP000078

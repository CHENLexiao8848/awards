import JSP000078.CyclicParityCounts

/-!
# An even consecutive marked gap in the near-saturated case

An even gap increases the odd-distance count by one. If both bases have
only the two near-saturated possible counts, it passes from the smaller
count to the larger. The predecessor distance forced at the latter base
then bounds the gap by two.
-/

namespace JSP000078

/-- Every distance after changing the base to the minimum is at most
the wrap distance `N - a`. -/
theorem mem_shiftAfterMinimum_le_wrap
    (S : Finset ℕ) (N a : ℕ) (hbound : ∀ x ∈ S, x < N)
    {d : ℕ} (hd : d ∈ shiftAfterMinimum S N a) : d ≤ N - a := by
  simp only [shiftAfterMinimum, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | ⟨x, hx, rfl⟩
  · exact le_rfl
  · have hxN := hbound x (Finset.mem_of_mem_erase hx)
    omega

/-- A positive even gap is exactly two if the shifted distance set
contains the full odd-class predecessor distance `N - 2`. -/
theorem even_gap_eq_two_of_shifted_predecessor
    (S : Finset ℕ) (N a : ℕ) (ha : a ∈ S) (hapos : 1 ≤ a)
    (hbound : ∀ x ∈ S, x < N) (hea : Even a)
    (hpred : N - 2 ∈ shiftAfterMinimum S N a) : a = 2 := by
  have haN := hbound a ha
  have hpredle := mem_shiftAfterMinimum_le_wrap S N a hbound hpred
  have hamod := Nat.even_iff.mp hea
  omega

/-- The near-saturated parity-count alternatives determine the counts
on the two sides of an even gap, and the shifted predecessor then
forces that gap to have length two. -/
theorem even_gap_forces_two
    (S : Finset ℕ) (N a k : ℕ) (_hk : 1 ≤ k)
    (hN : Odd N) (ha : a ∈ S) (hapos : 1 ≤ a)
    (hmin : ∀ x ∈ S, a ≤ x) (hbound : ∀ x ∈ S, x < N)
    (hea : Even a)
    (hSclasses : (S.filter Odd).card = k - 1 ∨ (S.filter Odd).card = k)
    (hTclasses : ((shiftAfterMinimum S N a).filter Odd).card = k - 1 ∨
      ((shiftAfterMinimum S N a).filter Odd).card = k)
    (hpred : N - 2 ∈ shiftAfterMinimum S N a) :
    (S.filter Odd).card = k - 1 ∧
      ((shiftAfterMinimum S N a).filter Odd).card = k ∧ a = 2 := by
  have hrec := odd_card_shiftAfterMinimum_of_even S N a hN ha hmin hbound hea
  have hgap := even_gap_eq_two_of_shifted_predecessor S N a ha hapos hbound hea hpred
  exact ⟨by omega, by omega, hgap⟩

end JSP000078

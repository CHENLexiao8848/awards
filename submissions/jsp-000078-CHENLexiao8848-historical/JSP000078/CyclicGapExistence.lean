import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Ring.Parity

/-!
# An even marked gap on an odd cycle

An even number of marked positions, including zero, cannot divide an odd
cycle into only odd gaps. The proof first tracks the parity of the largest
marked position by inserting maxima, then includes the final wrap to zero.
-/

namespace JSP000078

/-- With zero marked and every consecutive linear gap odd, the parity of
the last marked position plus one is the parity of the number of marks. -/
theorem max_add_one_mod_two_eq_card_of_odd_gaps (X : Finset ℕ)
    (hzero : 0 ∈ X)
    (hgaps : ∀ a ∈ X, ∀ b ∈ X, a < b →
      (∀ x ∈ X, ¬(a < x ∧ x < b)) → Odd (b - a)) :
    (X.max' ⟨0, hzero⟩ + 1) % 2 = X.card % 2 := by
  classical
  induction X using Finset.induction_on_max with
  | empty => simp at hzero
  | insert b S hb ih =>
      have hbNot : b ∉ S := fun h ↦ (hb b h).false
      by_cases hS : S.Nonempty
      · have hzeroS : 0 ∈ S := by
          rcases Finset.mem_insert.mp hzero with hzeroB | hzeroS
          · obtain ⟨x, hx⟩ := hS
            have hxb := hb x hx
            omega
          · exact hzeroS
        have hgapS : ∀ a ∈ S, ∀ c ∈ S, a < c →
            (∀ x ∈ S, ¬(a < x ∧ x < c)) → Odd (c - a) := by
          intro a ha c hc hac hnone
          apply hgaps a (Finset.mem_insert_of_mem ha) c (Finset.mem_insert_of_mem hc) hac
          intro x hx haxc
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · have hcb := hb c hc
            omega
          · exact hnone x hxS haxc
        have hprev := ih hzeroS hgapS
        let a := S.max' hS
        have haS : a ∈ S := S.max'_mem hS
        have hab : a < b := hb a haS
        have hlastGap : Odd (b - a) := by
          apply hgaps a (Finset.mem_insert_of_mem haS) b (Finset.mem_insert_self _ _) hab
          intro x hx haxb
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · omega
          · have hxa : x ≤ a := S.le_max' x hxS
            omega
        have hmax : (insert b S).max' ⟨0, hzero⟩ = b := by
          apply le_antisymm
          · apply Finset.max'_le
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hxS
            · rfl
            · exact (hb x hxS).le
          · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
        have hcard : (insert b S).card = S.card + 1 := Finset.card_insert_of_notMem hbNot
        have hmod := Nat.odd_iff.mp hlastGap
        change (a + 1) % 2 = S.card % 2 at hprev
        rw [hmax, hcard]
        omega
      · have hSEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        have hbzero : b = 0 := (by simpa using hzero : 0 = b).symm
        subst b
        simp

/-- Among an even number of marked positions on an odd cycle there is a
positive even gap, either between consecutive linear marks or wrapping
from the largest marked position back to zero. -/
theorem exists_even_cyclic_gap (X : Finset ℕ) (N : ℕ)
    (hN : Odd N) (hbound : ∀ x ∈ X, x < N) (hzero : 0 ∈ X) (hcard : Even X.card) :
    (∃ a ∈ X, ∃ b ∈ X, a < b ∧ Even (b - a) ∧
      ∀ x ∈ X, ¬(a < x ∧ x < b)) ∨
    (∃ a ∈ X, 0 < N - a ∧ Even (N - a) ∧ ∀ x ∈ X, x ≤ a) := by
  classical
  by_cases hlinear : ∃ a ∈ X, ∃ b ∈ X, a < b ∧ Even (b - a) ∧
      ∀ x ∈ X, ¬(a < x ∧ x < b)
  · exact Or.inl hlinear
  have hgaps : ∀ a ∈ X, ∀ b ∈ X, a < b →
      (∀ x ∈ X, ¬(a < x ∧ x < b)) → Odd (b - a) := by
    intro a ha b hb hab hnone
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hlinear ⟨a, ha, b, hb, hab, he, hnone⟩
  let a := X.max' ⟨0, hzero⟩
  have haX : a ∈ X := X.max'_mem ⟨0, hzero⟩
  have haN := hbound a haX
  have hlast := max_add_one_mod_two_eq_card_of_odd_gaps X hzero hgaps
  have hcardmod := Nat.even_iff.mp hcard
  have hNmod := Nat.odd_iff.mp hN
  change (a + 1) % 2 = X.card % 2 at hlast
  refine Or.inr ⟨a, haX, by omega, ?_, ?_⟩
  · rw [Nat.even_iff]
    omega
  · intro x hx
    exact X.le_max' x hx

end JSP000078

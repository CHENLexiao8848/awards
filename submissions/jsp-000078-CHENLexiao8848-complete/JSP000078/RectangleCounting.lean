import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# Distinct lengths obtained from a rectangle of positions

The Cauchy–Davenport bound for natural-number sums applies whenever each
coordinate contributes injectively to the resulting length. A fixed added
constant does not identify any lengths.
-/

namespace JSP000078

open scoped Pointwise

/-- Independent injective contributions from two nonempty finite sets
produce at least the sum of their cardinalities minus one distinct totals.
This applies to every rectangle of positions in the fan path argument. -/
theorem card_add_card_sub_one_le_card_rectangle_sum
    {α β : Type*} (A : Finset α) (B : Finset β)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (f : α → ℕ) (g : β → ℕ) (c : ℕ)
    (hf : Set.InjOn f A) (hg : Set.InjOn g B) :
    A.card + B.card - 1 ≤
      ((A ×ˢ B).image fun p ↦ f p.1 + g p.2 + c).card := by
  have hsum := cauchy_davenport_add_of_linearOrder_isCancelAdd
    (hA.image f) (hB.image g)
  rw [Finset.card_image_of_injOn hf, Finset.card_image_of_injOn hg] at hsum
  refine hsum.trans (Finset.card_le_card_of_injOn (fun n : ℕ ↦ n + c) ?_ ?_)
  · intro n hn
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  · intro n _ m _ hnm
    exact Nat.add_right_cancel hnm

end JSP000078

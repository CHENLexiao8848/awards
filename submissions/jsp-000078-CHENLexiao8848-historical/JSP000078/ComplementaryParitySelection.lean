import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card

/-!
# Selecting one parity from complementary cycle distances

For an odd circumference, replacing a proper distance by its complement
reverses parity and preserves distinctness within the replaced class.
The union below therefore contains at least half as many distinct distances
as the original set, rounded up, of either requested parity.
-/

namespace JSP000078

/-- Retain distances of the requested parity and complement the others. -/
def complementaryParityDistances (D : Finset ℕ) (N r : ℕ) : Finset ℕ :=
  (D.filter fun d ↦ d % 2 = r % 2) ∪
    ((D.filter fun d ↦ d % 2 ≠ r % 2).image fun d ↦ N - d)

theorem mem_complementaryParityDistances_iff (D : Finset ℕ) (N r t : ℕ) :
    t ∈ complementaryParityDistances D N r ↔
      (t ∈ D ∧ t % 2 = r % 2) ∨
        ∃ d ∈ D, d % 2 ≠ r % 2 ∧ N - d = t := by
  simp only [complementaryParityDistances, Finset.mem_union, Finset.mem_filter,
    Finset.mem_image]
  constructor
  · rintro (h | ⟨d, ⟨hd, hpar⟩, ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨d, hd, hpar, ht⟩
  · rintro (h | ⟨d, hd, hpar, ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨d, ⟨hd, hpar⟩, ht⟩

/-- Each selected distance stays proper, has the requested parity, and
comes from an original distance or its complementary arc. -/
theorem complementaryParityDistances_spec
    (D : Finset ℕ) (N r : ℕ) (hN : Odd N)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d < N)
    {t : ℕ} (ht : t ∈ complementaryParityDistances D N r) :
    (1 ≤ t ∧ t < N) ∧ t % 2 = r % 2 ∧
      (t ∈ D ∨ ∃ d ∈ D, t = N - d) := by
  rcases (mem_complementaryParityDistances_iff D N r t).mp ht with
    ⟨htD, hpar⟩ | ⟨d, hd, hpar, rfl⟩
  · exact ⟨hD t htD, hpar, Or.inl htD⟩
  · have hdB := hD d hd
    have hnmod := Nat.odd_iff.mp hN
    refine ⟨⟨by omega, by omega⟩, ?_, Or.inr ⟨d, hd, rfl⟩⟩
    omega

/-- Of at least `2k - 1` distances, one parity class has at least `k`
members. Complementing that class when necessary preserves its size. -/
theorem le_card_complementaryParityDistances
    (D : Finset ℕ) (N r k : ℕ) (hk : 1 ≤ k)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d < N) (hcard : 2 * k - 1 ≤ D.card) :
    k ≤ (complementaryParityDistances D N r).card := by
  let A := D.filter fun d ↦ d % 2 = r % 2
  let B := D.filter fun d ↦ d % 2 ≠ r % 2
  have hA : A.card ≤ (complementaryParityDistances D N r).card :=
    Finset.card_le_card Finset.subset_union_left
  have hBinj : Set.InjOn (fun d ↦ N - d) B := by
    intro d hd e he hde
    change N - d = N - e at hde
    have hdN := (hD d (Finset.mem_filter.mp hd).1).2
    have heN := (hD e (Finset.mem_filter.mp he).1).2
    omega
  have hB : B.card ≤ (complementaryParityDistances D N r).card := by
    calc
      B.card = (B.image fun d ↦ N - d).card :=
        (Finset.card_image_of_injOn hBinj).symm
      _ ≤ (complementaryParityDistances D N r).card :=
        Finset.card_le_card Finset.subset_union_right
  have hsum : A.card + B.card = D.card :=
    D.card_filter_add_card_filter_not (fun d ↦ d % 2 = r % 2)
  omega

/-- Existential interface for at least `k` proper complementary distances
of either desired parity. -/
theorem exists_complementary_distances_of_parity
    (D : Finset ℕ) (N r k : ℕ) (hN : Odd N) (hk : 1 ≤ k)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d < N) (hcard : 2 * k - 1 ≤ D.card) :
    ∃ T : Finset ℕ, k ≤ T.card ∧
      ∀ t ∈ T, (1 ≤ t ∧ t < N) ∧ t % 2 = r % 2 ∧
        (t ∈ D ∨ ∃ d ∈ D, t = N - d) := by
  exact ⟨complementaryParityDistances D N r,
    le_card_complementaryParityDistances D N r k hk hD hcard,
    fun _ ht ↦ complementaryParityDistances_spec D N r hN hD ht⟩

end JSP000078

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Exhausting the available odd lengths with spoke parity classes

If `2k` proper distances each supply an odd length in a set of cardinality
`k`, the two injective parity classes must each exhaust that length set.
In particular, the maximal cycle length is supplied by an odd distance.
-/

namespace JSP000078

/-- The two parity classes of distances saturate the available length set.
Only individual length memberships are assumed; equal image sets and exact
class cardinalities are conclusions. -/
theorem spoke_parity_exhaustion (D K : Finset ℕ) (N k : ℕ)
    (hDcard : D.card = 2 * k) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, ¬Odd d → (N - d) + 2 ∈ K) :
    (D.filter Odd).card = k ∧ (D.filter fun d ↦ ¬Odd d).card = k ∧
      (D.filter Odd).image (fun d ↦ d + 2) = K ∧
      (D.filter fun d ↦ ¬Odd d).image (fun d ↦ (N - d) + 2) = K := by
  classical
  let O := D.filter Odd
  let E := D.filter fun d ↦ ¬Odd d
  have hOsub : O.image (fun d ↦ d + 2) ⊆ K := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact hodd d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
  have hEsub : E.image (fun d ↦ (N - d) + 2) ⊆ K := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact heven d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
  have hOcard : (O.image (fun d ↦ d + 2)).card = O.card :=
    Finset.card_image_of_injOn (by
      intro d _ e _ heq
      change d + 2 = e + 2 at heq
      omega)
  have hEcard : (E.image (fun d ↦ (N - d) + 2)).card = E.card :=
    Finset.card_image_of_injOn (by
      intro d hd e he heq
      have hdN := (hbound d (Finset.mem_filter.mp hd).1).2
      have heN := (hbound e (Finset.mem_filter.mp he).1).2
      change N - d + 2 = N - e + 2 at heq
      omega)
  have hOle : O.card ≤ k := by
    have h := Finset.card_le_card hOsub
    omega
  have hEle : E.card ≤ k := by
    have h := Finset.card_le_card hEsub
    omega
  have hsum : O.card + E.card = 2 * k := by
    have h := D.card_filter_add_card_filter_not Odd
    dsimp only [O, E]
    omega
  have hOeq : O.card = k := by omega
  have hEeq : E.card = k := by omega
  have hOImage : O.image (fun d ↦ d + 2) = K :=
    Finset.eq_of_subset_of_card_le hOsub (by rw [hKcard, hOcard, hOeq])
  have hEImage : E.image (fun d ↦ (N - d) + 2) = K :=
    Finset.eq_of_subset_of_card_le hEsub (by rw [hKcard, hEcard, hEeq])
  exact ⟨hOeq, hEeq, hOImage, hEImage⟩

/-- The reflected non-odd class is exactly the even class. -/
theorem card_spoke_parity_classes (D K : Finset ℕ) (N k : ℕ)
    (hDcard : D.card = 2 * k) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, ¬Odd d → (N - d) + 2 ∈ K) :
    (D.filter Odd).card = k ∧ (D.filter Even).card = k := by
  obtain ⟨hO, hE, _, _⟩ := spoke_parity_exhaustion D K N k hDcard hKcard hbound hodd heven
  exact ⟨hO, by simpa only [Nat.not_odd_iff_even] using hE⟩

/-- A length `N` in the exhausted set is supplied by an odd distance
`d` with `d + 2 = N`, avoiding any premise involving truncated subtraction. -/
theorem exists_dist_eq_sub_two (D K : Finset ℕ) (N k : ℕ)
    (hDcard : D.card = 2 * k) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N) (hNmem : N ∈ K)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, ¬Odd d → (N - d) + 2 ∈ K) :
    ∃ d ∈ D, Odd d ∧ d + 2 = N := by
  obtain ⟨_, _, hImage, _⟩ :=
    spoke_parity_exhaustion D K N k hDcard hKcard hbound hodd heven
  have hNImage : N ∈ (D.filter Odd).image (fun d ↦ d + 2) := hImage.symm ▸ hNmem
  obtain ⟨d, hd, hdN⟩ := Finset.mem_image.mp hNImage
  exact ⟨d, (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2, hdN⟩

/-- In the source's saturated situation, `N - 2` is itself an odd selected distance. -/
theorem sub_two_mem_of_spoke_parity_exhaustion (D K : Finset ℕ) (N k : ℕ)
    (hDcard : D.card = 2 * k) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N) (hNmem : N ∈ K)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, ¬Odd d → (N - d) + 2 ∈ K) :
    N - 2 ∈ D ∧ Odd (N - 2) := by
  obtain ⟨d, hd, hdOdd, hdN⟩ := exists_dist_eq_sub_two D K N k hDcard hKcard hbound hNmem hodd heven
  have heq : N - 2 = d := by omega
  simpa only [heq] using And.intro hd hdOdd

end JSP000078

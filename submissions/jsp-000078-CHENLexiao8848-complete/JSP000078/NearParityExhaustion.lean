import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Parity counts one distance below full saturation

For `2k - 1` proper distances whose two parity classes each inject into a
set of `k` available lengths, one class has size `k` and the other has size
`k - 1`. Whichever class has size `k` exhausts the available length set.
These are finite arithmetic consequences of individual spoke-cycle
memberships, with no assumption on the parity of the circumference.
-/

namespace JSP000078

/-- The two possible parity splits and the image saturation of each
maximal class when there are exactly `2k - 1` proper distances. -/
theorem near_spoke_parity_exhaustion
    (D K : Finset ℕ) (N k : ℕ) (hk : 1 ≤ k)
    (hDcard : D.card = 2 * k - 1) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, Even d → N - d + 2 ∈ K) :
    (((D.filter Odd).card = k ∧ (D.filter Even).card = k - 1) ∨
      ((D.filter Odd).card = k - 1 ∧ (D.filter Even).card = k)) ∧
    ((D.filter Odd).card = k → (D.filter Odd).image (fun d ↦ d + 2) = K) ∧
    ((D.filter Even).card = k → (D.filter Even).image (fun d ↦ N - d + 2) = K) := by
  let O := D.filter Odd
  let E := D.filter Even
  have hOsub : O.image (fun d ↦ d + 2) ⊆ K := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact hodd d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
  have hEsub : E.image (fun d ↦ N - d + 2) ⊆ K := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact heven d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
  have hOcard : (O.image (fun d ↦ d + 2)).card = O.card :=
    Finset.card_image_of_injOn (by
      intro d _ e _ hde
      change d + 2 = e + 2 at hde
      omega)
  have hEcard : (E.image (fun d ↦ N - d + 2)).card = E.card :=
    Finset.card_image_of_injOn (by
      intro d hd e he hde
      have hdN := (hbound d (Finset.mem_filter.mp hd).1).2
      have heN := (hbound e (Finset.mem_filter.mp he).1).2
      change N - d + 2 = N - e + 2 at hde
      omega)
  have hOle : O.card ≤ k := by
    have h := Finset.card_le_card hOsub
    omega
  have hEle : E.card ≤ k := by
    have h := Finset.card_le_card hEsub
    omega
  have hsum : O.card + E.card = 2 * k - 1 := by
    have h := D.card_filter_add_card_filter_not Odd
    simpa only [Nat.not_odd_iff_even, hDcard] using h
  refine ⟨?_, ?_, ?_⟩
  · change (O.card = k ∧ E.card = k - 1) ∨ (O.card = k - 1 ∧ E.card = k)
    omega
  · intro hOeq
    exact Finset.eq_of_subset_of_card_le hOsub (by rw [hKcard, hOcard]; exact hOeq.ge)
  · intro hEeq
    exact Finset.eq_of_subset_of_card_le hEsub (by rw [hKcard, hEcard]; exact hEeq.ge)

/-- In the near-saturated situation the odd class has exactly `k` or
`k - 1` members, and the even class has the complementary size. -/
theorem near_spoke_parity_card_cases
    (D K : Finset ℕ) (N k : ℕ) (hk : 1 ≤ k)
    (hDcard : D.card = 2 * k - 1) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, Even d → N - d + 2 ∈ K) :
    ((D.filter Odd).card = k ∧ (D.filter Even).card = k - 1) ∨
      ((D.filter Odd).card = k - 1 ∧ (D.filter Even).card = k) :=
  (near_spoke_parity_exhaustion D K N k hk hDcard hKcard hbound hodd heven).1

/-- A maximal odd-distance class contains the predecessor distance
`N - 2` whenever the cycle length `N` is among the available lengths. -/
theorem sub_two_mem_of_near_odd_class_full
    (D K : Finset ℕ) (N k : ℕ) (hk : 1 ≤ k)
    (hDcard : D.card = 2 * k - 1) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N) (hNmem : N ∈ K)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, Even d → N - d + 2 ∈ K)
    (hOcard : (D.filter Odd).card = k) :
    N - 2 ∈ D ∧ Odd (N - 2) := by
  have hImage :=
    (near_spoke_parity_exhaustion D K N k hk hDcard hKcard hbound hodd heven).2.1 hOcard
  have hNImage : N ∈ (D.filter Odd).image (fun d ↦ d + 2) := hImage.symm ▸ hNmem
  obtain ⟨d, hd, hdN⟩ := Finset.mem_image.mp hNImage
  have heq : N - 2 = d := by omega
  simpa only [heq] using Finset.mem_filter.mp hd

/-- A maximal even-distance class contains distance two whenever `N`
itself is available: the reflected image can hit `N` only at that distance. -/
theorem two_mem_of_near_even_class_full
    (D K : Finset ℕ) (N k : ℕ) (hk : 1 ≤ k)
    (hDcard : D.card = 2 * k - 1) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N) (hNmem : N ∈ K)
    (hodd : ∀ d ∈ D, Odd d → d + 2 ∈ K)
    (heven : ∀ d ∈ D, Even d → N - d + 2 ∈ K)
    (hEcard : (D.filter Even).card = k) : 2 ∈ D := by
  have hImage :=
    (near_spoke_parity_exhaustion D K N k hk hDcard hKcard hbound hodd heven).2.2 hEcard
  have hNImage : N ∈ (D.filter Even).image (fun d ↦ N - d + 2) := hImage.symm ▸ hNmem
  obtain ⟨d, hd, hdN⟩ := Finset.mem_image.mp hNImage
  have hdD := (Finset.mem_filter.mp hd).1
  have hdBound := hbound d hdD
  have heq : d = 2 := by omega
  exact heq ▸ hdD

end JSP000078

import JSP000078.MarkedConnectorData
import JSP000078.ProperDistanceComplement
import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# Balanced distance classes forced by two connector choices

Two distinct connectors of the same parity give one more distinct sum
than any nonempty compatible distance class. On an odd circumference
the complementary distances have the opposite parity and occur at the
opposite marked bases. Therefore neither original parity class can
contain as many members as the total number of available odd lengths.
-/

namespace JSP000078

open scoped Pointwise

private theorem card_add_one_le_of_pair_sums
    (D K : Finset ℕ) (u v : ℕ) (hD : D.Nonempty) (huv : u ≠ v)
    (hsum : ∀ d ∈ D, ∀ t ∈ ({u, v} : Finset ℕ), d + t ∈ K) :
    D.card + 1 ≤ K.card := by
  have hT : ({u, v} : Finset ℕ).Nonempty := ⟨u, by simp⟩
  have hTcard : ({u, v} : Finset ℕ).card = 2 := Finset.card_pair huv
  have hsub : D + ({u, v} : Finset ℕ) ⊆ K := by
    intro n hn
    obtain ⟨d, hd, t, ht, rfl⟩ := Finset.mem_add.mp hn
    exact hsum d hd t ht
  have hcount := (cauchy_davenport_add_of_linearOrder_isCancelAdd hD hT).trans
    (Finset.card_le_card hsub)
  rw [hTcard] at hcount
  omega

/-- A uniform-parity class of proper distances has at most `k - 1`
members when both original and complementary odd sums with two
same-parity connectors lie in a `k`-element set. -/
theorem same_parity_connector_class_bound
    (D K : Finset ℕ) (N k r u v : ℕ) (hN : Odd N) (hKcard : K.card = k)
    (hbound : ∀ d ∈ D, 1 ≤ d ∧ d < N)
    (hparity : ∀ d ∈ D, d % 2 = r % 2) (huv : u ≠ v) (hsame : Even (u + v))
    (hdirect : ∀ d ∈ D, ∀ t ∈ ({u, v} : Finset ℕ), Odd (d + t) → d + t ∈ K)
    (hcomp : ∀ d ∈ D, ∀ t ∈ ({u, v} : Finset ℕ),
      Odd ((N - d) + t) → (N - d) + t ∈ K) :
    D.card ≤ k - 1 := by
  rcases D.eq_empty_or_nonempty with hD | hD
  · simp only [hD, Finset.card_empty]
    omega
  have hNmod := Nat.odd_iff.mp hN
  have hsameMod := Nat.even_iff.mp hsame
  by_cases htarget : (r + u) % 2 = 1
  · have hsum : ∀ d ∈ D, ∀ t ∈ ({u, v} : Finset ℕ), d + t ∈ K := by
      intro d hd t ht
      apply hdirect d hd t ht
      have hdmod := hparity d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [Nat.odd_iff]
      omega
    have hcount := card_add_one_le_of_pair_sums D K u v hD huv hsum
    omega
  · let E := D.image fun d ↦ N - d
    have hE : E.Nonempty := hD.image _
    have hEcard : E.card = D.card := Finset.card_image_of_injOn (by
      intro d hd e he hde
      have hdN := (hbound d hd).2
      have heN := (hbound e he).2
      change N - d = N - e at hde
      omega)
    have hsum : ∀ e ∈ E, ∀ t ∈ ({u, v} : Finset ℕ), e + t ∈ K := by
      intro e he t ht
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      apply hcomp d hd t ht
      have hdmod := hparity d hd
      have hdN := (hbound d hd).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [Nat.odd_iff]
      omega
    have hcount := card_add_one_le_of_pair_sums E K u v hE huv hsum
    omega

/-- Two distinct same-parity connectors force both parity classes of
proper distances at every marked base to have size `parameter - 1`. -/
theorem MarkedConnectorData.balanced_of_same_parity_connectors
    (H : MarkedConnectorData) {u v : ℕ}
    (hu : u ∈ H.connectors) (hv : v ∈ H.connectors)
    (huv : u ≠ v) (hsame : Even (u + v))
    {a : ℕ} (ha : a ∈ H.marks) :
    ((properDistances H.marks H.circumference a).filter Odd).card = H.parameter - 1 ∧
      ((properDistances H.marks H.circumference a).filter Even).card = H.parameter - 1 := by
  let D := properDistances H.marks H.circumference a
  have hDbound := properDistances_bounds H.marks H.mark_bounds ha
  have hmem : ∀ d ∈ D, ∀ t ∈ ({u, v} : Finset ℕ), Odd (d + t) → d + t ∈ H.lengths := by
    intro d hd t ht hodd
    have htH : t ∈ H.connectors := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hu
      · exact hv
    exact H.cycle_membership a ha d hd t htH hodd
  have hcomp : ∀ d ∈ D, ∀ t ∈ ({u, v} : Finset ℕ),
      Odd ((H.circumference - d) + t) → (H.circumference - d) + t ∈ H.lengths := by
    intro d hd t ht hodd
    obtain ⟨b, hb, _, _, hdcomp⟩ :=
      properDistances_complement_mem H.marks H.mark_bounds ha hd
    have htH : t ∈ H.connectors := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hu
      · exact hv
    exact H.cycle_membership b hb _ hdcomp t htH hodd
  have hOle : (D.filter Odd).card ≤ H.parameter - 1 := by
    apply same_parity_connector_class_bound (D.filter Odd) H.lengths H.circumference
      H.parameter 1 u v H.circumference_odd H.length_card
    · intro d hd
      exact hDbound d (Finset.mem_filter.mp hd).1
    · intro d hd
      simpa only [Nat.one_mod] using Nat.odd_iff.mp (Finset.mem_filter.mp hd).2
    · exact huv
    · exact hsame
    · intro d hd
      exact hmem d (Finset.mem_filter.mp hd).1
    · intro d hd
      exact hcomp d (Finset.mem_filter.mp hd).1
  have hEle : (D.filter Even).card ≤ H.parameter - 1 := by
    apply same_parity_connector_class_bound (D.filter Even) H.lengths H.circumference
      H.parameter 0 u v H.circumference_odd H.length_card
    · intro d hd
      exact hDbound d (Finset.mem_filter.mp hd).1
    · intro d hd
      simpa only [Nat.zero_mod] using Nat.even_iff.mp (Finset.mem_filter.mp hd).2
    · exact huv
    · exact hsame
    · intro d hd
      exact hmem d (Finset.mem_filter.mp hd).1
    · intro d hd
      exact hcomp d (Finset.mem_filter.mp hd).1
  have hDcard : D.card = 2 * H.parameter - 2 := by
    change (properDistances H.marks H.circumference a).card = _
    rw [properDistances_card H.marks H.mark_bounds ha, H.mark_card]
    have hk := H.parameter_ge_two
    omega
  have hsum : (D.filter Odd).card + (D.filter Even).card = D.card := by
    simpa only [Nat.not_odd_iff_even] using D.card_filter_add_card_filter_not Odd
  have hk := H.parameter_ge_two
  change (D.filter Odd).card = H.parameter - 1 ∧ (D.filter Even).card = H.parameter - 1
  exact ⟨by omega, by omega⟩

end JSP000078

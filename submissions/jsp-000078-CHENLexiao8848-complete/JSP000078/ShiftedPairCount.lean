import JSP000078.SeparatedSumCounting

/-!
# Counting shifted arc lengths with several connector choices

The source's Lemma 6 obtains new lengths either from three distinct
connector choices or from two choices and one extra length below every
sum. These estimates require only individual sum memberships.
-/

namespace JSP000078

open scoped Pointwise

/-- Three or more distinct connector lengths add at least two to the
number of distinct lengths in a nonempty arc-length set. -/
theorem card_add_two_le_of_three_connector_sumset
    (S T K : Finset ℕ) (hS : S.Nonempty) (hTcard : 3 ≤ T.card)
    (hsum : ∀ d ∈ S, ∀ t ∈ T, d + t ∈ K) :
    S.card + 2 ≤ K.card := by
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  have hsub : S + T ⊆ K := by
    intro n hn
    obtain ⟨d, hd, t, ht, rfl⟩ := Finset.mem_add.mp hn
    exact hsum d hd t ht
  have hcount := (cauchy_davenport_add_of_linearOrder_isCancelAdd hS hT).trans
    (Finset.card_le_card hsub)
  omega

/-- Two or more connector lengths, together with a smaller separately
realized length, also add at least two to the arc-length cardinality. -/
theorem card_add_two_le_of_sumset_and_small_extra
    (S T K : Finset ℕ) (e : ℕ) (hS : S.Nonempty) (hTcard : 2 ≤ T.card)
    (hsum : ∀ d ∈ S, ∀ t ∈ T, d + t ∈ K)
    (hsep : ∀ d ∈ S, ∀ t ∈ T, e < d + t) (he : e ∈ K) :
    S.card + 2 ≤ K.card := by
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  have hcount := card_low_add_sumset_le {e} S T K hS hT id
    (fun _ _ _ _ h ↦ h)
    (by intro i hi; simpa only [Finset.mem_singleton.mp hi, id_eq] using he)
    hsum (by
      intro i hi d hd t ht
      simpa only [Finset.mem_singleton.mp hi, id_eq] using hsep d hd t ht)
  simp only [Finset.card_singleton] at hcount
  omega

end JSP000078

import JSP000078.SeparatedSumCounting

/-!
# A triangle length below a two-choice sumset

When every sum of an arc length and one of two connector lengths is
strictly larger than three, the triangle supplies one additional distinct
length beyond the natural-number sumset bound.
-/

namespace JSP000078

/-- A nonempty sumset with two connector choices and the additional
length three contains at least two more lengths than the first factor. -/
theorem card_add_two_le_of_sumset_and_extra
    (S T K : Finset ℕ) (hS : S.Nonempty) (hTcard : T.card = 2)
    (hsum : ∀ d ∈ S, ∀ t ∈ T, d + t ∈ K)
    (hsep : ∀ d ∈ S, ∀ t ∈ T, 3 < d + t) (hthree : 3 ∈ K) :
    S.card + 2 ≤ K.card := by
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  have hcount := card_low_add_sumset_le {3} S T K hS hT id
    (fun _ _ _ _ h ↦ h)
    (by intro i hi; simpa only [Finset.mem_singleton.mp hi, id_eq] using hthree)
    hsum (by
      intro i hi d hd t ht
      simpa only [Finset.mem_singleton.mp hi, id_eq] using hsep d hd t ht)
  simp only [Finset.card_singleton, hTcard] at hcount
  omega

end JSP000078

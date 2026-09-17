import JSP000078.ShiftedPairCount

/-!
# Odd connector counts in the common-neighbor path argument

The two-connector case adds one smaller length to a sumset. In the
exceptional route configuration, two distinct smaller lengths supplement
an injectively shifted arc family. Parity is handled by the cycle
membership hypotheses of the graph layer.
-/

namespace JSP000078

/-- Two connector lengths at least three and arc lengths greater than
`g` give enough distinct sums above the separately realized length `g+2`. -/
theorem odd_connector_count
    (S T K : Finset ℕ) (g k : ℕ) (hk : 2 ≤ k)
    (hScard : S.card = k - 1) (hTcard : 2 ≤ T.card)
    (hS : ∀ d ∈ S, g < d) (hT : ∀ t ∈ T, 3 ≤ t)
    (hsum : ∀ d ∈ S, ∀ t ∈ T, d + t ∈ K) (hsmall : g + 2 ∈ K) :
    k + 1 ≤ K.card := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsep : ∀ d ∈ S, ∀ t ∈ T, g + 2 < d + t := by
    intro d hd t ht
    have hdg := hS d hd
    have ht3 := hT t ht
    omega
  have hcount := card_add_two_le_of_sumset_and_small_extra S T K (g + 2)
    hSne hTcard hsum hsep hsmall
  omega

/-- In the exceptional two-route configuration, `g+2` and `g+4` are
both smaller than every shifted arc length `d+b+4`. They therefore add
two distinct lengths to the `k-1`-element arc image. -/
theorem exceptional_odd_connector_count
    (S K : Finset ℕ) (g b k : ℕ) (hk : 2 ≤ k) (hb : 1 ≤ b)
    (hScard : S.card = k - 1) (hS : ∀ d ∈ S, g < d)
    (hshift : ∀ d ∈ S, d + b + 4 ∈ K)
    (hsmallTwo : g + 2 ∈ K) (hsmallFour : g + 4 ∈ K) :
    k + 1 ≤ K.card := by
  let U := S.image fun d ↦ d + b + 4
  have hUcard : U.card = S.card := Finset.card_image_of_injOn (by
    intro d _ e _ hde
    change d + b + 4 = e + b + 4 at hde
    omega)
  have hUsub : U ⊆ K := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact hshift d hd
  have hnotFour : g + 4 ∉ U := by
    intro hn
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hn
    have hdg := hS d hd
    omega
  have hnotTwo : g + 2 ∉ insert (g + 4) U := by
    intro hn
    rcases Finset.mem_insert.mp hn with heq | hn
    · omega
    · obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hn
      have hdg := hS d hd
      omega
  have hcard := Finset.card_le_card
    (Finset.insert_subset hsmallTwo (Finset.insert_subset hsmallFour hUsub))
  rw [Finset.card_insert_of_notMem hnotTwo, Finset.card_insert_of_notMem hnotFour,
    hUcard, hScard] at hcard
  omega

end JSP000078

import JSP000078.ExtraSmallLengthCount

/-!
# Connector choices when an outside path has an endpoint edge

For an outside path of length at least two, choose proper arc lengths
of the opposite parity. The long connector and one of the two short
connectors then give two distinct odd-cycle shifts, all larger than the
separately available triangle length.
-/

namespace JSP000078

/-- At least `k - 1` arc lengths, the two parity-compatible connector
choices, and a triangle give at least `k + 1` distinct lengths. -/
theorem shared_edge_connector_count
    (K S : Finset ℕ) (L k : ℕ) (hk : 2 ≤ k) (hL : 2 ≤ L)
    (hsize : k - 1 ≤ S.card) (hbound : ∀ d ∈ S, 2 ≤ d)
    (hparity : ∀ d ∈ S, d % 2 = (L + 1) % 2)
    (hshortTwo : ∀ d ∈ S, Odd (d + 2) → d + 2 ∈ K)
    (hshortThree : ∀ d ∈ S, Odd (d + 3) → d + 3 ∈ K)
    (hlong : ∀ d ∈ S, Odd (d + (L + 2)) → d + (L + 2) ∈ K)
    (htriangle : 3 ∈ K) : k + 1 ≤ K.card := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases Nat.even_or_odd L with hEven | hOdd
  · have hLmod := Nat.even_iff.mp hEven
    have hTcard : ({2, L + 2} : Finset ℕ).card = 2 :=
      Finset.card_pair (by omega)
    have hsum : ∀ d ∈ S, ∀ t ∈ ({2, L + 2} : Finset ℕ), d + t ∈ K := by
      intro d hd t ht
      have hdmod := hparity d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · apply hshortTwo d hd
        rw [Nat.odd_iff]
        omega
      · apply hlong d hd
        rw [Nat.odd_iff]
        omega
    have hsep : ∀ d ∈ S, ∀ t ∈ ({2, L + 2} : Finset ℕ), 3 < d + t := by
      intro d hd t ht
      have hdb := hbound d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      omega
    have hcount := card_add_two_le_of_sumset_and_extra S {2, L + 2} K hS
      hTcard hsum hsep htriangle
    omega
  · have hLmod := Nat.odd_iff.mp hOdd
    have hTcard : ({3, L + 2} : Finset ℕ).card = 2 :=
      Finset.card_pair (by omega)
    have hsum : ∀ d ∈ S, ∀ t ∈ ({3, L + 2} : Finset ℕ), d + t ∈ K := by
      intro d hd t ht
      have hdmod := hparity d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · apply hshortThree d hd
        rw [Nat.odd_iff]
        omega
      · apply hlong d hd
        rw [Nat.odd_iff]
        omega
    have hsep : ∀ d ∈ S, ∀ t ∈ ({3, L + 2} : Finset ℕ), 3 < d + t := by
      intro d hd t ht
      have hdb := hbound d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      omega
    have hcount := card_add_two_le_of_sumset_and_extra S {3, L + 2} K hS
      hTcard hsum hsep htriangle
    omega

end JSP000078

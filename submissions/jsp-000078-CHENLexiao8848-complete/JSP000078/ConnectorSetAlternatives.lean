import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Parity alternatives for the endpoint connector lengths

Outside route length `h` supplies a connector of length `h + 2`, in
addition to the connector of length two through one endpoint. The two
exceptional route sets are analyzed with these offsets retained.
-/

namespace JSP000078

/-- Connector lengths furnished by the common attachments and outside routes. -/
def routeConnectorLengths (R : Finset ℕ) : Finset ℕ := insert 2 (R.image fun h ↦ h + 2)

/-- Positive route lengths give one additional connector length, namely two. -/
theorem card_routeConnectorLengths (R : Finset ℕ) (hpos : ∀ h ∈ R, 1 ≤ h) :
    (routeConnectorLengths R).card = R.card + 1 := by
  have htwo : 2 ∉ R.image (fun h ↦ h + 2) := by
    intro h
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h
    have := hpos r hr
    omega
  rw [routeConnectorLengths, Finset.card_insert_of_notMem htwo]
  rw [Finset.card_image_of_injective _ (by
    intro a b h
    change a + 2 = b + 2 at h
    omega)]

/-- Four connector lengths force three even lengths or two odd lengths. -/
theorem connector_parity_alternative_of_three_routes
    (R : Finset ℕ) (hpos : ∀ h ∈ R, 1 ≤ h) (hcard : 3 ≤ R.card) :
    3 ≤ ((routeConnectorLengths R).filter Even).card ∨
      2 ≤ ((routeConnectorLengths R).filter Odd).card := by
  have hsize := card_routeConnectorLengths R hpos
  have hsum : ((routeConnectorLengths R).filter Even).card +
      ((routeConnectorLengths R).filter Odd).card = (routeConnectorLengths R).card := by
    simpa only [Nat.not_even_iff_odd] using
      (routeConnectorLengths R).card_filter_add_card_filter_not Even
  omega

private theorem three_even_connectors_of_members {R : Finset ℕ} {a b c : ℕ}
    (ha : a ∈ routeConnectorLengths R) (hb : b ∈ routeConnectorLengths R)
    (hc : c ∈ routeConnectorLengths R) (haE : Even a) (hbE : Even b) (hcE : Even c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ ((routeConnectorLengths R).filter Even).card := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆ (routeConnectorLengths R).filter Even := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, haE⟩
    · exact Finset.mem_filter.mpr ⟨hb, hbE⟩
    · exact Finset.mem_filter.mpr ⟨hc, hcE⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_triple_eq_three_iff.mpr ⟨hab, hac, hbc⟩] at hcard
  exact hcard

private theorem two_odd_connectors_of_members {R : Finset ℕ} {a b : ℕ}
    (ha : a ∈ routeConnectorLengths R) (hb : b ∈ routeConnectorLengths R)
    (haO : Odd a) (hbO : Odd b) (hab : a ≠ b) :
    2 ≤ ((routeConnectorLengths R).filter Odd).card := by
  have hsub : ({a, b} : Finset ℕ) ⊆ (routeConnectorLengths R).filter Odd := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, haO⟩
    · exact Finset.mem_filter.mpr ⟨hb, hbO⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hcard
  exact hcard

/-- The first exceptional crossing-chord route set always has enough
connectors of a useful parity. -/
theorem connector_parity_alternative_of_first_exception
    (R : Finset ℕ) (b : ℕ) (hb : 1 ≤ b) (hR : R = {b + 2, 3 * b + 2}) :
    3 ≤ ((routeConnectorLengths R).filter Even).card ∨
      2 ≤ ((routeConnectorLengths R).filter Odd).card := by
  have htwo : 2 ∈ routeConnectorLengths R := Finset.mem_insert_self _ _
  have hfirst : b + 4 ∈ routeConnectorLengths R := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨b + 2, by simp [hR], by omega⟩
  have hsecond : 3 * b + 4 ∈ routeConnectorLengths R := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨3 * b + 2, by simp [hR], by omega⟩
  rcases Nat.even_or_odd b with hbE | hbO
  · have hm := Nat.even_iff.mp hbE
    apply Or.inl
    apply three_even_connectors_of_members htwo hfirst hsecond even_two
    · rw [Nat.even_iff]; omega
    · rw [Nat.even_iff]; omega
    · omega
    · omega
    · omega
  · have hm := Nat.odd_iff.mp hbO
    apply Or.inr
    apply two_odd_connectors_of_members hfirst hsecond
    · rw [Nat.odd_iff]; omega
    · rw [Nat.odd_iff]; omega
    · omega

/-- The second crossing-chord route set has three even connectors when
the middle length is even, leaving only its odd-middle subcase. -/
theorem connector_parity_alternative_of_second_exception
    (R : Finset ℕ) (b : ℕ) (hb : 1 ≤ b) (hR : R = {2, b + 2}) :
    3 ≤ ((routeConnectorLengths R).filter Even).card ∨ Odd b := by
  rcases Nat.even_or_odd b with hbE | hbO
  · have hm := Nat.even_iff.mp hbE
    have htwo : 2 ∈ routeConnectorLengths R := Finset.mem_insert_self _ _
    have hfour : 4 ∈ routeConnectorLengths R := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨2, by simp [hR], rfl⟩
    have hlast : b + 4 ∈ routeConnectorLengths R := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨b + 2, by simp [hR], by omega⟩
    apply Or.inl
    apply three_even_connectors_of_members htwo hfour hlast even_two (by decide)
    · rw [Nat.even_iff]; omega
    · omega
    · omega
    · omega
  · exact Or.inr hbO

/-- The classified two-chord routes provide three even connectors, two
odd connectors, or the precise remaining odd-middle exceptional route set. -/
theorem connector_set_alternatives (R : Finset ℕ)
    (hpos : ∀ h ∈ R, 1 ≤ h)
    (hclass : 3 ≤ R.card ∨
      (∃ b, 1 ≤ b ∧ R = {b + 2, 3 * b + 2}) ∨
      (∃ b, 1 ≤ b ∧ R = {2, b + 2})) :
    3 ≤ ((routeConnectorLengths R).filter Even).card ∨
      2 ≤ ((routeConnectorLengths R).filter Odd).card ∨
      ∃ b, 1 ≤ b ∧ Odd b ∧ R = {2, b + 2} := by
  rcases hclass with hcard | ⟨b, hb, hR⟩ | ⟨b, hb, hR⟩
  · rcases connector_parity_alternative_of_three_routes R hpos hcard with he | ho
    · exact Or.inl he
    · exact Or.inr (Or.inl ho)
  · rcases connector_parity_alternative_of_first_exception R b hb hR with he | ho
    · exact Or.inl he
    · exact Or.inr (Or.inl ho)
  · rcases connector_parity_alternative_of_second_exception R b hb hR with he | hbO
    · exact Or.inl he
    · exact Or.inr (Or.inr ⟨b, hb, hbO, hR⟩)

end JSP000078

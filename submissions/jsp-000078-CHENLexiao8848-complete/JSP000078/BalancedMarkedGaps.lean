import JSP000078.CyclicDistanceRebase
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union

/-!
# An odd minimum gap when every marked base has balanced parity counts

Rebasing at a globally closest marked pair makes their distance the least
positive mark. If it were even, changing to the second mark would increase
the odd-distance count, contradicting the equal counts at all bases.
-/

namespace JSP000078

/-- A realized global minimum proper distance is odd whenever all marked
bases have the same number of odd proper distances. -/
theorem minimum_marked_gap_odd (X : Finset ℕ) (N m : ℕ)
    (hN : Odd N) (hX : ∀ x ∈ X, x < N)
    (hbalanced : ∀ a ∈ X, ((properDistances X N a).filter Odd).card = m)
    {a b g : ℕ} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (hg : g = cyclicDistance N a b)
    (hmin : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → g ≤ cyclicDistance N u v) : Odd g := by
  classical
  have hgD : g ∈ properDistances X N a :=
    Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨hab.symm, hb⟩, hg.symm⟩
  have hgBounds := properDistances_bounds X hX ha g hgD
  let Y := X.image (cyclicDistance N a)
  have hY : ∀ y ∈ Y, y < N := image_cyclicDistance_bounds X hX ha
  have hzero : 0 ∈ Y := zero_mem_image_cyclicDistance X hX ha
  have hgY : g ∈ Y := Finset.mem_image.mpr ⟨b, hb, hg.symm⟩
  have hYbalanced : ∀ y ∈ Y, ((properDistances Y N y).filter Odd).card = m :=
    all_properDistances_rebase X hX ha (fun D ↦ (D.filter Odd).card = m) hbalanced
  have hYmin : ∀ y ∈ Y, y ≠ 0 → g ≤ y := by
    intro y hy hyne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hax : a ≠ x := by
      intro heq
      subst x
      have hzeroDist : cyclicDistance N a a = 0 := by
        rw [cyclicDistance_eq_sub (hX a ha) (le_refl a), Nat.sub_self]
      exact hyne hzeroDist
    exact hmin a ha x hx hax
  have hzeroCount : (((Y.erase 0).filter Odd).card) = m := by
    have h := hYbalanced 0 hzero
    rwa [properDistances_zero Y hY] at h
  have hshift := properDistances_eq_shiftAfterMinimum Y hY hzero hgY hgBounds.1 hYmin
  have hshiftCount : ((shiftAfterMinimum (Y.erase 0) N g).filter Odd).card = m := by
    have h := hYbalanced g hgY
    rwa [hshift] at h
  apply Nat.not_even_iff_odd.mp
  intro hEven
  have hrec := odd_card_shiftAfterMinimum_of_even (Y.erase 0) N g hN
    (Finset.mem_erase.mpr ⟨by omega, hgY⟩)
    (fun x hx ↦ hYmin x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.mp hx).1)
    (fun x hx ↦ hY x (Finset.mem_of_mem_erase hx)) hEven
  omega

/-- Equal odd-distance counts at every marked base yield a realized
positive odd distance that is no greater than any other proper distance. -/
theorem exists_odd_minimum_marked_gap (X : Finset ℕ) (N m : ℕ)
    (hN : Odd N) (hX : ∀ x ∈ X, x < N) (hcard : 2 ≤ X.card)
    (hbalanced : ∀ a ∈ X, ((properDistances X N a).filter Odd).card = m) :
    ∃ (g a b : ℕ), a ∈ X ∧ b ∈ X ∧ a ≠ b ∧
      g = cyclicDistance N a b ∧ 1 ≤ g ∧ g < N ∧ Odd g ∧
      (∀ u ∈ X, ∀ v ∈ X, u ≠ v → g ≤ cyclicDistance N u v) := by
  classical
  let D := X.biUnion fun a ↦ properDistances X N a
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a₀, ha₀⟩ := hXne
  have hDa : (properDistances X N a₀).Nonempty := by
    apply Finset.card_pos.mp
    rw [properDistances_card X hX ha₀]
    omega
  obtain ⟨d₀, hd₀⟩ := hDa
  have hD : D.Nonempty := ⟨d₀, Finset.mem_biUnion.mpr ⟨a₀, ha₀, hd₀⟩⟩
  let g := D.min' hD
  have hgD : g ∈ D := D.min'_mem hD
  obtain ⟨a, ha, hga⟩ := Finset.mem_biUnion.mp hgD
  have hgBounds := properDistances_bounds X hX ha g hga
  obtain ⟨b, hbErase, hbg⟩ := Finset.mem_image.mp hga
  obtain ⟨hba, hb⟩ := Finset.mem_erase.mp hbErase
  have hab : a ≠ b := hba.symm
  have hmin : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → g ≤ cyclicDistance N u v := by
    intro u hu v hv huv
    apply D.min'_le
    apply Finset.mem_biUnion.mpr
    exact ⟨u, hu, Finset.mem_image.mpr
      ⟨v, Finset.mem_erase.mpr ⟨huv.symm, hv⟩, rfl⟩⟩
  have hgOdd := minimum_marked_gap_odd X N m hN hX hbalanced ha hb hab hbg.symm hmin
  exact ⟨g, a, b, ha, hb, hab, hbg.symm, hgBounds.1, hgBounds.2, hgOdd, hmin⟩

/-- The marked-cardinality form used in the balanced branch of Lemma 6. -/
theorem exists_odd_minimum_marked_gap_of_card (X : Finset ℕ) (N k : ℕ)
    (hN : Odd N) (hX : ∀ x ∈ X, x < N) (hk : 2 ≤ k) (hcard : X.card = 2 * k - 1)
    (hbalanced : ∀ a ∈ X, ((properDistances X N a).filter Odd).card = k - 1) :
    ∃ (g a b : ℕ), a ∈ X ∧ b ∈ X ∧ a ≠ b ∧
      g = cyclicDistance N a b ∧ 1 ≤ g ∧ g < N ∧ Odd g ∧
      (∀ u ∈ X, ∀ v ∈ X, u ≠ v → g ≤ cyclicDistance N u v) :=
  exists_odd_minimum_marked_gap X N (k - 1) hN hX (by omega) hbalanced

end JSP000078

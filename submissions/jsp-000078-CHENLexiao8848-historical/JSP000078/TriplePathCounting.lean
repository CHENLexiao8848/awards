import JSP000078.FanPathCounting

/-!
# Combining the three regions of a fan path

Three pairwise rectangle bounds force enough distinct path lengths when
there are at least five incident positions. The same conclusion for three
positions follows when the middle region is empty.
-/

namespace JSP000078

open SimpleGraph

/-- The three pairwise counting bounds yield at least `k + 1` lengths.
The only omitted case is `k = 1` with a nonempty middle region. -/
theorem succ_le_card_of_three_region_bounds
    (S L M R : Finset ℕ) (k : ℕ) (_hk : 1 ≤ k)
    (hcase : 2 ≤ k ∨ M = ∅) (hL : L.Nonempty) (hR : R.Nonempty)
    (htotal : L.card + M.card + R.card = 2 * k + 1)
    (hLR : L.card + R.card - 1 ≤ S.card)
    (hLM : M.Nonempty → L.card + M.card - 1 ≤ S.card)
    (hMR : M.Nonempty → M.card + R.card - 1 ≤ S.card) :
    k + 1 ≤ S.card := by
  have hLpos := Finset.card_pos.mpr hL
  have hRpos := Finset.card_pos.mpr hR
  rcases M.eq_empty_or_nonempty with hM | hM
  · have hMcard : M.card = 0 := by rw [hM, Finset.card_empty]
    omega
  · have hMpos := Finset.card_pos.mpr hM
    have hk2 : 2 ≤ k := hcase.resolve_right hM.ne_empty
    have hLM' := hLM hM
    have hMR' := hMR hM
    omega

/-- Realized path lengths satisfying the three-region bounds give a
family of `k + 1` simple paths with pairwise different lengths. -/
theorem exists_paths_of_three_region_bounds
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (S L M R : Finset ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hcase : 2 ≤ k ∨ M = ∅) (hL : L.Nonempty) (hR : R.Nonempty)
    (htotal : L.card + M.card + R.card = 2 * k + 1)
    (hLR : L.card + R.card - 1 ≤ S.card)
    (hLM : M.Nonempty → L.card + M.card - 1 ≤ S.card)
    (hMR : M.Nonempty → M.card + R.card - 1 ≤ S.card)
    (hreal : ∀ n ∈ S, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n) :
    ∃ P : Fin (k + 1) → G.Walk x y,
      (∀ i, (P i).IsPath) ∧
      Function.Injective (fun i ↦ (P i).length) ∧
      (∀ i, (P i).length ∈ S) := by
  exact exists_injective_length_paths_of_card_le S (k + 1)
    (succ_le_card_of_three_region_bounds S L M R k hk hcase hL hR
      htotal hLR hLM hMR) hreal

/-- Two simple paths with unequal lengths already supply a family
indexed by `Fin 2`; no relation between their internal vertices is needed. -/
theorem exists_two_paths_of_length_ne
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (p q : G.Walk x y) (hp : p.IsPath) (hq : q.IsPath)
    (hne : p.length ≠ q.length) :
    ∃ P : Fin 2 → G.Walk x y,
      (∀ i, (P i).IsPath) ∧ Function.Injective (fun i ↦ (P i).length) := by
  have hcard : 2 ≤ ({p.length, q.length} : Finset ℕ).card := by
    simp [Finset.card_pair hne]
  have hreal : ∀ n ∈ ({p.length, q.length} : Finset ℕ),
      ∃ r : G.Walk x y, r.IsPath ∧ r.length = n := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact ⟨p, hp, rfl⟩
    · exact ⟨q, hq, rfl⟩
  obtain ⟨P, hP, hinj, _⟩ := exists_injective_length_paths_of_card_le
    {p.length, q.length} 2 hcard hreal
  exact ⟨P, hP, hinj⟩

end JSP000078

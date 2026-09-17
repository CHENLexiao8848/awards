import JSP000078.Main

/-!
# The equality case of the finite odd-cycle-length bound

The existing historical structural theorem also gives the strict coloring
bound when the extremal complete graph is absent. Vertex deletion and
one-vertex separators preserve this absence, so the same structural proof
extends to the full equality criterion.
-/

namespace JSP000078

open SimpleGraph

universe u

/-- Without a clique on `2 * k + 2` vertices, at most `k` distinct odd
cycle lengths imply a coloring using only `2 * k + 1` colors. This includes
`k = 0`, where the clique-free hypothesis says that the graph has no edges. -/
theorem colorable_of_card_oddCycleLengths_le_of_cliqueFree
    {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hkcard : (oddCycleLengths G).card ≤ k)
    (hfree : G.CliqueFree (2 * k + 2)) : G.Colorable (2 * k + 1) := by
  classical
  by_cases hkzero : k = 0
  · subst k
    simpa only [Nat.mul_zero, Nat.zero_add] using
      (G.colorable_one_iff.mpr (G.cliqueFree_two.mp hfree))
  have hkpos : 1 ≤ k := by omega
  have hAll : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → (oddCycleLengths H).card ≤ k →
      H.CliqueFree (2 * k + 2) → H.Colorable (2 * k + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W instW H hn hK hF
      by_cases hsmall : Fintype.card W ≤ 2 * k + 1
      · exact H.colorable_of_fintype.mono hsmall
      have hcardThree : 3 ≤ Fintype.card W := by omega
      have hproper (S : Set W) (hS : S ≠ Set.univ) :
          (H.induce S).Colorable (2 * k + 1) := by
        have hmissing : ∃ x : W, x ∉ S := by
          by_contra hnone
          apply hS
          apply Set.eq_univ_of_forall
          intro x
          by_contra hx
          exact hnone ⟨x, hx⟩
        obtain ⟨x, hx⟩ := hmissing
        have hless : Fintype.card S < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt hx
        apply ih (Fintype.card S) hless S (H.induce S) rfl
        · exact (Finset.card_le_card (oddCycleLengths_induce_subset S)).trans hK
        · exact hF.comap (SimpleGraph.Embedding.induce S).isContained
      by_cases hlessK : (oddCycleLengths H).card < k
      · exact (colorable_two_mul_oddCycleLengths_card_add_two H).mono (by omega)
      have hKeq : (oddCycleLengths H).card = k := by omega
      by_cases htwo : TwoVertexConnected H
      · by_cases hlow : ∃ x : W, H.degree x < 2 * k + 1
        · obtain ⟨x, hx⟩ := hlow
          apply colorable_of_delete_colorable_of_degree_lt x (2 * k + 1) hx
          apply hproper ({x} : Set W)ᶜ
          intro hfull
          have hxmem : x ∈ ({x} : Set W)ᶜ := hfull.symm ▸ Set.mem_univ x
          exact hxmem (Set.mem_singleton x)
        · have hdegree : ∀ x : W, 2 * k + 1 ≤ H.degree x := by
            intro x
            have hx : ¬H.degree x < 2 * k + 1 := fun hx ↦ hlow ⟨x, hx⟩
            omega
          obtain ⟨hcomplete, hsize⟩ := gyarfas_structural_theorem k hkpos htwo hdegree hKeq
          have hχ := hF
          rw [hcomplete, ← hsize] at hχ
          exact ((SimpleGraph.IsContained.refl (⊤ : SimpleGraph W)).not_cliqueFree_card hχ).elim
      · obtain ⟨S, T, hcover, hS, hT, hoverlap, hcross⟩ :=
          exists_separator_cover_of_not_twoVertexConnected hcardThree htwo
        exact colorable_of_cover_of_no_cross_edges_colorable S T hcover hoverlap hcross
          (2 * k + 1) (hproper S hS) (hproper T hT)
  exact hAll (Fintype.card V) V G rfl hkcard hfree

/-- Equality in the finite upper bound occurs exactly when the graph contains
a clique on `2 * k + 2` vertices. The premise allows fewer than `k` odd lengths. -/
theorem chromaticNumber_eq_iff_not_cliqueFree_of_card_oddCycleLengths_le
    {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hkcard : (oddCycleLengths G).card ≤ k) :
    G.chromaticNumber = (2 * k + 2 : ℕ) ↔ ¬G.CliqueFree (2 * k + 2) := by
  constructor
  · intro hχ hfree
    have hbound :=
      (colorable_of_card_oddCycleLengths_le_of_cliqueFree G k hkcard hfree).chromaticNumber_le
    rw [hχ] at hbound
    have := ENat.natCast_le_natCast.mp hbound
    omega
  · intro hclique
    apply le_antisymm (chromaticNumber_le_of_card_oddCycleLengths_le G k hkcard)
    have hbound := chromaticNumber_mono_of_hom
      (SimpleGraph.topEmbeddingOfNotCliqueFree hclique).toHom
    simpa using hbound

end JSP000078

import JSP000078.HistoricalStructuralSpec
import JSP000078.CycleClosedWalkBipartite
import JSP000078.LowDegreeColorExtension
import JSP000078.ColoringSeparator
import JSP000078.SeparatorSets

/-!
# The coloring consequence of Gyárfás's structural theorem

This file proves a conditional implication from the historical structural
theorem by induction on the number of vertices. The structural premise
is explicit and must be discharged separately. No independent numerical
coloring theorem is imported or assumed.
-/

namespace JSP000078

open SimpleGraph

/-- Gyárfás's structural theorem implies the numerical coloring bound.
The premise is the complete structural statement, not a coloring or
chromatic-number conclusion. -/
theorem colorable_of_structural_theorem
    (hStruct : HistoricalGyarfasStructuralTheorem)
    {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hkcard : (oddCycleLengths G).card ≤ k) : G.Colorable (2 * k + 2) := by
  classical
  have hAll : ∀ n : ℕ, ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → (oddCycleLengths H).card ≤ k → H.Colorable (2 * k + 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W instW H hn hK
      by_cases hsmall : Fintype.card W ≤ 2 * k + 2
      · exact H.colorable_of_fintype.mono hsmall
      have hcardThree : 3 ≤ Fintype.card W := by omega
      have hproper (S : Set W) (hS : S ≠ Set.univ) :
          (H.induce S).Colorable (2 * k + 2) := by
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
        exact (Finset.card_le_card (oddCycleLengths_induce_subset S)).trans hK
      by_cases hempty : oddCycleLengths H = ∅
      · exact (isBipartite_of_odd_lengths_empty_independent hempty).mono (by omega)
      have hKpos : 1 ≤ (oddCycleLengths H).card := by
        have hpos : 0 < (oddCycleLengths H).card := Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hempty)
        omega
      by_cases htwo : TwoVertexConnected H
      · by_cases hlow : ∃ x : W, H.degree x < 2 * k + 2
        · obtain ⟨x, hx⟩ := hlow
          apply colorable_of_delete_colorable_of_degree_lt x (2 * k + 2) hx
          apply hproper ({x} : Set W)ᶜ
          intro hfull
          have hxmem : x ∈ ({x} : Set W)ᶜ := hfull.symm ▸ Set.mem_univ x
          exact hxmem (Set.mem_singleton x)
        · have hdegree : ∀ x : W, 2 * (oddCycleLengths H).card + 1 ≤ H.degree x := by
            intro x
            have hx : ¬H.degree x < 2 * k + 2 := fun hx ↦ hlow ⟨x, hx⟩
            omega
          obtain ⟨_, hsize⟩ := hStruct H (oddCycleLengths H).card hKpos htwo hdegree rfl
          omega
      · obtain ⟨S, T, hcover, hS, hT, hoverlap, hcross⟩ :=
          exists_separator_cover_of_not_twoVertexConnected hcardThree htwo
        exact colorable_of_cover_of_no_cross_edges_colorable S T hcover hoverlap hcross
          (2 * k + 2) (hproper S hS) (hproper T hT)
  exact hAll (Fintype.card V) V G rfl hkcard

/-- Chromatic-number form of the same conditional structural implication. -/
theorem chromaticNumber_le_of_structural_theorem
    (hStruct : HistoricalGyarfasStructuralTheorem)
    {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hkcard : (oddCycleLengths G).card ≤ k) : G.chromaticNumber ≤ (2 * k + 2 : ℕ) :=
  (colorable_of_structural_theorem hStruct G k hkcard).chromaticNumber_le

end JSP000078

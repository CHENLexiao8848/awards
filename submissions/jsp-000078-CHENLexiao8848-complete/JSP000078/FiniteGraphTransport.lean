import JSP000078.MathlibBridge

/-!
# Transporting finite graph statements across vertex universes

Graph isomorphisms preserve the set of distinct odd cycle lengths. Every
finite graph is isomorphic to Mathlib's `overFin` model, so a coloring
theorem for all graphs on `Fin n` transfers to arbitrary finite vertex
types without changing the numerical parameter.
-/

namespace JSP000078

open SimpleGraph

/-- Isomorphic finite graphs have exactly the same distinct odd lengths. -/
theorem oddCycleLengths_eq_of_iso
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    oddCycleLengths G = oddCycleLengths H := by
  apply Finset.Subset.antisymm
  · exact oddCycleLengths_subset_of_injective_hom e.toHom e.injective
  · exact oddCycleLengths_subset_of_injective_hom e.symm.toHom e.symm.injective

/-- Colorability transfers in both directions along a graph isomorphism. -/
theorem colorable_iff_of_iso
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (m : ℕ) : G.Colorable m ↔ H.Colorable m :=
  ⟨fun h ↦ h.of_hom e.symm.toHom, fun h ↦ h.of_hom e.toHom⟩

/-- A numerical theorem on all finite `Fin n` models applies to every
finite vertex type, including vertex types in higher universes. The
finite-model theorem remains an explicit premise to be discharged. -/
theorem colorable_of_fin_models
    (hFin : ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
      H.Colorable (2 * (oddCycleLengths H).card + 2))
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.Colorable (2 * (oddCycleLengths G).card + 2) := by
  let H : SimpleGraph (Fin (Fintype.card V)) := G.overFin rfl
  let e : G ≃g H := G.overFinIso rfl
  have hlengths : oddCycleLengths G = oddCycleLengths H := oddCycleLengths_eq_of_iso e
  have hc : H.Colorable (2 * (oddCycleLengths H).card + 2) := hFin _ H
  rw [← hlengths] at hc
  exact hc.of_hom e.toHom

/-- The at-most-`k` bound follows from the exact-cardinality finite-model
theorem by transporting first and enlarging the palette. -/
theorem colorable_of_fin_models_of_card_le
    (hFin : ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
      H.Colorable (2 * (oddCycleLengths H).card + 2))
    {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : (oddCycleLengths G).card ≤ k) : G.Colorable (2 * k + 2) :=
  (colorable_of_fin_models hFin G).mono (by omega)

end JSP000078

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Gluing colorings across a separator of at most one vertex

Colorings agreeing on the overlap of two covering vertex sets combine
when no edge joins their disjoint parts. If the overlap has at most one
vertex, a color permutation makes the two colorings agree there.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Agreeing colorings on a two-set vertex cover glue when no edge
joins the portions exclusive to different sets. -/
theorem exists_coloring_of_cover_of_agree
    {α : Type*} (S T : Set V) (hcover : S ∪ T = Set.univ)
    (hcross : ∀ u ∈ S, u ∉ T → ∀ v ∈ T, v ∉ S → ¬G.Adj u v)
    (cS : (G.induce S).Coloring α) (cT : (G.induce T).Coloring α)
    (hagree : ∀ v (hvS : v ∈ S) (hvT : v ∈ T), cS ⟨v, hvS⟩ = cT ⟨v, hvT⟩) :
    ∃ C : G.Coloring α,
      (∀ v (hvS : v ∈ S), C v = cS ⟨v, hvS⟩) ∧
      (∀ v (hvT : v ∈ T), C v = cT ⟨v, hvT⟩) := by
  classical
  have hinT (v : V) (hvS : v ∉ S) : v ∈ T := by
    have hv : v ∈ S ∪ T := hcover.symm ▸ Set.mem_univ v
    exact hv.resolve_left hvS
  let color : V → α := fun v ↦ if hvS : v ∈ S then cS ⟨v, hvS⟩ else cT ⟨v, hinT v hvS⟩
  have honS (v : V) (hvS : v ∈ S) : color v = cS ⟨v, hvS⟩ := by
    simp only [color, dite_eq_left hvS]
  have honT (v : V) (hvT : v ∈ T) : color v = cT ⟨v, hvT⟩ := by
    by_cases hvS : v ∈ S
    · rw [honS v hvS]
      exact hagree v hvS hvT
    · simp only [color, dite_eq_right hvS]
  have hvalid : ∀ {u v : V}, G.Adj u v → color u ≠ color v := by
    intro u v huv
    by_cases huS : u ∈ S
    · by_cases hvS : v ∈ S
      · rw [honS u huS, honS v hvS]
        exact cS.valid (show (G.induce S).Adj ⟨u, huS⟩ ⟨v, hvS⟩ from huv)
      · have hvT := hinT v hvS
        have huT : u ∈ T := by
          by_contra huT
          exact hcross u huS huT v hvT hvS huv
        rw [honT u huT, honT v hvT]
        exact cT.valid (show (G.induce T).Adj ⟨u, huT⟩ ⟨v, hvT⟩ from huv)
    · have huT := hinT u huS
      by_cases hvS : v ∈ S
      · have hvT : v ∈ T := by
          by_contra hvT
          exact hcross v hvS hvT u huT huS huv.symm
        rw [honT u huT, honT v hvT]
        exact cT.valid (show (G.induce T).Adj ⟨u, huT⟩ ⟨v, hvT⟩ from huv)
      · have hvT := hinT v hvS
        rw [honT u huT, honT v hvT]
        exact cT.valid (show (G.induce T).Adj ⟨u, huT⟩ ⟨v, hvT⟩ from huv)
  exact ⟨Coloring.mk color hvalid, honS, honT⟩

/-- A color permutation aligns two colorings on an overlap containing
at most one vertex, permitting them to glue across a one-vertex separator
or across disjoint components. -/
theorem colorable_of_cover_of_no_cross_edges
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hoverlap : (S ∩ T).Subsingleton)
    (hcross : ∀ u ∈ S, u ∉ T → ∀ v ∈ T, v ∉ S → ¬G.Adj u v)
    (m : ℕ) (cS : (G.induce S).Coloring (Fin m)) (cT : (G.induce T).Coloring (Fin m)) :
    G.Colorable m := by
  classical
  by_cases hnonempty : (S ∩ T).Nonempty
  · obtain ⟨x, hxS, hxT⟩ := hnonempty
    let e := Equiv.swap (cT ⟨x, hxT⟩) (cS ⟨x, hxS⟩)
    let cT' := (G.induce T).recolorOfEquiv e cT
    have hagree : ∀ v (hvS : v ∈ S) (hvT : v ∈ T),
        cS ⟨v, hvS⟩ = cT' ⟨v, hvT⟩ := by
      intro v hvS hvT
      have hvx : v = x := hoverlap ⟨hvS, hvT⟩ ⟨hxS, hxT⟩
      subst v
      change cS ⟨x, hxS⟩ = e (cT ⟨x, hxT⟩)
      exact (Equiv.swap_apply_left _ _).symm
    obtain ⟨C, _, _⟩ := exists_coloring_of_cover_of_agree S T hcover hcross cS cT' hagree
    exact ⟨C⟩
  · have hagree : ∀ v (hvS : v ∈ S) (hvT : v ∈ T),
        cS ⟨v, hvS⟩ = cT ⟨v, hvT⟩ := by
      intro v hvS hvT
      exact (hnonempty ⟨v, hvS, hvT⟩).elim
    obtain ⟨C, _, _⟩ := exists_coloring_of_cover_of_agree S T hcover hcross cS cT hagree
    exact ⟨C⟩

/-- Proposition-level version of gluing across an overlap of at most
one vertex. No separate nonempty-palette hypothesis is required. -/
theorem colorable_of_cover_of_no_cross_edges_colorable
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hoverlap : (S ∩ T).Subsingleton)
    (hcross : ∀ u ∈ S, u ∉ T → ∀ v ∈ T, v ∉ S → ¬G.Adj u v)
    (m : ℕ) (hcS : (G.induce S).Colorable m) (hcT : (G.induce T).Colorable m) :
    G.Colorable m := by
  obtain ⟨cS⟩ := hcS
  obtain ⟨cT⟩ := hcT
  exact colorable_of_cover_of_no_cross_edges S T hcover hoverlap hcross m cS cT

end JSP000078

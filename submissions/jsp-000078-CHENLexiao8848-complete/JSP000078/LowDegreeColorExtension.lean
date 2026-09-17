import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Extending a coloring across a low-degree vertex

The neighbors of a vertex of degree less than the palette size cannot
use every color. Assigning a missing neighbor color to that vertex
extends the coloring of its induced deletion.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A coloring of the induced deletion extends across a vertex whose
degree is strictly smaller than the number of colors. -/
theorem exists_coloring_extension_of_degree_lt (x : V) (m : ℕ)
    (hdegree : G.degree x < m)
    (c : (G.induce ({x} : Set V)ᶜ).Coloring (Fin m)) :
    ∃ C : G.Coloring (Fin m),
      ∀ v (hv : v ≠ x), C v = c ⟨v, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hv⟩ := by
  classical
  let neighborColor : {v // v ∈ G.neighborFinset x} → Fin m := fun v ↦
    c ⟨v.val, by
      have hxv := (G.mem_neighborFinset x v.val).mp v.property
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxv.ne.symm⟩
  let used : Finset (Fin m) := (G.neighborFinset x).attach.image neighborColor
  have hused : used.card ≤ G.degree x := by
    calc
      used.card ≤ (G.neighborFinset x).attach.card := Finset.card_image_le
      _ = G.degree x := by rw [Finset.card_attach, G.card_neighborFinset_eq_degree]
  have husedlt : used.card < (Finset.univ : Finset (Fin m)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨free, _, hfree⟩ := Finset.exists_mem_notMem_of_card_lt_card husedlt
  have hfreeNeighbor (v : V) (hv : v ≠ x) (hxv : G.Adj x v) :
      free ≠ c ⟨v, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hv⟩ := by
    intro heq
    apply hfree
    have hvN : v ∈ G.neighborFinset x := (G.mem_neighborFinset x v).mpr hxv
    apply Finset.mem_image.mpr
    exact ⟨⟨v, hvN⟩, Finset.mem_attach _ _, heq.symm⟩
  let color : V → Fin m := fun v ↦ if hv : v = x then free else
    c ⟨v, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hv⟩
  have hvalid : ∀ {u v : V}, G.Adj u v → color u ≠ color v := by
    intro u v huv
    by_cases hux : u = x
    · subst u
      have hvx : v ≠ x := huv.ne.symm
      simpa only [color, dite_eq_left rfl, dite_eq_right hvx] using hfreeNeighbor v hvx huv
    · by_cases hvx : v = x
      · subst v
        simpa only [color, dite_eq_left rfl, dite_eq_right hux] using
          (hfreeNeighbor u hux huv.symm).symm
      · have hvalidC := c.valid (show (G.induce ({x} : Set V)ᶜ).Adj
            ⟨u, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hux⟩
            ⟨v, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hvx⟩ from huv)
        simpa only [color, dite_eq_right hux, dite_eq_right hvx] using hvalidC
  refine ⟨Coloring.mk color hvalid, ?_⟩
  intro v hv
  change color v = _
  simp only [color, dite_eq_right hv]

/-- Colorability extends across a low-degree vertex from its induced
deletion, with the same number of colors. -/
theorem colorable_of_delete_coloring_of_degree_lt (x : V) (m : ℕ)
    (hdegree : G.degree x < m)
    (c : (G.induce ({x} : Set V)ᶜ).Coloring (Fin m)) : G.Colorable m := by
  obtain ⟨C, _⟩ := exists_coloring_extension_of_degree_lt x m hdegree c
  exact ⟨C⟩

/-- Proposition-level form of the low-degree extension step. -/
theorem colorable_of_delete_colorable_of_degree_lt (x : V) (m : ℕ)
    (hdegree : G.degree x < m)
    (hc : (G.induce ({x} : Set V)ᶜ).Colorable m) : G.Colorable m := by
  obtain ⟨c⟩ := hc
  exact colorable_of_delete_coloring_of_degree_lt x m hdegree c

end JSP000078

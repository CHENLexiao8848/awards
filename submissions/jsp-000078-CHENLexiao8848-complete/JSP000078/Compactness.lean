/-
Copyright 2026 MaxwellLaw.
Released under Apache 2.0 license as described in LICENSE-APACHE-2.0.

Formalization assisted by OpenAI Codex. This application of compactness uses
Mathlib's Rado selection lemma, formalized by Bhavik Mehta; see FULL_SCOPE_PROVENANCE.md.
-/
import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace JSP000078

/-- The de Bruijn--Erdős compactness principle for a fixed finite palette.
No finiteness, countability, or local finiteness assumption is made on `V`.
The zero-color case is included. -/
theorem colorable_of_finite_induced {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable n) :
    G.Colorable n := by
  classical
  let c (s : Finset V) : (G.induce (s : Set V)).Coloring (Fin n) := (h s).some
  obtain ⟨f, hf⟩ := Finset.rado_selection_subtype
    (β := fun _ : V => Fin n) (fun s => c s)
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro v w hvw
  obtain ⟨t, hst, ht⟩ := hf {v, w}
  have hv : v ∈ ({v, w} : Finset V) := by simp
  have hw : w ∈ ({v, w} : Finset V) := by simp
  have hfv := ht ⟨v, hv⟩
  have hfw := ht ⟨w, hw⟩
  rw [hfv, hfw]
  exact (c t).valid hvw

end JSP000078

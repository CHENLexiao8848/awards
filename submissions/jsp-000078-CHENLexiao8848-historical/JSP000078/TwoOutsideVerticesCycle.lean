import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Extending a cycle through two outside vertices

Two distinct outside vertices adjacent to every cycle vertex allow two
consecutive rim edges to be replaced by two-edge detours. The resulting
simple cycle is longer by exactly two.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two distinct vertices outside a simple cycle, each adjacent to every
cycle vertex, produce a simple cycle two edges longer. -/
theorem exists_cycle_through_two_outside_universal_vertices
    {c u v : V} {C : G.Walk c c} (hC : C.IsCycle)
    (hu : u ∉ C.support) (hv : v ∉ C.support) (huv : u ≠ v)
    (huAdj : ∀ w ∈ C.support, G.Adj u w)
    (hvAdj : ∀ w ∈ C.support, G.Adj v w) :
    ∃ E : G.Walk c c, E.IsCycle ∧ E.length = C.length + 2 := by
  let R := C.drop 2
  have hR : R.IsPath := hC.isPath_drop (by decide : 0 < 2)
  have hRsub : R.support ⊆ C.support := (C.isSubwalk_drop 2).support_subset
  have hOneNot : C.getVert 1 ∉ R.support := by
    intro hOne
    obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp hOne
    have hlen : R.length = C.length - 2 := C.drop_length 2
    have hN := hC.three_le_length
    have hget : C.getVert (2 + n) = C.getVert 1 := by
      simpa only [R, Walk.drop_getVert] using hn
    have heq : 2 + n = 1 := hC.getVert_injOn
      (by change 1 ≤ 2 + n ∧ 2 + n ≤ C.length; omega)
      (by change 1 ≤ 1 ∧ 1 ≤ C.length; omega) hget
    omega
  have huR : u ∉ R.support := fun hw ↦ hu (hRsub hw)
  have hvR : v ∉ R.support := fun hw ↦ hv (hRsub hw)
  have hOnev : C.getVert 1 ≠ v := by
    intro heq
    exact hv (heq ▸ C.getVert_mem_support 1)
  have huOne : u ≠ C.getVert 1 := by
    intro heq
    exact hu (heq.symm ▸ C.getVert_mem_support 1)
  have hcu : G.Adj c u := (huAdj c C.start_mem_support).symm
  have hu1 : G.Adj u (C.getVert 1) := huAdj _ (C.getVert_mem_support 1)
  have h1v : G.Adj (C.getVert 1) v := (hvAdj _ (C.getVert_mem_support 1)).symm
  have hv2 : G.Adj v (C.getVert 2) := hvAdj _ (C.getVert_mem_support 2)
  let Q := (R.cons hv2).cons h1v
  have hQ : Q.IsPath := by
    apply (hR.cons hvR).cons
    simp only [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hOnev, hOneNot⟩
  have huQ : u ∉ Q.support := by
    simp only [Q, Walk.support_cons, List.mem_cons, not_or]
    exact ⟨huOne, huv, huR⟩
  let E := ((Q.cons hu1).cons hcu)
  have hlen : E.length = C.length + 2 := by
    have hN := hC.three_le_length
    simp only [E, Q, R, Walk.length_cons, Walk.drop_length]
    omega
  refine ⟨E, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, ?_⟩, hlen⟩
  · simpa [E] using And.intro hQ huQ
  · have hN := hC.three_le_length
    omega

end JSP000078

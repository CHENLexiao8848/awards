import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Vertex cardinalities of spanning and almost-spanning cycles

A simple cycle has exactly as many distinct vertices as edges. Covering all
vertices by the cycle and possibly one outside vertex therefore determines
the graph's order, after which full degree forces completeness.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c : V}

/-- A simple cycle has one distinct support vertex per edge. -/
theorem card_cycle_support [DecidableEq V] {C : G.Walk c c} (hC : C.IsCycle) :
    C.support.toFinset.card = C.length := by
  have hsets : C.support.toFinset = C.support.tail.toFinset := by
    ext v
    simp only [List.mem_toFinset]
    constructor
    · intro hv
      rcases (C.mem_support_iff).mp hv with rfl | htail
      · exact C.end_mem_tail_support hC.not_nil
      · exact htail
    · exact List.mem_of_mem_tail
  rw [hsets, List.toFinset_card_of_nodup hC.support_nodup]
  simp only [List.length_tail, Walk.length_support, Nat.add_sub_cancel]

/-- A spanning simple cycle determines the total number of vertices. -/
theorem card_vertex_eq_cycle_length [Fintype V] {C : G.Walk c c}
    (hC : C.IsCycle) (hcover : ∀ v : V, v ∈ C.support) :
    Fintype.card V = C.length := by
  classical
  have hset : C.support.toFinset = Finset.univ := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcover v
  have hcard := card_cycle_support hC
  simpa only [hset, Finset.card_univ] using hcard

/-- A simple cycle together with one outside vertex determines the graph order. -/
theorem card_vertex_eq_cycle_length_add_one [Fintype V] {C : G.Walk c c}
    (hC : C.IsCycle) {v : V} (hv : v ∉ C.support)
    (hcover : ∀ w : V, w ∈ C.support ∨ w = v) :
    Fintype.card V = C.length + 1 := by
  classical
  have hset : Finset.univ = insert v C.support.toFinset := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, List.mem_toFinset, true_iff]
    exact (hcover w).symm
  have hvfin : v ∉ C.support.toFinset := by simpa only [List.mem_toFinset] using hv
  rw [← Finset.card_univ, hset, Finset.card_insert_of_notMem hvfin, card_cycle_support hC]

/-- If every vertex has all possible neighbors, the graph is complete. -/
theorem graph_eq_top_of_degree_eq_card_sub_one [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v : V, G.degree v = Fintype.card V - 1) : G = ⊤ := by
  apply SimpleGraph.eq_top_iff_forall_isUniversal.mpr
  intro v
  exact (G.degree_eq_card_sub_one v).mp (hdeg v)

/-- A lower bound of the graph order minus one already forces completeness. -/
theorem graph_eq_top_of_card_sub_one_le_degree [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v : V, Fintype.card V - 1 ≤ G.degree v) : G = ⊤ := by
  apply graph_eq_top_of_degree_eq_card_sub_one
  intro v
  have hlt := G.degree_lt_card_verts v
  have hlo := hdeg v
  omega

end JSP000078

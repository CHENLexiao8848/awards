import JSP000078.OutsideNeighborPredecessor
import JSP000078.SaturatedNeighborSet
import JSP000078.CycleCardinality

/-! # A sufficiently large outside-neighbor set fills the odd cycle -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The selected 2k+1 neighbors of an outside vertex exhaust an odd
cycle whenever the graph has just k distinct odd cycle lengths. -/
theorem outside_neighbor_set_eq_cycle {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hv : v ∉ C.support)
    (k : ℕ) (hK : (oddCycleLengths G).card = k) (X : Finset V)
    (hcard : X.card = 2 * k + 1)
    (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj v x) :
    (∀ x ∈ C.support, G.Adj v x) ∧ C.length = 2 * k + 1 := by
  classical
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have heq : X = C.support.toFinset := cycle_subset_eq_support_of_predecessor_closed
    hC hCO X hXne (fun x hx ↦ (hX x hx).1)
    (fun x hx ↦ outside_neighbors_predecessor_mem hC hCO hv k hK X hcard hX hx)
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (hX x (heq.symm ▸ List.mem_toFinset.mpr hx)).2
  · have hlen := card_cycle_support hC
    rw [← heq] at hlen
    omega

/-- Under an independent-complement hypothesis, an outside vertex of
degree at least 2k+1 is adjacent to the whole odd cycle. -/
theorem outside_vertex_saturated_of_degree [DecidableRel G.Adj]
    {c v : V} {C : G.Walk c c} (hC : C.IsCycle) (hCO : Odd C.length)
    (hv : v ∉ C.support) (k : ℕ) (hK : (oddCycleLengths G).card = k)
    (hdeg : 2 * k + 1 ≤ G.degree v)
    (hInd : ∀ x y : V, x ∉ C.support → y ∉ C.support → ¬G.Adj x y) :
    (∀ x ∈ C.support, G.Adj v x) ∧ C.length = 2 * k + 1 := by
  classical
  have hsize : 2 * k + 1 ≤ (G.neighborFinset v).card := by
    simpa only [G.card_neighborFinset_eq_degree] using hdeg
  obtain ⟨X, hsub, hcard⟩ := Finset.exists_subset_card_eq hsize
  apply outside_neighbor_set_eq_cycle hC hCO hv k hK X hcard
  intro x hx
  have hadj : G.Adj v x := (G.mem_neighborFinset v x).mp (hsub hx)
  refine ⟨?_, hadj⟩
  by_contra hxC
  exact hInd v x hv hxC hadj

end JSP000078

import JSP000078.SharedCycleComparison
import JSP000078.FanHom
import JSP000078.MathlibBridge

/-! # Odd lengths of a fan meeting a longest odd cycle at only one vertex -/

namespace JSP000078

open SimpleGraph

/-- The length of the longest odd cycle is new beyond all odd lengths
of a graph supported on a set intersecting it in at most one vertex. -/
theorem card_odd_lengths_supported_at_one_vertex_lt
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c d x : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : IsLongestOddCycle C)
    (hDC : ∀ w ∈ D.support, w ∈ C.support → w = x)
    {H : SimpleGraph {v : V // v ∈ D.support}}
    (hHG : H ≤ G.induce {v | v ∈ D.support}) :
    (oddCycleLengths H).card < (oddCycleLengths G).card := by
  classical
  have hsub : oddCycleLengths H ⊆ oddCycleLengths G :=
    oddCycleLengths_subset_of_injective_hom (fanInclusionHom hHG) (fanInclusionHom_injective hHG)
  have hCmem : C.length ∈ oddCycleLengths G :=
    (mem_oddCycleLengths G).mpr ⟨hC.2.1, c, C, hC.1, rfl⟩
  have hCnot : C.length ∉ oddCycleLengths H := by
    intro hmem
    obtain ⟨ho, v, P, hp, hlen⟩ := (mem_oddCycleLengths H).mp hmem
    let Q := P.map (fanInclusionHom hHG)
    have hQ : Q.IsCycle := hp.map (fanInclusionHom_injective hHG)
    have hQL : Q.length = C.length := by simpa only [Q, Walk.length_map] using hlen
    have hQO : Odd Q.length := by simpa only [hQL] using ho
    have hQC : ∀ w ∈ Q.support, w ∈ C.support → w = x := by
      intro w hwQ hwC
      exact hDC w (support_map_fanInclusionHom hHG P w hwQ) hwC
    have hlt := odd_cycle_length_lt_longest_of_intersection_subset_singleton hG hC hQ hQO hQC
    omega
  have hcard := Finset.card_le_card (Finset.insert_subset hCmem hsub)
  rw [Finset.card_insert_of_notMem hCnot] at hcard
  omega

end JSP000078

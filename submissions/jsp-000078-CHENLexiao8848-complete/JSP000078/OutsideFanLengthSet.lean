import JSP000078.GyarfasLemmaOne
import JSP000078.FanHom
import JSP000078.MathlibBridge

/-! # An outside fan cannot already contain all the odd cycle lengths -/

namespace JSP000078

open SimpleGraph

/-- Every odd cycle length of a graph supported outside a longest odd
cycle is strictly shorter, by the historical two-link lemma. -/
theorem odd_lengths_of_disjoint_supported_graph_shorter
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : IsLongestOddCycle C)
    (hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support})
    {H : SimpleGraph {v : V // v ∈ D.support}}
    (hHG : H ≤ G.induce {v | v ∈ D.support}) {n : ℕ}
    (hn : n ∈ oddCycleLengths H) : n < C.length := by
  classical
  obtain ⟨hOdd, v, P, hP, hlen⟩ := (mem_oddCycleLengths H).mp hn
  let f := fanInclusionHom hHG
  let Q := P.map f
  have hQ : Q.IsCycle := hP.map (fanInclusionHom_injective hHG)
  have hQL : Q.length = n := by simpa only [Q, Walk.length_map] using hlen
  have hQO : Odd Q.length := by simpa only [hQL] using hOdd
  have hCQ : Disjoint {w | w ∈ C.support} {w | w ∈ Q.support} := by
    apply Set.disjoint_left.mpr
    intro w hwC hwQ
    have hwD := support_map_fanInclusionHom hHG P w hwQ
    exact Set.disjoint_left.mp hCD hwC hwD
  have hlt := outside_odd_cycle_length_lt_longest hG hC hQ hQO hCQ
  omega

/-- The original longest odd length is new beyond every outside graph's
odd lengths. Consequently its cardinality is strictly larger. -/
theorem card_odd_lengths_supported_outside_lt
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : IsLongestOddCycle C)
    (hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support})
    {H : SimpleGraph {v : V // v ∈ D.support}}
    (hHG : H ≤ G.induce {v | v ∈ D.support}) :
    (oddCycleLengths H).card < (oddCycleLengths G).card := by
  classical
  have hsub : oddCycleLengths H ⊆ oddCycleLengths G :=
    oddCycleLengths_subset_of_injective_hom (fanInclusionHom hHG) (fanInclusionHom_injective hHG)
  have hCmem : C.length ∈ oddCycleLengths G :=
    (mem_oddCycleLengths G).mpr ⟨hC.2.1, c, C, hC.1, rfl⟩
  have hCnot : C.length ∉ oddCycleLengths H := by
    intro h
    exact (Nat.lt_irrefl C.length) (odd_lengths_of_disjoint_supported_graph_shorter hG hC hCD hHG h)
  have hcard := Finset.card_le_card (Finset.insert_subset hCmem hsub)
  rw [Finset.card_insert_of_notMem hCnot] at hcard
  omega

end JSP000078

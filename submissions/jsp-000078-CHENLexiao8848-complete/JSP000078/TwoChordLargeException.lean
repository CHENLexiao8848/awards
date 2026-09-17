import JSP000078.RouteFamilyContradiction
import JSP000078.TwoChordRouteFamily
import JSP000078.SharedEdgeException

/-! # The two-endpoint-chord exception for parameters at least two -/

namespace JSP000078

open SimpleGraph

/-- With 2k−1 common cycle attachments and a proper chord at each
outside path endpoint, k≥2 is impossible under the k-odd-length bound. -/
theorem two_endpoint_chords_impossible_large
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (X : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hK : (oddCycleLengths G).card = k) (hXcard : X.card = 2 * k - 1)
    (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x)
    {i j : ℕ} (hi : 2 ≤ i) (hiL : i ≤ P.length) (hj : j + 2 ≤ P.length)
    (hAi : G.Adj A (P.getVert i)) (hBj : G.Adj B (P.getVert j)) : False := by
  have hL : 2 ≤ P.length := by omega
  by_cases hedge : G.Adj A B
  · exact shared_endpoint_edge_exception hG hC hP hL hPC hedge X k (by omega) hK hXcard hX
  · obtain ⟨R, hR, _, hclass⟩ := exists_classified_two_chord_routes hP hedge hi hiL hj hAi hBj
    have hA : A ∉ C.support := fun h ↦ Set.disjoint_left.mp hPC P.start_mem_support h
    have hReal : ∀ h ∈ R, ∃ Q : G.Walk A B, Q.IsPath ∧ Q.length = h ∧
        Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} := by
      intro h hh
      obtain ⟨Q, hQ, hQL, hsub⟩ := hR h hh
      exact ⟨Q, hQ, hQL, Set.disjoint_left.mpr fun v hvQ hvC ↦
        Set.disjoint_left.mp hPC (hsub hvQ) hvC⟩
    exact impossible_of_classified_common_neighbor_routes hC.1 hC.2.1 hA hAB X hX R
      hReal k hk hXcard hK hclass

end JSP000078

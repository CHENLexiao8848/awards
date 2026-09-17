import JSP000078.SharedEdgeCycle
import JSP000078.CommonAttachmentGeometry
import JSP000078.GyarfasLemmaOne

/-! # The one-length shared-endpoint-edge exception -/

namespace JSP000078

open SimpleGraph

/-- With only one odd cycle length, an outside endpoint edge and a
shared cycle attachment contradict a longest odd cycle in a 2-connected graph. -/
theorem shared_endpoint_edge_impossible_one_odd_length
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c A B x : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hL : 2 ≤ P.length)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hx : x ∈ C.support) (hAx : G.Adj A x) (hBx : G.Adj B x) (hAB : G.Adj A B)
    (hK : (oddCycleLengths G).card = 1) : False := by
  classical
  have hedgeC : Disjoint {v | v ∈ hAB.toWalk.support} {v | v ∈ C.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hvC
    have hvab : v = A ∨ v = B := by
      simpa only [Set.mem_ofPred_eq, Adj.support_toWalk, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hv
    rcases hvab with rfl | rfl
    · exact Set.disjoint_left.mp hPC P.start_mem_support hvC
    · exact Set.disjoint_left.mp hPC P.end_mem_support hvC
  have hnilC : ∀ v ∈ (Walk.nil : G.Walk x x).support, v ∈ C.support := by
    intro v hv
    have hvx : v = x := by simpa using hv
    exact hvx ▸ hx
  obtain ⟨tri, htri, htriL⟩ := exists_cycle_of_outside_path_and_cycle_arc
    hAB.isPath_toWalk (by simp : (Walk.nil : G.Walk x x).IsPath) hAB.ne hedgeC hnilC hAx hBx
  have h3 : 3 ∈ oddCycleLengths G := by
    apply (mem_oddCycleLengths G).mpr
    refine ⟨by decide, A, tri, htri, ?_⟩
    simpa only [Adj.length_toWalk, Walk.length_nil] using htriL
  have huniq : ∀ n ∈ oddCycleLengths G, n = 3 := by
    obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hK
    have hm3 : m = 3 := by simpa only [hm, Finset.mem_singleton, eq_comm] using h3
    intro n hn
    simpa only [hm, hm3, Finset.mem_singleton] using hn
  have hCN : C.length = 3 := huniq C.length
    ((mem_oddCycleLengths G).mpr ⟨hC.2.1, c, C, hC.1, rfl⟩)
  rcases Nat.even_or_odd P.length with hEven | hOdd
  · obtain ⟨D, hD, hDL, hsub⟩ := exists_cycle_of_path_endpoint_edge hP hL hAB
    have hDO : Odd D.length := by rw [hDL]; exact hEven.add_odd odd_one
    have hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support} :=
      Set.disjoint_left.mpr fun v hvC hvD ↦ Set.disjoint_left.mp hPC (hsub hvD) hvC
    have hlt := outside_odd_cycle_length_lt_longest hG hC hD hDO hCD
    have hDN := huniq D.length ((mem_oddCycleLengths G).mpr ⟨hDO, A, D, hD, rfl⟩)
    omega
  · obtain ⟨D, hD, hDL⟩ := exists_cycle_of_outside_path_and_cycle_arc
      hP (by simp : (Walk.nil : G.Walk x x).IsPath) hAB.ne hPC hnilC hAx hBx
    simp only [Walk.length_nil, Nat.add_zero] at hDL
    have hDO : Odd D.length := by rw [hDL]; exact hOdd.add_even even_two
    have hDN := huniq D.length ((mem_oddCycleLengths G).mpr ⟨hDO, A, D, hD, rfl⟩)
    omega

end JSP000078

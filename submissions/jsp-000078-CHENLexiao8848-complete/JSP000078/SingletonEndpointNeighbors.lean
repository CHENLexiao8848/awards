import JSP000078.SharedAttachmentManyChords
import JSP000078.SharedFanLengthSet
import JSP000078.SharedFanCycleCount
import JSP000078.GyarfasLemmaTwo
import JSP000078.EndpointDegree
import JSP000078.EndpointConfigurationBridge

/-! # The singleton cycle-neighbor branch in the structural proof -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A high-degree endpoint with a unique cycle neighbor, shared by the
other endpoint, creates a sufficiently large fan meeting the odd cycle at
only that neighbor. Both alternatives for the fan contradict its length count. -/
theorem singleton_endpoint_cycle_neighbors_impossible
    (hG : TwoVertexConnected G) (k : ℕ) (hk : 1 ≤ k) (hK : (oddCycleLengths G).card = k)
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length)
    (hdegree : 2 * k + 1 ≤ G.degree A)
    (hXY : cycleNeighborVertices G C A = cycleNeighborVertices G C B)
    (hXcard : (cycleNeighborVertices G C A).card = 1) : False := by
  classical
  obtain ⟨x, hXeq⟩ := Finset.card_eq_one.mp hXcard
  have hxA : x ∈ cycleNeighborVertices G C A := by rw [hXeq]; simp
  have hxB : x ∈ cycleNeighborVertices G C B := hXY ▸ hxA
  have hxC := (mem_cycleNeighborVertices.mp hxA).1
  have hAx := (mem_cycleNeighborVertices.mp hxA).2
  have hBx := (mem_cycleNeighborVertices.mp hxB).2
  have hdeg := endpoint_degree_of_longest_outside_path hP hAB hPC hmax
  have hchord : 2 * k - 1 ≤ (pathChordVertices G P).card := by omega
  have hZ : ∀ v ∈ pathChordVertices G P, v ∈ P.support ∧ v ≠ P.getVert 1 ∧ G.Adj A v :=
    fun v hv ↦ mem_pathChordVertices.mp hv
  obtain ⟨S, hScard, hS⟩ := exists_path_chord_indices P (pathChordVertices G P) hZ
  have hScount : 2 * k - 1 ≤ S.card := by omega
  have hSp : ∀ i ∈ S, 2 ≤ i ∧ i ≤ P.length ∧ G.Adj A (P.getVert i) := hS
  have hxP : x ∉ P.support := fun h ↦ Set.disjoint_left.mp hPC h hxC
  let D := (P.concat hBx).concat hAx.symm
  have hD : D.IsCycle := shared_attachment_cycle_isCycle hP hAB hxP hAx hBx
  have hxD : x ∈ D.support := (mem_support_shared_attachment_cycle P hAx hBx).mpr (Or.inr rfl)
  let R := C.rotate x hxC
  have hR : IsLongestOddCycle R := hC.rotate hxC
  have hDR : ∀ w ∈ D.support, w ∈ R.support → w = x := by
    intro w hwD hwR
    rcases (mem_support_shared_attachment_cycle P hAx hBx).mp hwD with hwP | hwx
    · exact (Set.disjoint_left.mp hPC hwP ((C.mem_support_rotate_iff x hxC).mp hwR)).elim
    · exact hwx
  obtain ⟨H, F, hHG, _, hFcard⟩ := exists_fan_on_shared_attachment_cycle hP hAB hxP
    hAx hBx S k hScount hSp
  rcases incident_chord_bipartite_or_many_odd_lengths H F k hk hFcard with hBip | hMany
  · have hcount := odd_cycle_lengths_of_shared_bipartite_fan hG hR.1 hR.2.1 hD hxD hDR
      hHG F k hk hFcard hBip
    omega
  · have hlt := card_odd_lengths_supported_at_one_vertex_lt hG hR hDR hHG
    omega

end JSP000078

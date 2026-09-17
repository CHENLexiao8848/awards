import JSP000078.ChordVertexIndices
import JSP000078.PathSupportBounds

/-!
# Degree counts at endpoints of a longest outside path

Every endpoint neighbor lies on the forbidden cycle or on the path.
These disjoint vertex sets contribute the cycle-neighbor count and the
proper-chord count, together with the initial path neighbor counted once.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Split the initial endpoint's degree into cycle neighbors, proper
path-chord neighbors, and the one initial path edge. Only endpoint
neighbor containment is needed for this finite-set identity. -/
theorem endpoint_degree_of_neighbor_containment
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hneighbors : ∀ v, G.Adj A v → v ∈ C.support ∨ v ∈ P.support) :
    G.degree A = (cycleNeighborVertices G C A).card +
      (pathChordVertices G P).card + 1 := by
  classical
  have hPpos : 0 < P.length :=
    Nat.pos_of_ne_zero fun h ↦ hAB (Walk.eq_of_length_eq_zero h)
  have hAsnd : G.Adj A (P.getVert 1) := by
    simpa only [Walk.getVert_zero, Nat.zero_add] using P.adj_getVert_succ hPpos
  have hnotChord : P.getVert 1 ∉ pathChordVertices G P := by
    simp only [mem_pathChordVertices, ne_eq, not_true_eq_false, false_and, and_false, not_false_eq_true]
  have hdisjoint : Disjoint (cycleNeighborVertices G C A)
      (insert (P.getVert 1) (pathChordVertices G P)) := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvP
    have hvCycle := (mem_cycleNeighborVertices.mp hvC).1
    have hvPath : v ∈ P.support := by
      rcases Finset.mem_insert.mp hvP with rfl | hvChord
      · exact P.getVert_mem_support 1
      · exact (mem_pathChordVertices.mp hvChord).1
    exact Set.disjoint_left.mp hPC hvPath hvCycle
  have hneighborSet : G.neighborFinset A = cycleNeighborVertices G C A ∪
      insert (P.getVert 1) (pathChordVertices G P) := by
    ext v
    constructor
    · intro hv
      have hAv := (G.mem_neighborFinset A v).mp hv
      rcases hneighbors v hAv with hvC | hvP
      · exact Finset.mem_union_left _ (mem_cycleNeighborVertices.mpr ⟨hvC, hAv⟩)
      · apply Finset.mem_union_right
        by_cases hvsnd : v = P.getVert 1
        · exact Finset.mem_insert.mpr (Or.inl hvsnd)
        · exact Finset.mem_insert_of_mem (mem_pathChordVertices.mpr ⟨hvP, hvsnd, hAv⟩)
    · intro hv
      apply (G.mem_neighborFinset A v).mpr
      rcases Finset.mem_union.mp hv with hvC | hvP
      · exact (mem_cycleNeighborVertices.mp hvC).2
      · rcases Finset.mem_insert.mp hvP with rfl | hvChord
        · exact hAsnd
        · exact (mem_pathChordVertices.mp hvChord).2.2
  rw [← G.card_neighborFinset_eq_degree A, hneighborSet,
    Finset.card_union_of_disjoint hdisjoint, Finset.card_insert_of_notMem hnotChord]
  omega

/-- A longest simple path outside a prescribed cycle satisfies the
initial-endpoint degree decomposition used in the source's main proof. -/
theorem endpoint_degree_of_longest_outside_path
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length) :
    G.degree A = (cycleNeighborVertices G C A).card +
      (pathChordVertices G P).card + 1 := by
  apply endpoint_degree_of_neighbor_containment hAB hPC
  intro v hAv
  apply neighbor_mem_forbidden_or_support_of_longest_path_start
    (S := {v | v ∈ C.support}) hP
  · intro w hw hCw
    exact Set.disjoint_left.mp hPC hw hCw
  · intro x y Q hQ havoid
    apply hmax x y Q hQ
    exact Set.disjoint_left.mpr fun w hwQ hwC ↦ havoid w hwQ hwC
  · exact hAv

/-- The same degree decomposition at the final endpoint uses the proper
chord set of the reversed path. -/
theorem endpoint_degree_of_longest_outside_path_end
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length) :
    G.degree B = (cycleNeighborVertices G C B).card +
      (pathChordVertices G P.reverse).card + 1 := by
  apply endpoint_degree_of_longest_outside_path hP.reverse hAB.symm
  · simpa only [Walk.support_reverse, List.mem_reverse] using hPC
  · intro x y Q hQ hQC
    simpa only [Walk.length_reverse] using hmax x y Q hQ hQC

end JSP000078

import JSP000078.PathEndpointFan
import JSP000078.FanSubgraph
import JSP000078.OutsideFanLengthSet
import JSP000078.DisjointFanCycleCount
import JSP000078.GyarfasLemmaTwo
import JSP000078.PathSupportBounds
import JSP000078.ChordVertexIndices

/-! # Both endpoints of a longest outside path meet the odd cycle -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The initial endpoint cannot have all its neighbors outside the
longest odd cycle: its path fan yields an extra odd length in either case. -/
theorem longest_outside_path_start_meets_cycle
    (hG : TwoVertexConnected G) (k : ℕ) (hk : 1 ≤ k)
    (hK : (oddCycleLengths G).card = k) {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length)
    (hdegree : 2 * k + 1 ≤ G.degree A) :
    (cycleNeighborVertices G C A).Nonempty := by
  classical
  by_contra hnone
  have hneighbors : ∀ v : V, G.Adj A v → v ∈ P.support := by
    intro v hAv
    have hcases := neighbor_mem_forbidden_or_support_of_longest_path_start
      (S := {v | v ∈ C.support}) hP
      (fun w hw hwC ↦ Set.disjoint_left.mp hPC hw hwC)
      (fun x y Q hQ hav ↦ hmax x y Q hQ (Set.disjoint_left.mpr fun w hwQ hwC ↦ hav w hwQ hwC)) hAv
    rcases hcases with hvC | hvP
    · exact (hnone ⟨v, mem_cycleNeighborVertices.mpr ⟨hvC, hAv⟩⟩).elim
    · exact hvP
  obtain ⟨D, J, hD, hDsub, hJcard, hJ⟩ :=
    exists_cycle_with_many_chords_of_path_neighbors hP hneighbors k hk hdegree
  obtain ⟨J', hJsub, hJ'card⟩ := Finset.exists_subset_card_eq hJcard
  have hJ' : ∀ j ∈ J', 2 ≤ j.val ∧ j.val + 2 ≤ D.length ∧ G.Adj A (D.getVert j.val) :=
    fun j hj ↦ hJ j (hJsub hj)
  have hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support} :=
    Set.disjoint_left.mpr fun v hvC hvD ↦ Set.disjoint_left.mp hPC (hDsub hvD) hvC
  obtain ⟨H, F, hHG, _, hFcard⟩ := exists_cycle_fan_on_support hD J' hJ'
  have hFcount : F.indices.card = 2 * k - 1 := hFcard.trans hJ'card
  rcases incident_chord_bipartite_or_many_odd_lengths H F k hk hFcount with hBip | hMany
  · have hcount := odd_cycle_lengths_of_disjoint_bipartite_fan hG hC.1 hC.2.1 hD hCD
      hHG F k hk hFcount hBip
    omega
  · have hlt := card_odd_lengths_supported_outside_lt hG hC hCD hHG
    omega

/-- Both ends meet the cycle; the second conclusion follows by reversing
the same longest path, without changing its support or maximality. -/
theorem longest_outside_path_ends_meet_cycle
    (hG : TwoVertexConnected G) (k : ℕ) (hk : 1 ≤ k)
    (hK : (oddCycleLengths G).card = k) {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length)
    (hdegA : 2 * k + 1 ≤ G.degree A) (hdegB : 2 * k + 1 ≤ G.degree B) :
    (cycleNeighborVertices G C A).Nonempty ∧ (cycleNeighborVertices G C B).Nonempty := by
  refine ⟨longest_outside_path_start_meets_cycle hG k hk hK hC hP hPC hmax hdegA, ?_⟩
  apply longest_outside_path_start_meets_cycle hG k hk hK hC hP.reverse
  · simpa only [Walk.support_reverse, List.mem_reverse] using hPC
  · intro x y Q hQ hQC
    simpa only [Walk.length_reverse] using hmax x y Q hQ hQC
  · exact hdegB

end JSP000078

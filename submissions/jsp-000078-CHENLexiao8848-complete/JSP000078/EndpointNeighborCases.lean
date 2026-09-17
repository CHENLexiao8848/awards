import JSP000078.EndpointDegree
import JSP000078.GyarfasLemmaFour
import JSP000078.GyarfasLemmaEight
import JSP000078.EndpointCountArithmetic

/-!
# The unequal cycle-neighbor case for a longest outside path

The smaller endpoint's degree and the endpoint count leave only the
two-large-attachment exception, already ruled out by the corrected
historical Lemma 8. All finite sets are the actual neighbor and chord sets.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Different cycle-neighbor sets at the oriented endpoints of a
longest outside path are impossible under the historical degree bound. -/
theorem unequal_endpoint_cycle_neighbors_impossible
    (k : ℕ) (hk : 1 ≤ k) (hK : (oddCycleLengths G).card = k)
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length)
    (hdegreeA : 2 * k + 1 ≤ G.degree A)
    (hXne : (cycleNeighborVertices G C A).Nonempty)
    (hXYcard : (cycleNeighborVertices G C A).card ≤ (cycleNeighborVertices G C B).card)
    (hXYne : cycleNeighborVertices G C A ≠ cycleNeighborVertices G C B) : False := by
  classical
  let X := cycleNeighborVertices G C A
  let Y := cycleNeighborVertices G C B
  let Z := pathChordVertices G P
  have hextra : ∃ y ∈ Y, y ∉ X := by
    by_contra hnone
    have hsub : Y ⊆ X := by
      intro y hy
      by_contra hyX
      exact hnone ⟨y, hy, hyX⟩
    have heq : Y = X := Finset.eq_of_subset_of_card_le hsub hXYcard
    exact hXYne heq.symm
  obtain ⟨y, hyY, hyX⟩ := hextra
  have hyC : y ∈ C.support := (mem_cycleNeighborVertices.mp hyY).1
  have hBy : G.Adj B y := (mem_cycleNeighborVertices.mp hyY).2
  have hX : ∀ v ∈ X, v ∈ C.support ∧ v ≠ y ∧ G.Adj A v := by
    intro v hv
    obtain ⟨hvC, hAv⟩ := mem_cycleNeighborVertices.mp hv
    exact ⟨hvC, fun heq ↦ hyX (heq ▸ hv), hAv⟩
  have hZ : ∀ v ∈ Z, v ∈ P.support ∧ v ≠ P.getVert 1 ∧ G.Adj A v :=
    fun _ hv ↦ mem_pathChordVertices.mp hv
  have hcount := odd_lengths_of_endpoint_neighbor_sets hC hP hAB hPC hyC hBy X Z hXne hX hZ
  have hdeg := endpoint_degree_of_longest_outside_path hP hAB hPC hmax
  have hdegree : 2 * k ≤ X.card + Z.card := by
    change G.degree A = X.card + Z.card + 1 at hdeg
    omega
  have hcount' : Z.card + (X.card + 1) / 2 ≤ k := by
    rw [hK] at hcount
    exact hcount
  obtain ⟨_, hXcard⟩ := distinct_neighbors_exception_cases X.card Z.card k hdegree hcount'
  have hYcard : 2 * k ≤ Y.card := by
    change X.card ≤ Y.card at hXYcard
    omega
  have hXadj : ∀ v ∈ X, v ∈ C.support ∧ G.Adj A v :=
    fun _ hv ↦ mem_cycleNeighborVertices.mp hv
  have hYadj : ∀ v ∈ Y, v ∈ C.support ∧ G.Adj B v :=
    fun _ hv ↦ mem_cycleNeighborVertices.mp hv
  exact two_large_endpoint_attachment_sets_impossible hC.1 hC.2.1 hP hAB hPC
    X Y k hk hK hXcard hYcard hXadj hYadj

end JSP000078

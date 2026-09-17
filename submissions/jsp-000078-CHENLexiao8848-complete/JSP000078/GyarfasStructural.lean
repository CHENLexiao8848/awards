import JSP000078.GyarfasLemmaFive
import JSP000078.LongestOutsidePath
import JSP000078.LongestOutsideEndpoints
import JSP000078.EndpointNeighborCases
import JSP000078.EqualEndpointManyNeighbors
import JSP000078.SingletonEndpointNeighbors

/-!
# Gyárfás's structural theorem

This implements the longest-odd-cycle and longest-outside-path proof. Every
endpoint branch is discharged by the published counting lemmas and the
explicitly verified boundary completions.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The endpoints of a nontrivial longest outside path give a contradiction
once both have the required minimum degree. -/
theorem no_nontrivial_longest_outside_path
    (hG : TwoVertexConnected G) (k : ℕ) (hk : 1 ≤ k)
    (hK : (oddCycleLengths G).card = k)
    (hdegree : ∀ v : V, 2 * k + 1 ≤ G.degree v)
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length) : False := by
  classical
  have oriented : ∀ a b : V, ∀ Q : G.Walk a b, Q.IsPath → a ≠ b →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} →
      (∀ x y : V, ∀ R : G.Walk x y, R.IsPath →
        Disjoint {v | v ∈ R.support} {v | v ∈ C.support} → R.length ≤ Q.length) →
      (cycleNeighborVertices G C a).card ≤ (cycleNeighborVertices G C b).card → False := by
    intro a b Q hQ hab hQC hQmax horder
    obtain ⟨hAnon, _⟩ := longest_outside_path_ends_meet_cycle hG k hk hK hC hQ hQC
      hQmax (hdegree a) (hdegree b)
    by_cases hsame : cycleNeighborVertices G C a = cycleNeighborVertices G C b
    · by_cases hmany : 2 ≤ (cycleNeighborVertices G C a).card
      · exact equal_endpoint_many_neighbors_impossible hG hC hQ hab hQC hQmax k hk hK
          (hdegree a) (hdegree b) hsame hmany
      · have hcard : (cycleNeighborVertices G C a).card = 1 := by
          have := Finset.card_pos.mpr hAnon
          omega
        exact singleton_endpoint_cycle_neighbors_impossible hG k hk hK hC hQ hab hQC
          hQmax (hdegree a) hsame hcard
    · exact unequal_endpoint_cycle_neighbors_impossible k hk hK hC hQ hab hQC hQmax
        (hdegree a) hAnon horder hsame
  rcases le_total (cycleNeighborVertices G C A).card (cycleNeighborVertices G C B).card with h | h
  · exact oriented A B P hP hAB hPC hmax h
  · apply oriented B A P.reverse hP.reverse hAB.symm
    · simpa only [Walk.support_reverse, List.mem_reverse] using hPC
    · intro x y Q hQ hQC
      simpa only [Walk.length_reverse] using hmax x y Q hQ hQC
    · exact h

/-- Gyárfás (1992), Theorem 1: a 2-connected graph with exactly k≥1
odd cycle lengths and minimum degree at least 2k+1 is the complete graph
on exactly 2k+2 vertices. -/
theorem gyarfas_structural_theorem (k : ℕ) (hk : 1 ≤ k)
    (hG : TwoVertexConnected G) (hdegree : ∀ v : V, 2 * k + 1 ≤ G.degree v)
    (hK : (oddCycleLengths G).card = k) : G = ⊤ ∧ Fintype.card V = 2 * k + 2 := by
  classical
  have hnon : (oddCycleLengths G).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, C, hC⟩ := exists_longest_odd_cycle hnon
  have hInd : ∀ x y : V, x ∉ C.support → y ∉ C.support → ¬G.Adj x y := by
    intro x y hx hy hxy
    obtain ⟨A, B, P, hP, hAB, hPC, hmax⟩ :=
      exists_nontrivial_longest_outside_path C ⟨x, y, hx, hy, hxy⟩
    exact no_nontrivial_longest_outside_path hG k hk hK hdegree hC hP hAB hPC hmax
  exact complete_of_independent_outside_longest_odd_cycle k hk hdegree hK hC hInd

/-- The complete source structural proposition, with no remaining mathematical premise. -/
theorem historicalGyarfasStructuralTheorem : HistoricalGyarfasStructuralTheorem := by
  intro V _ G _ k hk hG hdegree hK
  exact gyarfas_structural_theorem k hk hG hdegree hK

end JSP000078

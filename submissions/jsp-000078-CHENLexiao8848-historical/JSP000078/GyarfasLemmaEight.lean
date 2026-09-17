import JSP000078.DistinctAttachmentsLarge
import JSP000078.DistinctAttachmentsOne
import JSP000078.HistoricalExceptionsSpec

/-!
# The distinct-neighbor exception with the retained endpoint orientation

The source's smaller-endpoint choice ensures both endpoints have at least
2k cycle neighbors. This condition is essential to a correct standalone
form of the exceptional case.
-/

namespace JSP000078

open SimpleGraph

theorem two_large_endpoint_attachment_sets_impossible
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (X Y : Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hK : (oddCycleLengths G).card = k) (hXcard : X.card = 2 * k) (hYcard : 2 * k ≤ Y.card)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ G.Adj A v)
    (hY : ∀ v ∈ Y, v ∈ C.support ∧ G.Adj B v) : False := by
  obtain ⟨Y', hsub, hY'card⟩ := Finset.exists_subset_card_eq hYcard
  have hY' : ∀ v ∈ Y', v ∈ C.support ∧ G.Adj B v := fun v hv ↦ hY v (hsub hv)
  by_cases hk1 : k = 1
  · exact distinct_attachments_impossible_one hC hCO hP hAB hPC X Y'
      (hk1 ▸ hK) (by simpa only [hk1] using hXcard) (by simpa only [hk1] using hY'card) hX hY'
  · exact distinct_attachments_impossible_large hC hCO hP hAB hPC X Y' k
      (by omega) hK hXcard hY'card hX hY'

/-- The source-context Lemma 8 obligation is discharged, retaining the
larger second endpoint's attachment count that its proof uses implicitly. -/
theorem historicalDistinctEndpointException : HistoricalDistinctEndpointException := by
  intro V _ G _ k c A B C P hk _ _ hK hC hP hAB hPC _ hXcard hXY _ _
  classical
  have hYcard : 2 * k ≤ (cycleNeighborVertices G C B).card := by omega
  have hX : ∀ v ∈ cycleNeighborVertices G C A, v ∈ C.support ∧ G.Adj A v := by
    intro v hv
    simpa only [cycleNeighborVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  have hY : ∀ v ∈ cycleNeighborVertices G C B, v ∈ C.support ∧ G.Adj B v := by
    intro v hv
    simpa only [cycleNeighborVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  exact (two_large_endpoint_attachment_sets_impossible hC.1 hC.2.1 hP hAB hPC
    (cycleNeighborVertices G C A) (cycleNeighborVertices G C B) k hk hK hXcard hYcard hX hY).elim

end JSP000078

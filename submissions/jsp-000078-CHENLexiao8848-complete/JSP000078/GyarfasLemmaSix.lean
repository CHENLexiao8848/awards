import JSP000078.TwoChordLargeException
import JSP000078.TwoChordOneException
import JSP000078.ChordVertexIndices

/-! # The equal-neighbor one-chord exception in the historical proof -/

namespace JSP000078

open SimpleGraph

/-- Both proper endpoint chords and 2k−1 selected common cycle neighbors
contradict the k-odd-length hypothesis. The singleton case uses vertex deletion. -/
theorem two_endpoint_chords_impossible
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (X : Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hK : (oddCycleLengths G).card = k) (hXcard : X.card = 2 * k - 1)
    (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x)
    {i j : ℕ} (hi : 2 ≤ i) (hiL : i ≤ P.length) (hj : j + 2 ≤ P.length)
    (hAi : G.Adj A (P.getVert i)) (hBj : G.Adj B (P.getVert j)) : False := by
  by_cases hk1 : k = 1
  · have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hXne
    exact one_odd_length_shared_attachment_chord_impossible hG hC.1 hC.2.1 (hk1 ▸ hK)
      hP hAB hPC (hX x hx).1 (hX x hx).2.1 (hX x hx).2.2 hi hiL hAi
  · exact two_endpoint_chords_impossible_large hG hC hP hAB hPC X k (by omega)
      hK hXcard hX hi hiL hj hAi hBj

/-- The exact inherited-context Lemma 6 proposition, including the
shared endpoint-edge boundary omitted by the source's route classification. -/
theorem historicalEqualEndpointChordException : HistoricalEqualEndpointChordException := by
  intro V _ G _ k c A B C P hk hG _ hK hC hP hAB hPC _ hXY hXcard hAcard hBcard
  classical
  have hAnon : (pathChordVertices G P).Nonempty := Finset.card_pos.mp (by omega)
  have hBnon : (pathChordVertices G P.reverse).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi, hiL, hAi⟩ := exists_path_proper_chord_index P hAnon
  obtain ⟨j, hj, hBj⟩ := exists_path_reverse_proper_chord_index P hBnon
  have hX : ∀ x ∈ cycleNeighborVertices G C A, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x := by
    intro x hx
    have ha := mem_cycleNeighborVertices.mp hx
    have hb := mem_cycleNeighborVertices.mp (hXY ▸ hx)
    exact ⟨ha.1, ha.2, hb.2⟩
  exact (two_endpoint_chords_impossible hG hC hP hAB hPC (cycleNeighborVertices G C A)
    k hk hK hXcard hX hi hiL hj hAi hBj).elim

end JSP000078

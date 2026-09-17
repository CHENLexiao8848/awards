import JSP000078.GyarfasLemmaFour
import JSP000078.GyarfasLemmaSix
import JSP000078.GyarfasLemmaSeven
import JSP000078.EndpointDegree
import JSP000078.EndpointCountArithmetic

/-!
# The equal endpoint-neighbor branch with at least two neighbors

Exclude one common cycle neighbor when applying Lemma 4. The resulting
degree and length bounds leave either enough common neighbors for Lemma 7
or exactly one proper chord at each endpoint for Lemma 6.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Lemma 4 after excluding a common cycle neighbor from an endpoint's
cycle-neighbor set, leaving a nonempty attachment set. -/
theorem endpoint_neighbor_count_excluding_common
    {c A B y : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hsize : 2 ≤ (cycleNeighborVertices G C A).card)
    (hy : y ∈ cycleNeighborVertices G C A) (hBy : G.Adj B y) :
    (pathChordVertices G P).card +
      ((cycleNeighborVertices G C A).card - 1 + 1) / 2 ≤ (oddCycleLengths G).card := by
  classical
  have hXne : ((cycleNeighborVertices G C A).erase y).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hy]; omega)
  have hcount := odd_lengths_of_endpoint_neighbor_sets hC hP hAB hPC
    (mem_cycleNeighborVertices.mp hy).1 hBy
    ((cycleNeighborVertices G C A).erase y) (pathChordVertices G P) hXne
    (by
      intro v hv
      obtain ⟨hvy, hvX⟩ := Finset.mem_erase.mp hv
      have hvdata := mem_cycleNeighborVertices.mp hvX
      exact ⟨hvdata.1, hvy, hvdata.2⟩)
    (fun _ hv ↦ mem_pathChordVertices.mp hv)
  simpa only [Finset.card_erase_of_mem hy] using hcount

/-- Equal endpoint cycle-neighbor sets of size at least two are
impossible under the historical degree and odd-length hypotheses. The
singleton attachment case is intentionally separate. -/
theorem equal_endpoint_many_neighbors_impossible [DecidableRel G.Adj]
    (hG : TwoVertexConnected G) {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hmax : ∀ x y : V, ∀ Q : G.Walk x y, Q.IsPath →
      Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length)
    (k : ℕ) (hk : 1 ≤ k) (hK : (oddCycleLengths G).card = k)
    (hdegA : 2 * k + 1 ≤ G.degree A) (hdegB : 2 * k + 1 ≤ G.degree B)
    (hXY : cycleNeighborVertices G C A = cycleNeighborVertices G C B)
    (hsize : 2 ≤ (cycleNeighborVertices G C A).card) : False := by
  classical
  let X := cycleNeighborVertices G C A
  let qA := (pathChordVertices G P).card
  let qB := (pathChordVertices G P.reverse).card
  have hXne : X.Nonempty := Finset.card_pos.mp (by change 0 < (cycleNeighborVertices G C A).card; omega)
  obtain ⟨y, hy⟩ := hXne
  have hXY' : X = cycleNeighborVertices G C B := hXY
  have hyA := mem_cycleNeighborVertices.mp hy
  have hyB := mem_cycleNeighborVertices.mp (hXY' ▸ hy)
  have hcountA : qA + (X.card - 1 + 1) / 2 ≤ k := by
    simpa only [hK] using endpoint_neighbor_count_excluding_common hC hP hAB hPC hsize hy hyB.2
  have hdegreeA := endpoint_degree_of_longest_outside_path hP hAB hPC hmax
  have hdegreeB := endpoint_degree_of_longest_outside_path_end hP hAB hPC hmax
  change G.degree A = X.card + qA + 1 at hdegreeA
  rw [← hXY] at hdegreeB
  change G.degree B = X.card + qB + 1 at hdegreeB
  have hXall : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x := by
    intro x hx
    have hxA := mem_cycleNeighborVertices.mp hx
    have hxB := mem_cycleNeighborVertices.mp (hXY' ▸ hx)
    exact ⟨hxA.1, hxA.2, hxB.2⟩
  have hcases := equal_neighbors_exception_cases X.card qA k
    (by change 1 ≤ (cycleNeighborVertices G C A).card; omega) (by omega) hcountA
  rcases hcases with ⟨hqA, htotal⟩ | ⟨_, htotal⟩
  · have hXcard : X.card = 2 * k - 1 := by omega
    have hPrevC : Disjoint {v | v ∈ P.reverse.support} {v | v ∈ C.support} := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hPC
    have hsizeB : 2 ≤ (cycleNeighborVertices G C B).card := by simpa only [← hXY] using hsize
    have hcountB : qB + (X.card - 1 + 1) / 2 ≤ k := by
      have h := endpoint_neighbor_count_excluding_common hC hP.reverse hAB.symm hPrevC
        hsizeB (hXY' ▸ hy) hyA.2
      simpa only [← hXY, hK] using h
    have hqB : qB = 1 := by
      have hcasesB := equal_neighbors_exception_cases X.card qB k
        (by change 1 ≤ (cycleNeighborVertices G C A).card; omega) (by omega) hcountB
      omega
    have hAnon : (pathChordVertices G P).Nonempty := Finset.card_pos.mp (by change 0 < qA; omega)
    have hBnon : (pathChordVertices G P.reverse).Nonempty := Finset.card_pos.mp (by change 0 < qB; omega)
    obtain ⟨i, hi, hiL, hAi⟩ := exists_path_proper_chord_index P hAnon
    obtain ⟨j, hj, hBj⟩ := exists_path_reverse_proper_chord_index P hBnon
    exact two_endpoint_chords_impossible hG hC hP hAB hPC X k hk hK hXcard hXall hi hiL hj hAi hBj
  · have hXlarge : 2 * k ≤ X.card := by omega
    obtain ⟨Y, hYX, hYcard⟩ := Finset.exists_subset_card_eq hXlarge
    have hcount := odd_lengths_of_common_endpoint_neighbors hC.1 hC.2.1 hP hAB hPC
      Y k hk hYcard (fun x hx ↦ hXall x (hYX hx))
    omega

end JSP000078

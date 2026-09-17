import JSP000078.SharedEdgeGeometry
import JSP000078.SharedEdgeConnectorCount
import JSP000078.SharedEdgeOneLength
import JSP000078.EndpointConfigurationBridge

/-! # The shared-endpoint-edge boundary omitted by the two-chord classification -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- For k≥2, an endpoint edge, a shared attachment, and 2k−2 other
attachments force k+1 odd lengths. Triangle length three supplies the extra length. -/
theorem odd_lengths_of_shared_endpoint_edge_large {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B} (hC : IsLongestOddCycle C)
    (hP : P.IsPath) (hL : 2 ≤ P.length)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hAB : G.Adj A B) (hAc : G.Adj A c) (hBc : G.Adj B c)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 1 ≤ d ∧ d < C.length ∧ G.Adj A (C.getVert d))
    (k : ℕ) (hk : 2 ≤ k) (hcard : 2 * k - 2 ≤ D.card) :
    k + 1 ≤ (oddCycleLengths G).card := by
  let T := complementaryParityDistances D C.length (P.length + 1)
  have hsize : k - 1 ≤ T.card := le_card_complementaryParityDistances
    D C.length (P.length + 1) (k - 1) (by omega)
    (fun d hd ↦ ⟨(hD d hd).1, (hD d hd).2.1⟩) (by omega)
  obtain ⟨h3, hmem⟩ := shared_edge_complementary_distances_data hC hP hPC hAB hAc hBc
    D (fun d hd ↦ ⟨(hD d hd).1, (hD d hd).2.1⟩)
    (fun d hd ↦ (hD d hd).2.2) (P.length + 1)
  apply shared_edge_connector_count (oddCycleLengths G) T P.length k hk hL hsize
    (fun d hd ↦ (hmem d hd).1.1) (fun d hd ↦ (hmem d hd).2.1)
    (fun d hd ↦ (hmem d hd).2.2.1) (fun d hd ↦ (hmem d hd).2.2.2.1)
    ?_ h3
  intro d hd ho
  simpa only [Nat.add_assoc] using (hmem d hd).2.2.2.2
    (by simpa only [Nat.add_assoc] using ho)

/-- Selected common neighbors discharge the shared-edge exception for
all k, including the separate one-odd-length connectivity argument. -/
theorem shared_endpoint_edge_exception
    (hG : TwoVertexConnected G) {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hL : 2 ≤ P.length)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support}) (hAB : G.Adj A B)
    (X : Finset V) (k : ℕ) (hk : 1 ≤ k) (hK : (oddCycleLengths G).card = k)
    (hcard : X.card = 2 * k - 1)
    (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x) : False := by
  classical
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hXne
  by_cases hk1 : k = 1
  · exact shared_endpoint_edge_impossible_one_odd_length hG hC hP hL hPC
      (hX x hx).1 (hX x hx).2.1 (hX x hx).2.2 hAB (hk1 ▸ hK)
  · let R := C.rotate x (hX x hx).1
    have hR : IsLongestOddCycle R := hC.rotate (hX x hx).1
    have hPR : Disjoint {v | v ∈ P.support} {v | v ∈ R.support} := by
      apply Set.disjoint_left.mpr
      intro v hvP hvR
      exact Set.disjoint_left.mp hPC hvP ((C.mem_support_rotate_iff x (hX x hx).1).mp hvR)
    have hXR : ∀ v ∈ X.erase x, v ∈ R.support ∧ v ≠ x ∧ G.Adj A v := by
      intro v hv
      obtain ⟨hvx, hvX⟩ := Finset.mem_erase.mp hv
      exact ⟨(C.mem_support_rotate_iff x (hX x hx).1).mpr (hX v hvX).1, hvx, (hX v hvX).2.1⟩
    obtain ⟨D, hDcard, hD⟩ := exists_cycle_attachment_indices hR.1 (X.erase x) hXR
    have hDsize : 2 * k - 2 ≤ D.card := by
      rw [hDcard, Finset.card_erase_of_mem hx, hcard]
      omega
    have hcount := odd_lengths_of_shared_endpoint_edge_large hR hP hL hPR hAB
      (hX x hx).2.1 (hX x hx).2.2 D hD k (by omega) hDsize
    omega

end JSP000078

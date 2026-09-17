import JSP000078.CommonNeighborCount
import JSP000078.EndpointConfigurationBridge

/-! # The common-neighbor exception in Gyárfás's structural proof -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A nonempty outside path and 2k attachments at its first endpoint
give k+1 odd lengths if the last endpoint shares just one attachment. -/
theorem odd_lengths_of_shared_attachment {c A B x : V}
    {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (X : Finset V) (k : ℕ) (hk : 1 ≤ k) (hcard : X.card = 2 * k)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ G.Adj A v)
    (hx : x ∈ X) (hBx : G.Adj B x) :
    k + 1 ≤ (oddCycleLengths G).card := by
  classical
  let R := C.rotate x (hX x hx).1
  have hR : R.IsCycle := hC.rotate (hX x hx).1
  have hRO : Odd R.length := by simpa only [R, Walk.length_rotate] using hCO
  have hPR : Disjoint {v | v ∈ P.support} {v | v ∈ R.support} := by
    apply Set.disjoint_left.mpr
    intro v hvP hvR
    exact Set.disjoint_left.mp hPC hvP ((C.mem_support_rotate_iff x (hX x hx).1).mp hvR)
  have hXR : ∀ v ∈ X.erase x, v ∈ R.support ∧ v ≠ x ∧ G.Adj A v := by
    intro v hv
    obtain ⟨hvx, hvX⟩ := Finset.mem_erase.mp hv
    exact ⟨(C.mem_support_rotate_iff x (hX x hx).1).mpr (hX v hvX).1, hvx, (hX v hvX).2⟩
  obtain ⟨D, hDcard, hD⟩ := exists_cycle_attachment_indices hR (X.erase x) hXR
  apply odd_lengths_of_many_common_base_spokes hR hRO hP hAB hPR
    (hX x hx).2 hBx D hD k hk
  rw [hDcard, Finset.card_erase_of_mem hx, hcard]

/-- Gyárfás Lemma 7 in a stronger form requiring only the selected
common neighbors, not equality of the complete neighbor sets. -/
theorem odd_lengths_of_common_endpoint_neighbors {c A B : V}
    {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (X : Finset V) (k : ℕ) (hk : 1 ≤ k) (hcard : X.card = 2 * k)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ G.Adj A v ∧ G.Adj B v) :
    k + 1 ≤ (oddCycleLengths G).card := by
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hXne
  exact odd_lengths_of_shared_attachment hC hCO hP hAB hPC X k hk hcard
    (fun v hv ↦ ⟨(hX v hv).1, (hX v hv).2.1⟩) hx (hX x hx).2.2

end JSP000078

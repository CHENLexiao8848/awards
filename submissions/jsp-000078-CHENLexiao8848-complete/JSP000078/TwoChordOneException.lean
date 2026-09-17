import JSP000078.TwoChordOneOddPath
import JSP000078.SharedAttachmentEvenFan
import JSP000078.SharedFanContradiction
import JSP000078.EndpointConfigurationBridge

/-! # The singleton common-neighbor case completed using vertex deletion -/

namespace JSP000078

open SimpleGraph

/-- The one-odd-length case of the endpoint-chord exception actually
needs just one proper initial chord and a shared cycle attachment. -/
theorem one_odd_length_shared_attachment_chord_impossible
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c A B x : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hK : (oddCycleLengths G).card = 1)
    (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hx : x ∈ C.support) (hAx : G.Adj A x) (hBx : G.Adj B x)
    {i : ℕ} (hi : 2 ≤ i) (hiL : i ≤ P.length) (hAi : G.Adj A (P.getVert i)) : False := by
  classical
  rcases Nat.even_or_odd P.length with hEven | hOdd
  · let R := C.rotate x hx
    have hR : R.IsCycle := hC.rotate hx
    have hRO : Odd R.length := by simpa only [R, Walk.length_rotate] using hCO
    have hPR : Disjoint {v | v ∈ P.support} {v | v ∈ R.support} := by
      apply Set.disjoint_left.mpr
      intro v hvP hvR
      exact Set.disjoint_left.mp hPC hvP ((C.mem_support_rotate_iff x hx).mp hvR)
    let D := (P.concat hBx).concat hAx.symm
    have hxP : x ∉ P.support := fun h ↦ Set.disjoint_left.mp hPC h hx
    have hD : D.IsCycle := shared_attachment_cycle_isCycle hP hAB hxP hAx hBx
    have hxD : x ∈ D.support := (mem_support_shared_attachment_cycle P hAx hBx).mpr (Or.inr rfl)
    have hDR : ∀ v ∈ D.support, v ∈ R.support → v = x := by
      intro v hvD hvR
      rcases (mem_support_shared_attachment_cycle P hAx hBx).mp hvD with hvP | hvx
      · exact (Set.disjoint_left.mp hPR hvP hvR).elim
      · exact hvx
    obtain ⟨H, F, hHG, _, hFcard, hBip⟩ := exists_bipartite_fan_of_shared_attachment_even_path
      hG hK hR hRO hP hAB hPR hAx hBx hEven hi hiL hAi
    have hcount := two_le_oddCycleLengths_of_shared_bipartite_fan hG hR hRO hD hxD hDR
      hHG F hFcard hBip
    omega
  · exact one_odd_length_odd_outside_path_chord_impossible hG hC hCO hK hP hAB hOdd
      hPC hx hAx hBx hi hiL hAi

end JSP000078

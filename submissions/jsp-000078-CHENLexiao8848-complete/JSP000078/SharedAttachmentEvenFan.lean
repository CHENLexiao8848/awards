import JSP000078.FanSubgraph
import JSP000078.EvenFanBipartite
import JSP000078.SharedAttachmentCycle
import JSP000078.PathChordParity

/-!
# The bipartite one-chord fan in the one-odd-length case

Closing an even outside path at a common cycle attachment gives an even
cycle. Every proper initial chord lands at an odd position, so the exact
selected one-chord graph on this new cycle is bipartite.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Preserve the parity of selected chord positions when forming the
exact fan on an even cycle's support subtype. -/
theorem exists_bipartite_cycle_fan_on_support {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hEven : Even C.length) (J : Finset (Fin C.length))
    (hJ : ∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ C.length ∧ G.Adj c (C.getVert j.val))
    (hJO : ∀ j ∈ J, Odd j.val) :
    ∃ (H : SimpleGraph {v : V // v ∈ C.support}) (F : CycleWithIncidentChords H),
      H ≤ G.induce {v | v ∈ C.support} ∧ F.cycle.length = C.length ∧
        F.indices.card = J.card ∧ H.IsBipartite := by
  classical
  obtain ⟨H, F, hHG, hlen, hcard, hidx⟩ := exists_cycle_fan_on_support_indices hC J hJ
  refine ⟨H, F, hHG, hlen, hcard, F.isBipartite_of_even_length_of_odd_indices ?_ ?_⟩
  · simpa only [hlen] using hEven
  · intro j hj
    have hjval : j.val ∈ J.image (fun i ↦ i.val) := by
      rw [← hidx]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hjval
    exact heq ▸ hJO i hi

/-- An even outside path with a proper initial chord and a shared cycle
attachment gives a bipartite exact one-chord fan. Its vertices are exactly
the outside path vertices together with the shared attachment. -/
theorem exists_bipartite_fan_of_shared_attachment_even_path [Fintype V]
    (hG : TwoVertexConnected G) (hK : (oddCycleLengths G).card = 1)
    {x A B : V} {C : G.Walk x x} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hAx : G.Adj A x) (hBx : G.Adj B x) (hEven : Even P.length)
    {i : ℕ} (hi : 2 ≤ i) (hiL : i ≤ P.length) (hAi : G.Adj A (P.getVert i)) :
    let D := (P.concat hBx).concat hAx.symm
    ∃ (H : SimpleGraph {v : V // v ∈ D.support}) (F : CycleWithIncidentChords H),
      H ≤ G.induce {v | v ∈ D.support} ∧ F.cycle.length = P.length + 2 ∧
        F.indices.card = 1 ∧ H.IsBipartite := by
  classical
  let D := (P.concat hBx).concat hAx.symm
  have hxP : x ∉ P.support := fun hx ↦ Set.disjoint_left.mp hPC hx C.start_mem_support
  have hD : D.IsCycle := shared_attachment_cycle_isCycle hP hAB hxP hAx hBx
  have hDlen : D.length = P.length + 2 := shared_attachment_cycle_length P hAx hBx
  have hDEven : Even D.length := by rw [hDlen]; exact hEven.add even_two
  have hiD : i < D.length := by omega
  let j : Fin D.length := ⟨i, hiD⟩
  have hproper : ∀ z ∈ ({j} : Finset (Fin D.length)),
      2 ≤ z.val ∧ z.val + 2 ≤ D.length ∧ G.Adj A (D.getVert z.val) := by
    intro z hz
    have hzj : z = j := Finset.mem_singleton.mp hz
    subst z
    exact shared_attachment_cycle_chord P hAx hBx hi hiL hAi
  have hodd : ∀ z ∈ ({j} : Finset (Fin D.length)), Odd z.val := by
    intro z hz
    have hzj : z = j := Finset.mem_singleton.mp hz
    subst z
    exact path_chord_index_odd_of_one_odd_length hG hK hC hCO hP hPC hi hiL hAi
  obtain ⟨H, F, hHG, hFL, hFJ, hBip⟩ := exists_bipartite_cycle_fan_on_support hD hDEven {j} hproper hodd
  exact ⟨H, F, hHG, hFL.trans hDlen, by simpa only [Finset.card_singleton] using hFJ, hBip⟩

end JSP000078

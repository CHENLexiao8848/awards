import JSP000078.SharedEdgeCycle
import JSP000078.SingleOddLength

/-! # Chords inside the complement of the only odd cycle length -/

namespace JSP000078

open SimpleGraph

/-- A proper chord from a path's start outside an odd cycle must land
at an odd path position when the graph has only one odd cycle length. -/
theorem path_chord_index_odd_of_one_odd_length
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) (hK : (oddCycleLengths G).card = 1)
    {c A B : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hP : P.IsPath)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    {i : ℕ} (hi : 2 ≤ i) (hiL : i ≤ P.length) (hAi : G.Adj A (P.getVert i)) : Odd i := by
  have hprefL : (P.take i).length = i := by simp only [Walk.take_length, Nat.min_eq_left hiL]
  obtain ⟨D, hD, hDL, hsub⟩ := exists_cycle_of_path_endpoint_edge (hP.take i) (by omega) hAi
  have hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support} := by
    apply Set.disjoint_left.mpr
    intro v hvC hvD
    exact Set.disjoint_left.mp hPC ((P.isSubwalk_take i).support_subset (hsub hvD)) hvC
  have hEven := every_cycle_disjoint_from_cycle_even hG hK hC hCO hD hCD
  have he := Nat.even_iff.mp hEven
  rw [hDL, hprefL] at he
  rw [Nat.odd_iff]
  omega

end JSP000078

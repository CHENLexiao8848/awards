import JSP000078.PathSpokes
import JSP000078.SingleOddLength
import JSP000078.AttachmentCycles

/-! # The singleton-attachment exception with an odd outside path -/

namespace JSP000078

open SimpleGraph

/-- In the one-odd-length case, an odd outside path with a proper
initial chord cannot have a common cycle attachment at its endpoints. -/
theorem one_odd_length_odd_outside_path_chord_impossible
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : TwoVertexConnected G) {c A B x : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : C.IsCycle) (hCO : Odd C.length) (hK : (oddCycleLengths G).card = 1)
    (hP : P.IsPath) (hAB : A ≠ B) (hPO : Odd P.length)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hx : x ∈ C.support) (hAx : G.Adj A x) (hBx : G.Adj B x)
    {i : ℕ} (hi : 2 ≤ i) (hiL : i ≤ P.length) (hAi : G.Adj A (P.getVert i)) : False := by
  classical
  let D : G.Walk A A := (P.take i).concat hAi.symm
  have hDL : D.length = i + 1 := by simp only [D, Walk.length_concat, Walk.take_length, Nat.min_eq_left hiL]
  have hDcycle : D.IsCycle := by
    have hrev : D = ((P.take i).reverse.cons hAi).reverse := by simp [D, Walk.concat_eq_append]
    rw [hrev]
    apply Walk.IsCycle.reverse
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa using (hP.take i).reverse
    · simp only [Walk.length_cons, Walk.length_reverse, Walk.take_length, Nat.min_eq_left hiL]
      omega
  have hDsub : D.support ⊆ P.support := by
    intro v hv
    simp only [D, Walk.support_concat, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact (P.isSubwalk_take i).support_subset hv
    · exact P.start_mem_support
  have hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support} :=
    Set.disjoint_left.mpr fun v hvC hvD ↦ Set.disjoint_left.mp hPC (hDsub hvD) hvC
  have hDE := every_cycle_disjoint_from_cycle_even hG hK hC hCO hDcycle hCD
  have hiOdd : Odd i := by
    have he := Nat.even_iff.mp hDE
    rw [hDL] at he
    rw [Nat.odd_iff]
    omega
  obtain ⟨Q, hQ, hQL, hQsub⟩ := exists_path_of_path_start_spoke_support_subset hP
    (by omega) hiL hAi
  have hQPC : Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} :=
    Set.disjoint_left.mpr fun v hvQ hvC ↦ Set.disjoint_left.mp hPC (hQsub hvQ) hvC
  have hQO : Odd Q.length := by
    have hpm := Nat.odd_iff.mp hPO
    have him := Nat.odd_iff.mp hiOdd
    rw [Nat.odd_iff, hQL]
    omega
  have hnilC : ∀ v ∈ (Walk.nil : G.Walk x x).support, v ∈ C.support := by
    intro v hv
    have hvx : v = x := by simpa using hv
    exact hvx ▸ hx
  obtain ⟨E, hE, hEL⟩ := exists_cycle_of_outside_path_and_cycle_arc hP
    (by simp : (Walk.nil : G.Walk x x).IsPath) hAB hPC hnilC hAx hBx
  obtain ⟨F, hF, hFL⟩ := exists_cycle_of_outside_path_and_cycle_arc hQ
    (by simp : (Walk.nil : G.Walk x x).IsPath) hAB hQPC hnilC hAx hBx
  simp only [Walk.length_nil, Nat.add_zero] at hEL hFL
  have hEO : Odd E.length := by rw [hEL]; exact hPO.add_even even_two
  have hFO : Odd F.length := by rw [hFL]; exact hQO.add_even even_two
  have heq := odd_cycle_lengths_equal_of_card_one hK hE hEO hF hFO
  omega

end JSP000078

import JSP000078.PathGluing

/-! # The explicit cycle formed by an outside path and a common attachment -/

namespace JSP000078

open SimpleGraph

/-- Append the two edges through a vertex outside a nonempty simple path. -/
theorem shared_attachment_cycle_isCycle {V : Type*} {G : SimpleGraph V}
    {A B x : V} {P : G.Walk A B} (hP : P.IsPath) (hAB : A ≠ B)
    (hx : x ∉ P.support) (hAx : G.Adj A x) (hBx : G.Adj B x) :
    ((P.concat hBx).concat hAx.symm).IsCycle := by
  let Q : G.Walk B A := .cons hBx (.cons hAx.symm .nil)
  have hQ : Q.IsPath := by
    apply Walk.IsPath.cons
    · exact hAx.symm.isPath_toWalk
    · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(fun h ↦ hx (h ▸ P.end_mem_support)), hAB.symm⟩
  have hinter : ∀ v ∈ P.support, v ∈ Q.support → v = A ∨ v = B := by
    intro v hvP hvQ
    have hv : v = B ∨ v = x ∨ v = A := by
      simpa only [Q, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] using hvQ
    rcases hv with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact (hx hvP).elim
    · exact Or.inl rfl
  have hlen : 3 ≤ P.length + Q.length := by
    have hp : 0 < P.length := Nat.pos_of_ne_zero fun h ↦ hAB (Walk.eq_of_length_eq_zero h)
    simp only [Q, Walk.length_cons, Walk.length_nil]
    omega
  have hc := isCycle_append_of_support_intersection hP hQ hinter hlen
  have heq : (P.concat hBx).concat hAx.symm = P.append Q := by
    rw [Walk.concat_eq_append, Walk.concat_eq_append, ← Walk.append_assoc]
    rfl
  exact heq ▸ hc

/-- The two appended attachment edges increase the length by exactly two. -/
theorem shared_attachment_cycle_length {V : Type*} {G : SimpleGraph V}
    {A B x : V} (P : G.Walk A B) (hAx : G.Adj A x) (hBx : G.Adj B x) :
    ((P.concat hBx).concat hAx.symm).length = P.length + 2 := by
  simp only [Walk.length_concat]

/-- The explicit attachment cycle uses the original path support and
one additional vertex. The repeated initial endpoint adds no new vertex. -/
theorem mem_support_shared_attachment_cycle {V : Type*} {G : SimpleGraph V}
    {A B x v : V} (P : G.Walk A B) (hAx : G.Adj A x) (hBx : G.Adj B x) :
    v ∈ ((P.concat hBx).concat hAx.symm).support ↔ v ∈ P.support ∨ v = x := by
  simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact Or.inl P.start_mem_support
  · intro h
    exact Or.inl h

/-- All original path positions are unchanged by appending the two
attachment edges, including the old final position. -/
theorem shared_attachment_cycle_getVert {V : Type*} {G : SimpleGraph V}
    {A B x : V} (P : G.Walk A B) (hAx : G.Adj A x) (hBx : G.Adj B x)
    {i : ℕ} (hi : i ≤ P.length) :
    ((P.concat hBx).concat hAx.symm).getVert i = P.getVert i := by
  rw [Walk.concat_eq_append, Walk.getVert_append', ite_eq_left (by simp only [Walk.length_concat]; omega)]
  rw [Walk.concat_eq_append, Walk.getVert_append', ite_eq_left hi]

/-- The new attachment vertex occupies the position after the final
vertex of the original path. -/
theorem shared_attachment_cycle_getVert_attachment {V : Type*} {G : SimpleGraph V}
    {A B x : V} (P : G.Walk A B) (hAx : G.Adj A x) (hBx : G.Adj B x) :
    ((P.concat hBx).concat hAx.symm).getVert (P.length + 1) = x := by
  rw [Walk.concat_eq_append, Walk.getVert_append', ite_eq_left (by simp only [Walk.length_concat]; omega)]
  simpa only [Walk.length_concat] using (P.concat hBx).getVert_length

/-- Every original proper initial chord is still a proper chord of the
explicit cycle after the two attachment edges are appended. -/
theorem shared_attachment_cycle_chord {V : Type*} {G : SimpleGraph V}
    {A B x : V} (P : G.Walk A B) (hAx : G.Adj A x) (hBx : G.Adj B x)
    {i : ℕ} (hi : 2 ≤ i) (hiL : i ≤ P.length) (hAi : G.Adj A (P.getVert i)) :
    2 ≤ i ∧ i + 2 ≤ ((P.concat hBx).concat hAx.symm).length ∧
      G.Adj A (((P.concat hBx).concat hAx.symm).getVert i) := by
  refine ⟨hi, ?_, ?_⟩
  · rw [shared_attachment_cycle_length P hAx hBx]
    omega
  · rw [shared_attachment_cycle_getVert P hAx hBx hiL]
    exact hAi

end JSP000078

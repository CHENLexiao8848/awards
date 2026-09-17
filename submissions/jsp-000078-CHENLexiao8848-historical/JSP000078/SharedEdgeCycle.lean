import JSP000078.PathGluing

/-! # Closing a simple outside path by the endpoint edge -/

namespace JSP000078

open SimpleGraph

/-- An endpoint edge closes a simple path of at least two edges to a
simple cycle one edge longer, with unchanged support. -/
theorem exists_cycle_of_path_endpoint_edge {V : Type*} {G : SimpleGraph V}
    {a b : V} {P : G.Walk a b} (hP : P.IsPath) (hL : 2 ≤ P.length)
    (hab : G.Adj a b) :
    ∃ C : G.Walk a a, C.IsCycle ∧ C.length = P.length + 1 ∧ C.support ⊆ P.support := by
  let Q := hab.toWalk
  have hQ : Q.IsPath := hab.isPath_toWalk
  have hinter : ∀ v ∈ P.support, v ∈ Q.support → v = a ∨ v = b := by
    intro v _ hv
    simpa only [Q, Adj.support_toWalk, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hv
  let C := P.append Q.reverse
  have hC : C.IsCycle := isCycle_append_reverse_of_support_intersection hP hQ hinter (by
    simpa only [Q, Adj.length_toWalk] using Nat.add_le_add_right hL 1)
  refine ⟨C, hC, by simp [C, Q], ?_⟩
  intro v hv
  rcases (Walk.mem_support_append_iff P Q.reverse).mp hv with hp | hq
  · exact hp
  · have hvab : v = a ∨ v = b := by
      simpa only [Walk.support_reverse, List.mem_reverse, Q, Adj.support_toWalk,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hq
    rcases hvab with rfl | rfl
    · exact P.start_mem_support
    · exact P.end_mem_support

end JSP000078

import JSP000078.PathGluing

/-!
# Neighbors and arcs on a simple cycle

Rotating a cycle allows an arbitrary vertex on its support to serve as the
initial vertex.  This supplies neighboring cycle vertices and the two arcs
between any distinct pair of cycle vertices.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c a b : V}

/-- Every vertex on a simple cycle has a distinct neighboring vertex on the cycle. -/
theorem exists_adjacent_vertex_on_cycle
    (C : G.Walk c c) (hC : C.IsCycle) (ha : a ∈ C.support) :
    ∃ a₂ ∈ C.support, G.Adj a₂ a ∧ a₂ ≠ a := by
  classical
  let R := C.rotate a ha
  have hR : R.IsCycle := hC.rotate ha
  have hAdj : G.Adj R.snd a := (R.adj_snd hR.not_nil).symm
  refine ⟨R.snd, ?_, hAdj, hAdj.ne⟩
  exact (C.mem_support_rotate_iff a ha).mp (R.getVert_mem_support 1)

/-- Two distinct cycle vertices split a rotated cycle into complementary
simple arcs.  Their only common vertices are their two endpoints. -/
theorem exists_cycle_arcs_eq_rotate [DecidableEq V]
    (C : G.Walk c c) (hC : C.IsCycle)
    (ha : a ∈ C.support) (hb : b ∈ C.support) (hab : a ≠ b) :
    ∃ (p : G.Walk a b) (q : G.Walk b a),
      p.IsPath ∧ q.IsPath ∧ p.append q = C.rotate a ha ∧
      p.length + q.length = C.length ∧
      p.support ⊆ C.support ∧ q.support ⊆ C.support ∧
      (∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b) := by
  let R := C.rotate a ha
  have hR : R.IsCycle := hC.rotate ha
  have hbR : b ∈ R.support := (C.mem_support_rotate_iff a ha).mpr hb
  let p := R.takeUntil b hbR
  let q := R.dropUntil b hbR
  have hpq : p.append q = R := R.take_spec hbR
  have hcycle : (p.append q).IsCycle := hpq.symm ▸ hR
  have hp : p.IsPath := hR.isPath_takeUntil hbR
  have hq : q.IsPath := hcycle.isPath_of_append_right (Walk.not_nil_of_ne hab)
  refine ⟨p, q, hp, hq, hpq, ?_, ?_, ?_,
    support_intersection_of_isCycle_append hcycle⟩
  · have hl := congrArg Walk.length hpq
    simpa only [Walk.length_append, R, Walk.length_rotate] using hl
  · intro x hx
    exact (C.mem_support_rotate_iff a ha).mp (R.support_takeUntil_subset_support hbR hx)
  · intro x hx
    exact (C.mem_support_rotate_iff a ha).mp (R.support_dropUntil_subset_support hbR hx)

/-- Any two distinct vertices on a simple cycle determine two internally
disjoint simple paths directed from the first vertex to the second. -/
theorem exists_cycle_arcs
    {C : G.Walk c c} (hC : C.IsCycle)
    (ha : a ∈ C.support) (hb : b ∈ C.support) (hab : a ≠ b) :
    ∃ p q : G.Walk a b, p.IsPath ∧ q.IsPath ∧
      (∀ x ∈ p.support, x ∈ C.support) ∧
      (∀ x ∈ q.support, x ∈ C.support) ∧
      (∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b) ∧
      p.length + q.length = C.length := by
  classical
  obtain ⟨p, q, hp, hq, _, hlen, hpC, hqC, hinter⟩ :=
    exists_cycle_arcs_eq_rotate C hC ha hb hab
  refine ⟨p, q.reverse, hp, hq.reverse, fun _ hx ↦ hpC hx, ?_, ?_, ?_⟩
  · intro x hx
    exact hqC (by simpa only [Walk.support_reverse, List.mem_reverse] using hx)
  · intro x hxp hxq
    exact hinter x hxp (by simpa only [Walk.support_reverse, List.mem_reverse] using hxq)
  · simpa only [Walk.length_reverse] using hlen

end JSP000078

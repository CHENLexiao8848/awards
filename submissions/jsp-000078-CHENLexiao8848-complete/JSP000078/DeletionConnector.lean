import JSP000078.CycleLinking
import JSP000078.PathTrimming

/-!
# Clean connectors after deleting a shared cycle vertex

Deleting the possible shared vertex leaves a vertex on each cycle. A path
between them can be trimmed so that it meets each original cycle only at
the corresponding endpoint.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Two cycles can be joined away from any deleted vertex, with exactly
one contact on each cycle. This conclusion itself needs no intersection
assumption on the cycle supports. -/
theorem exists_clean_cycle_connector_avoiding_vertex
    (hG : TwoVertexConnected G) {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : C.IsCycle) (hD : D.IsCycle) (x : V) :
    ∃ (u v : V) (q : G.Walk u v),
      q.IsPath ∧ u ∈ C.support ∧ u ≠ x ∧ v ∈ D.support ∧ v ≠ x ∧
      x ∉ q.support ∧
      (∀ w ∈ q.support, w ∈ C.support → w = u) ∧
      (∀ w ∈ q.support, w ∈ D.support → w = v) := by
  obtain ⟨u₀, hu₀, hu₀ne⟩ := exists_mem_cycle_support_ne hC x
  obtain ⟨v₀, hv₀, hv₀ne⟩ := exists_mem_cycle_support_ne hD x
  obtain ⟨p, hp, havoid⟩ := exists_path_avoiding_vertex hG x u₀ v₀ hu₀ne hv₀ne
  let A : Set V := {w | w ∈ C.support ∧ w ≠ x}
  let B : Set V := {w | w ∈ D.support ∧ w ≠ x}
  obtain ⟨u, v, q, hq, hu, hv, hsub, hqA, hqB⟩ :=
    exists_trimmed_path_between_sets (A := A) (B := B) p hp ⟨hu₀, hu₀ne⟩ ⟨hv₀, hv₀ne⟩
  have hqAvoid : x ∉ q.support := fun hx ↦ havoid (hsub hx)
  refine ⟨u, v, q, hq, hu.1, hu.2, hv.1, hv.2, hqAvoid, ?_, ?_⟩
  · intro w hw hwC
    exact hqA w hw ⟨hwC, fun heq ↦ hqAvoid (heq ▸ hw)⟩
  · intro w hw hwD
    exact hqB w hw ⟨hwD, fun heq ↦ hqAvoid (heq ▸ hw)⟩

/-- When the two cycle supports meet only at the deleted vertex, the
clean connector has distinct endpoints and is consequently nonempty. -/
theorem exists_clean_connector_between_cycles_sharing_vertex
    (hG : TwoVertexConnected G) {x d : V} {C : G.Walk x x} {D : G.Walk d d}
    (hC : C.IsCycle) (hD : D.IsCycle)
    (hinter : ∀ w ∈ C.support, w ∈ D.support → w = x) :
    ∃ (u v : V) (q : G.Walk u v),
      q.IsPath ∧ u ∈ C.support ∧ u ≠ x ∧ v ∈ D.support ∧ v ≠ x ∧
      u ≠ v ∧ x ∉ q.support ∧
      (∀ w ∈ q.support, w ∈ C.support → w = u) ∧
      (∀ w ∈ q.support, w ∈ D.support → w = v) := by
  obtain ⟨u, v, q, hq, huC, hux, hvD, hvx, havoid, hqC, hqD⟩ :=
    exists_clean_cycle_connector_avoiding_vertex hG hC hD x
  refine ⟨u, v, q, hq, huC, hux, hvD, hvx, ?_, havoid, hqC, hqD⟩
  intro huv
  exact hux (hinter u huC (huv.symm ▸ hvD))

end JSP000078

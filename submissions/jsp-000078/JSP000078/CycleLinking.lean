import JSP000078.HistoricalSpec
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Connectivity facts used by the historical two-link argument

Single-vertex deletion cannot separate the supports of two simple cycles.
The simultaneous two-link conclusion will require a path rerouting argument.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A simple cycle contains a vertex different from any specified vertex. -/
theorem exists_mem_cycle_support_ne {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (z : V) : ∃ a ∈ C.support, a ≠ z := by
  by_cases hcz : c = z
  · refine ⟨C.snd, C.getVert_mem_support 1, ?_⟩
    have h := (C.adj_snd hC.not_nil).ne.symm
    simpa [hcz] using h
  · exact ⟨c, C.start_mem_support, hcz⟩

/-- Single-vertex deletion connectivity supplies a path with support avoiding that vertex. -/
theorem exists_path_avoiding_vertex [Fintype V]
    (hG : TwoVertexConnected G) (z a b : V) (ha : a ≠ z) (hb : b ≠ z) :
    ∃ p : G.Walk a b, p.IsPath ∧ z ∉ p.support := by
  classical
  let a' : ↑(({z} : Set V)ᶜ) := ⟨a, by simpa using ha⟩
  let b' : ↑(({z} : Set V)ᶜ) := ⟨b, by simpa using hb⟩
  obtain ⟨q, hq⟩ := exists_path_in_vertex_deletion hG z a' b'
  let e : G.induce ({z} : Set V)ᶜ ↪g G := SimpleGraph.Embedding.induce _
  have havoid : z ∉ (q.map e.toHom).support := by
    intro hz
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨v, _, hv⟩ := hz
    have hvz : (v : V) ≠ z := by
      exact v.property
    exact hvz hv
  exact ⟨q.map e.toHom, hq.map e.injective, havoid⟩

/-- No single vertex separates the vertex sets of two simple cycles. -/
theorem exists_cycle_link_avoiding_vertex [Fintype V]
    (hG : TwoVertexConnected G) {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : C.IsCycle) (hD : D.IsCycle) (z : V) :
    ∃ (a b : V) (p : G.Walk a b),
      a ∈ C.support ∧ b ∈ D.support ∧ p.IsPath ∧ z ∉ p.support := by
  obtain ⟨a, ha, haz⟩ := exists_mem_cycle_support_ne hC z
  obtain ⟨b, hb, hbz⟩ := exists_mem_cycle_support_ne hD z
  obtain ⟨p, hp, hz⟩ := exists_path_avoiding_vertex hG z a b haz hbz
  exact ⟨a, b, p, ha, hb, hp, hz⟩

end JSP000078

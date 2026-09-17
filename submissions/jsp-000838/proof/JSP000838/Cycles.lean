import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import JSP000838.Gluing

namespace JSP000838

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Every simple cycle has at least `s` edges; forests satisfy this for every `s`. -/
def NoShortCycles (s : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ v (w : G.Walk v v), w.IsCycle → s ≤ w.length

theorem noShortCycles_iff_le_egirth (s : ℕ) :
    NoShortCycles s G ↔ (s : ℕ∞) ≤ G.egirth := by
  rw [SimpleGraph.le_egirth]
  simp only [NoShortCycles, ENat.natCast_le_natCast]

theorem NoShortCycles.mono {s t : ℕ} (h : NoShortCycles s G) (ht : t ≤ s) :
    NoShortCycles t G := fun v w hw => ht.trans (h v w hw)

theorem NoShortCycles.not_cycle_length {s k : ℕ} (h : NoShortCycles s G)
    (hk : k < s) {v : V} {w : G.Walk v v} (hw : w.IsCycle) : w.length ≠ k := by
  intro heq
  have hle := h v w hw
  omega

theorem NoShortCycles.no_triangle (h : NoShortCycles 5 G)
    {v : V} {w : G.Walk v v} (hw : w.IsCycle) : w.length ≠ 3 :=
  h.not_cycle_length (by decide) hw

theorem NoShortCycles.no_four_cycle (h : NoShortCycles 5 G)
    {v : V} {w : G.Walk v v} (hw : w.IsCycle) : w.length ≠ 4 :=
  h.not_cycle_length (by decide) hw

/-- The excluded cycles are arbitrary subgraph copies, not merely induced copies. -/
theorem NoShortCycles.not_contains_cycleGraph {s k : ℕ} (h : NoShortCycles s G)
    (hk : 2 < k) (hks : k < s) : ¬ SimpleGraph.cycleGraph k ⊑ G := by
  intro hc
  obtain ⟨v, w, hw, hlen⟩ := (SimpleGraph.cycleGraph_isContained_iff hk).mp hc
  exact h.not_cycle_length hks hw hlen

theorem NoShortCycles.no_C3_copy (h : NoShortCycles 5 G) :
    ¬ SimpleGraph.cycleGraph 3 ⊑ G :=
  h.not_contains_cycleGraph (by decide) (by decide)

theorem NoShortCycles.no_C4_copy (h : NoShortCycles 5 G) :
    ¬ SimpleGraph.cycleGraph 4 ⊑ G :=
  h.not_contains_cycleGraph (by decide) (by decide)

/-- Adjacency-level exclusion of triangles and quadrilaterals is the genuine
simple-cycle condition at threshold five. -/
theorem noShortCycles_of_triangleFree_fourCycleFree
    (h3 : Gluing.TriangleFree G) (h4 : Gluing.FourCycleFree G) : NoShortCycles 5 G := by
  intro v w hw
  have hlen := hw.three_le_length
  by_contra h
  have hshort : w.length = 3 ∨ w.length = 4 := by omega
  rcases hshort with hlen | hlen
  · have h01 := w.adj_getVert_succ (i := 0) (by omega)
    have h12 := w.adj_getVert_succ (i := 1) (by omega)
    have h20 : G.Adj (w.getVert 2) (w.getVert 0) := by
      simpa [← hlen] using w.adj_getVert_succ (i := 2) (by omega)
    exact h3 _ _ _ h01 h12 h20
  · have h01 := w.adj_getVert_succ (i := 0) (by omega)
    have h12 := w.adj_getVert_succ (i := 1) (by omega)
    have h23 := w.adj_getVert_succ (i := 2) (by omega)
    have h30 : G.Adj (w.getVert 3) (w.getVert 0) := by
      simpa [← hlen] using w.adj_getVert_succ (i := 3) (by omega)
    have h02 : w.getVert 0 ≠ w.getVert 2 := by
      intro heq
      have := hw.getVert_injOn' (by simp) (by simp; omega) heq
      omega
    have h13 : w.getVert 1 ≠ w.getVert 3 := by
      intro heq
      have := hw.getVert_injOn' (by simp; omega) (by simp; omega) heq
      omega
    exact h4 _ _ _ _ h02 h13 h01 h12 h23 h30

end JSP000838

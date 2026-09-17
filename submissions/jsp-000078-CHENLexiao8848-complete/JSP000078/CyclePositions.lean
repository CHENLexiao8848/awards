import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Canonical positions of vertices on a cycle

The first occurrence in the support gives an index strictly before the
repeated final endpoint. Only membership in the cycle is needed; the
cycle need not span the ambient graph.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The first support position of a vertex, using classical equality. -/
noncomputable def cyclePosition {c : V} (C : G.Walk c c) (v : V) : ℕ := by
  classical
  exact C.support.idxOf v

theorem getVert_cyclePosition {c v : V} (C : G.Walk c c) (hv : v ∈ C.support) :
    C.getVert (cyclePosition C v) = v := by
  classical
  exact C.getVert_support_idxOf hv

theorem cyclePosition_base {c : V} (C : G.Walk c c) : cyclePosition C c = 0 := by
  classical
  unfold cyclePosition
  rw [← Walk.cons_tail_support C, List.idxOf_cons_self]

/-- On a cycle the first occurrence precedes the repeated final base. -/
theorem cyclePosition_lt {c v : V} {C : G.Walk c c} (hC : C.IsCycle)
    (hv : v ∈ C.support) : cyclePosition C v < C.length := by
  classical
  by_cases hvc : v = c
  · subst v
    rw [cyclePosition_base]
    have := hC.three_le_length
    omega
  · simpa only [Walk.length_takeUntil, cyclePosition] using
      C.length_takeUntil_lt_length hv hvc

/-- Indexing and taking the vertex at an index are inverse before the
repeated terminal cycle vertex. -/
theorem cyclePosition_getVert {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    {i : ℕ} (hi : i < C.length) : cyclePosition C (C.getVert i) = i := by
  apply hC.getVert_injOn'
  · have h := cyclePosition_lt hC (C.getVert_mem_support i)
    change cyclePosition C (C.getVert i) ≤ C.length - 1
    omega
  · change i ≤ C.length - 1
    omega
  · exact getVert_cyclePosition C (C.getVert_mem_support i)

/-- Distinct vertices in the cycle support have distinct positions. -/
theorem cyclePosition_injOn {c : V} (C : G.Walk c c) :
    Set.InjOn (cyclePosition C) {v | v ∈ C.support} := by
  intro u hu v hv hpos
  exact (getVert_cyclePosition C hu).symm.trans
    ((congrArg C.getVert hpos).trans (getVert_cyclePosition C hv))

theorem cyclePosition_pos_iff {c v : V} (C : G.Walk c c) (hv : v ∈ C.support) :
    0 < cyclePosition C v ↔ v ≠ c := by
  constructor
  · intro hpos hvc
    subst v
    rw [cyclePosition_base] at hpos
    omega
  · intro hvc
    apply Nat.pos_of_ne_zero
    intro hz
    have h := getVert_cyclePosition C hv
    rw [hz, Walk.getVert_zero] at h
    exact hvc h.symm

end JSP000078

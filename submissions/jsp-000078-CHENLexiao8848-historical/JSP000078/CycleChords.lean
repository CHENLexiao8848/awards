import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# The two cycles cut out by a chord

A chord from a cycle's initial vertex to an internal vertex closes either
of the two complementary arcs. Both resulting walks are simple cycles,
with the respective arc lengths plus one.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A chord at position `j`, away from the two original neighboring
vertices, gives cycles of lengths `j + 1` and `C.length - j + 1`. -/
theorem exists_cycles_of_cycle_getVert_adj {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {j : ℕ} (hj2 : 2 ≤ j) (hjend : j + 2 ≤ C.length)
    (ha : G.Adj c (C.getVert j)) :
    ∃ E F : G.Walk c c, E.IsCycle ∧ F.IsCycle ∧
      E.length = j + 1 ∧ F.length = C.length - j + 1 := by
  let E : G.Walk c c := .cons ha (C.take j).reverse
  let F : G.Walk c c := .cons ha (C.drop j)
  have hlenE : E.length = j + 1 := by
    simp [E, Nat.min_eq_left (show j ≤ C.length by omega)]
  have hlenF : F.length = C.length - j + 1 := by simp [F]
  have hE : E.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, by omega⟩
    simpa [E] using (hC.isPath_take (show j < C.length by omega)).reverse
  have hF : F.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, by omega⟩
    simpa [F] using hC.isPath_drop (show 0 < j by omega)
  exact ⟨E, F, hE, hF, hlenE, hlenF⟩

end JSP000078

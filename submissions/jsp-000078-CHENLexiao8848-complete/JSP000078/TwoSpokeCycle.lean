import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Cycles obtained from two spokes and an arc

A simple path avoiding a vertex becomes a cycle when both endpoints are
joined to that vertex. Applied to an internal arc of a cycle, this gives
the two-spoke lengths needed for the cycle-and-chords argument.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A nonempty simple path avoiding `c`, together with spokes from `c` to
both endpoints, gives a simple cycle two edges longer than the path. -/
theorem exists_cycle_of_path_two_spokes {a b c : V} {q : G.Walk a b}
    (hq : q.IsPath) (hc : c ∉ q.support) (ha : G.Adj c a) (hb : G.Adj c b)
    (hpos : 0 < q.length) :
    ∃ E : G.Walk c c, E.IsCycle ∧ E.length = q.length + 2 := by
  let E : G.Walk c c := .cons ha (q.concat hb.symm)
  have hlen : E.length = q.length + 2 := by simp [E, Nat.add_assoc]
  refine ⟨E, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by omega⟩, hlen⟩
  simpa [E] using hq.concat hc hb.symm

/-- Two spokes from the initial vertex of a simple cycle to positions
`i < j` enclose a cycle of length `j - i + 2`. Neither position is the
initial vertex or its repeated occurrence at the end. -/
theorem exists_cycle_of_cycle_two_spokes {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j < C.length)
    (hai : G.Adj c (C.getVert i)) (haj : G.Adj c (C.getVert j)) :
    ∃ E : G.Walk c c, E.IsCycle ∧ E.length = j - i + 2 := by
  let R := (C.drop i).take (j - i)
  have hRlen : R.length = j - i := by
    simp only [R, Walk.take_length, Walk.drop_length]
    exact Nat.min_eq_left (by omega)
  have hend : (C.drop i).getVert (j - i) = C.getVert j := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le (Nat.le_of_lt hij)]
  let q : G.Walk (C.getVert i) (C.getVert j) := R.copy rfl hend
  have hqlen : q.length = j - i := by simpa only [q, Walk.length_copy] using hRlen
  have hq : q.IsPath := by
    simpa only [q, Walk.isPath_copy] using (hC.isPath_drop (by omega : 0 < i)).take (j - i)
  have hc : c ∉ q.support := by
    intro hcmem
    have hcR : c ∈ R.support := by simpa only [q, Walk.support_copy] using hcmem
    obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp hcR
    have hnle : n ≤ j - i := by omega
    have hget : C.getVert (i + n) = c := by
      simpa only [R, Walk.take_getVert, Nat.min_eq_right hnle, Walk.drop_getVert] using hn
    have hends := (hC.getVert_endpoint_iff (by omega : i + n ≤ C.length)).mp hget
    omega
  obtain ⟨E, hE, hlen⟩ := exists_cycle_of_path_two_spokes hq hc hai haj (by omega)
  exact ⟨E, hE, by omega⟩

end JSP000078

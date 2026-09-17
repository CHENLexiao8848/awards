import JSP000078.TwoSpokeCycle

/-!
# Spokes from the initial vertex of a simple path

Two incident edges and the intervening path segment give a cycle. A single
incident edge followed by the remaining suffix gives a shorter simple path
between the original endpoints. These are the path-side constructions in
Gyárfás's Lemma 4.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A noninitial suffix of a simple path avoids the original initial
vertex, including the suffix consisting only of the final vertex. -/
theorem path_start_notMem_support_drop {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {i : ℕ} (hi : 1 ≤ i) (hile : i ≤ p.length) :
    a ∉ (p.drop i).support := by
  intro ha
  obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  have hnle : n ≤ p.length - i := by
    simpa only [Walk.drop_length] using hnlen
  have hget : p.getVert (i + n) = p.getVert 0 := by
    simpa only [Walk.drop_getVert, Walk.getVert_zero] using hn
  have hzero : i + n = 0 := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) hget
  omega

/-- Two spokes from the initial vertex of a simple path to positions
`1 ≤ i < j ≤ length` give a simple cycle of length `j - i + 2`. -/
theorem exists_cycle_of_path_start_two_spokes {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ p.length)
    (hai : G.Adj a (p.getVert i)) (haj : G.Adj a (p.getVert j)) :
    ∃ E : G.Walk a a, E.IsCycle ∧ E.length = j - i + 2 := by
  let R := (p.drop i).take (j - i)
  have hRlen : R.length = j - i := by
    simp only [R, Walk.take_length, Walk.drop_length]
    exact Nat.min_eq_left (by omega)
  have hend : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le hij.le]
  let q : G.Walk (p.getVert i) (p.getVert j) := R.copy rfl hend
  have hqlen : q.length = j - i := by simpa only [q, Walk.length_copy] using hRlen
  have hq : q.IsPath := by
    simpa only [q, Walk.isPath_copy] using (hp.drop i).take (j - i)
  have ha : a ∉ q.support := by
    intro hamem
    have haR : a ∈ R.support := by simpa only [q, Walk.support_copy] using hamem
    obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp haR
    have hnle : n ≤ j - i := by omega
    have hget : (p.drop i).getVert n = a := by
      simpa only [R, Walk.take_getVert, Nat.min_eq_right hnle] using hn
    have hmem : a ∈ (p.drop i).support :=
      Walk.mem_support_iff_exists_getVert.mpr ⟨n, hget, by
        simp only [Walk.drop_length]
        omega⟩
    exact path_start_notMem_support_drop hp hi (by omega) hmem
  obtain ⟨E, hE, hlen⟩ := exists_cycle_of_path_two_spokes hq ha hai haj (by omega)
  exact ⟨E, hE, by omega⟩

/-- Following a spoke from the start to a later vertex and then the path
suffix gives a simple path of length `length - i + 1`. -/
theorem exists_path_of_path_start_spoke {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {i : ℕ} (hi : 1 ≤ i) (hile : i ≤ p.length)
    (hai : G.Adj a (p.getVert i)) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length - i + 1 := by
  refine ⟨Walk.cons hai (p.drop i), ?_, ?_⟩
  · exact (hp.drop i).cons (path_start_notMem_support_drop hp hi hile)
  · simp only [Walk.length_cons, Walk.drop_length]

/-- The shortcut path through a start spoke uses only vertices of the
original path. This retains disjointness from any external cycle. -/
theorem exists_path_of_path_start_spoke_support_subset {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {i : ℕ} (hi : 1 ≤ i) (hile : i ≤ p.length)
    (hai : G.Adj a (p.getVert i)) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length - i + 1 ∧
      q.support ⊆ p.support := by
  refine ⟨Walk.cons hai (p.drop i), ?_, ?_, ?_⟩
  · exact (hp.drop i).cons (path_start_notMem_support_drop hp hi hile)
  · simp only [Walk.length_cons, Walk.drop_length]
  · intro v hv
    simp only [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact p.start_mem_support
    · obtain ⟨n, hn, _⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      rw [Walk.drop_getVert] at hn
      rw [← hn]
      exact p.getVert_mem_support (i + n)

end JSP000078

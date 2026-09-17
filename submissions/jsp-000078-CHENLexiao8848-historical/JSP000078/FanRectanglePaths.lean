import JSP000078.CycleSegments
import JSP000078.PathGluing

/-!
# The three rectangle path families in an incident-chord cycle

Two disjoint rim intervals can be joined through the common spoke vertex.
The three possible placements relative to the requested endpoints give
the length rectangles used in Gyárfás's Lemma 3.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Join disjoint paths through a new vertex adjacent to the end of the
first and start of the second. Zero-length paths are allowed. -/
theorem isPath_join_through_vertex {x a b y c : V}
    {P : G.Walk x a} {Q : G.Walk b y} (hP : P.IsPath) (hQ : Q.IsPath)
    (hPQ : Disjoint {v | v ∈ P.support} {v | v ∈ Q.support})
    (hcP : c ∉ P.support) (hcQ : c ∉ Q.support)
    (ha : G.Adj c a) (hb : G.Adj c b) :
    ((P.concat ha.symm).append (.cons hb Q)).IsPath := by
  apply isPath_append_of_support_intersection (hP.concat hcP ha.symm) (hQ.cons hcQ)
  intro v hvP hvQ
  have hvP' : v ∈ P.support ∨ v = c := by simpa using hvP
  have hvQ' : v = c ∨ v ∈ Q.support := by simpa using hvQ
  rcases hvP' with hvP' | hvc
  · rcases hvQ' with hvc | hvQ'
    · exact hvc
    · exact (Set.disjoint_left.mp hPQ hvP' hvQ').elim
  · exact hvc

/-- Existential form of joining two disjoint paths through a vertex, with
the exact sum of both rim lengths and the two spoke edges. -/
theorem exists_path_join_through_vertex {x a b y c : V}
    {P : G.Walk x a} {Q : G.Walk b y} (hP : P.IsPath) (hQ : Q.IsPath)
    (hPQ : Disjoint {v | v ∈ P.support} {v | v ∈ Q.support})
    (hcP : c ∉ P.support) (hcQ : c ∉ Q.support)
    (ha : G.Adj c a) (hb : G.Adj c b) :
    ∃ W : G.Walk x y, W.IsPath ∧ W.length = P.length + Q.length + 2 := by
  refine ⟨(P.concat ha.symm).append (.cons hb Q),
    isPath_join_through_vertex hP hQ hPQ hcP hcQ ha hb, ?_⟩
  simp only [Walk.length_append, Walk.length_concat, Walk.length_cons]
  omega

/-- An internal cycle interval does not contain the base vertex. -/
theorem base_notMem_support_of_cycle_interval {c a b : V} {C : G.Walk c c}
    (hC : C.IsCycle) {P : G.Walk a b} {i j : ℕ} (hi : 1 ≤ i) (hj : j < C.length)
    (hP : ∀ v ∈ P.support, ∃ n : ℕ, i ≤ n ∧ n ≤ j ∧ C.getVert n = v) :
    c ∉ P.support := by
  intro hc
  obtain ⟨n, hin, hnj, hn⟩ := hP c hc
  have hend := (hC.getVert_endpoint_iff (by omega : n ≤ C.length)).mp hn
  omega

/-- The left-right rectangle: descend from `r` to `i`, cross the base,
then descend from `j` to `s`. -/
theorem exists_fan_path_LR {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    {i r s j : ℕ} (hi : 1 ≤ i) (hir : i ≤ r) (hrs : r < s)
    (hsj : s ≤ j) (hj : j < C.length)
    (hai : G.Adj c (C.getVert i)) (haj : G.Adj c (C.getVert j)) :
    ∃ W : G.Walk (C.getVert r) (C.getVert s),
      W.IsPath ∧ W.length = (r - i) + (j - s) + 2 := by
  obtain ⟨P, hP, hPlen, hPmem⟩ := exists_cycle_segment hC hir (by omega : r < C.length)
  obtain ⟨Q, hQ, hQlen, hQmem⟩ := exists_cycle_segment hC hsj hj
  have hPsup : ∀ v ∈ P.reverse.support,
      ∃ n : ℕ, i ≤ n ∧ n ≤ r ∧ C.getVert n = v := by
    intro v hv
    exact (hPmem v).mp (by simpa using hv)
  have hQsup : ∀ v ∈ Q.reverse.support,
      ∃ n : ℕ, s ≤ n ∧ n ≤ j ∧ C.getVert n = v := by
    intro v hv
    exact (hQmem v).mp (by simpa using hv)
  have hdis := disjoint_support_of_separated_cycle_intervals hC hrs hj hPsup hQsup
  have hcP := base_notMem_support_of_cycle_interval hC hi (by omega : r < C.length) hPsup
  have hcQ := base_notMem_support_of_cycle_interval hC (by omega : 1 ≤ s) hj hQsup
  obtain ⟨W, hW, hWlen⟩ := exists_path_join_through_vertex hP.reverse hQ.reverse hdis hcP hcQ hai haj
  exact ⟨W, hW, by simpa only [Walk.length_reverse, hPlen, hQlen] using hWlen⟩

/-- The left-middle rectangle: descend from `r` to `i`, cross the base,
then ascend from `j` to `s`. -/
theorem exists_fan_path_LM {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    {i r j s : ℕ} (hi : 1 ≤ i) (hir : i ≤ r) (hrj : r < j)
    (hjs : j < s) (hs : s < C.length)
    (hai : G.Adj c (C.getVert i)) (haj : G.Adj c (C.getVert j)) :
    ∃ W : G.Walk (C.getVert r) (C.getVert s),
      W.IsPath ∧ W.length = (r - i) + (s - j) + 2 := by
  obtain ⟨P, hP, hPlen, hPmem⟩ := exists_cycle_segment hC hir (by omega : r < C.length)
  obtain ⟨Q, hQ, hQlen, hQmem⟩ := exists_cycle_segment hC hjs.le hs
  have hPsup : ∀ v ∈ P.reverse.support,
      ∃ n : ℕ, i ≤ n ∧ n ≤ r ∧ C.getVert n = v := by
    intro v hv
    exact (hPmem v).mp (by simpa using hv)
  have hQsup : ∀ v ∈ Q.support,
      ∃ n : ℕ, j ≤ n ∧ n ≤ s ∧ C.getVert n = v := fun v hv ↦ (hQmem v).mp hv
  have hdis := disjoint_support_of_separated_cycle_intervals hC hrj hs hPsup hQsup
  have hcP := base_notMem_support_of_cycle_interval hC hi (by omega : r < C.length) hPsup
  have hcQ := base_notMem_support_of_cycle_interval hC (by omega : 1 ≤ j) hs hQsup
  obtain ⟨W, hW, hWlen⟩ := exists_path_join_through_vertex hP.reverse hQ hdis hcP hcQ hai haj
  exact ⟨W, hW, by simpa only [Walk.length_reverse, hPlen, hQlen] using hWlen⟩

/-- The middle-right rectangle: ascend from `r` to `i`, cross the base,
then descend from `j` to `s`. -/
theorem exists_fan_path_MR {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    {r i s j : ℕ} (hr : 1 ≤ r) (hri : r < i) (his : i < s)
    (hsj : s ≤ j) (hj : j < C.length)
    (hai : G.Adj c (C.getVert i)) (haj : G.Adj c (C.getVert j)) :
    ∃ W : G.Walk (C.getVert r) (C.getVert s),
      W.IsPath ∧ W.length = (i - r) + (j - s) + 2 := by
  obtain ⟨P, hP, hPlen, hPmem⟩ := exists_cycle_segment hC hri.le (by omega : i < C.length)
  obtain ⟨Q, hQ, hQlen, hQmem⟩ := exists_cycle_segment hC hsj hj
  have hPsup : ∀ v ∈ P.support,
      ∃ n : ℕ, r ≤ n ∧ n ≤ i ∧ C.getVert n = v := fun v hv ↦ (hPmem v).mp hv
  have hQsup : ∀ v ∈ Q.reverse.support,
      ∃ n : ℕ, s ≤ n ∧ n ≤ j ∧ C.getVert n = v := by
    intro v hv
    exact (hQmem v).mp (by simpa using hv)
  have hdis := disjoint_support_of_separated_cycle_intervals hC his hj hPsup hQsup
  have hcP := base_notMem_support_of_cycle_interval hC hr (by omega : i < C.length) hPsup
  have hcQ := base_notMem_support_of_cycle_interval hC (by omega : 1 ≤ s) hj hQsup
  obtain ⟨W, hW, hWlen⟩ := exists_path_join_through_vertex hP hQ.reverse hdis hcP hcQ hai haj
  exact ⟨W, hW, by simpa only [Walk.length_reverse, hPlen, hQlen] using hWlen⟩

end JSP000078

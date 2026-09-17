import JSP000078.PathSpokes

/-!
# Paths using chords at both endpoints of a simple path

Interior intervals can be traversed in either direction between the two
endpoint chords. Strict interior bounds exclude repeated initial or final
vertices. The shared edge between the two endpoints is treated separately.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An indexed interval strictly inside a simple path is a simple path
avoiding both original endpoints and using only original support vertices. -/
theorem exists_internal_path_segment {A B : V} {p : G.Walk A B} (hp : p.IsPath)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j < p.length) :
    ∃ q : G.Walk (p.getVert i) (p.getVert j), q.IsPath ∧ q.length = j - i ∧
      q.support ⊆ p.support ∧ A ∉ q.support ∧ B ∉ q.support := by
  let R := (p.take j).drop i
  have hstart : (p.take j).getVert i = p.getVert i := by
    rw [Walk.take_getVert, Nat.min_eq_right hij]
  let q : G.Walk (p.getVert i) (p.getVert j) := R.copy hstart rfl
  have hlen : q.length = j - i := by
    simp only [q, Walk.length_copy, R, Walk.drop_length, Walk.take_length, Nat.min_eq_left hj.le]
  have hcoords : ∀ v ∈ q.support, ∃ n, i ≤ n ∧ n ≤ j ∧ p.getVert n = v := by
    intro v hv
    have hvR : v ∈ R.support := by simpa only [q, Walk.support_copy] using hv
    obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp hvR
    have hRlen : R.length = j - i := by simpa only [q, Walk.length_copy] using hlen
    have hnle : i + n ≤ j := by omega
    refine ⟨i + n, by omega, hnle, ?_⟩
    simpa only [R, Walk.drop_getVert, Walk.take_getVert, Nat.min_eq_right hnle] using hn
  refine ⟨q, ?_, hlen, ?_, ?_, ?_⟩
  · simpa only [q, Walk.isPath_copy] using (hp.take j).drop i
  · intro v hv
    obtain ⟨n, _, _, hn⟩ := hcoords v hv
    exact hn ▸ p.getVert_mem_support n
  · intro hA
    obtain ⟨n, hin, hnj, hn⟩ := hcoords A hA
    have hnzero : n = 0 := hp.getVert_injOn (by change n ≤ p.length; omega)
      (by change 0 ≤ p.length; omega) (by simpa only [Walk.getVert_zero] using hn)
    omega
  · intro hB
    obtain ⟨n, hin, hnj, hn⟩ := hcoords B hB
    have hnend : n = p.length := hp.getVert_injOn (by change n ≤ p.length; omega)
      (by change p.length ≤ p.length; omega) (by simpa only [Walk.getVert_length] using hn)
    omega

/-- Attach an internal simple path to two distinct external endpoints. -/
theorem exists_path_of_internal_path_and_endpoint_edges {A B x y : V}
    {q : G.Walk x y} (hq : q.IsPath) (hA : A ∉ q.support) (hB : B ∉ q.support)
    (hAB : A ≠ B) (hAx : G.Adj A x) (hBy : G.Adj B y) :
    ∃ W : G.Walk A B, W.IsPath ∧ W.length = q.length + 2 ∧
      (∀ v ∈ W.support, v = A ∨ v ∈ q.support ∨ v = B) := by
  let W := (q.concat hBy.symm).cons hAx
  refine ⟨W, ?_, ?_, ?_⟩
  · apply (hq.concat hB hBy.symm).cons
    simpa only [Walk.support_concat, List.mem_append, List.mem_singleton, not_or] using
      And.intro hA hAB
  · simp only [W, Walk.length_cons, Walk.length_concat]
  · intro v hv
    simpa only [W, Walk.support_cons, Walk.support_concat, List.mem_cons,
      List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] using hv

/-- Noncrossing endpoint chords can be joined along the increasing
internal segment. Coincident interior chord endpoints are allowed. -/
theorem exists_path_of_two_endpoint_chords_noncrossing {A B : V} {p : G.Walk A B}
    (hp : p.IsPath) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j < p.length)
    (hAi : G.Adj A (p.getVert i)) (hBj : G.Adj B (p.getVert j)) :
    ∃ W : G.Walk A B, W.IsPath ∧ W.length = j - i + 2 ∧ W.support ⊆ p.support := by
  obtain ⟨q, hq, hlen, hsub, hA, hB⟩ := exists_internal_path_segment hp hi hij hj
  have hAB : A ≠ B := by
    intro heq
    have hnil := hp.nil_iff_eq.mpr heq
    have hz := hnil.length_eq_zero
    omega
  obtain ⟨W, hW, hWlen, hWsup⟩ :=
    exists_path_of_internal_path_and_endpoint_edges hq hA hB hAB hAi hBj
  refine ⟨W, hW, by omega, ?_⟩
  intro v hv
  rcases hWsup v hv with rfl | hv | rfl
  · exact p.start_mem_support
  · exact hsub hv
  · exact p.end_mem_support

/-- Crossing endpoint chords can be joined along the reversed internal
segment. Strict interior bounds prevent revisiting either endpoint. -/
theorem exists_path_of_two_endpoint_chords_crossing {A B : V} {p : G.Walk A B}
    (hp : p.IsPath) {i j : ℕ} (hj : 1 ≤ j) (hji : j < i) (hi : i < p.length)
    (hAi : G.Adj A (p.getVert i)) (hBj : G.Adj B (p.getVert j)) :
    ∃ W : G.Walk A B, W.IsPath ∧ W.length = i - j + 2 ∧ W.support ⊆ p.support := by
  obtain ⟨q, hq, hlen, hsub, hA, hB⟩ := exists_internal_path_segment hp hj hji.le hi
  have hAB : A ≠ B := by
    intro heq
    have hnil := hp.nil_iff_eq.mpr heq
    have hz := hnil.length_eq_zero
    omega
  have hArev : A ∉ q.reverse.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hA
  have hBrev : B ∉ q.reverse.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hB
  obtain ⟨W, hW, hWlen, hWsup⟩ :=
    exists_path_of_internal_path_and_endpoint_edges hq.reverse hArev hBrev hAB hAi hBj
  refine ⟨W, hW, ?_, ?_⟩
  · simpa only [Walk.length_reverse, hlen] using hWlen
  · intro v hv
    rcases hWsup v hv with rfl | hv | rfl
    · exact p.start_mem_support
    · exact hsub (by simpa only [Walk.support_reverse, List.mem_reverse] using hv)
    · exact p.end_mem_support

/-- Following a path prefix and a chord to the final endpoint gives a
simple route of length `j + 1`, including a direct endpoint edge at `j=0`. -/
theorem exists_path_of_path_end_spoke_support_subset {A B : V} {p : G.Walk A B}
    (hp : p.IsPath) {j : ℕ} (hj : j < p.length) (hBj : G.Adj B (p.getVert j)) :
    ∃ W : G.Walk A B, W.IsPath ∧ W.length = j + 1 ∧ W.support ⊆ p.support := by
  have hrAdj : G.Adj B (p.reverse.getVert (p.length - j)) := by
    simpa only [Walk.getVert_reverse, Nat.sub_sub_self hj.le] using hBj
  obtain ⟨Q, hQ, hQlen, hQsub⟩ := exists_path_of_path_start_spoke_support_subset hp.reverse
    (show 1 ≤ p.length - j by omega)
    (by simp only [Walk.length_reverse]; omega : p.length - j ≤ p.reverse.length) hrAdj
  refine ⟨Q.reverse, hQ.reverse, ?_, ?_⟩
  · simpa only [Walk.length_reverse, Nat.sub_sub_self hj.le] using hQlen
  · intro v hv
    have hvQ : v ∈ Q.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hv
    simpa only [Walk.support_reverse, List.mem_reverse] using hQsub hvQ

/-- If the two endpoint chords are the same edge, that edge gives a
length-one route; the original simple path remains another route. -/
theorem exists_path_of_endpoint_edge {A B : V} (hAB : G.Adj A B) :
    ∃ W : G.Walk A B, W.IsPath ∧ W.length = 1 := by
  exact ⟨hAB.toWalk, hAB.isPath_toWalk, by simp⟩

end JSP000078

import JSP000078.PathGluing
import JSP000078.EndpointConfigurationBridge
import Mathlib.Data.Finset.Max

/-!
# A cycle with many incident chords at an endpoint of a path

Close the path prefix ending at the farthest selected neighbor of its
initial vertex. Every other selected neighbor except the first rim
neighbor supplies a proper chord of that cycle.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Closing a simple path prefix at an adjacent endpoint preserves all
its indexed vertices and produces one additional edge. -/
theorem exists_cycle_of_path_prefix_neighbor {A B : V} {P : G.Walk A B}
    (hP : P.IsPath) {m : ℕ} (hm : 2 ≤ m) (hmL : m ≤ P.length)
    (hAm : G.Adj A (P.getVert m)) :
    ∃ D : G.Walk A A, D.IsCycle ∧ D.length = m + 1 ∧
      D.support ⊆ P.support ∧ ∀ i ≤ m, D.getVert i = P.getVert i := by
  let R := P.take m
  let Q := hAm.toWalk
  let D := R.append Q.reverse
  have hRlen : R.length = m := by
    simp only [R, Walk.take_length, Nat.min_eq_left hmL]
  have hcycle : D.IsCycle := by
    apply isCycle_append_reverse_of_support_intersection (hP.take m) hAm.isPath_toWalk
    · intro v _ hv
      simpa only [Q, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using hv
    · change 3 ≤ R.length + Q.length
      simp only [hRlen, Q, Adj.length_toWalk]
      omega
  refine ⟨D, hcycle, ?_, ?_, ?_⟩
  · simp only [D, Walk.length_append, Walk.length_reverse, hRlen, Q, Adj.length_toWalk]
  · intro v hv
    rcases (Walk.mem_support_append_iff R Q.reverse).mp hv with hvR | hvQ
    · exact (P.isSubwalk_take m).support_subset hvR
    · have hvEnds : v = A ∨ v = P.getVert m := by
        simpa only [Walk.support_reverse, List.mem_reverse, Q, Adj.support_toWalk,
          List.mem_cons, List.not_mem_nil, or_false] using hvQ
      rcases hvEnds with rfl | rfl
      · exact P.start_mem_support
      · exact P.getVert_mem_support m
  · intro i hi
    simp only [D, Walk.getVert_append', hRlen, hi, ite_true, R,
      Walk.take_getVert, Nat.min_eq_right hi]

/-- At least `2k+1` selected endpoint neighbors on a simple path give a
cycle inside that path with at least `2k-1` proper incident chords. -/
theorem exists_cycle_with_many_chords_of_path_indices
    {A B : V} {P : G.Walk A B} (hP : P.IsPath)
    (S : Finset ℕ) (k : ℕ) (hk : 1 ≤ k) (hcard : 2 * k + 1 ≤ S.card)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ P.length ∧ G.Adj A (P.getVert i)) :
    ∃ (D : G.Walk A A) (J : Finset (Fin D.length)), D.IsCycle ∧
      D.support ⊆ P.support ∧ 2 * k - 1 ≤ J.card ∧
      (∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ D.length ∧ G.Adj A (D.getVert j.val)) := by
  classical
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  let m := S.max' hSne
  have hmS : m ∈ S := S.max'_mem hSne
  have hleMax : ∀ i ∈ S, i ≤ m := fun i hi ↦ S.le_max' i hi
  have hmTwo : 2 ≤ m := by
    by_contra hnot
    have hsub : S ⊆ ({1} : Finset ℕ) := by
      intro i hi
      have hiPos := (hS i hi).1
      have hiMax := hleMax i hi
      simp only [Finset.mem_singleton]
      omega
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨D, hD, hDlen, hDsub, hget⟩ := exists_cycle_of_path_prefix_neighbor hP
    hmTwo (hS m hmS).2.1 (hS m hmS).2.2
  let T := (S.erase 1).erase m
  have hTsub : ∀ i ∈ T, i ∈ S := by
    intro i hi
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  have hTbound : ∀ i ∈ T, 2 ≤ i ∧ i < m := by
    intro i hi
    obtain ⟨him, hiOne⟩ := Finset.mem_erase.mp hi
    obtain ⟨hi1, hiS⟩ := Finset.mem_erase.mp hiOne
    have hiPos := (hS i hiS).1
    have hiMax := hleMax i hiS
    omega
  have hTcard : 2 * k - 1 ≤ T.card := by
    have hc₁ : S.card ≤ (S.erase 1).card + 1 := by
      by_cases h1 : 1 ∈ S
      · rw [Finset.card_erase_of_mem h1]
        omega
      · rw [Finset.erase_eq_of_notMem h1]
        omega
    have hc₂ : (S.erase 1).card ≤ T.card + 1 := by
      by_cases hm : m ∈ S.erase 1
      · dsimp only [T]
        rw [Finset.card_erase_of_mem hm]
        omega
      · dsimp only [T]
        rw [Finset.erase_eq_of_notMem hm]
        omega
    omega
  let f : T → Fin D.length := fun i ↦ ⟨i.val, by
    have hib := hTbound i.val i.property
    omega⟩
  let J : Finset (Fin D.length) := Finset.univ.image f
  have hJcard : J.card = T.card := by
    dsimp only [J]
    rw [Finset.card_image_of_injective _ (by
      intro i j hij
      apply Subtype.ext
      exact congrArg Fin.val hij), Finset.card_univ, Fintype.card_coe]
  refine ⟨D, J, hD, hDsub, by omega, ?_⟩
  intro j hj
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
  have hiBound := hTbound i.val i.property
  have hiS := hTsub i.val i.property
  refine ⟨hiBound.1, by dsimp only [f]; omega, ?_⟩
  have hadj := (hS i.val hiS).2.2
  dsimp only [f]
  rw [hget i.val hiBound.2.le]
  exact hadj

/-- A high-degree endpoint whose neighbors all lie on a simple path
supplies the incident-chord cycle used when that endpoint has no neighbor
on the selected outside odd cycle. -/
theorem exists_cycle_with_many_chords_of_path_neighbors [Fintype V] [DecidableRel G.Adj]
    {A B : V} {P : G.Walk A B} (hP : P.IsPath)
    (hneighbors : ∀ v : V, G.Adj A v → v ∈ P.support)
    (k : ℕ) (hk : 1 ≤ k) (hdegree : 2 * k + 1 ≤ G.degree A) :
    ∃ (D : G.Walk A A) (J : Finset (Fin D.length)), D.IsCycle ∧
      D.support ⊆ P.support ∧ 2 * k - 1 ≤ J.card ∧
      (∀ j ∈ J, 2 ≤ j.val ∧ j.val + 2 ≤ D.length ∧ G.Adj A (D.getVert j.val)) := by
  classical
  let S := (G.neighborFinset A).image (pathPosition P)
  have hScard : S.card = G.degree A := by
    dsimp only [S]
    rw [Finset.card_image_of_injOn, G.card_neighborFinset_eq_degree]
    intro u hu v hv hpos
    have huP := hneighbors u (G.mem_neighborFinset A u |>.mp hu)
    have hvP := hneighbors v (G.mem_neighborFinset A v |>.mp hv)
    exact (getVert_pathPosition P huP).symm.trans
      ((congrArg P.getVert hpos).trans (getVert_pathPosition P hvP))
  have hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ P.length ∧ G.Adj A (P.getVert i) := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    have hAv := (G.mem_neighborFinset A v).mp hv
    have hvP := hneighbors v hAv
    have hget := getVert_pathPosition P hvP
    have hpos : 1 ≤ pathPosition P v := by
      by_contra hnot
      have hzero : pathPosition P v = 0 := by omega
      rw [hzero, Walk.getVert_zero] at hget
      exact hAv.ne hget
    exact ⟨hpos, pathPosition_le P hvP, by simpa only [hget] using hAv⟩
  exact exists_cycle_with_many_chords_of_path_indices hP S k hk (by omega) hS

end JSP000078

import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# A longest simple path outside a prescribed support

Mathlib supplies a longest path in the finite induced graph on a nonempty
vertex set. Mapping it to the ambient graph and inducing competitors back
preserves simplicity and lengths, giving maximality in ambient terminology.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A nonempty vertex subset of a finite graph contains an ambient simple
path longest among all simple paths supported in that subset. -/
theorem exists_longest_path_in_set (S : Set V) (hS : S.Nonempty) :
    ∃ (A B : V) (P : G.Walk A B), P.IsPath ∧
      (∀ v ∈ P.support, v ∈ S) ∧
      (∀ (a b : V) (Q : G.Walk a b), Q.IsPath →
        (∀ v ∈ Q.support, v ∈ S) → Q.length ≤ P.length) := by
  classical
  let : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  let H := G.induce S
  obtain ⟨A, B, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length H
  let f := (SimpleGraph.Embedding.induce S (G := G)).toHom
  let P := p.map f
  have hP : P.IsPath := hp.map (SimpleGraph.Embedding.induce S (G := G)).injective
  have hPsub : ∀ v ∈ P.support, v ∈ S := by
    intro v hv
    rw [Walk.support_map] at hv
    obtain ⟨w, _, hwv⟩ := List.mem_map.mp hv
    exact hwv ▸ w.property
  refine ⟨A.val, B.val, P, hP, hPsub, ?_⟩
  intro a b Q hQ hQS
  let q := Q.induce S hQS
  have hmap : q.map f = Q := Q.map_induce hQS
  have hq : q.IsPath := Walk.IsPath.of_map (hmap.symm ▸ hQ)
  have hqlen : q.length = Q.length := by
    calc
      q.length = (q.map f).length := (Walk.length_map f q).symm
      _ = Q.length := congrArg (fun W : G.Walk a b ↦ W.length) hmap
  have hbound := hmax _ _ q hq
  change Q.length ≤ (p.map f).length
  rw [Walk.length_map, ← hqlen]
  exact hbound

/-- A nonempty complement of a walk's support has a longest simple path
whose full support is disjoint from that walk. -/
theorem exists_longest_outside_path {c d : V} (C : G.Walk c d)
    (houtside : ∃ v : V, v ∉ C.support) :
    ∃ (A B : V) (P : G.Walk A B), P.IsPath ∧
      Disjoint {v | v ∈ P.support} {v | v ∈ C.support} ∧
      (∀ (a b : V) (Q : G.Walk a b), Q.IsPath →
        Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length) := by
  obtain ⟨A, B, P, hP, hPout, hmax⟩ :=
    exists_longest_path_in_set (G := G) {v | v ∉ C.support} houtside
  refine ⟨A, B, P, hP, Set.disjoint_left.mpr (fun v hvP hvC ↦ hPout v hvP hvC), ?_⟩
  intro a b Q hQ hdis
  exact hmax a b Q hQ (fun v hvQ hvC ↦ Set.disjoint_left.mp hdis hvQ hvC)

/-- If there is an edge outside the prescribed support, a longest outside
path has distinct endpoints. This excludes the independent-complement case. -/
theorem exists_nontrivial_longest_outside_path {c d : V} (C : G.Walk c d)
    (hedge : ∃ u v : V, u ∉ C.support ∧ v ∉ C.support ∧ G.Adj u v) :
    ∃ (A B : V) (P : G.Walk A B), P.IsPath ∧ A ≠ B ∧
      Disjoint {v | v ∈ P.support} {v | v ∈ C.support} ∧
      (∀ (a b : V) (Q : G.Walk a b), Q.IsPath →
        Disjoint {v | v ∈ Q.support} {v | v ∈ C.support} → Q.length ≤ P.length) := by
  obtain ⟨u, v, hu, hv, huv⟩ := hedge
  obtain ⟨A, B, P, hP, hdis, hmax⟩ := exists_longest_outside_path C ⟨u, hu⟩
  have hedgeDis : Disjoint {w | w ∈ huv.toWalk.support} {w | w ∈ C.support} := by
    apply Set.disjoint_left.mpr
    intro w hw hwC
    have hwuv : w = u ∨ w = v := by
      simpa only [Set.mem_ofPred_eq, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using hw
    rcases hwuv with rfl | rfl
    · exact hu hwC
    · exact hv hwC
  have hpositive : 1 ≤ P.length := by
    have h := hmax u v huv.toWalk huv.isPath_toWalk hedgeDis
    simpa only [Adj.length_toWalk] using h
  have hAB : A ≠ B := by
    intro hsame
    have hnil := hP.nil_iff_eq.mpr hsame
    have hzero := hnil.length_eq_zero
    omega
  exact ⟨A, B, P, hP, hAB, hdis, hmax⟩

end JSP000078

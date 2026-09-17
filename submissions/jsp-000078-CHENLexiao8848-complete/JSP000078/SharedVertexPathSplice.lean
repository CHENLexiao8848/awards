import JSP000078.CycleArcs
import Mathlib.Algebra.Ring.Parity

/-!
# Splicing paths through a shared vertex to an odd cycle

Two same-parity paths in a vertex set meeting an odd cycle only at their
initial vertex can be closed by one clean connector and a fixed cycle arc.
The resulting cycles have different odd lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A path in `T`, a clean connector, and an arc on a cycle meeting `T`
only at the common initial vertex form a simple cycle. -/
theorem isCycle_shared_vertex_path_splice {x u v : V} {T : Set V}
    {C : G.Walk x x} {p : G.Walk x v} {q : G.Walk u v} {U : G.Walk x u}
    (hp : p.IsPath) (hq : q.IsPath) (hU : U.IsPath)
    (hpT : ∀ w ∈ p.support, w ∈ T) (hUC : ∀ w ∈ U.support, w ∈ C.support)
    (hTC : ∀ w ∈ T, w ∈ C.support → w = x)
    (hqC : ∀ w ∈ q.support, w ∈ C.support → w = u)
    (hqT : ∀ w ∈ q.support, w ∈ T → w = v)
    (hux : u ≠ x) (hvx : v ≠ x) :
    ((p.append q.reverse).append U.reverse).IsCycle := by
  have hpq : (p.append q.reverse).IsPath := by
    apply isPath_append_of_support_intersection hp hq.reverse
    intro w hwp hwq
    exact hqT w (by simpa only [Walk.support_reverse, List.mem_reverse] using hwq) (hpT w hwp)
  have huC : u ∈ C.support := hUC u U.end_mem_support
  have hvT : v ∈ T := hpT v p.end_mem_support
  have huv : u ≠ v := by
    intro heq
    exact hux (hTC u (heq.symm ▸ hvT) huC)
  have hpPos : 0 < p.length := Nat.pos_of_ne_zero fun h ↦ hvx (Walk.eq_of_length_eq_zero h).symm
  have hqPos : 0 < q.length := Nat.pos_of_ne_zero fun h ↦ huv (Walk.eq_of_length_eq_zero h)
  have hUPos : 0 < U.length := Nat.pos_of_ne_zero fun h ↦ hux (Walk.eq_of_length_eq_zero h).symm
  apply isCycle_append_of_support_intersection hpq hU.reverse
  · intro w hwpq hwU
    have hwC : w ∈ C.support := hUC w (by simpa only [Walk.support_reverse, List.mem_reverse] using hwU)
    rcases (Walk.mem_support_append_iff p q.reverse).mp hwpq with hwp | hwq
    · exact Or.inl (hTC w (hpT w hwp) hwC)
    · exact Or.inr (hqC w (by simpa only [Walk.support_reverse, List.mem_reverse] using hwq) hwC)
  · simp only [Walk.length_append, Walk.length_reverse]
    omega

/-- Two different same-parity paths in a set sharing only `x` with an
odd cycle give two different odd cycle lengths through a clean connector. -/
theorem exists_two_odd_cycles_of_shared_vertex_paths
    {x u v : V} {T : Set V} {C : G.Walk x x}
    (hC : C.IsCycle) (hCOdd : Odd C.length)
    (huC : u ∈ C.support) (hux : u ≠ x) (hvx : v ≠ x)
    (p₁ p₂ : G.Walk x v) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hp₁T : ∀ w ∈ p₁.support, w ∈ T) (hp₂T : ∀ w ∈ p₂.support, w ∈ T)
    (hlen : p₁.length ≠ p₂.length) (hpar : p₁.length % 2 = p₂.length % 2)
    (hTC : ∀ w ∈ T, w ∈ C.support → w = x)
    (q : G.Walk u v) (hq : q.IsPath)
    (hqC : ∀ w ∈ q.support, w ∈ C.support → w = u)
    (hqT : ∀ w ∈ q.support, w ∈ T → w = v) :
    ∃ E F : G.Walk x x, E.IsCycle ∧ F.IsCycle ∧
      Odd E.length ∧ Odd F.length ∧ E.length ≠ F.length := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU₁C, hU₂C, _, hsum⟩ :=
    exists_cycle_arcs hC C.start_mem_support huC hux.symm
  have hoddSum : Odd (U₁.length + U₂.length) := hsum.symm ▸ hCOdd
  have chooseArc : ∃ U : G.Walk x u, U.IsPath ∧
      (∀ w ∈ U.support, w ∈ C.support) ∧ Odd (p₁.length + q.length + U.length) := by
    by_cases hodd : Odd (p₁.length + q.length + U₁.length)
    · exact ⟨U₁, hU₁, hU₁C, hodd⟩
    · refine ⟨U₂, hU₂, hU₂C, ?_⟩
      have hsumMod := Nat.odd_iff.mp hoddSum
      have hnmod : (p₁.length + q.length + U₁.length) % 2 ≠ 1 := by
        simpa only [Nat.odd_iff] using hodd
      rw [Nat.odd_iff]
      omega
  obtain ⟨U, hU, hUC, hodd₁⟩ := chooseArc
  let E := (p₁.append q.reverse).append U.reverse
  let F := (p₂.append q.reverse).append U.reverse
  have hEL : E.length = p₁.length + q.length + U.length := by
    simp only [E, Walk.length_append, Walk.length_reverse]
  have hFL : F.length = p₂.length + q.length + U.length := by
    simp only [F, Walk.length_append, Walk.length_reverse]
  refine ⟨E, F, isCycle_shared_vertex_path_splice hp₁ hq hU hp₁T hUC hTC hqC hqT hux hvx,
    isCycle_shared_vertex_path_splice hp₂ hq hU hp₂T hUC hTC hqC hqT hux hvx, ?_, ?_, ?_⟩
  · simpa only [hEL] using hodd₁
  · have hoddMod := Nat.odd_iff.mp hodd₁
    rw [Nat.odd_iff, hFL]
    omega
  · intro heq
    rw [hEL, hFL] at heq
    exact hlen (by omega)

end JSP000078

import JSP000078.Linkage
import JSP000078.CycleArcs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# An initial two-arm configuration between disjoint cycles

Trim a connecting path between the two cycles. At its first endpoint, a
neighbor on the first cycle supplies a second arm, while the first arm is
the path of length zero. The trimmed path is the stem.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c d : V}

/-- Connectivity and two disjoint cycles supply a two-arm configuration. -/
theorem nonempty_linkageY_of_disjoint_cycles
    (hG : G.Connected) (C : G.Walk c c) (D : G.Walk d d)
    (hC : C.IsCycle) (_hD : D.IsCycle)
    (hCD : Disjoint {v : V | v ∈ C.support} {v : V | v ∈ D.support}) :
    Nonempty (LinkageY G {v : V | v ∈ C.support} {v : V | v ∈ D.support}) := by
  obtain ⟨P, hP⟩ := hG.exists_isPath c d
  obtain ⟨a, b, stem, hstem, ha, hb, _, hstemC, hstemD⟩ :=
    exists_trimmed_path_between_sets (A := {v : V | v ∈ C.support})
      (B := {v : V | v ∈ D.support}) P hP C.start_mem_support D.start_mem_support
  obtain ⟨a₂, ha₂, hAdj, hne⟩ := exists_adjacent_vertex_on_cycle C hC ha
  have hEdgeC : ∀ v ∈ hAdj.toWalk.support, v ∈ C.support := by
    intro v hv
    simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ha₂
    · exact ha
  refine ⟨{
    left₁ := a
    left₂ := a₂
    branch := a
    right := b
    arm₁ := .nil
    arm₂ := hAdj.toWalk
    stem := stem
    path₁ := by simp
    path₂ := hAdj.isPath_toWalk
    pathStem := hstem
    left₁_mem := ha
    left₂_mem := ha₂
    left_ne := hne.symm
    right_mem := hb
    arms_inter := ?_
    arm₁_stem := ?_
    arm₂_stem := ?_
    arm₁_B := ?_
    arm₂_B := ?_
    stem_A := hstemC
    stem_B := hstemD }⟩
  · intro v hv _
    simpa using hv
  · intro v hv _
    simpa using hv
  · intro v hvEdge hvStem
    exact hstemC v hvStem (hEdgeC v hvEdge)
  · intro v hv _
    simpa using hv
  · intro v hvEdge hvD
    exact (Set.disjoint_left.mp hCD (hEdgeC v hvEdge) hvD).elim

end JSP000078

import JSP000078.DeletionConnector
import JSP000078.FanHom
import JSP000078.SharedVertexPathSplice
import JSP000078.Basic

/-!
# A one-chord bipartite fan sharing a vertex with an odd cycle

Vertex-deletion connectivity supplies a clean connector away from the shared
vertex. Two different same-parity fan paths can then be closed on one fixed
arc of the odd cycle, yielding two different odd cycle lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A bipartite one-chord fan supported on a cycle meeting an odd cycle
only at one vertex yields two odd cycles of different lengths. -/
theorem exists_two_odd_cycles_of_shared_bipartite_fan
    (hG : TwoVertexConnected G) {x d : V} {C : G.Walk x x} {D : G.Walk d d}
    (hC : C.IsCycle) (hCOdd : Odd C.length) (hD : D.IsCycle) (hxD : x ∈ D.support)
    (hDC : ∀ w ∈ D.support, w ∈ C.support → w = x)
    {H : SimpleGraph {v : V // v ∈ D.support}}
    (hHG : H ≤ G.induce {v : V | v ∈ D.support})
    (F : CycleWithIncidentChords H) (hcard : F.indices.card = 1) (hB : H.IsBipartite) :
    ∃ E F' : G.Walk x x, E.IsCycle ∧ F'.IsCycle ∧
      Odd E.length ∧ Odd F'.length ∧ E.length ≠ F'.length := by
  obtain ⟨u, v, q, hq, huC, hux, hvD, hvx, _, _, hqC, hqD⟩ :=
    exists_clean_connector_between_cycles_sharing_vertex hG hC hD
      (fun w hwC hwD ↦ hDC w hwD hwC)
  let a : {w : V // w ∈ D.support} := ⟨x, hxD⟩
  let b : {w : V // w ∈ D.support} := ⟨v, hvD⟩
  have hab : a ≠ b := by
    intro heq
    have hval := congrArg Subtype.val heq
    exact hvx hval.symm
  obtain ⟨P, hP, hPT, hInj, hpar⟩ :=
    exists_mapped_fan_paths D hHG F 1 (by decide) (by simpa using hcard) hB a b hab
  have hlen : (P 0).length ≠ (P 1).length := by
    intro heq
    have h01 : (0 : Fin 2) = 1 := hInj heq
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  exact exists_two_odd_cycles_of_shared_vertex_paths
    (T := {w : V | w ∈ D.support}) hC hCOdd huC hux hvx
    (P 0) (P 1) (hP 0) (hP 1) (hPT 0) (hPT 1) hlen (hpar 0 1) hDC q hq hqC hqD

/-- The shared-fan construction forces at least two distinct odd cycle lengths. -/
theorem two_le_oddCycleLengths_of_shared_bipartite_fan
    (hG : TwoVertexConnected G) {x d : V} {C : G.Walk x x} {D : G.Walk d d}
    (hC : C.IsCycle) (hCOdd : Odd C.length) (hD : D.IsCycle) (hxD : x ∈ D.support)
    (hDC : ∀ w ∈ D.support, w ∈ C.support → w = x)
    {H : SimpleGraph {v : V // v ∈ D.support}}
    (hHG : H ≤ G.induce {v : V | v ∈ D.support})
    (F : CycleWithIncidentChords H) (hcard : F.indices.card = 1) (hB : H.IsBipartite) :
    2 ≤ (oddCycleLengths G).card := by
  classical
  obtain ⟨E, F', hE, hF, hEOdd, hFOdd, hne⟩ :=
    exists_two_odd_cycles_of_shared_bipartite_fan hG hC hCOdd hD hxD hDC hHG F hcard hB
  have hEmem : E.length ∈ oddCycleLengths G :=
    (mem_oddCycleLengths G).mpr ⟨hEOdd, x, E, hE, rfl⟩
  have hFmem : F'.length ∈ oddCycleLengths G :=
    (mem_oddCycleLengths G).mpr ⟨hFOdd, x, F', hF, rfl⟩
  have hsub : ({E.length, F'.length} : Finset ℕ) ⊆ oddCycleLengths G := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact hEmem
    · exact hFmem
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hcount
  exact hcount

end JSP000078

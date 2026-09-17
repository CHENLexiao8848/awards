import JSP000078.DeletionConnector
import JSP000078.FanHom
import JSP000078.SharedVertexPathSplice
import JSP000078.Basic

/-!
# Many odd lengths from a fan sharing one vertex with an odd cycle

One fixed cycle arc and one clean connector add the same length to every
path in a same-parity fan family, preserving distinctness of lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A distinct same-parity path family in a set meeting an odd cycle only
at its initial vertex supplies equally many odd cycle lengths. -/
theorem odd_cycle_lengths_of_shared_vertex_path_family
    {x u v : V} {T : Set V} {C : G.Walk x x}
    (hC : C.IsCycle) (hCO : Odd C.length) (huC : u ∈ C.support)
    (hux : u ≠ x) (hvx : v ≠ x)
    (hTC : ∀ w ∈ T, w ∈ C.support → w = x)
    (q : G.Walk u v) (hq : q.IsPath)
    (hqC : ∀ w ∈ q.support, w ∈ C.support → w = u)
    (hqT : ∀ w ∈ q.support, w ∈ T → w = v)
    {n : ℕ} (hn : 0 < n) (P : Fin n → G.Walk x v)
    (hP : ∀ i, (P i).IsPath) (hPT : ∀ i, ∀ w ∈ (P i).support, w ∈ T)
    (hInj : Function.Injective fun i ↦ (P i).length)
    (hPar : ∀ i j, (P i).length % 2 = (P j).length % 2) :
    n ≤ (oddCycleLengths G).card := by
  classical
  obtain ⟨U, W, hU, hW, hUC, hWC, _, hsum⟩ :=
    exists_cycle_arcs hC C.start_mem_support huC hux.symm
  let i₀ : Fin n := ⟨0, hn⟩
  have harc : ∃ R : G.Walk x u, R.IsPath ∧
      (∀ w ∈ R.support, w ∈ C.support) ∧ Odd ((P i₀).length + q.length + R.length) := by
    by_cases hodd : Odd ((P i₀).length + q.length + U.length)
    · exact ⟨U, hU, hUC, hodd⟩
    · refine ⟨W, hW, hWC, ?_⟩
      have hNmod := Nat.odd_iff.mp hCO
      have hnot : ((P i₀).length + q.length + U.length) % 2 ≠ 1 := by
        simpa only [Nat.odd_iff] using hodd
      rw [Nat.odd_iff]
      omega
  obtain ⟨R, hR, hRC, hROdd⟩ := harc
  let E : Fin n → G.Walk x x := fun i ↦ ((P i).append q.reverse).append R.reverse
  have hE : ∀ i, (E i).IsCycle := fun i ↦
    isCycle_shared_vertex_path_splice (hP i) hq hR (hPT i) hRC hTC hqC hqT hux hvx
  have hEL : ∀ i, (E i).length = (P i).length + q.length + R.length := by
    intro i
    simp only [E, Walk.length_append, Walk.length_reverse]
  have hEOdd : ∀ i, Odd (E i).length := by
    intro i
    have hpar := hPar i i₀
    have hodd := Nat.odd_iff.mp hROdd
    rw [Nat.odd_iff, hEL]
    omega
  have hEInj : Function.Injective fun i ↦ (E i).length := by
    intro i j hij
    apply hInj
    change (E i).length = (E j).length at hij
    rw [hEL i, hEL j] at hij
    change (P i).length = (P j).length
    omega
  have hsub : (Finset.univ.image fun i : Fin n ↦ (E i).length) ⊆ oddCycleLengths G := by
    intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_oddCycleLengths G).mpr ⟨hEOdd i, x, E i, hE i, rfl⟩
  have hcount := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hEInj, Finset.card_univ, Fintype.card_fin] using hcount

/-- A bipartite fan sharing exactly one allowed vertex with an odd cycle
produces `k+1` distinct odd cycle lengths through a deletion connector. -/
theorem odd_cycle_lengths_of_shared_bipartite_fan
    (hG : TwoVertexConnected G) {x d : V} {C : G.Walk x x} {D : G.Walk d d}
    (hC : C.IsCycle) (hCO : Odd C.length) (hD : D.IsCycle) (hxD : x ∈ D.support)
    (hDC : ∀ w ∈ D.support, w ∈ C.support → w = x)
    {H : SimpleGraph {v : V // v ∈ D.support}}
    (hHG : H ≤ G.induce {v : V | v ∈ D.support}) (F : CycleWithIncidentChords H)
    (k : ℕ) (hk : 1 ≤ k) (hcard : F.indices.card = 2 * k - 1) (hBip : H.IsBipartite) :
    k + 1 ≤ (oddCycleLengths G).card := by
  obtain ⟨u, v, q, hq, huC, hux, hvD, hvx, _, _, hqC, hqD⟩ :=
    exists_clean_connector_between_cycles_sharing_vertex hG hC hD
      (fun w hwC hwD ↦ hDC w hwD hwC)
  let a : {w : V // w ∈ D.support} := ⟨x, hxD⟩
  let b : {w : V // w ∈ D.support} := ⟨v, hvD⟩
  have hab : a ≠ b := fun heq ↦ hvx (congrArg Subtype.val heq).symm
  obtain ⟨P, hP, hPT, hInj, hPar⟩ :=
    exists_mapped_fan_paths D hHG F k hk hcard hBip a b hab
  exact odd_cycle_lengths_of_shared_vertex_path_family hC hCO huC hux hvx hDC
    q hq hqC hqD (by omega) P hP hPT hInj hPar

end JSP000078

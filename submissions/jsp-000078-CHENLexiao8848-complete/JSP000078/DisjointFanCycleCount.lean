import JSP000078.HistoricalLinking
import JSP000078.FanHom
import JSP000078.OddCycleSplice
import JSP000078.Basic

/-!
# Odd cycles from a disjoint bipartite fan

Clean links and a fixed arc of an odd cycle turn same-parity fan paths
into odd cycles. The links and chosen arc add one fixed length, preserving
the distinction between the original path lengths.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A family of distinct same-parity paths in a set disjoint from an odd
cycle gives equally many odd cycle lengths when joined by two clean links. -/
theorem odd_cycle_lengths_of_clean_links_and_path_family {c a₁ a₂ b₁ b₂ : V}
    {C : G.Walk c c} (hC : C.IsCycle) (hCO : Odd C.length) (S : Set V)
    (hCS : Disjoint {v | v ∈ C.support} S)
    {p : G.Walk a₁ b₁} {q : G.Walk a₂ b₂} (hp : p.IsPath) (hq : q.IsPath)
    (ha₁ : a₁ ∈ C.support) (ha₂ : a₂ ∈ C.support) (hb₁ : b₁ ∈ S) (hb₂ : b₂ ∈ S)
    (hpq : Disjoint {v | v ∈ p.support} {v | v ∈ q.support})
    (hpC : ∀ v ∈ p.support, v ∈ C.support → v = a₁)
    (hqC : ∀ v ∈ q.support, v ∈ C.support → v = a₂)
    (hpS : ∀ v ∈ p.support, v ∈ S → v = b₁)
    (hqS : ∀ v ∈ q.support, v ∈ S → v = b₂)
    {n : ℕ} (hn : 0 < n) (Q : Fin n → G.Walk b₁ b₂)
    (hQ : ∀ i, (Q i).IsPath) (hQS : ∀ i, ∀ v ∈ (Q i).support, v ∈ S)
    (hInj : Function.Injective fun i ↦ (Q i).length)
    (hPar : ∀ i j, (Q i).length % 2 = (Q j).length % 2) :
    n ≤ (oddCycleLengths G).card := by
  classical
  have haa : a₁ ≠ a₂ := by
    intro h
    exact Set.disjoint_left.mp hpq p.start_mem_support (h ▸ q.start_mem_support)
  have hab₁ : a₁ ≠ b₁ := fun h ↦ Set.disjoint_left.mp hCS ha₁ (h ▸ hb₁)
  have hab₂ : a₂ ≠ b₂ := fun h ↦ Set.disjoint_left.mp hCS ha₂ (h ▸ hb₂)
  have hpPos : 0 < p.length := Nat.pos_of_ne_zero fun h ↦ hab₁ (Walk.eq_of_length_eq_zero h)
  have hqPos : 0 < q.length := Nat.pos_of_ne_zero fun h ↦ hab₂ (Walk.eq_of_length_eq_zero h)
  obtain ⟨U, W, hU, hW, hUC, hWC, _, hUWlen⟩ := exists_cycle_arcs hC ha₁ ha₂ haa
  let i₀ : Fin n := ⟨0, hn⟩
  have harc : ∃ T : G.Walk a₁ a₂, T.IsPath ∧
      (∀ v ∈ T.support, v ∈ C.support) ∧
      Odd (T.length + p.length + q.length + (Q i₀).length) := by
    by_cases hodd : Odd (U.length + p.length + q.length + (Q i₀).length)
    · exact ⟨U, hU, hUC, hodd⟩
    · refine ⟨W, hW, hWC, ?_⟩
      rw [Nat.odd_iff] at hCO hodd ⊢
      omega
  obtain ⟨T, hT, hTC, hTO⟩ := harc
  have hTPos : 0 < T.length := Nat.pos_of_ne_zero fun h ↦ haa (Walk.eq_of_length_eq_zero h)
  let E : Fin n → G.Walk a₁ a₁ := fun i ↦
    (T.append q).append ((Q i).reverse.append p.reverse)
  have hE : ∀ i, (E i).IsCycle := by
    intro i
    exact isCycle_splice_paths_between_sets hCS hT (hQ i) hp hq hTC (hQS i) hpq
      hpC hqC hpS hqS (by omega)
  have hEL : ∀ i, (E i).length = T.length + p.length + q.length + (Q i).length := by
    intro i
    simp only [E, Walk.length_append, Walk.length_reverse]
    omega
  have hEO : ∀ i, Odd (E i).length := by
    intro i
    rw [hEL]
    have hpar := hPar i i₀
    rw [Nat.odd_iff] at hTO ⊢
    omega
  have hEI : Function.Injective fun i ↦ (E i).length := by
    intro i j hij
    apply hInj
    change (E i).length = (E j).length at hij
    rw [hEL i, hEL j] at hij
    change (Q i).length = (Q j).length
    omega
  have hsub : (Finset.univ.image fun i : Fin n ↦ (E i).length) ⊆ oddCycleLengths G := by
    intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_oddCycleLengths G).mpr ⟨hEO i, a₁, E i, hE i, rfl⟩
  have hcount := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hEI, Finset.card_univ, Fintype.card_fin] using hcount

/-- A bipartite fan on a cycle disjoint from an odd cycle supplies more
odd lengths via two clean links and its same-parity distinct path family. -/
theorem odd_cycle_lengths_of_disjoint_bipartite_fan
    (hG : TwoVertexConnected G) {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : C.IsCycle) (hCO : Odd C.length) (hD : D.IsCycle)
    (hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support})
    {H : SimpleGraph {v : V // v ∈ D.support}}
    (hHG : H ≤ G.induce {v | v ∈ D.support}) (F : CycleWithIncidentChords H)
    (k : ℕ) (hk : 1 ≤ k) (hcard : F.indices.card = 2 * k - 1) (hBip : H.IsBipartite) :
    k + 1 ≤ (oddCycleLengths G).card := by
  obtain ⟨a₁, a₂, b₁, b₂, p, q, hp, hq, ha₁, ha₂, hb₁, hb₂, hpq, hpC, hqC, hpD, hqD⟩ :=
    twoDisjointCycleLinks_of_twoVertexConnected hG c d C D hC hD hCD
  have hbb : b₁ ≠ b₂ := by
    intro h
    exact Set.disjoint_left.mp hpq p.end_mem_support (h ▸ q.end_mem_support)
  let b₁' : {v : V // v ∈ D.support} := ⟨b₁, hb₁⟩
  let b₂' : {v : V // v ∈ D.support} := ⟨b₂, hb₂⟩
  have hbb' : b₁' ≠ b₂' := fun h ↦ hbb (congrArg Subtype.val h)
  obtain ⟨Q, hQ, hQD, hQI, hQpar⟩ :=
    exists_mapped_fan_paths D hHG F k hk hcard hBip b₁' b₂' hbb'
  exact odd_cycle_lengths_of_clean_links_and_path_family hC hCO {v | v ∈ D.support}
    hCD hp hq ha₁ ha₂ hb₁ hb₂ hpq hpC hqC hpD hqD (by omega) Q hQ hQD hQI hQpar

end JSP000078

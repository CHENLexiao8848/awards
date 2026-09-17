import JSP000078.HistoricalSpec
import Mathlib.Data.Fintype.EquivFin

/-!
# Proper vertex covers separated by at most one vertex

A disconnected graph separates into a reachable component and its
complement. If deleting a vertex disconnects the graph, adjoining the
deleted vertex to both lifted components gives an overlap of at most
one vertex. These covers support induction and coloring gluing.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Failure of preconnectedness gives a proper disjoint cover with no
crossing edge. No finiteness or nonempty-type hypothesis is necessary. -/
theorem exists_disjoint_cover_of_not_preconnected (hG : ¬G.Preconnected) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ≠ Set.univ ∧ T ≠ Set.univ ∧
      Disjoint S T ∧ (∀ u ∈ S, ∀ v ∈ T, ¬G.Adj u v) := by
  classical
  have hpairs : ∃ a b : V, ¬G.Reachable a b := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hG
  obtain ⟨a, b, hab⟩ := hpairs
  let S : Set V := {v | G.Reachable a v}
  refine ⟨S, Sᶜ, Set.union_compl_self S, ?_, ?_, ?_, ?_⟩
  · intro hSuniv
    have hbS : b ∈ S := hSuniv.symm ▸ Set.mem_univ b
    exact hab hbS
  · intro hTuniv
    have haComp : a ∈ Sᶜ := hTuniv.symm ▸ Set.mem_univ a
    exact haComp (SimpleGraph.Reachable.rfl : G.Reachable a a)
  · exact Set.disjoint_left.mpr fun _ hu hnot ↦ hnot hu
  · intro u hu v hv huv
    exact hv (hu.trans huv.reachable)

/-- A disconnected nonempty graph has a proper cover whose intersection
is empty and hence subsingleton. -/
theorem exists_separator_cover_of_not_connected [Nonempty V] (hG : ¬G.Connected) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ≠ Set.univ ∧ T ≠ Set.univ ∧
      (S ∩ T).Subsingleton ∧
      (∀ u ∈ S, u ∉ T → ∀ v ∈ T, v ∉ S → ¬G.Adj u v) := by
  have hpre : ¬G.Preconnected := fun h ↦ hG ⟨h⟩
  obtain ⟨S, T, hcover, hS, hT, hdisjoint, hcross⟩ :=
    exists_disjoint_cover_of_not_preconnected hpre
  refine ⟨S, T, hcover, hS, hT, ?_, ?_⟩
  · intro u hu v _
    exact (Set.disjoint_left.mp hdisjoint hu.1 hu.2).elim
  · intro u hu _ v hv _
    exact hcross u hu v hv

/-- If deletion of one vertex is not preconnected, lift a component
partition and adjoin the deleted vertex to both parts. -/
theorem exists_separator_cover_of_delete_not_preconnected (x : V)
    (hG : ¬(G.induce ({x} : Set V)ᶜ).Preconnected) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ≠ Set.univ ∧ T ≠ Set.univ ∧
      (S ∩ T).Subsingleton ∧
      (∀ u ∈ S, u ∉ T → ∀ v ∈ T, v ∉ S → ¬G.Adj u v) := by
  classical
  have hpairs : ∃ a b : ↥(({x} : Set V)ᶜ),
      ¬(G.induce ({x} : Set V)ᶜ).Reachable a b := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hG
  obtain ⟨a, b, hab⟩ := hpairs
  let U : Set V := {v | ∃ hv : v ∈ ({x} : Set V)ᶜ,
    (G.induce ({x} : Set V)ᶜ).Reachable a ⟨v, hv⟩}
  let S : Set V := insert x U
  let T : Set V := insert x Uᶜ
  have haU : a.val ∈ U := ⟨a.property, SimpleGraph.Reachable.rfl⟩
  have hbU : b.val ∉ U := by
    rintro ⟨_, hb⟩
    exact hab hb
  have hax : a.val ≠ x := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using a.property
  have hbx : b.val ≠ x := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using b.property
  refine ⟨S, T, ?_, ?_, ?_, ?_, ?_⟩
  · ext v
    simp only [S, T, Set.mem_union, Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hv : v ∈ U
    · exact Or.inl (Or.inr hv)
    · exact Or.inr (Or.inr hv)
  · intro hSuniv
    have hbS : b.val ∈ S := hSuniv.symm ▸ Set.mem_univ b.val
    exact (Set.mem_insert_iff.mp hbS).elim hbx hbU
  · intro hTuniv
    have haT : a.val ∈ T := hTuniv.symm ▸ Set.mem_univ a.val
    exact (Set.mem_insert_iff.mp haT).elim hax (fun h ↦ h haU)
  · intro u hu v hv
    have hux : u = x := by
      rcases Set.mem_insert_iff.mp hu.1 with hux | huU
      · exact hux
      · rcases Set.mem_insert_iff.mp hu.2 with hux | huNot
        · exact hux
        · exact (huNot huU).elim
    have hvx : v = x := by
      rcases Set.mem_insert_iff.mp hv.1 with hvx | hvU
      · exact hvx
      · rcases Set.mem_insert_iff.mp hv.2 with hvx | hvNot
        · exact hvx
        · exact (hvNot hvU).elim
    exact hux.trans hvx.symm
  · intro u huS huT v hvT hvS huv
    have hux : u ≠ x := fun h ↦ huT (Set.mem_insert_iff.mpr (Or.inl h))
    have hvx : v ≠ x := fun h ↦ hvS (Set.mem_insert_iff.mpr (Or.inl h))
    have huU : u ∈ U := (Set.mem_insert_iff.mp huS).resolve_left hux
    have hvU : v ∉ U := fun h ↦ hvS (Set.mem_insert_iff.mpr (Or.inr h))
    obtain ⟨huDel, hau⟩ := huU
    have hvDel : v ∈ ({x} : Set V)ᶜ := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hvx
    exact hvU ⟨hvDel, hau.trans (show (G.induce ({x} : Set V)ᶜ).Adj
      ⟨u, huDel⟩ ⟨v, hvDel⟩ from huv).reachable⟩

/-- A graph on at least three vertices which fails vertex
2-connectivity splits into two proper covering sets overlapping in at
most one vertex, with no edge between their exclusive parts. -/
theorem exists_separator_cover_of_not_twoVertexConnected [Fintype V]
    (hcard : 3 ≤ Fintype.card V) (hG : ¬TwoVertexConnected G) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ≠ Set.univ ∧ T ≠ Set.univ ∧
      (S ∩ T).Subsingleton ∧
      (∀ u ∈ S, u ∉ T → ∀ v ∈ T, v ∉ S → ¬G.Adj u v) := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  by_cases hconnected : G.Connected
  · have hcut : ∃ x : V, ¬(G.induce ({x} : Set V)ᶜ).Connected := by
      by_contra hnone
      apply hG
      refine ⟨hcard, hconnected, ?_⟩
      intro x
      by_contra hx
      exact hnone ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hcut
    have hdelNonempty : Nonempty ↥(({x} : Set V)ᶜ) := by
      obtain ⟨y, hy⟩ := exists_ne x
      exact ⟨⟨y, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy⟩⟩
    have hdelPre : ¬(G.induce ({x} : Set V)ᶜ).Preconnected :=
      fun hp ↦ hx { preconnected := hp, nonempty := hdelNonempty }
    exact exists_separator_cover_of_delete_not_preconnected x hdelPre
  · exact exists_separator_cover_of_not_connected hconnected

end JSP000078

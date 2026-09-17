import JSP000078.EndpointConfiguration
import JSP000078.OutsideRoutes

/-! # Selected outside routes for the endpoint configuration -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def EndpointConfiguration.spokes (E : EndpointConfiguration G) : Finset ℕ := insert 1 E.chords

theorem EndpointConfiguration.spokes_nonempty (E : EndpointConfiguration G) : E.spokes.Nonempty :=
  ⟨1, Finset.mem_insert_self _ _⟩

theorem EndpointConfiguration.spokes_bounds (E : EndpointConfiguration G) :
    ∀ d ∈ E.spokes, 1 ≤ d ∧ d ≤ E.outside.length := by
  intro d hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · have hpos : 0 < E.outside.length := Nat.pos_of_ne_zero fun h ↦
      E.ends_ne (Walk.eq_of_length_eq_zero h)
    omega
  · have h := E.chord_bounds d hd
    omega

theorem EndpointConfiguration.spokes_adj (E : EndpointConfiguration G) :
    ∀ d ∈ E.spokes, G.Adj E.first (E.outside.getVert d) := by
  intro d hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact E.outside.adj_snd (Walk.not_nil_of_ne E.ends_ne)
  · exact E.chord_adj d hd

theorem EndpointConfiguration.card_spokes (E : EndpointConfiguration G) :
    E.spokes.card = E.chords.card + 1 := by
  apply Finset.card_insert_of_notMem
  intro h
  have := (E.chord_bounds 1 h).1
  omega

def EndpointConfiguration.routeLengths (E : EndpointConfiguration G) : Finset ℕ :=
  JSP000078.routeLengths E.outside E.spokes

def EndpointConfiguration.tailLength (E : EndpointConfiguration G) : ℕ :=
  routeTailLength E.outside E.spokes E.spokes_nonempty

theorem EndpointConfiguration.card_routeLengths (E : EndpointConfiguration G) :
    E.routeLengths.card = E.chords.card + 1 := by
  rw [routeLengths, routeLengths_card E.outside E.spokes (fun d hd ↦ (E.spokes_bounds d hd).2)]
  exact E.card_spokes

theorem EndpointConfiguration.route_min_mem (E : EndpointConfiguration G) :
    E.tailLength + 1 ∈ E.routeLengths :=
  routeTailLength_add_one_mem E.outside E.spokes E.spokes_nonempty

theorem EndpointConfiguration.route_lower (E : EndpointConfiguration G) {u : ℕ}
    (hu : u ∈ E.routeLengths) : E.tailLength + 1 ≤ u :=
  routeTailLength_add_one_le_of_mem E.outside E.spokes E.spokes_nonempty hu

theorem EndpointConfiguration.exists_route (E : EndpointConfiguration G) {u : ℕ}
    (hu : u ∈ E.routeLengths) :
    ∃ P : G.Walk E.first E.last, P.IsPath ∧ P.length = u ∧ P.support ⊆ E.outside.support :=
  exists_path_of_mem_routeLengths E.outside_path E.spokes E.spokes_bounds E.spokes_adj hu

theorem EndpointConfiguration.exists_low_cycle (E : EndpointConfiguration G) {u : ℕ}
    (hu : u ∈ E.routeLengths) (he : Even (u - E.tailLength)) :
    ∃ C : G.Walk E.first E.first, C.IsCycle ∧ C.length = u - E.tailLength + 1 :=
  exists_cycle_of_even_mem_routeLengths E.outside_path E.spokes E.spokes_nonempty
    E.spokes_bounds E.spokes_adj hu he

end JSP000078

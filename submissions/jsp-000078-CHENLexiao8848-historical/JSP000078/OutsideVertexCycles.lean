import JSP000078.CycleArcs
import JSP000078.TwoSpokeCycle
import JSP000078.Basic

/-!
# Cycles through a vertex outside a given cycle

Two neighbors of an outside vertex divide the original cycle into two
arcs. Each arc, with its two spokes to the outside vertex, gives a simple
cycle whose length is the arc length plus two.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An outside vertex and two distinct neighbors on a cycle produce
cycles on both complementary arcs. -/
theorem exists_cycles_of_outside_vertex_cycle_arcs {c v x y : V}
    {C : G.Walk c c} (hC : C.IsCycle) (hv : v ∉ C.support)
    (hx : x ∈ C.support) (hy : y ∈ C.support) (hxy : x ≠ y)
    (hvx : G.Adj v x) (hvy : G.Adj v y) :
    ∃ (U V' : G.Walk x y) (E F : G.Walk v v),
      U.IsPath ∧ V'.IsPath ∧
      (∀ z ∈ U.support, z ∈ C.support) ∧
      (∀ z ∈ V'.support, z ∈ C.support) ∧
      U.length + V'.length = C.length ∧
      E.IsCycle ∧ F.IsCycle ∧ E.length = U.length + 2 ∧ F.length = V'.length + 2 := by
  obtain ⟨U, V', hU, hV, hUC, hVC, _, hlen⟩ := exists_cycle_arcs hC hx hy hxy
  have hvU : v ∉ U.support := fun h ↦ hv (hUC v h)
  have hvV : v ∉ V'.support := fun h ↦ hv (hVC v h)
  have hUpos : 0 < U.length := Nat.pos_of_ne_zero fun h ↦ hxy (Walk.eq_of_length_eq_zero h)
  have hVpos : 0 < V'.length := Nat.pos_of_ne_zero fun h ↦ hxy (Walk.eq_of_length_eq_zero h)
  obtain ⟨E, hE, hElen⟩ := exists_cycle_of_path_two_spokes hU hvU hvx hvy hUpos
  obtain ⟨F, hF, hFlen⟩ := exists_cycle_of_path_two_spokes hV hvV hvx hvy hVpos
  exact ⟨U, V', E, F, hU, hV, hUC, hVC, hlen, hE, hF, hElen, hFlen⟩

/-- With the original cycle based at the first neighbor, an outside
vertex gives cycles of the exact complementary index lengths plus two. -/
theorem exists_cycles_of_outside_vertex_at_index {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hv : v ∉ C.support) {t : ℕ}
    (htpos : 1 ≤ t) (htN : t < C.length)
    (hvc : G.Adj v c) (hvt : G.Adj v (C.getVert t)) :
    ∃ E F : G.Walk v v, E.IsCycle ∧ F.IsCycle ∧
      E.length = t + 2 ∧ F.length = (C.length - t) + 2 := by
  have hvU : v ∉ (C.take t).support := fun h ↦ hv ((C.isSubwalk_take t).support_subset h)
  have hvV : v ∉ (C.drop t).support := fun h ↦ hv ((C.isSubwalk_drop t).support_subset h)
  have hUlen : (C.take t).length = t := by simp only [Walk.take_length, Nat.min_eq_left htN.le]
  have hVlen : (C.drop t).length = C.length - t := Walk.drop_length C t
  obtain ⟨E, hE, hElen⟩ := exists_cycle_of_path_two_spokes
    (hC.isPath_take htN) hvU hvc hvt (by omega)
  obtain ⟨F, hF, hFlen⟩ := exists_cycle_of_path_two_spokes
    (hC.isPath_drop htpos) hvV hvt hvc (by omega)
  exact ⟨E, F, hE, hF, by omega, by omega⟩

/-- An odd forward arc length plus two is an actual odd cycle length. -/
theorem outside_vertex_forward_length_mem [Fintype V] {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hv : v ∉ C.support) {t : ℕ}
    (htpos : 1 ≤ t) (htN : t < C.length)
    (hvc : G.Adj v c) (hvt : G.Adj v (C.getVert t)) (hodd : Odd (t + 2)) :
    t + 2 ∈ oddCycleLengths G := by
  obtain ⟨E, _, hE, _, hElen, _⟩ :=
    exists_cycles_of_outside_vertex_at_index hC hv htpos htN hvc hvt
  exact (mem_oddCycleLengths G).mpr ⟨hodd, v, E, hE, hElen⟩

/-- An odd complementary arc length plus two is an actual odd cycle length. -/
theorem outside_vertex_complement_length_mem [Fintype V] {c v : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hv : v ∉ C.support) {t : ℕ}
    (htpos : 1 ≤ t) (htN : t < C.length)
    (hvc : G.Adj v c) (hvt : G.Adj v (C.getVert t))
    (hodd : Odd (C.length - t + 2)) :
    C.length - t + 2 ∈ oddCycleLengths G := by
  obtain ⟨_, F, _, hF, _, hFlen⟩ :=
    exists_cycles_of_outside_vertex_at_index hC hv htpos htN hvc hvt
  exact (mem_oddCycleLengths G).mpr ⟨hodd, v, F, hF, hFlen⟩

end JSP000078

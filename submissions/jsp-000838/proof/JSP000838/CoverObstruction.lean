import JSP000838.OrderedObstruction

namespace JSP000838

variable {V : Type*}

/-- A nonempty path of cover relations strictly increases in the ambient order. -/
theorem transGen_covBy_lt [PartialOrder V] {u v : V}
    (h : Relation.TransGen (fun x y : V => x ⋖ y) u v) : u < v := by
  induction h with
  | single h => exact h.lt
  | tail _ h ih => exact ih.trans h.lt

/-- Cover relations are acyclic. -/
theorem acyclic_covBy [PartialOrder V] : Acyclic (fun x y : V => x ⋖ y) := by
  intro v hv
  exact lt_irrefl v (transGen_covBy_lt hv)

/-- The order-theoretic cover relation orients precisely the Hasse graph. -/
theorem isOrientation_hasse_covBy [PartialOrder V] :
    IsOrientation (SimpleGraph.hasse V) (fun x y : V => x ⋖ y) := by
  refine ⟨fun _ _ => Iff.rfl, ?_⟩
  intro u v huv hvu
  exact lt_asymm huv.lt hvu.lt

/-- The finite ordered-cycle obstruction also directly excludes the historical
Hasse-diagram representation. -/
theorem HasOrderedFiveCycle.not_isCoverGraph [Fintype V] {G : SimpleGraph V}
    (hG : HasOrderedFiveCycle G) : ¬ IsCoverGraph G := by
  rintro ⟨P, hP⟩
  let : PartialOrder V := P
  let D : V → V → Prop := fun x y => x ⋖ y
  have hD : Acyclic D := acyclic_covBy
  have ho : IsOrientation G D := by
    rw [← hP]
    exact isOrientation_hasse_covBy
  obtain ⟨r, hr⟩ := hD.exists_ranking
  obtain ⟨f, hf, h01, h12, h23, h34, h04⟩ := hG r
  have d01 : D (f 0) (f 1) := ho.edge_of_rank_lt hr h01 (hf (by decide))
  have d12 : D (f 1) (f 2) := ho.edge_of_rank_lt hr h12 (hf (by decide))
  have d23 : D (f 2) (f 3) := ho.edge_of_rank_lt hr h23 (hf (by decide))
  have d34 : D (f 3) (f 4) := ho.edge_of_rank_lt hr h34 (hf (by decide))
  have d04 : D (f 0) (f 4) := ho.edge_of_rank_lt hr h04 (hf (by decide))
  exact d04.2 d01.lt ((d12.lt.trans d23.lt).trans d34.lt)

/-- The obstruction excludes arbitrary subgraph copies in any Hasse diagram,
including a diagram on an infinite ambient poset. -/
theorem HasOrderedFiveCycle.not_hasse_subgraph [Fintype V] {G : SimpleGraph V}
    (hG : HasOrderedFiveCycle G) (W : Type*) [PartialOrder W] :
    ¬ SimpleGraph.IsContained G (SimpleGraph.hasse W) := by
  rintro ⟨f⟩
  let D : V → V → Prop := fun x y => G.Adj x y ∧ f x ⋖ f y
  have hpath : ∀ {u v}, Relation.TransGen D u v → f u < f v := by
    intro u v h
    induction h with
    | single h => exact h.2.lt
    | tail _ h ih => exact ih.trans h.2.lt
  have hD : Acyclic D := fun v hv => lt_irrefl (f v) (hpath hv)
  have ho : IsOrientation G D := by
    constructor
    · intro x y
      constructor
      · intro hxy
        rcases f.toHom.map_adj hxy with hforward | hbackward
        · exact Or.inl ⟨hxy, hforward⟩
        · exact Or.inr ⟨hxy.symm, hbackward⟩
      · rintro (hxy | hyx)
        · exact hxy.1
        · exact hyx.1.symm
    · intro x y hxy hyx
      exact lt_asymm hxy.2.lt hyx.2.lt
  obtain ⟨r, hr⟩ := hD.exists_ranking
  obtain ⟨v, hv, h01, h12, h23, h34, h04⟩ := hG r
  have d01 := ho.edge_of_rank_lt hr h01 (hv (by decide : (0 : Fin 5) < 1))
  have d12 := ho.edge_of_rank_lt hr h12 (hv (by decide : (1 : Fin 5) < 2))
  have d23 := ho.edge_of_rank_lt hr h23 (hv (by decide : (2 : Fin 5) < 3))
  have d34 := ho.edge_of_rank_lt hr h34 (hv (by decide : (3 : Fin 5) < 4))
  have d04 := ho.edge_of_rank_lt hr h04 (hv (by decide : (0 : Fin 5) < 4))
  exact d04.2.2 d01.2.lt ((d12.2.lt.trans d23.2.lt).trans d34.2.lt)

end JSP000838

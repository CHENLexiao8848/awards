import JSP000078.GyarfasLemmaThree

/-!
# Lifting fan paths from a vertex subtype into the ambient graph

An exact fan may use only some of the induced edges on a cycle support.
Its inclusion is injective, so mapping preserves path simplicity and
lengths, while every mapped support vertex remains on the chosen support.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {S : Set V} {H : SimpleGraph S}

/-- Include a graph below an induced subgraph into its ambient graph. -/
def fanInclusionHom (hHG : H ≤ G.induce S) : H →g G where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    exact hHG hab

@[simp]
theorem fanInclusionHom_apply (hHG : H ≤ G.induce S) (a : S) :
    fanInclusionHom hHG a = a.val := rfl

theorem fanInclusionHom_injective (hHG : H ≤ G.induce S) :
    Function.Injective (fanInclusionHom hHG) := Subtype.val_injective

/-- Mapping a walk on the vertex subtype preserves its length. -/
theorem length_map_fanInclusionHom (hHG : H ≤ G.induce S) {a b : S}
    (p : H.Walk a b) : (p.map (fanInclusionHom hHG)).length = p.length :=
  Walk.length_map _ _

/-- The inclusion is injective, so a fan path remains simple in the ambient graph. -/
theorem isPath_map_fanInclusionHom (hHG : H ≤ G.induce S) {a b : S}
    {p : H.Walk a b} (hp : p.IsPath) : (p.map (fanInclusionHom hHG)).IsPath :=
  hp.map (fanInclusionHom_injective hHG)

/-- Every vertex of a mapped walk lies in its original vertex subset. -/
theorem support_map_fanInclusionHom (hHG : H ≤ G.induce S) {a b : S}
    (p : H.Walk a b) : ∀ v ∈ (p.map (fanInclusionHom hHG)).support, v ∈ S := by
  intro v hv
  rw [Walk.support_map] at hv
  obtain ⟨w, _, hwv⟩ := List.mem_map.mp hv
  exact hwv ▸ w.property

/-- A fan on a vertex subset supplies its distinct, same-parity path
family directly as ambient paths with support in that subset. -/
theorem exists_mapped_fan_paths_on_set (hHG : H ≤ G.induce S)
    (F : CycleWithIncidentChords H) (k : ℕ) (hk : 1 ≤ k)
    (hcard : F.indices.card = 2 * k - 1) (hB : H.IsBipartite)
    (a b : S) (hab : a ≠ b) :
    ∃ P : Fin (k + 1) → G.Walk a.val b.val,
      (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ∈ S) ∧
      Function.Injective (fun i ↦ (P i).length) ∧
      (∀ i j, (P i).length % 2 = (P j).length % 2) := by
  obtain ⟨p, hp, hinj⟩ := F.exists_distinct_path_lengths k hk hcard a b hab
  let P : Fin (k + 1) → G.Walk a.val b.val := fun i ↦ (p i).map (fanInclusionHom hHG)
  refine ⟨P, fun i ↦ isPath_map_fanInclusionHom hHG (hp i),
    fun i ↦ support_map_fanInclusionHom hHG (p i), ?_, ?_⟩
  · intro i j hij
    apply hinj
    change ((p i).map (fanInclusionHom hHG)).length =
      ((p j).map (fanInclusionHom hHG)).length at hij
    rw [length_map_fanInclusionHom hHG, length_map_fanInclusionHom hHG] at hij
    exact hij
  · intro i j
    change ((p i).map (fanInclusionHom hHG)).length % 2 =
      ((p j).map (fanInclusionHom hHG)).length % 2
    rw [length_map_fanInclusionHom hHG, length_map_fanInclusionHom hHG]
    exact walk_length_mod_two_eq_of_bipartite hB (p i) (p j)

/-- Cycle-support version of the lifted fan path family. The chosen
ambient closed walk need not be simple for this inclusion statement. -/
theorem exists_mapped_fan_paths {c : V} (C : G.Walk c c)
    {H : SimpleGraph {v : V // v ∈ C.support}}
    (hHG : H ≤ G.induce {v : V | v ∈ C.support})
    (F : CycleWithIncidentChords H) (k : ℕ) (hk : 1 ≤ k)
    (hcard : F.indices.card = 2 * k - 1) (hB : H.IsBipartite)
    (a b : {v : V // v ∈ C.support}) (hab : a ≠ b) :
    ∃ P : Fin (k + 1) → G.Walk a.val b.val,
      (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ∈ C.support) ∧
      Function.Injective (fun i ↦ (P i).length) ∧
      (∀ i j, (P i).length % 2 = (P j).length % 2) :=
  exists_mapped_fan_paths_on_set hHG F k hk hcard hB a b hab

end JSP000078

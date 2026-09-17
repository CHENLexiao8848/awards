import JSP000838.HasseBridge
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Sort

namespace JSP000838

variable {V : Type*} [Fintype V]

/-- Every ordering of the vertices contains a five-cycle whose first four
edges advance in that ordering and whose fifth edge joins the endpoints. -/
def HasOrderedFiveCycle (G : SimpleGraph V) : Prop :=
  ∀ r : V ≃ Fin (Fintype.card V), ∃ f : Fin 5 → V,
    StrictMono (r ∘ f) ∧
    G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧
    G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 4) ∧ G.Adj (f 0) (f 4)

/-- A finite acyclic relation admits a bijective ranking that increases along
every arc. -/
theorem Acyclic.exists_ranking {D : V → V → Prop} (hD : Acyclic D) :
    ∃ r : V ≃ Fin (Fintype.card V), ∀ u v, D u v → r u < r v := by
  classical
  let : PartialOrder V := reachabilityOrder D hD
  let : Fintype (LinearExtension V) := (inferInstance : Fintype V)
  let e : Fin (Fintype.card V) ≃o LinearExtension V :=
    monoEquivOfFin (LinearExtension V) rfl
  let r : V ≃ Fin (Fintype.card V) :=
    (Equiv.refl V).trans e.symm.toEquiv
  refine ⟨r, fun u v huv => ?_⟩
  have hle : toLinearExtension u ≤ toLinearExtension v :=
    toLinearExtension.monotone (show u ≤ v from Relation.ReflTransGen.single huv)
  have hne : toLinearExtension u ≠ toLinearExtension v := by
    intro heq
    have huv_eq : u = v := heq
    exact hD.ne (Relation.TransGen.single huv) huv_eq
  have hlt : toLinearExtension u < toLinearExtension v := lt_of_le_of_ne hle hne
  exact e.symm.strictMono hlt

theorem IsOrientation.edge_of_rank_lt {G : SimpleGraph V} {D : V → V → Prop}
    (hD : IsOrientation G D) {r : V ≃ Fin (Fintype.card V)}
    (hr : ∀ u v, D u v → r u < r v) {u v : V}
    (hadj : G.Adj u v) (hlt : r u < r v) : D u v := by
  rcases (hD.1 u v).1 hadj with huv | hvu
  · exact huv
  · exact False.elim (lt_asymm hlt (hr v u hvu))

/-- An ordered five-cycle in a topological ordering is a quasicycle. Therefore
a graph containing such a cycle in every ordering has no robust orientation. -/
theorem HasOrderedFiveCycle.not_robust {G : SimpleGraph V} (hG : HasOrderedFiveCycle G)
    (D : V → V → Prop) : ¬ IsRobustAcyclicOrientation G D := by
  intro hD
  obtain ⟨r, hr⟩ := hD.2.1.exists_ranking
  obtain ⟨f, hf, h01, h12, h23, h34, h04⟩ := hG r
  have d01 : D (f 0) (f 1) := hD.1.edge_of_rank_lt hr h01 (hf (by decide))
  have d12 : D (f 1) (f 2) := hD.1.edge_of_rank_lt hr h12 (hf (by decide))
  have d23 : D (f 2) (f 3) := hD.1.edge_of_rank_lt hr h23 (hf (by decide))
  have d34 : D (f 3) (f 4) := hD.1.edge_of_rank_lt hr h34 (hf (by decide))
  have d04 : D (f 0) (f 4) := hD.1.edge_of_rank_lt hr h04 (hf (by decide))
  exact hD.no_intermediate d04
    ⟨f 1, .single d01, ((Relation.TransGen.single d12).tail d23).tail d34⟩

end JSP000838

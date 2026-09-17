import JSP000838.Gluing
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace JSP000838.Gluing

variable {V W : Type*}

/-- An injective relabelling preserves absence of triangles. -/
theorem TriangleFree.map {G : SimpleGraph V} (hG : TriangleFree G) (f : V ↪ W) :
    TriangleFree (G.map f) := by
  intro a b c hab hbc hca
  obtain ⟨a', b', hab', rfl, rfl⟩ := (SimpleGraph.map_adj f G a b).mp hab
  obtain ⟨b'', c', hbc', hb, rfl⟩ := (SimpleGraph.map_adj f G (f b') c).mp hbc
  have heq : b'' = b' := f.injective hb
  subst b''
  exact hG a' b' c' hab' hbc' (SimpleGraph.map_adj_apply.mp hca)

/-- An injective relabelling preserves absence of arbitrary four-cycles. -/
theorem FourCycleFree.map {G : SimpleGraph V} (hG : FourCycleFree G) (f : V ↪ W) :
    FourCycleFree (G.map f) := by
  intro a b c d hac hbd hab hbc hcd hda
  obtain ⟨a', b', hab', rfl, rfl⟩ := (SimpleGraph.map_adj f G a b).mp hab
  obtain ⟨b'', c', hbc', hb, rfl⟩ := (SimpleGraph.map_adj f G (f b') c).mp hbc
  have heb : b'' = b' := f.injective hb
  subst b''
  obtain ⟨c'', d', hcd', hc, rfl⟩ := (SimpleGraph.map_adj f G (f c') d).mp hcd
  have hec : c'' = c' := f.injective hc
  subst c''
  exact hG a' b' c' d' (fun h => hac (congrArg f h))
    (fun h => hbd (congrArg f h)) hab' hbc' hcd' (SimpleGraph.map_adj_apply.mp hda)

end JSP000838.Gluing

namespace JSP000838.LocalCycle

variable {V : Type*} {S : Finset V}

def embedding (e : Fin 5 ≃ S) : Fin 5 ↪ V where
  toFun i := (e i).1
  inj' _ _ h := e.injective (Subtype.ext h)

/-- A five-cycle on the five vertices listed by the equivalence `e`. -/
def graph (e : Fin 5 ≃ S) : SimpleGraph V :=
  (SimpleGraph.cycleGraph 5).map (embedding e)

theorem supported (e : Fin 5 ≃ S) {x y : V} (h : (graph e).Adj x y) :
    x ∈ S ∧ y ∈ S := by
  obtain ⟨i, j, _, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (embedding e) (SimpleGraph.cycleGraph 5) x y).mp h
  exact ⟨(e i).2, (e j).2⟩

theorem base_triangleFree : Gluing.TriangleFree (SimpleGraph.cycleGraph 5) := by
  unfold Gluing.TriangleFree
  decide

theorem base_fourCycleFree : Gluing.FourCycleFree (SimpleGraph.cycleGraph 5) := by
  unfold Gluing.FourCycleFree
  decide

theorem triangleFree (e : Fin 5 ≃ S) : Gluing.TriangleFree (graph e) :=
  base_triangleFree.map (embedding e)

theorem fourCycleFree (e : Fin 5 ≃ S) : Gluing.FourCycleFree (graph e) :=
  base_fourCycleFree.map (embedding e)

theorem adj_iff (e : Fin 5 ≃ S) (i j : Fin 5) :
    (graph e).Adj (e i : V) (e j : V) ↔ (SimpleGraph.cycleGraph 5).Adj i j :=
  SimpleGraph.map_adj_apply

theorem adj01 (e : Fin 5 ≃ S) : (graph e).Adj (e 0 : V) (e 1 : V) :=
  (adj_iff e 0 1).mpr (by decide)

theorem adj12 (e : Fin 5 ≃ S) : (graph e).Adj (e 1 : V) (e 2 : V) :=
  (adj_iff e 1 2).mpr (by decide)

theorem adj23 (e : Fin 5 ≃ S) : (graph e).Adj (e 2 : V) (e 3 : V) :=
  (adj_iff e 2 3).mpr (by decide)

theorem adj34 (e : Fin 5 ≃ S) : (graph e).Adj (e 3 : V) (e 4 : V) :=
  (adj_iff e 3 4).mpr (by decide)

theorem adj04 (e : Fin 5 ≃ S) : (graph e).Adj (e 0 : V) (e 4 : V) :=
  (adj_iff e 0 4).mpr (by decide)

end JSP000838.LocalCycle

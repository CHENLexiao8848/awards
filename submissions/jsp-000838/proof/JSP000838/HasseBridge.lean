import JSP000838.ReverseEdge
import JSP000838.Reachability

namespace JSP000838

variable {V : Type*} {G : SimpleGraph V} {D : V → V → Prop}

/-- Robustness says that each original arc is a cover of the reachability order. -/
theorem IsRobustAcyclicOrientation.edge_iff_covBy
    (h : IsRobustAcyclicOrientation G D) (u v : V) :
    D u v ↔ @CovBy V (reachabilityOrder D h.2.1).toLT u v := by
  constructor
  · intro huv
    change Relation.TransGen D u v ∧
      (∀ ⦃w⦄, Relation.TransGen D u w → ¬ Relation.TransGen D w v)
    exact ⟨.single huv, fun {w} huw hwv => h.no_intermediate huv ⟨w, huw, hwv⟩⟩
  · exact covBy_reachabilityOrder_implies_edge h.2.1

/-- The graph of a robust acyclic orientation is precisely the Hasse graph of
its reachability partial order. This requires no finiteness assumption. -/
theorem IsRobustAcyclicOrientation.hasse_eq
    (h : IsRobustAcyclicOrientation G D) :
    @SimpleGraph.hasse V (reachabilityOrder D h.2.1).toPreorder = G := by
  ext u v
  change (@CovBy V (reachabilityOrder D h.2.1).toLT u v ∨
    @CovBy V (reachabilityOrder D h.2.1).toLT v u) ↔ G.Adj u v
  rw [← h.edge_iff_covBy u v, ← h.edge_iff_covBy v u]
  exact (h.1.1 u v).symm

theorem IsRobustAcyclicOrientation.isCoverGraph
    (h : IsRobustAcyclicOrientation G D) : IsCoverGraph G :=
  ⟨reachabilityOrder D h.2.1, h.hasse_eq⟩

/-- A graph excluded by the historical Hasse-diagram formulation has no JSP
robust acyclic orientation. -/
theorem not_robust_of_not_cover (hG : ¬ IsCoverGraph G) (D : V → V → Prop) :
    ¬ IsRobustAcyclicOrientation G D :=
  fun h => hG h.isCoverGraph

end JSP000838

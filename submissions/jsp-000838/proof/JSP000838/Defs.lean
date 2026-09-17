import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Logic.Relation

namespace JSP000838

variable {V : Type*}

/-- Every graph edge receives exactly one direction, and there are no extra arcs. -/
def IsOrientation (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  (∀ u v, G.Adj u v ↔ D u v ∨ D v u) ∧
  (∀ u v, D u v → ¬ D v u)

/-- Acyclicity forbids every nonempty directed closed walk. -/
def Acyclic (D : V → V → Prop) : Prop :=
  ∀ v, ¬ Relation.TransGen D v v

def IsAcyclicOrientation (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  IsOrientation G D ∧ Acyclic D

/-- Delete the arc `u → v` and insert the arc `v → u`. -/
def reverseEdge (D : V → V → Prop) (u v x y : V) : Prop :=
  (D x y ∧ ¬ (x = u ∧ y = v)) ∨ (x = v ∧ y = u)

/-- Acyclic initially and after reversing each individual oriented edge. -/
def IsRobustAcyclicOrientation (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  IsOrientation G D ∧ Acyclic D ∧
    ∀ u v, D u v → Acyclic (reverseEdge D u v)

/-- The given graph is the undirected Hasse diagram of a partial order on its vertices. -/
def IsCoverGraph (G : SimpleGraph V) : Prop :=
  ∃ P : PartialOrder V, @SimpleGraph.hasse V P.toPreorder = G

end JSP000838

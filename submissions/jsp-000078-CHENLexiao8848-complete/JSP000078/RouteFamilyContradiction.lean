import JSP000078.ConnectorClassCounts
import JSP000078.ExceptionalConnectorCount
import JSP000078.ConnectorSetAlternatives
import JSP000078.ConnectorGeometry

/-! # Contradiction from the classified endpoint-chord route lengths -/

namespace JSP000078

open SimpleGraph

/-- The numerical alternatives for a two-chord route family all contradict
the available odd lengths after its graph witnesses have been supplied. -/
theorem MarkedConnectorData.false_of_classified_routes (M : MarkedConnectorData)
    (R : Finset ℕ) (hconn : M.connectors = routeConnectorLengths R)
    (hpos : ∀ h ∈ R, 1 ≤ h)
    (hclass : 3 ≤ R.card ∨
      (∃ b, 1 ≤ b ∧ R = {b + 2, 3 * b + 2}) ∨
      (∃ b, 1 ≤ b ∧ R = {2, b + 2})) : False := by
  rcases connector_set_alternatives R hpos hclass with heven | hodd | ⟨b, hb, hbo, hR⟩
  · apply M.false_of_three_same_parity_connectors 0
    simpa only [hconn, Nat.zero_mod, ← Nat.even_iff] using heven
  · apply M.false_of_two_odd_connectors
    simpa only [hconn] using hodd
  · apply M.false_of_exceptional_connectors b hb hbo
    · rw [hconn, routeConnectorLengths, hR]
      simp
    · rw [hconn, routeConnectorLengths, hR]
      simp

/-- Genuine route witnesses supply the marked connector data; none of
the contradictory cardinality estimates is assumed in this graph theorem. -/
theorem impossible_of_classified_common_neighbor_routes
    {V : Type*} [Fintype V] {G : SimpleGraph V} {c A B : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (hA : A ∉ C.support) (hAB : A ≠ B)
    (X : Finset V) (hX : ∀ x ∈ X, x ∈ C.support ∧ G.Adj A x ∧ G.Adj B x)
    (R : Finset ℕ)
    (hR : ∀ h ∈ R, ∃ P : G.Walk A B, P.IsPath ∧ P.length = h ∧
      Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (k : ℕ) (hk : 2 ≤ k) (hcard : X.card = 2 * k - 1)
    (hK : (oddCycleLengths G).card = k)
    (hclass : 3 ≤ R.card ∨
      (∃ b, 1 ≤ b ∧ R = {b + 2, 3 * b + 2}) ∨
      (∃ b, 1 ≤ b ∧ R = {2, b + 2})) : False := by
  classical
  let M := markedConnectorDataOfRoutes hC hCO hA hAB X hX R hR k hk hcard hK
  apply M.false_of_classified_routes R rfl ?_ hclass
  intro h hh
  obtain ⟨P, _, hPL, _⟩ := hR h hh
  have hp : 0 < P.length := Nat.pos_of_ne_zero fun heq ↦ hAB (Walk.eq_of_length_eq_zero heq)
  omega

end JSP000078

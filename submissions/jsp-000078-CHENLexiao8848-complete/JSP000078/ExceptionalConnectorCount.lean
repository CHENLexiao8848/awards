import JSP000078.MarkedConnectorBalance
import JSP000078.BalancedMarkedGaps
import JSP000078.OddConnectorCount

/-!
# The odd-middle exceptional connector set

Connectors of lengths two and four force balanced marked-distance classes.
Their two short cycles at an odd minimum gap sit below all cycles formed
from an even distance and the remaining odd connector.
-/

namespace JSP000078

/-- The exceptional connector set containing `2`, `4`, and `b + 4` for
positive odd `b` cannot fit in the recorded `k` odd lengths. -/
theorem MarkedConnectorData.false_of_exceptional_connectors (H : MarkedConnectorData)
    (b : ℕ) (hb : 1 ≤ b) (hbOdd : Odd b)
    (hfour : 4 ∈ H.connectors) (hlast : b + 4 ∈ H.connectors) : False := by
  have hbalance : ∀ a ∈ H.marks,
      ((properDistances H.marks H.circumference a).filter Odd).card = H.parameter - 1 := by
    intro a ha
    exact (H.balanced_of_same_parity_connectors H.connector_two hfour (by decide) (by decide) ha).1
  obtain ⟨g, a, c, ha, hc, hac, hgc, hgpos, hgN, hgOdd, hmin⟩ :=
    exists_odd_minimum_marked_gap_of_card H.marks H.circumference H.parameter
      H.circumference_odd H.mark_bounds H.parameter_ge_two H.mark_card hbalance
  have hgD : g ∈ properDistances H.marks H.circumference a :=
    Finset.mem_image.mpr ⟨c, Finset.mem_erase.mpr ⟨hac.symm, hc⟩, hgc.symm⟩
  let S := (properDistances H.marks H.circumference a).filter Even
  have hScard : S.card = H.parameter - 1 :=
    (H.balanced_of_same_parity_connectors H.connector_two hfour (by decide) (by decide) ha).2
  have hSgt : ∀ d ∈ S, g < d := by
    intro d hd
    obtain ⟨hdD, hdEven⟩ := Finset.mem_filter.mp hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hdD
    obtain ⟨hxa, hxX⟩ := Finset.mem_erase.mp hx
    have hge : g ≤ d := hxd ▸ hmin a ha x hxX hxa.symm
    have hgmod := Nat.odd_iff.mp hgOdd
    have hdmod := Nat.even_iff.mp hdEven
    omega
  have hshift : ∀ d ∈ S, d + b + 4 ∈ H.lengths := by
    intro d hd
    obtain ⟨hdD, hdEven⟩ := Finset.mem_filter.mp hd
    have hodd : Odd (d + (b + 4)) := by
      have hdmod := Nat.even_iff.mp hdEven
      have hbmod := Nat.odd_iff.mp hbOdd
      rw [Nat.odd_iff]
      omega
    simpa only [Nat.add_assoc] using H.cycle_membership a ha d hdD (b + 4) hlast hodd
  have hsmallTwo : g + 2 ∈ H.lengths :=
    H.cycle_membership a ha g hgD 2 H.connector_two (hgOdd.add_even even_two)
  have hsmallFour : g + 4 ∈ H.lengths :=
    H.cycle_membership a ha g hgD 4 hfour (hgOdd.add_even (by decide))
  have hcount := exceptional_odd_connector_count S H.lengths g b H.parameter
    H.parameter_ge_two hb hScard hSgt hshift hsmallTwo hsmallFour
  have hcard := H.length_card
  omega

end JSP000078

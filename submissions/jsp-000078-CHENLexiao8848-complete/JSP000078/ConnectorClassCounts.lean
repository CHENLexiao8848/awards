import JSP000078.MarkedConnectorBalance
import JSP000078.BalancedMarkedGaps
import JSP000078.OddConnectorCount

/-!
# Excluding large connector parity classes

Balanced proper-distance classes contradict three same-parity connector
choices by a sumset count. Two odd connector choices also contradict
the smaller cycle supplied by a globally shortest, necessarily odd,
marked distance.
-/

namespace JSP000078

/-- Three connectors in any one parity class already exceed the
available number of odd lengths. -/
theorem MarkedConnectorData.false_of_three_same_parity_connectors
    (H : MarkedConnectorData) (r : ℕ)
    (hcard : 3 ≤ (H.connectors.filter fun t ↦ t % 2 = r % 2).card) : False := by
  let T := H.connectors.filter fun t ↦ t % 2 = r % 2
  change 3 ≤ T.card at hcard
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  have huH := (Finset.mem_filter.mp hu).1
  have hvH := (Finset.mem_filter.mp hv).1
  have hupar := (Finset.mem_filter.mp hu).2
  have hvpar := (Finset.mem_filter.mp hv).2
  have hsame : Even (u + v) := Nat.even_iff.mpr (by omega)
  have hmarks : H.marks.Nonempty := Finset.card_pos.mp (by
    have hk := H.parameter_ge_two
    have hm := H.mark_card
    omega)
  obtain ⟨a, ha⟩ := hmarks
  let D := properDistances H.marks H.circumference a
  have hbalanced := H.balanced_of_same_parity_connectors huH hvH huv hsame ha
  have hKcard := H.length_card
  have hk := H.parameter_ge_two
  by_cases hr : r % 2 = 0
  · let S := D.filter Odd
    have hScard : S.card = H.parameter - 1 := hbalanced.1
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hsum : ∀ d ∈ S, ∀ t ∈ T, d + t ∈ H.lengths := by
      intro d hd t ht
      obtain ⟨hdD, hdOdd⟩ := Finset.mem_filter.mp hd
      obtain ⟨htH, htpar⟩ := Finset.mem_filter.mp ht
      apply H.cycle_membership a ha d hdD t htH
      have hdmod := Nat.odd_iff.mp hdOdd
      rw [Nat.odd_iff]
      omega
    have hcount := card_add_two_le_of_three_connector_sumset S T H.lengths hS hcard hsum
    omega
  · let S := D.filter Even
    have hScard : S.card = H.parameter - 1 := hbalanced.2
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hsum : ∀ d ∈ S, ∀ t ∈ T, d + t ∈ H.lengths := by
      intro d hd t ht
      obtain ⟨hdD, hdEven⟩ := Finset.mem_filter.mp hd
      obtain ⟨htH, htpar⟩ := Finset.mem_filter.mp ht
      apply H.cycle_membership a ha d hdD t htH
      have hdmod := Nat.even_iff.mp hdEven
      rw [Nat.odd_iff]
      omega
    have hcount := card_add_two_le_of_three_connector_sumset S T H.lengths hS hcard hsum
    omega

/-- Two odd connectors force balanced marked distances. Their globally
smallest distance is odd, supplying a smaller odd cycle outside the
sumset formed with every even distance at that base. -/
theorem MarkedConnectorData.false_of_two_odd_connectors
    (H : MarkedConnectorData) (hoddcard : 2 ≤ (H.connectors.filter Odd).card) : False := by
  let T := H.connectors.filter Odd
  change 2 ≤ T.card at hoddcard
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  obtain ⟨huH, huOdd⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvH, hvOdd⟩ := Finset.mem_filter.mp hv
  have hsame : Even (u + v) := huOdd.add_odd hvOdd
  have hbalanced : ∀ a ∈ H.marks,
      ((properDistances H.marks H.circumference a).filter Odd).card = H.parameter - 1 := by
    intro a ha
    exact (H.balanced_of_same_parity_connectors huH hvH huv hsame ha).1
  obtain ⟨g, a, b, ha, hb, hab, hg, _, _, hgOdd, hmin⟩ :=
    exists_odd_minimum_marked_gap_of_card H.marks H.circumference H.parameter
      H.circumference_odd H.mark_bounds H.parameter_ge_two H.mark_card hbalanced
  have hgD : g ∈ properDistances H.marks H.circumference a :=
    Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨hab.symm, hb⟩, hg.symm⟩
  let S := (properDistances H.marks H.circumference a).filter Even
  have hScard : S.card = H.parameter - 1 :=
    (H.balanced_of_same_parity_connectors huH hvH huv hsame ha).2
  have hS : ∀ d ∈ S, g < d := by
    intro d hd
    obtain ⟨hdD, hdEven⟩ := Finset.mem_filter.mp hd
    obtain ⟨z, hz, hzd⟩ := Finset.mem_image.mp hdD
    obtain ⟨hza, hzH⟩ := Finset.mem_erase.mp hz
    have hgd : g ≤ d := hzd ▸ hmin a ha z hzH hza.symm
    have hgmod := Nat.odd_iff.mp hgOdd
    have hdmod := Nat.even_iff.mp hdEven
    omega
  have hT : ∀ t ∈ T, 3 ≤ t := by
    intro t ht
    obtain ⟨htH, htOdd⟩ := Finset.mem_filter.mp ht
    have ht2 := H.connector_pos t htH
    have htmod := Nat.odd_iff.mp htOdd
    omega
  have hsum : ∀ d ∈ S, ∀ t ∈ T, d + t ∈ H.lengths := by
    intro d hd t ht
    obtain ⟨hdD, hdEven⟩ := Finset.mem_filter.mp hd
    obtain ⟨htH, htOdd⟩ := Finset.mem_filter.mp ht
    exact H.cycle_membership a ha d hdD t htH (hdEven.add_odd htOdd)
  have hsmall : g + 2 ∈ H.lengths :=
    H.cycle_membership a ha g hgD 2 H.connector_two (hgOdd.add_even even_two)
  have hcount := odd_connector_count S T H.lengths g H.parameter H.parameter_ge_two
    hScard hoddcard hS hT hsum hsmall
  have hKcard := H.length_card
  omega

end JSP000078

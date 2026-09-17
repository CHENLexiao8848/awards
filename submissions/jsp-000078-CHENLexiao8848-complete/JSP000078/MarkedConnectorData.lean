import JSP000078.CyclicDistanceSets

/-! # Marked-cycle and outside connector data for the two-chord exception -/

namespace JSP000078

/-- Every selected directed marked distance combines with each selected
connector length when the result is odd. Length two is always available
through a single outside endpoint. -/
structure MarkedConnectorData where
  circumference : ℕ
  parameter : ℕ
  marks : Finset ℕ
  lengths : Finset ℕ
  connectors : Finset ℕ
  circumference_odd : Odd circumference
  parameter_ge_two : 2 ≤ parameter
  mark_bounds : ∀ x ∈ marks, x < circumference
  mark_card : marks.card = 2 * parameter - 1
  length_card : lengths.card = parameter
  connector_two : 2 ∈ connectors
  connector_pos : ∀ t ∈ connectors, 2 ≤ t
  cycle_membership : ∀ a ∈ marks, ∀ d ∈ properDistances marks circumference a,
    ∀ t ∈ connectors, Odd (d + t) → d + t ∈ lengths

end JSP000078

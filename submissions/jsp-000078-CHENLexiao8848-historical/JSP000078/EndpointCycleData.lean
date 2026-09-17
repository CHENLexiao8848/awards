import JSP000078.Basic

/-!
# Length data for Gyárfás's endpoint-neighbor counting argument

The structure records the individual cycle witnesses and their maximality
constraints, rather than assuming any conclusion about how many lengths occur.
The arithmetic count and the graph realization are separate proof obligations.
-/

namespace JSP000078

/-- Exact length constraints extracted from a longest odd cycle, an outside
path and its incident chords, and distinct attachment arcs on the cycle. -/
structure EndpointCycleData where
  bound : ℕ
  tailLength : ℕ
  outsideLengths : Finset ℕ
  attachmentLengths : Finset ℕ
  oddLengths : Finset ℕ
  bound_odd : Odd bound
  attachment_nonempty : attachmentLengths.Nonempty
  attachment_bounds : ∀ t ∈ attachmentLengths, 1 ≤ t ∧ t < bound
  outside_lower : ∀ u ∈ outsideLengths, tailLength + 1 ≤ u
  outside_min_mem : tailLength + 1 ∈ outsideLengths
  max_odd : ∀ n ∈ oddLengths, n ≤ bound
  low_cycle : ∀ u ∈ outsideLengths, Even (u - tailLength) → u - tailLength + 1 ∈ oddLengths
  direct_cycle : ∀ u ∈ outsideLengths, ∀ t ∈ attachmentLengths,
    Odd (u + t + 2) → u + t + 2 ∈ oddLengths
  complementary_cycle : ∀ u ∈ outsideLengths, ∀ t ∈ attachmentLengths,
    Odd (u + (bound - t) + 2) → u + (bound - t) + 2 ∈ oddLengths

/-- The remaining pure counting implication uses individual cycle-length
constraints, with no cardinal lower bound among its assumptions. -/
def HistoricalEndpointLengthCount : Prop :=
  ∀ D : EndpointCycleData,
    D.outsideLengths.card - 1 + (D.attachmentLengths.card + 1) / 2 ≤ D.oddLengths.card

end JSP000078

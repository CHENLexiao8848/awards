import JSP000078.Basic

/-! # Length data for two outside endpoints with common cycle attachments -/

namespace JSP000078

/-- For each desired-parity arc length, the same outside vertex supplies
a cycle two edges longer, and the outside path supplies a second cycle
longer by its path length. Individual memberships are required only when odd. -/
structure CommonAttachmentData where
  oddLengths : Finset ℕ
  pathLength : ℕ
  path_pos : 1 ≤ pathLength
  arcLengths : Finset ℕ
  arc_nonempty : arcLengths.Nonempty
  arc_pos : ∀ t ∈ arcLengths, 1 ≤ t
  direct : ∀ t ∈ arcLengths, Odd (t + 2) → t + 2 ∈ oddLengths
  mixed : ∀ t ∈ arcLengths, Odd (t + pathLength + 2) → t + pathLength + 2 ∈ oddLengths
  shared : Odd (pathLength + 2) → pathLength + 2 ∈ oddLengths

end JSP000078

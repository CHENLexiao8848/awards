import JSP000078.OddClosedWalk
import JSP000078.MathlibBridge

/-! # The no-odd-length base case independent of the numerical theorem -/

namespace JSP000078

open SimpleGraph

/-- A finite graph with an empty odd-length set is two-colorable, using
odd closed-walk extraction rather than the chromatic bound being proved. -/
theorem isBipartite_of_odd_lengths_empty_independent {V : Type*} [Fintype V]
    {G : SimpleGraph V} (h : oddCycleLengths G = ∅) : G.IsBipartite := by
  apply isBipartite_of_no_odd_cycle
  exact oddCycleLengths_eq_empty_iff.mp h

end JSP000078

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Ring.Parity

/-!
# Distinct odd cycle lengths

The finite set below records lengths of actual simple cycles. Membership
does not depend on the number of cycles of a given length.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Every simple cycle has at most as many edges as the graph has vertices. -/
theorem cycle_length_le_card {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.length ≤ Fintype.card V := by
  have ht := hp.isPath_tail.length_lt
  rw [Walk.length_tail] at ht
  omega

/-- The distinct odd lengths of simple cycles in a finite graph. -/
noncomputable def oddCycleLengths : Finset ℕ := by
  classical
  exact (Finset.range (Fintype.card V + 1)).filter fun n =>
    Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n

/-- Membership describes actual odd simple cycles, without truncation. -/
theorem mem_oddCycleLengths {n : ℕ} :
    n ∈ oddCycleLengths G ↔
      Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n := by
  classical
  simp only [oddCycleLengths, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · rintro ⟨hn, v, p, hp, hpn⟩
    refine ⟨?_, hn, v, p, hp, hpn⟩
    rw [← hpn]
    exact Nat.lt_succ_of_le (cycle_length_le_card G hp)

end JSP000078

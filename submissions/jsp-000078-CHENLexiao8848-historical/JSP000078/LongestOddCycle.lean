import JSP000078.MathlibBridge
import Mathlib.Data.Finset.Max

/-! # Longest odd cycles in finite graphs -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A cycle is a longest odd cycle when it is odd and bounds every odd cycle length. -/
def IsLongestOddCycle {c : V} (C : G.Walk c c) : Prop :=
  C.IsCycle ∧ Odd C.length ∧
    ∀ (d : V) (D : G.Walk d d), D.IsCycle → Odd D.length → D.length ≤ C.length

/-- A nonempty set of odd cycle lengths has a cycle realizing its maximum. -/
theorem exists_longest_odd_cycle (h : (oddCycleLengths G).Nonempty) :
    ∃ (c : V) (C : G.Walk c c), IsLongestOddCycle C := by
  obtain ⟨hodd, c, C, hC, hlen⟩ :=
    (mem_oddCycleLengths G).mp ((oddCycleLengths G).max'_mem h)
  refine ⟨c, C, hC, hlen ▸ hodd, ?_⟩
  intro d D hD hoddD
  rw [hlen]
  exact (oddCycleLengths G).le_max' D.length
    ((mem_oddCycleLengths G).mpr ⟨hoddD, d, D, hD, rfl⟩)

end JSP000078

import JSP000078.GyarfasLemmaOne

/-!
# Consequences of having exactly one odd cycle length

All odd simple cycles then have the same length, so each is a longest
odd cycle. Gyárfás's two-link Lemma 1 rules out an odd cycle disjoint
from any one of them in a 2-connected graph.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- If only one distinct odd cycle length occurs, any two odd simple
cycles have equal lengths. -/
theorem odd_cycle_lengths_equal_of_card_one
    (hK : (oddCycleLengths G).card = 1)
    {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : C.IsCycle) (hCO : Odd C.length) (hD : D.IsCycle) (hDO : Odd D.length) :
    D.length = C.length := by
  obtain ⟨n, hn⟩ := Finset.card_eq_one.mp hK
  have hCmem := (mem_oddCycleLengths G).mpr ⟨hCO, c, C, hC, rfl⟩
  have hDmem := (mem_oddCycleLengths G).mpr ⟨hDO, d, D, hD, rfl⟩
  have hCn : C.length = n := by simpa only [hn, Finset.mem_singleton] using hCmem
  have hDn : D.length = n := by simpa only [hn, Finset.mem_singleton] using hDmem
  exact hDn.trans hCn.symm

/-- Every odd simple cycle is longest when the set of odd lengths is
a singleton. -/
theorem isLongestOddCycle_of_card_one
    (hK : (oddCycleLengths G).card = 1) {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) : IsLongestOddCycle C := by
  refine ⟨hC, hCO, ?_⟩
  intro d D hD hDO
  exact (odd_cycle_lengths_equal_of_card_one hK hC hCO hD hDO).le

/-- In a 2-connected graph with one odd cycle length, every simple
cycle vertex-disjoint from a given odd cycle is even. -/
theorem every_cycle_disjoint_from_cycle_even
    (hG : TwoVertexConnected G) (hK : (oddCycleLengths G).card = 1)
    {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : C.IsCycle) (hCO : Odd C.length) (hD : D.IsCycle)
    (hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support}) : Even D.length := by
  apply Nat.not_odd_iff_even.mp
  intro hDO
  have hlong := isLongestOddCycle_of_card_one hK hC hCO
  have hlt := outside_odd_cycle_length_lt_longest hG hlong hD hDO hCD
  have heq := odd_cycle_lengths_equal_of_card_one hK hC hCO hD hDO
  omega

end JSP000078

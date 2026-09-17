import JSP000078.HistoricalLinking
import JSP000078.OddCycleSplice
import JSP000078.LongestOddCycle

/-!
# Gyárfás's Lemma 1

An odd cycle disjoint from a longest odd cycle is strictly shorter. The
published proof uses two disjoint links and complementary odd-cycle splices.
Both constructions and their exact length sum are proved in the imports.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Gyárfás (1992), Lemma 1, printed pages 42-43. -/
theorem outside_odd_cycle_length_lt_longest
    (hG : TwoVertexConnected G) {c d : V} {C : G.Walk c c} {D : G.Walk d d}
    (hC : IsLongestOddCycle C) (hD : D.IsCycle) (hDO : Odd D.length)
    (hCD : Disjoint {v | v ∈ C.support} {v | v ∈ D.support}) :
    D.length < C.length := by
  obtain ⟨a₁, a₂, b₁, b₂, p, q, hp, hq, ha₁, ha₂, hb₁, hb₂, hpq,
      hpC, hqC, hpD, hqD⟩ :=
    twoDisjointCycleLinks_of_twoVertexConnected hG c d C D hC.1 hD hCD
  obtain ⟨E, F, hE, hF, hEO, hFO, hlen⟩ :=
    exists_two_odd_cycles_of_two_links hC.1 hD hC.2.1 hDO hCD hp hq
      ha₁ ha₂ hb₁ hb₂ hpq hpC hqC hpD hqD
  have hEL := hC.2.2 a₁ E hE hEO
  have hFL := hC.2.2 a₁ F hF hFO
  have hab : a₁ ≠ b₁ := fun h ↦ Set.disjoint_left.mp hCD ha₁ (h ▸ hb₁)
  have hpPos : 0 < p.length :=
    Nat.pos_of_ne_zero fun h ↦ hab (Walk.eq_of_length_eq_zero h)
  omega

end JSP000078

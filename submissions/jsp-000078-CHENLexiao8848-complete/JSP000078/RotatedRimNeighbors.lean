import JSP000078.CycleRotationPositions
import JSP000078.OddCyclePairNeighbors

/-!
# Rim-neighbor pairs after rotating a cycle

The first and penultimate vertices of a rotated cycle are the two rim
neighbors of its new base. Their unordered pair determines that base
on a simple cycle of length at least five.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A rotated vertex at any proper index has the corresponding modular
canonical position, for an arbitrary supported choice of new base. -/
theorem getVert_rotate_supported {c y : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hy : y ∈ C.support) {j : ℕ} (hj : j < C.length) :
    (C.rotate y hy).getVert j = C.getVert ((cyclePosition C y + j) % C.length) := by
  have hgeneral (i : ℕ) (hi : i < C.length) (z : V) (hz : z ∈ C.support)
      (hiz : C.getVert i = z) :
      (C.rotate z hz).getVert j = C.getVert ((i + j) % C.length) := by
    subst z
    exact getVert_rotate_getVert hC hi hj
  exact hgeneral _ (cyclePosition_lt hC hy) y hy (getVert_cyclePosition C hy)

/-- The first and penultimate vertices after rotation are the successor
and predecessor in the original canonical coordinates. -/
theorem rotated_rim_pair_eq {c y : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hy : y ∈ C.support) :
    s((C.rotate y hy).getVert 1, (C.rotate y hy).getVert (C.length - 1)) =
      s(C.getVert ((cyclePosition C y + 1) % C.length),
        C.getVert ((cyclePosition C y + C.length - 1) % C.length)) := by
  have hN := hC.three_le_length
  rw [getVert_rotate_supported hC hy (by omega : 1 < C.length),
    getVert_rotate_supported hC hy (by omega : C.length - 1 < C.length)]
  have heq : cyclePosition C y + (C.length - 1) = cyclePosition C y + C.length - 1 := by omega
  rw [heq]

/-- Equal unordered rim-neighbor pairs identify their rotated bases
on every simple cycle of length at least five. -/
theorem rotated_rim_neighbors_injective {c y z : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hN : 5 ≤ C.length)
    (hy : y ∈ C.support) (hz : z ∈ C.support)
    (hpair : s((C.rotate y hy).getVert 1, (C.rotate y hy).getVert (C.length - 1)) =
      s((C.rotate z hz).getVert 1, (C.rotate z hz).getVert (C.length - 1))) :
    y = z := by
  rw [rotated_rim_pair_eq hC hy, rotated_rim_pair_eq hC hz] at hpair
  have hreverse :
      s(C.getVert ((cyclePosition C y + C.length - 1) % C.length),
        C.getVert ((cyclePosition C y + 1) % C.length)) =
      s(C.getVert ((cyclePosition C z + C.length - 1) % C.length),
        C.getVert ((cyclePosition C z + 1) % C.length)) := by
    exact Sym2.eq_swap.trans (hpair.trans Sym2.eq_swap)
  have hpos := cycle_rim_neighbors_injective hC hN
    (cyclePosition_lt hC hy) (cyclePosition_lt hC hz) hreverse
  exact cyclePosition_injOn C hy hz hpos

end JSP000078

import JSP000078.CyclePositions

/-!
# Coordinates after rotating a simple cycle

Rotating to position `i` adds `i` to subsequent positions modulo the cycle
length. The canonical first-occurrence position then recovers that residue.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Rotating a simple cycle to its vertex at position `i` shifts every
nonterminal position by `i` modulo the cycle length. -/
theorem getVert_rotate_getVert [DecidableEq V] {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    {i j : ℕ} (hi : i < C.length) (hj : j < C.length) :
    (C.rotate (C.getVert i) (C.getVert_mem_support i)).getVert j =
      C.getVert ((i + j) % C.length) := by
  have hidx : C.support.idxOf (C.getVert i) = i := by
    apply hC.getVert_injOn'
    · change C.support.idxOf (C.getVert i) ≤ C.length - 1
      by_cases hbase : C.getVert i = c
      · rw [hbase, ← Walk.cons_tail_support C, List.idxOf_cons_self]
        omega
      · have ht := C.length_takeUntil_lt_length (C.getVert_mem_support i) hbase
        rw [Walk.length_takeUntil] at ht
        omega
    · change i ≤ C.length - 1
      omega
    · exact C.getVert_support_idxOf (C.getVert_mem_support i)
  simp only [Walk.rotate, Walk.getVert_append, Walk.dropUntil_eq_drop,
    Walk.takeUntil_eq_take, Walk.length_copy, Walk.getVert_copy, Walk.drop_length,
    Walk.drop_getVert, Walk.take_getVert, hidx]
  split_ifs with hbefore
  · rw [Nat.mod_eq_of_lt (by omega : i + j < C.length)]
  · have hrem : (i + j) % C.length = i + j - C.length := by
      rw [Nat.mod_eq_sub_mod (by omega : C.length ≤ i + j)]
      exact Nat.mod_eq_of_lt (by omega)
    have hmin : min i (j - (C.length - i)) = j - (C.length - i) :=
      Nat.min_eq_right (by omega)
    rw [hmin, hrem]
    congr 1
    omega

/-- The original cycle coordinate of a vertex in a rotated cycle is the
sum of the old base coordinate and the new coordinate modulo the length. -/
theorem cyclePosition_getVert_rotate [DecidableEq V] {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {i j : ℕ} (hi : i < C.length) (hj : j < C.length) :
    cyclePosition C ((C.rotate (C.getVert i) (C.getVert_mem_support i)).getVert j) =
      (i + j) % C.length := by
  rw [getVert_rotate_getVert hC hi hj]
  apply cyclePosition_getVert hC
  exact Nat.mod_lt _ (by have := hC.three_le_length; omega)

/-- Rotation transports the vertex two steps before the new base to the
corresponding residue in the old cycle coordinates. -/
theorem getVert_rotate_two_before [DecidableEq V] {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) {i : ℕ} (hi : i < C.length) :
    (C.rotate (C.getVert i) (C.getVert_mem_support i)).getVert (C.length - 2) =
      C.getVert ((i + C.length - 2) % C.length) := by
  have hlen := hC.three_le_length
  have h := getVert_rotate_getVert hC hi (show C.length - 2 < C.length by omega)
  simpa only [show i + (C.length - 2) = i + C.length - 2 by omega] using h

/-- Canonical original position of the vertex two steps before a rotated
base. This is the natural-number form of the residue closure step. -/
theorem cyclePosition_getVert_rotate_two_before [DecidableEq V]
    {c : V} {C : G.Walk c c} (hC : C.IsCycle) {i : ℕ} (hi : i < C.length) :
    cyclePosition C
      ((C.rotate (C.getVert i) (C.getVert_mem_support i)).getVert (C.length - 2)) =
      (i + C.length - 2) % C.length := by
  rw [getVert_rotate_two_before hC hi]
  apply cyclePosition_getVert hC
  exact Nat.mod_lt _ (by have := hC.three_le_length; omega)

end JSP000078

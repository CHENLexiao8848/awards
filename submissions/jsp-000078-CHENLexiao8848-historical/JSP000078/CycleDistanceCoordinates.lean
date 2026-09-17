import JSP000078.CyclicDistanceSets
import JSP000078.CycleRotationPositions

/-!
# Cyclic distances as rotated cycle coordinates

The position of a vertex after rotating to another vertex is the forward
cyclic distance between their original canonical positions.
-/

namespace JSP000078

open SimpleGraph

/-- Adding a forward cyclic distance to its base recovers the target
canonical position modulo the circumference. -/
theorem add_cyclicDistance_mod {N i j : ℕ} (hi : i < N) (hj : j < N) :
    (i + cyclicDistance N i j) % N = j := by
  by_cases hij : i ≤ j
  · rw [cyclicDistance_eq_sub hj hij, Nat.add_sub_of_le hij, Nat.mod_eq_of_lt hj]
  · rw [cyclicDistance_eq_wrap hi (by omega : j < i)]
    have hsum : i + (N + j - i) = j + N := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- A target cycle position, expressed after rotating to another indexed
vertex, is their forward cyclic distance. -/
theorem cyclePosition_rotate_getVert {c : V} {C : G.Walk c c} (hC : C.IsCycle)
    {i j : ℕ} (hi : i < C.length) (hj : j < C.length) :
    cyclePosition (C.rotate (C.getVert i) (C.getVert_mem_support i)) (C.getVert j) =
      cyclicDistance C.length i j := by
  let R := C.rotate (C.getVert i) (C.getVert_mem_support i)
  have hR : R.IsCycle := hC.rotate (C.getVert_mem_support i)
  have hlen : R.length = C.length := C.length_rotate _ _
  have hd : cyclicDistance C.length i j < C.length :=
    cyclicDistance_lt (by have := hC.three_le_length; omega)
  have hget : R.getVert (cyclicDistance C.length i j) = C.getVert j := by
    rw [getVert_rotate_getVert hC hi hd, add_cyclicDistance_mod hi hj]
  have hpos := cyclePosition_getVert hR (show cyclicDistance C.length i j < R.length by omega)
  simpa only [hget] using hpos

/-- Canonical coordinates of arbitrary supported vertices transform by
forward cyclic distance under rotation. No spanning-cycle hypothesis is needed. -/
theorem cyclePosition_rotate {c x y : V} {C : G.Walk c c} (hC : C.IsCycle)
    (hx : x ∈ C.support) (hy : y ∈ C.support) :
    cyclePosition (C.rotate x hx) y =
      cyclicDistance C.length (cyclePosition C x) (cyclePosition C y) := by
  have hgeneral (i j : ℕ) (hi : i < C.length) (hj : j < C.length)
      (u v : V) (hu : u ∈ C.support) (hiu : C.getVert i = u) (hjv : C.getVert j = v) :
      cyclePosition (C.rotate u hu) v = cyclicDistance C.length i j := by
    subst u
    subst v
    exact cyclePosition_rotate_getVert hC hi hj
  exact hgeneral _ _ (cyclePosition_lt hC hx) (cyclePosition_lt hC hy) x y hx
    (getVert_cyclePosition C hx) (getVert_cyclePosition C hy)

end JSP000078

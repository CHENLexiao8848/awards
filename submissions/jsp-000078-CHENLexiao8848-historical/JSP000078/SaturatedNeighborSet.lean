import JSP000078.CycleRotationPositions
import JSP000078.OddCyclicClosure

/-!
# Saturated neighbor sets on an odd cycle

The selected-neighbor parity count supplies a predecessor two steps before
every selected vertex. In cyclic coordinates this is closure under
subtraction by two; on an odd cycle the selected set is therefore the
whole cycle support.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The canonical coordinate of the two-step predecessor, read after
rotating to `x`, is the coordinate of `x` minus two modulo the cycle length. -/
theorem cyclePosition_rotate_predecessor_zmod {c x : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hx : x ∈ C.support) :
    (cyclePosition C ((C.rotate x hx).getVert (C.length - 2)) : ZMod C.length) =
      (cyclePosition C x : ZMod C.length) - 2 := by
  have hN := hC.three_le_length
  have hgeneral (i : ℕ) (hi : i < C.length) (y : V) (hy : y ∈ C.support)
      (hiy : C.getVert i = y) :
      (C.rotate y hy).getVert (C.length - 2) =
        C.getVert ((i + (C.length - 2)) % C.length) := by
    subst y
    exact getVert_rotate_getVert hC hi (by omega)
  have hshift : (C.rotate x hx).getVert (C.length - 2) =
      C.getVert ((cyclePosition C x + (C.length - 2)) % C.length) := by
    exact hgeneral _ (cyclePosition_lt hC hx) x hx (getVert_cyclePosition C hx)
  rw [hshift, cyclePosition_getVert hC (Nat.mod_lt _ (by omega)), ZMod.natCast_mod]
  rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ C.length),
    Nat.cast_two, ZMod.natCast_self]
  ring

/-- A nonempty set on an odd simple cycle containing the predecessor
two positions before each of its vertices is the whole cycle vertex set. -/
theorem cycle_subset_eq_support_of_predecessor_closed {c : V} {C : G.Walk c c}
    (hC : C.IsCycle) (hCO : Odd C.length) (X : Finset V) (hXne : X.Nonempty)
    (hX : ∀ x ∈ X, x ∈ C.support)
    (hpred : ∀ x (hx : x ∈ X),
      (C.rotate x (hX x hx)).getVert (C.length - 2) ∈ X) :
    X = C.support.toFinset := by
  classical
  have hN := hC.three_le_length
  let : NeZero C.length := ⟨by omega⟩
  let S : Finset (ZMod C.length) :=
    X.image fun x ↦ (cyclePosition C x : ZMod C.length)
  have hSne : S.Nonempty := hXne.image _
  have hSclosed : ∀ z ∈ S, z - 2 ∈ S := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    exact ⟨(C.rotate x (hX x hx)).getVert (C.length - 2), hpred x hx,
      cyclePosition_rotate_predecessor_zmod hC (hX x hx)⟩
  have hSuniv := odd_cyclic_sub_two_closed_eq_univ hCO S hSne hSclosed
  apply Finset.ext
  intro w
  constructor
  · intro hw
    exact List.mem_toFinset.mpr (hX w hw)
  · intro hw
    have hwC := List.mem_toFinset.mp hw
    have hcoord : (cyclePosition C w : ZMod C.length) ∈ S := by
      rw [hSuniv]
      exact Finset.mem_univ _
    obtain ⟨x, hx, hcast⟩ := Finset.mem_image.mp hcoord
    have hpos : cyclePosition C x = cyclePosition C w := by
      have hval := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast_of_lt (cyclePosition_lt hC (hX x hx)),
        ZMod.val_natCast_of_lt (cyclePosition_lt hC hwC)] using hval
    have hxw := cyclePosition_injOn C (hX x hx) hwC hpos
    exact hxw ▸ hx

end JSP000078

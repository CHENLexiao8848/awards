import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-!
# Closure under moving two positions around an odd cycle

A nonempty set of positions on an odd cycle that contains the position
two steps before each of its members contains every position. This is
the finite cyclic consequence of the saturated odd-distance count in
Gyárfás's Lemma 5.
-/

namespace JSP000078

/-- On an odd cyclic index set, closure under subtraction by two forces
a nonempty finite set to contain every index. -/
theorem odd_cyclic_sub_two_closed_eq_univ
    {N : ℕ} [NeZero N] (hN : Odd N)
    (S : Finset (ZMod N)) (hS : S.Nonempty)
    (hclosed : ∀ x ∈ S, x - 2 ∈ S) : S = Finset.univ := by
  obtain ⟨m, hm⟩ := hN
  obtain ⟨x, hx⟩ := hS
  have hiter (n : ℕ) : x - 2 * (n : ZMod N) ∈ S := by
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      convert hclosed _ ih using 1
      push_cast
      ring
  have hmod : (2 : ZMod N) * (m : ZMod N) + 1 = 0 := by
    calc
      (2 : ZMod N) * (m : ZMod N) + 1 = ((2 * m + 1 : ℕ) : ZMod N) := by
        push_cast
        rfl
      _ = (N : ZMod N) := by rw [hm]
      _ = 0 := ZMod.natCast_self N
  have hinv : (2 : ZMod N) * (-(m : ZMod N)) = 1 := by
    calc
      (2 : ZMod N) * (-(m : ZMod N)) = 1 - (2 * (m : ZMod N) + 1) := by ring
      _ = 1 := by rw [hmod]; ring
  apply Finset.eq_univ_of_forall
  intro y
  let z : ZMod N := (x - y) * (-(m : ZMod N))
  have hsolve : x - 2 * (z.val : ZMod N) = y := by
    rw [ZMod.natCast_zmod_val]
    calc
      x - 2 * z = x - (x - y) * (2 * (-(m : ZMod N))) := by dsimp [z]; ring
      _ = y := by rw [hinv]; ring
  exact hsolve ▸ hiter z.val

end JSP000078

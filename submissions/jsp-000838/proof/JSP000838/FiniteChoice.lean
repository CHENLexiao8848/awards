import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

namespace JSP000838

/-- If the union bound is strict, one assignment agrees somewhere with each
prescribed assignment. The forbidden families are counted by an explicit
finite surjection, without probability or an external counting oracle. -/
theorem exists_assignment_hits_all
    {I Orders A : Type*} [Fintype I] [Fintype Orders] [Fintype A]
    (forbidden : Orders → I → A)
    (hbound : Fintype.card Orders * (Fintype.card A - 1) ^ Fintype.card I <
      Fintype.card A ^ Fintype.card I) :
    ∃ f : I → A, ∀ o : Orders, ∃ i : I, f i = forbidden o i := by
  classical
  by_contra h
  push Not at h
  let Bad (o : Orders) := ∀ i : I, {a : A // a ≠ forbidden o i}
  let forget : (Σ o : Orders, Bad o) → (I → A) := fun p i => (p.2 i).1
  have hsurj : Function.Surjective forget := by
    intro f
    obtain ⟨o, ho⟩ := h f
    exact ⟨⟨o, fun i => ⟨f i, ho i⟩⟩, rfl⟩
  have hcard := Fintype.card_le_of_surjective forget hsurj
  have hbad (o : Orders) : Fintype.card (Bad o) =
      (Fintype.card A - 1) ^ Fintype.card I := by
    simp [Bad, Fintype.card_pi, Fintype.card_subtype_compl]
  have hle : Fintype.card A ^ Fintype.card I ≤
      Fintype.card Orders * (Fintype.card A - 1) ^ Fintype.card I := by
    simpa [Fintype.card_sigma, hbad, Fintype.card_fun] using hcard
  exact (not_le_of_gt hbound) hle

/-- The version with numbered choices used by the finite construction. -/
theorem exists_fin_assignment_hits_all
    {I Orders : Type*} [Fintype I] [Fintype Orders] {k : ℕ}
    (forbidden : Orders → I → Fin k)
    (hbound : Fintype.card Orders * (k - 1) ^ Fintype.card I <
      k ^ Fintype.card I) :
    ∃ f : I → Fin k, ∀ o : Orders, ∃ i : I, f i = forbidden o i := by
  exact exists_assignment_hits_all forbidden (by simpa using hbound)

/-- The fixed numerical estimate is small enough for kernel-checked arithmetic. -/
theorem choice_ratio_bound : 2 * 119 ^ 120 < (120 : ℕ) ^ 120 := by
  norm_num

/-- Amplify the fixed estimate without evaluating the large exponents. -/
theorem choice_count_bound (n : ℕ) (hn : n ≠ 0) :
    (2 ^ 96) ^ n * 119 ^ (120 * 96 * n) < (120 : ℕ) ^ (120 * 96 * n) := by
  have hpow := pow_lt_pow_left₀ choice_ratio_bound (Nat.zero_le _)
    (show 96 * n ≠ 0 from Nat.mul_ne_zero (by decide) hn)
  simpa only [mul_pow, pow_mul, Nat.mul_assoc] using hpow

/-- The parameters used by the finite Nešetřil–Rödl counting argument. -/
theorem choice_count_bound_large :
    (2 ^ 96) ^ (2 ^ 96) * 119 ^ (120 * 96 * (2 ^ 96)) <
      (120 : ℕ) ^ (120 * 96 * (2 ^ 96)) := by
  exact choice_count_bound (2 ^ 96) (pow_ne_zero _ (by decide))

/-- Transport the fixed estimate through symbolic parameters. Keeping these
parameters abstract avoids reducing astronomically large natural powers. -/
theorem choice_count_bound_parameters (N M : ℕ)
    (hN : N = 2 ^ 96) (hM : M = 120 * 96 * N) :
    N ^ N * 119 ^ M < 120 ^ M := by
  subst M
  subst N
  exact choice_count_bound_large

end JSP000838

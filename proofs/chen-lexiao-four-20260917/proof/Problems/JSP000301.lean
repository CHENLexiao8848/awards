import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000301: consecutive powerful numbers need not include a square

This formalizes the yes/no version explicitly specified in the prize catalog.
The witnesses are 12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2.
It does not claim a counting theorem for infinitely many such pairs.
Source: https://doi.org/10.1080/00150517.1976.12430562
-/

namespace JSP000301

/-- A positive integer is powerful when every prime divisor divides it at least twice. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem powerful_12167 : Powerful 12167 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hd
  have hd23 : p ∣ 23 := hp.dvd_of_dvd_pow (show p ∣ 23 ^ 3 by norm_num at hd ⊢; exact hd)
  have he : p = 23 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd23
  subst p
  norm_num

theorem powerful_12168 : Powerful 12168 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hd
  have hf : p ∣ 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num at hd ⊢; exact hd
  rcases hp.dvd_mul.mp hf with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h)
      subst p
      norm_num
    · have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h)
      subst p
      norm_num
  · have he : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h)
    subst p
    norm_num

private theorem not_square_between (n : ℕ) (lo : 110 ^ 2 < n) (hi : n < 111 ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨a, ha⟩
  rcases le_or_gt a 110 with h | h
  · nlinarith
  · have : 111 ≤ a := by omega
    nlinarith

theorem not_isSquare_12167 : ¬ IsSquare (12167 : ℕ) :=
  not_square_between 12167 (by norm_num) (by norm_num)

theorem not_isSquare_12168 : ¬ IsSquare (12168 : ℕ) :=
  not_square_between 12168 (by norm_num) (by norm_num)

/-- Complete counterexample to the catalog question. -/
theorem exists_consecutive_powerful_not_square :
    ∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  exact ⟨12167, powerful_12167, powerful_12168, not_isSquare_12167, not_isSquare_12168⟩

theorem conjecture_false :
    ¬ (∀ n : ℕ, Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases h 12167 powerful_12167 powerful_12168 with hs | hs
  · exact not_isSquare_12167 hs
  · exact not_isSquare_12168 hs

end JSP000301

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace JSP000633

/-- Optimizing the alteration inequality at twice the maximum admissible density. -/
theorem polynomial_of_alteration (n m k : ℝ) (hn : 0 < n) (hm : 1 ≤ m) (hk : 0 ≤ k)
    (h : ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      p * n - k * n * p ^ 3 - k * n ^ 2 * p ^ 4 ≤ m) :
    n ^ 2 ≤ (4 + 24 * k) * m ^ 3 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  have hm3 : 0 ≤ m ^ 3 := by positivity
  have hcube : m ^ 2 ≤ m ^ 3 := by nlinarith [mul_nonneg hm2 (sub_nonneg.mpr hm)]
  by_cases hnm : n ≤ 2 * m
  · have hs : n ^ 2 ≤ 4 * m ^ 2 := by nlinarith [sq_nonneg (2*m-n)]
    nlinarith [mul_nonneg hk hm3]
  · have hp0 : 0 ≤ 2 * m / n := le_of_lt (div_pos (by positivity) hn)
    have hp1 : 2 * m / n ≤ 1 := (div_le_one hn).mpr (by linarith)
    have hh := h (2*m/n) hp0 hp1
    have hid : 2*m/n*n - k*n*(2*m/n)^3 - k*n^2*(2*m/n)^4 =
        (2*m*n^2 - 8*k*m^3 - 16*k*m^4)/n^2 := by
      field_simp
      ring
    rw [hid] at hh
    have hh2 : 2*m*n^2 - 8*k*m^3 - 16*k*m^4 ≤ m*n^2 :=
      (div_le_iff₀ (sq_pos_of_pos hn)).mp hh
    have hpow : m ^ 3 ≤ m ^ 4 := by
      nlinarith [mul_nonneg hm3 (sub_nonneg.mpr hm)]
    have hkm : 8*k*m^3 ≤ 8*k*m^4 := mul_le_mul_of_nonneg_left hpow (by positivity)
    have hmid : m * n^2 ≤ m * (24*k*m^3) := by nlinarith
    have hn2 : n^2 ≤ 24*k*m^3 := (mul_le_mul_iff_right₀ hm0).mp hmid
    nlinarith

end JSP000633

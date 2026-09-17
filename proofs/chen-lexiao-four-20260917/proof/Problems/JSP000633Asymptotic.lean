import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Analytic consequences of the cubic cardinality bound used in JSP-000633.
These lemmas do not assume or replace the combinatorial existence theorem. -/

namespace JSP000633
open Filter
open scoped Topology

theorem cubic_bound_implies_rpow_bound {n b C : ℝ}
    (hn : 0 ≤ n) (hb : 0 ≤ b) (hC : 0 < C)
    (h : n ^ 2 ≤ C * b ^ 3) :
    (1 / C ^ (1 / 3 : ℝ)) * n ^ (2 / 3 : ℝ) ≤ b := by
  have hr := Real.rpow_le_rpow (sq_nonneg n) h (by norm_num : 0 ≤ (1 / 3 : ℝ))
  have hnroot : (n ^ 2 : ℝ) ^ (1 / 3 : ℝ) = n ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn]
    norm_num
  have hbroot : (b ^ 3 : ℝ) ^ (1 / 3 : ℝ) = b := by
    rw [← Real.rpow_natCast b 3, ← Real.rpow_mul hb]
    norm_num
  rw [hnroot, Real.mul_rpow hC.le (pow_nonneg hb 3), hbroot] at hr
  have hpos : 0 < C ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hC _
  calc
    (1 / C ^ (1 / 3 : ℝ)) * n ^ (2 / 3 : ℝ) =
        n ^ (2 / 3 : ℝ) / C ^ (1 / 3 : ℝ) := by ring
    _ ≤ b := (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hr)

/-- Any fixed smaller power, with any fixed coefficient, is eventually dominated. -/
theorem eventually_smaller_power {c α M : ℝ} (hc : 0 < c) (hα : α < 2 / 3) :
    ∀ᶠ n : ℕ in atTop,
      M * (n : ℝ) ^ α < c * (n : ℝ) ^ (2 / 3 : ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / 3 - α)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_gt_atTop (M / c)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hcp : M < c * (n : ℝ) ^ (2 / 3 - α) := by
    simpa [mul_comm] using (div_lt_iff₀ hc).mp hn
  have hmul := mul_lt_mul_of_pos_right hcp (Real.rpow_pos_of_pos hnpos α)
  calc
    M * (n : ℝ) ^ α < (c * (n : ℝ) ^ (2 / 3 - α)) * (n : ℝ) ^ α := hmul
    _ = c * (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hnpos]
      congr 2
      ring

theorem eventually_sqrt_multiple {c M : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, M * Real.sqrt n < c * (n : ℝ) ^ (2 / 3 : ℝ) := by
  simpa [Real.sqrt_eq_rpow] using
    (eventually_smaller_power (M := M) (α := 1 / 2) hc (by norm_num))

/-- The exponent improvement can be taken as 1/12 above 1/2. -/
theorem eventually_positive_power_improvement {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + 1 / 12 : ℝ) <
      c * (n : ℝ) ^ (2 / 3 : ℝ) := by
  simpa using
    (eventually_smaller_power (M := 1) (α := 1 / 2 + 1 / 12) hc (by norm_num))

end JSP000633

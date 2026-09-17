import Mathlib.Data.Nat.Basic

/-!
# Arithmetic in Gyárfás's endpoint-neighbor argument

Lemma 4 (printed pages 44–45) combines the two bounds `q + M` and `q + N`,
where `M + N = p`. The proof of Theorem 1 (printed page 42) uses the resulting
ceiling bound to reduce the unequal- and equal-neighbor cases to the precise
exceptional parameter values handled by Lemmas 6–8.

All declarations here concern natural numbers only. They supply the arithmetic
steps after the corresponding graph counting estimates have been proved.
-/

namespace JSP000078

/-- The low family of `I` lengths and a disjoint sumset of at least
`J + M - 1` lengths supply `q + M` lengths when `I + J = q + 1`.
The arithmetic implication remains valid when the natural subtraction
truncates; applications obtain the sumset bound from nonempty factors. -/
theorem endpoint_pair_count_of_partition
    (I J M q K : ℕ) (hpartition : I + J = q + 1)
    (hcount : I + (J + M - 1) ≤ K) : q + M ≤ K := by
  omega

/-- The final arithmetic step of Lemma 4: one of the two attachment-path
parity classes has at least the ceiling of half the total size. -/
theorem max_count_half
    (p q M N K : ℕ) (hsplit : M + N = p)
    (hM : q + M ≤ K) (hN : q + N ≤ K) :
    q + (p + 1) / 2 ≤ K := by
  omega

/-- For a nonempty attachment set it suffices to have the counting bound
for each nonempty parity class. This form avoids applying a sumset bound
when one of its factors is empty. -/
theorem max_count_half_of_nonempty_classes
    (p q M N K : ℕ) (hp : 1 ≤ p) (hsplit : M + N = p)
    (hM : 1 ≤ M → q + M ≤ K) (hN : 1 ≤ N → q + N ≤ K) :
    q + (p + 1) / 2 ≤ K := by
  omega

/-- In Case 1 of the proof of Theorem 1, the degree bound and Lemma 4
leave only `q = 0` and `p = 2k`, which is the case addressed by Lemma 8. -/
theorem distinct_neighbors_exception_cases
    (p q k : ℕ) (hdegree : 2 * k ≤ p + q)
    (hcount : q + (p + 1) / 2 ≤ k) :
    q = 0 ∧ p = 2 * k := by
  omega

/-- Outside the sole Case 1 exception, Lemma 4's numerical lower bound
already exceeds the number `k` of distinct odd cycle lengths. -/
theorem lt_count_of_distinct_neighbors_not_exception
    (p q k : ℕ) (hdegree : 2 * k ≤ p + q)
    (hexception : ¬ (q = 0 ∧ p = 2 * k)) :
    k < q + (p + 1) / 2 := by
  omega

/-- In Case 2, one common neighbor is excluded before applying Lemma 4.
The only surviving cases are `q = 1, p = 2k - 1`, or `q = 0` and
`p ∈ {2k, 2k + 1}`, precisely the alternatives stated on printed page 42. -/
theorem equal_neighbors_exception_cases
    (p q k : ℕ) (hp : 1 ≤ p) (hdegree : 2 * k ≤ p + q)
    (hcount : q + (p - 1 + 1) / 2 ≤ k) :
    (q = 1 ∧ p + q = 2 * k) ∨
      (q = 0 ∧ (p + q = 2 * k ∨ p + q = 2 * k + 1)) := by
  omega

/-- Outside the three Case 2 parameter possibilities, the numerical
estimate obtained by excluding one common neighbor is strictly too large. -/
theorem lt_count_of_equal_neighbors_not_exception
    (p q k : ℕ) (hp : 1 ≤ p) (hdegree : 2 * k ≤ p + q)
    (hexception : ¬ ((q = 1 ∧ p + q = 2 * k) ∨
      (q = 0 ∧ (p + q = 2 * k ∨ p + q = 2 * k + 1)))) :
    k < q + (p - 1 + 1) / 2 := by
  omega

end JSP000078

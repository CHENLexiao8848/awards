import JSP000078.CyclicDistanceSets

/-!
# Complementary proper distances at the opposite marked base

Reversing a pair of distinct marked vertices complements its forward
distance. Global lower bounds on all proper marked distances therefore
hold for both a distance and its complementary arc.
-/

namespace JSP000078

/-- The two directed distances between distinct canonical positions add
up to the circumference. -/
theorem cyclicDistance_add_reverse {N a b : ℕ}
    (ha : a < N) (hb : b < N) (hab : a ≠ b) :
    cyclicDistance N a b + cyclicDistance N b a = N := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rw [cyclicDistance_eq_sub hb hab.le, cyclicDistance_eq_wrap hb hab]
    omega
  · rw [cyclicDistance_eq_wrap ha hba, cyclicDistance_eq_sub ha hba.le]
    omega

/-- The complementary forward distance is the forward distance with the
ordered pair reversed. -/
theorem circumference_sub_cyclicDistance {N a b : ℕ}
    (ha : a < N) (hb : b < N) (hab : a ≠ b) :
    N - cyclicDistance N a b = cyclicDistance N b a := by
  have hsum := cyclicDistance_add_reverse ha hb hab
  omega

/-- Every proper distance has its complement in the proper distance set
based at its target marked position. -/
theorem properDistances_complement_mem (X : Finset ℕ) {N a d : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) (hd : d ∈ properDistances X N a) :
    ∃ b ∈ X, b ≠ a ∧ cyclicDistance N a b = d ∧
      N - d ∈ properDistances X N b := by
  obtain ⟨b, hb, hbd⟩ := Finset.mem_image.mp hd
  obtain ⟨hba, hbX⟩ := Finset.mem_erase.mp hb
  refine ⟨b, hbX, hba, hbd, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_erase.mpr ⟨hba.symm, ha⟩, ?_⟩
  rw [← hbd, circumference_sub_cyclicDistance (hX a ha) (hX b hbX) hba.symm]

/-- A global lower bound for proper marked distances also bounds both
arcs corresponding to any one such distance. -/
theorem properDistances_bounds_of_global_min (X : Finset ℕ) {N g a d : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X)
    (hmin : ∀ b ∈ X, ∀ t ∈ properDistances X N b, g ≤ t)
    (hd : d ∈ properDistances X N a) : g ≤ d ∧ g ≤ N - d := by
  obtain ⟨b, hb, _, _, hcomp⟩ := properDistances_complement_mem X hX ha hd
  exact ⟨hmin a ha d hd, hmin b hb (N - d) hcomp⟩

/-- Any original-or-complementary selection preserves a global lower
bound on all proper marked distances. -/
theorem complementary_choice_ge_global_min (X : Finset ℕ) {N g a t : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X)
    (hmin : ∀ b ∈ X, ∀ d ∈ properDistances X N b, g ≤ d)
    (ht : t ∈ properDistances X N a ∨
      ∃ d ∈ properDistances X N a, t = N - d) : g ≤ t := by
  rcases ht with ht | ⟨d, hd, rfl⟩
  · exact hmin a ha t ht
  · exact (properDistances_bounds_of_global_min X hX ha hmin hd).2

end JSP000078

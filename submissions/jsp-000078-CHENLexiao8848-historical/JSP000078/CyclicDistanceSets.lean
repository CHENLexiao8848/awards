import JSP000078.CyclicParityCounts

/-!
# Proper distances between marked cyclic positions

Canonical positions lie strictly below the circumference. Translating
them modulo that circumference preserves distinctness, and changing the
base from zero to the least positive marked position has an explicit
erase, subtract, and wrap description.
-/

namespace JSP000078

/-- Forward distance from cyclic position `a` to position `x`. -/
def cyclicDistance (N a x : ℕ) : ℕ := (x + N - a) % N

/-- Proper distances from one marked base to all other marked positions. -/
def properDistances (X : Finset ℕ) (N a : ℕ) : Finset ℕ :=
  (X.erase a).image (cyclicDistance N a)

/-- A nonwrapping distance is ordinary natural subtraction. -/
theorem cyclicDistance_eq_sub {N a x : ℕ}
    (hx : x < N) (hax : a ≤ x) : cyclicDistance N a x = x - a := by
  unfold cyclicDistance
  have heq : x + N - a = (x - a) + N := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- A wrapping distance goes through the end of the cyclic interval. -/
theorem cyclicDistance_eq_wrap {N a x : ℕ}
    (ha : a < N) (hxa : x < a) : cyclicDistance N a x = N + x - a := by
  unfold cyclicDistance
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem cyclicDistance_eq {N a x : ℕ} (ha : a < N) (hx : x < N) :
    cyclicDistance N a x = if a ≤ x then x - a else N + x - a := by
  split_ifs with hax
  · exact cyclicDistance_eq_sub hx hax
  · exact cyclicDistance_eq_wrap ha (by omega)

theorem cyclicDistance_lt {N a x : ℕ} (hN : 0 < N) : cyclicDistance N a x < N :=
  Nat.mod_lt _ hN

/-- Translation around the cycle is injective on canonical positions. -/
theorem cyclicDistance_injOn {N a : ℕ} (ha : a < N) :
    Set.InjOn (cyclicDistance N a) {x | x < N} := by
  intro x hx y hy hxy
  change x < N at hx
  change y < N at hy
  rw [cyclicDistance_eq ha hx, cyclicDistance_eq ha hy] at hxy
  split_ifs at hxy <;> omega

theorem properDistances_card (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) :
    (properDistances X N a).card = X.card - 1 := by
  unfold properDistances
  rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem ha]
  intro x hx y hy hxy
  exact cyclicDistance_injOn (hX a ha)
    (hX x (Finset.mem_of_mem_erase hx)) (hX y (Finset.mem_of_mem_erase hy)) hxy

theorem properDistances_bounds (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) :
    ∀ d ∈ properDistances X N a, 1 ≤ d ∧ d < N := by
  intro d hd
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
  have hxX := Finset.mem_of_mem_erase hx
  have hxa := (Finset.mem_erase.mp hx).1
  have haN := hX a ha
  have hxN := hX x hxX
  rw [cyclicDistance_eq haN hxN]
  split_ifs <;> constructor <;> omega

theorem properDistances_zero (X : Finset ℕ) {N : ℕ}
    (hX : ∀ x ∈ X, x < N) : properDistances X N 0 = X.erase 0 := by
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    simpa only [cyclicDistance_eq_sub (hX x (Finset.mem_of_mem_erase hx))
      (Nat.zero_le x), Nat.sub_zero] using hx
  · intro hd
    apply Finset.mem_image.mpr
    exact ⟨d, hd, by
      simpa only [Nat.sub_zero] using cyclicDistance_eq_sub
        (hX d (Finset.mem_of_mem_erase hd)) (Nat.zero_le d)⟩

/-- The full translated marked set is the proper-distance set together
with its new base position zero. -/
theorem image_cyclicDistance_eq_insert_zero (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) :
    X.image (cyclicDistance N a) = insert 0 (properDistances X N a) := by
  have haa : cyclicDistance N a a = 0 := by
    simpa only [Nat.sub_self] using cyclicDistance_eq_sub (hX a ha) (le_refl a)
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    by_cases hxa : x = a
    · subst x
      exact Finset.mem_insert.mpr (Or.inl haa)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨x, Finset.mem_erase.mpr ⟨hxa, hx⟩, rfl⟩)
  · intro hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Finset.mem_image.mpr ⟨a, ha, haa⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_image.mpr ⟨x, Finset.mem_of_mem_erase hx, rfl⟩

/-- Rebase the marked positions at their least positive member. Zero
becomes the wrap distance and all other surviving positions are shifted
by ordinary subtraction. -/
theorem properDistances_eq_shiftAfterMinimum (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (hzero : 0 ∈ X) (ha : a ∈ X) (hapos : 0 < a)
    (hmin : ∀ x ∈ X, x ≠ 0 → a ≤ x) :
    properDistances X N a = shiftAfterMinimum (X.erase 0) N a := by
  have haN := hX a ha
  have hwrap : cyclicDistance N a 0 = N - a := by
    simpa only [Nat.add_zero] using cyclicDistance_eq_wrap haN hapos
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hxa, hxX⟩ := Finset.mem_erase.mp hx
    by_cases hxzero : x = 0
    · subst x
      exact Finset.mem_insert.mpr (Or.inl hwrap)
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨x, Finset.mem_erase.mpr ⟨hxa, Finset.mem_erase.mpr ⟨hxzero, hxX⟩⟩,
        (cyclicDistance_eq_sub (hX x hxX) (hmin x hxX hxzero)).symm⟩
  · intro hd
    rcases Finset.mem_insert.mp hd with hwrapeq | himage
    · apply Finset.mem_image.mpr
      exact ⟨0, Finset.mem_erase.mpr ⟨by omega, hzero⟩, hwrap.trans hwrapeq.symm⟩
    · obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp himage
      obtain ⟨hxa, hxzeroSet⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxzero, hxX⟩ := Finset.mem_erase.mp hxzeroSet
      apply Finset.mem_image.mpr
      exact ⟨x, Finset.mem_erase.mpr ⟨hxa, hxX⟩,
        (cyclicDistance_eq_sub (hX x hxX) (hmin x hxX hxzero)).trans hxd⟩

end JSP000078

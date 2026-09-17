import JSP000078.CyclicDistanceSets

/-!
# Rebasing marked cyclic positions

Translating every marked position and its base by the same cyclic offset
leaves the proper distance set unchanged. The translated marked set has
the same cardinality, consists of canonical positions, and contains zero
when the translating base was marked.
-/

namespace JSP000078

/-- A common cyclic change of origin preserves directed distances. -/
theorem cyclicDistance_rebase {N a b x : ℕ}
    (ha : a < N) (hb : b < N) (hx : x < N) :
    cyclicDistance N (cyclicDistance N a b) (cyclicDistance N a x) =
      cyclicDistance N b x := by
  have hN : 0 < N := by omega
  rw [cyclicDistance_eq (cyclicDistance_lt hN) (cyclicDistance_lt hN),
    cyclicDistance_eq ha hb, cyclicDistance_eq ha hx, cyclicDistance_eq hb hx]
  split_ifs <;> omega

/-- Every translated marked position still lies below the circumference. -/
theorem image_cyclicDistance_bounds (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) :
    ∀ y ∈ X.image (cyclicDistance N a), y < N := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  exact cyclicDistance_lt (by have := hX a ha; omega)

/-- Translating by a selected base puts zero among the marked positions. -/
theorem zero_mem_image_cyclicDistance (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) :
    0 ∈ X.image (cyclicDistance N a) := by
  exact Finset.mem_image.mpr ⟨a, ha, by
    simpa only [Nat.sub_self] using cyclicDistance_eq_sub (hX a ha) (le_refl a)⟩

/-- A cyclic translation preserves the cardinality of a marked set. -/
theorem card_image_cyclicDistance (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) :
    (X.image (cyclicDistance N a)).card = X.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  exact cyclicDistance_injOn (hX a ha) (hX x hx) (hX y hy) hxy

/-- Rebasing all marked positions preserves the proper distance set at
each corresponding marked vertex. -/
theorem properDistances_rebase (X : Finset ℕ) {N a b : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) (hb : b ∈ X) :
    properDistances (X.image (cyclicDistance N a)) N (cyclicDistance N a b) =
      properDistances X N b := by
  have haN := hX a ha
  have hbN := hX b hb
  ext d
  constructor
  · intro hd
    obtain ⟨y, hy, hyd⟩ := Finset.mem_image.mp hd
    obtain ⟨hyb, hyY⟩ := Finset.mem_erase.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyY
    have hxb : x ≠ b := fun h ↦ hyb (h ▸ rfl)
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_erase.mpr ⟨hxb, hx⟩,
      (cyclicDistance_rebase haN hbN (hX x hx)).symm.trans hyd⟩
  · intro hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    obtain ⟨hxb, hxX⟩ := Finset.mem_erase.mp hx
    apply Finset.mem_image.mpr
    refine ⟨cyclicDistance N a x, Finset.mem_erase.mpr ⟨?_, ?_⟩, ?_⟩
    · intro h
      exact hxb (cyclicDistance_injOn haN (hX x hxX) hbN h)
    · exact Finset.mem_image.mpr ⟨x, hxX, rfl⟩
    · exact (cyclicDistance_rebase haN hbN (hX x hxX)).trans hxd

/-- Any predicate on proper distance sets holding at every marked base
continues to hold after a cyclic change of origin. -/
theorem all_properDistances_rebase (X : Finset ℕ) {N a : ℕ}
    (hX : ∀ x ∈ X, x < N) (ha : a ∈ X) (Q : Finset ℕ → Prop)
    (hQ : ∀ b ∈ X, Q (properDistances X N b)) :
    ∀ y ∈ X.image (cyclicDistance N a),
      Q (properDistances (X.image (cyclicDistance N a)) N y) := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  rw [properDistances_rebase X hX ha hb]
  exact hQ b hb

end JSP000078

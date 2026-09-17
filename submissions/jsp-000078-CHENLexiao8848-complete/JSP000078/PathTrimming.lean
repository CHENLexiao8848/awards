import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Find

/-!
# Trimming paths between vertex sets

A path joining two vertex sets can be shortened until its initial and final
vertices are its only intersections with the respective sets.  The support of
the resulting path stays inside the original support, so any disjointness or
vertex-avoidance condition on the original path is preserved.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A B : Set V} {a b : V}

/-- Trim a path between two sets so that it meets each set only at its
corresponding endpoint.  Finiteness and disjointness of the sets are unnecessary. -/
theorem exists_trimmed_path_between_sets
    (p : G.Walk a b) (hp : p.IsPath) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ (a' b' : V) (q : G.Walk a' b'),
      q.IsPath ∧ a' ∈ A ∧ b' ∈ B ∧ q.support ⊆ p.support ∧
      (∀ v ∈ q.support, v ∈ A → v = a') ∧
      (∀ v ∈ q.support, v ∈ B → v = b') := by
  classical
  let candidate : ℕ → Prop := fun n ↦
    ∃ (x y : V) (q : G.Walk x y),
      q.IsPath ∧ x ∈ A ∧ y ∈ B ∧ q.support ⊆ p.support ∧ q.length = n
  have hex : ∃ n, candidate n :=
    ⟨p.length, a, b, p, hp, ha, hb, fun _ hv ↦ hv, rfl⟩
  obtain ⟨x, y, q, hq, hx, hy, hsub, hlen⟩ := Nat.find_spec hex
  refine ⟨x, y, q, hq, hx, hy, hsub, ?_, ?_⟩
  · intro v hv hvA
    by_contra hvx
    have hshort : (q.dropUntil v hv).length < Nat.find hex := by
      rw [← hlen]
      exact q.length_dropUntil_lt_length hv hvx
    apply Nat.find_min hex hshort
    exact ⟨v, y, q.dropUntil v hv, hq.dropUntil hv, hvA, hy,
      fun _ hz ↦ hsub (q.support_dropUntil_subset_support hv hz), rfl⟩
  · intro v hv hvB
    by_contra hvy
    have hshort : (q.takeUntil v hv).length < Nat.find hex := by
      rw [← hlen]
      exact q.length_takeUntil_lt_length hv hvy
    apply Nat.find_min hex hshort
    exact ⟨x, v, q.takeUntil v hv, hq.takeUntil hv, hx, hvB,
      fun _ hz ↦ hsub (q.support_takeUntil_subset_support hv hz), rfl⟩

/-- The trimming conclusion also holds for an arbitrary walk: first erase
repeated-vertex detours, then trim the resulting path. -/
theorem exists_trimmed_path_of_walk_between_sets
    (p : G.Walk a b) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ (a' b' : V) (q : G.Walk a' b'),
      q.IsPath ∧ a' ∈ A ∧ b' ∈ B ∧ q.support ⊆ p.support ∧
      (∀ v ∈ q.support, v ∈ A → v = a') ∧
      (∀ v ∈ q.support, v ∈ B → v = b') := by
  classical
  obtain ⟨a', b', q, hq, ha', hb', hsub, hA, hB⟩ :=
    exists_trimmed_path_between_sets p.bypass p.bypass_isPath ha hb
  exact ⟨a', b', q, hq, ha', hb',
    fun _ hv ↦ p.support_bypass_subset_support (hsub hv), hA, hB⟩

end JSP000078

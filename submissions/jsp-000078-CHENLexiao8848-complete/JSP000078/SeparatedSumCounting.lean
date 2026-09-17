import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# A low family separated from a sumset

Gyárfás's Lemma 4 obtains short odd cycle lengths below every length in
another family formed by adding two independently varying path lengths.
Separation makes the two finite sets disjoint, so their cardinality bounds add.
-/

namespace JSP000078

open scoped Pointwise

/-- An injective low family and a sumset strictly above it contribute
disjoint lengths to `K`. The two sumset factors must be nonempty. -/
theorem card_low_add_sumset_le
    (I J T K : Finset ℕ) (hJ : J.Nonempty) (hT : T.Nonempty)
    (f : ℕ → ℕ) (hf : Set.InjOn f I)
    (hlow : ∀ i ∈ I, f i ∈ K)
    (hhigh : ∀ j ∈ J, ∀ t ∈ T, j + t ∈ K)
    (hsep : ∀ i ∈ I, ∀ j ∈ J, ∀ t ∈ T, f i < j + t) :
    I.card + (J.card + T.card - 1) ≤ K.card := by
  have hdisjoint : Disjoint (I.image f) (J + T) := by
    apply Finset.disjoint_left.mpr
    intro n hnlow hnhigh
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hnlow
    obtain ⟨j, hj, t, ht, hsum⟩ := Finset.mem_add.mp hnhigh
    exact (ne_of_lt (hsep i hi j hj t ht)) hsum.symm
  have hsub : I.image f ∪ (J + T) ⊆ K := by
    intro n hn
    rcases Finset.mem_union.mp hn with hlowmem | hhighmem
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hlowmem
      exact hlow i hi
    · obtain ⟨j, hj, t, ht, rfl⟩ := Finset.mem_add.mp hhighmem
      exact hhigh j hj t ht
  calc
    I.card + (J.card + T.card - 1) ≤ I.card + (J + T).card :=
      Nat.add_le_add_left (cauchy_davenport_add_of_linearOrder_isCancelAdd hJ hT) _
    _ = (I.image f ∪ (J + T)).card := by
      rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injOn hf]
    _ ≤ K.card := Finset.card_le_card hsub

/-- When the low and first sumset indices partition `q + 1` paths, the
separated families supply at least `q + T.card` distinct lengths. -/
theorem add_card_le_of_separated_sumset_partition
    (I J T K : Finset ℕ) (q : ℕ)
    (hpartition : I.card + J.card = q + 1)
    (hJ : J.Nonempty) (hT : T.Nonempty)
    (f : ℕ → ℕ) (hf : Set.InjOn f I)
    (hlow : ∀ i ∈ I, f i ∈ K)
    (hhigh : ∀ j ∈ J, ∀ t ∈ T, j + t ∈ K)
    (hsep : ∀ i ∈ I, ∀ j ∈ J, ∀ t ∈ T, f i < j + t) :
    q + T.card ≤ K.card := by
  have hcount := card_low_add_sumset_le I J T K hJ hT f hf hlow hhigh hsep
  omega

end JSP000078

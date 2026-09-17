import JSP000078.FanPositions

/-! # Three regions of spoke positions cut out by two internal vertices -/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V}

noncomputable def CycleWithIncidentChords.leftPositions (F : CycleWithIncidentChords H) (r : ℕ) : Finset ℕ :=
  F.spokePositions.filter (· ≤ r)

noncomputable def CycleWithIncidentChords.middlePositions (F : CycleWithIncidentChords H) (r s : ℕ) : Finset ℕ :=
  F.spokePositions.filter fun i ↦ r < i ∧ i < s

noncomputable def CycleWithIncidentChords.rightPositions (F : CycleWithIncidentChords H) (s : ℕ) : Finset ℕ :=
  F.spokePositions.filter (s ≤ ·)

theorem CycleWithIncidentChords.leftPositions_nonempty (F : CycleWithIncidentChords H)
    {r : ℕ} (hr : 1 ≤ r) : (F.leftPositions r).Nonempty := by
  exact ⟨1, Finset.mem_filter.mpr ⟨F.mem_spokePositions.mpr (Or.inl rfl), hr⟩⟩

theorem CycleWithIncidentChords.rightPositions_nonempty (F : CycleWithIncidentChords H)
    {s : ℕ} (hs : s < F.cycle.length) : (F.rightPositions s).Nonempty := by
  refine ⟨F.cycle.length - 1, Finset.mem_filter.mpr ⟨?_, by omega⟩⟩
  exact F.mem_spokePositions.mpr (Or.inr (Or.inl rfl))

/-- The three position regions form a disjoint partition. -/
theorem CycleWithIncidentChords.card_positions_sum (F : CycleWithIncidentChords H)
    {r s : ℕ} (hrs : r < s) :
    (F.leftPositions r).card + (F.middlePositions r s).card +
      (F.rightPositions s).card = F.spokePositions.card := by
  classical
  have h₁ := F.spokePositions.card_filter_add_card_filter_not (fun i ↦ i ≤ r)
  have h₂ := (F.spokePositions.filter fun i ↦ ¬i ≤ r).card_filter_add_card_filter_not
    (fun i ↦ i < s)
  have hm : ((F.spokePositions.filter fun i ↦ ¬i ≤ r).filter fun i ↦ i < s) =
      F.middlePositions r s := by
    ext i
    simp only [middlePositions, Finset.mem_filter, Nat.not_le]
    tauto
  have hr : ((F.spokePositions.filter fun i ↦ ¬i ≤ r).filter fun i ↦ ¬i < s) =
      F.rightPositions s := by
    ext i
    simp only [rightPositions, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, by omega⟩
    · intro h
      exact ⟨⟨h.1, by omega⟩, by omega⟩
  rw [hm, hr] at h₂
  change (F.spokePositions.filter fun i ↦ i ≤ r).card + _ + _ = _
  omega

/-- Rectangle length sets for the three pairs of position regions. -/
noncomputable def CycleWithIncidentChords.lengthsLR (F : CycleWithIncidentChords H) (r s : ℕ) : Finset ℕ :=
  ((F.leftPositions r) ×ˢ (F.rightPositions s)).image fun p ↦ (r - p.1) + (p.2 - s) + 2

noncomputable def CycleWithIncidentChords.lengthsLM (F : CycleWithIncidentChords H) (r s : ℕ) : Finset ℕ :=
  ((F.leftPositions r) ×ˢ (F.middlePositions r s)).image fun p ↦ (r - p.1) + (s - p.2) + 2

noncomputable def CycleWithIncidentChords.lengthsMR (F : CycleWithIncidentChords H) (r s : ℕ) : Finset ℕ :=
  ((F.middlePositions r s) ×ˢ (F.rightPositions s)).image fun p ↦ (p.1 - r) + (p.2 - s) + 2

end JSP000078

import JSP000078.EndpointConfiguration
import JSP000078.CyclePositions

/-!
# From selected neighbor vertices to endpoint configurations

Rotation places the last endpoint's chosen cycle neighbor at position
zero. Injective cycle and path positions turn the selected vertex sets
into the indexed attachment and chord sets without changing their sizes.
-/

namespace JSP000078

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Rotating a longest odd cycle preserves longestness. -/
theorem IsLongestOddCycle.rotate {c y : V} {C : G.Walk c c}
    (hC : IsLongestOddCycle C) (hy : y ∈ C.support) [DecidableEq V] :
    IsLongestOddCycle (C.rotate y hy) := by
  refine ⟨hC.1.rotate hy, ?_, ?_⟩
  · simpa only [Walk.length_rotate] using hC.2.1
  · intro d D hD hDO
    simpa only [Walk.length_rotate] using hC.2.2 d D hD hDO

/-- A finite set of nonbase cycle neighbors becomes a set of positive
attachment indices with exactly the same cardinality. -/
theorem exists_cycle_attachment_indices {c A : V} {C : G.Walk c c}
    (hC : C.IsCycle) (X : Finset V)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ v ≠ c ∧ G.Adj A v) :
    ∃ T : Finset ℕ, T.card = X.card ∧
      (∀ t ∈ T, 1 ≤ t ∧ t < C.length ∧ G.Adj A (C.getVert t)) := by
  classical
  refine ⟨X.image (cyclePosition C), ?_, ?_⟩
  · apply Finset.card_image_iff.mpr
    intro u hu v hv hpos
    exact cyclePosition_injOn C (hX u hu).1 (hX v hv).1 hpos
  · intro t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hvC, hvc, hAv⟩ := hX v hv
    refine ⟨(cyclePosition_pos_iff C hvC).mpr hvc, cyclePosition_lt hC hvC, ?_⟩
    simpa only [getVert_cyclePosition C hvC] using hAv

/-- The canonical support position of a vertex on a path. -/
noncomputable def pathPosition {A B : V} (P : G.Walk A B) (v : V) : ℕ := by
  classical
  exact P.support.idxOf v

theorem getVert_pathPosition {A B v : V} (P : G.Walk A B) (hv : v ∈ P.support) :
    P.getVert (pathPosition P v) = v := by
  classical
  exact P.getVert_support_idxOf hv

theorem pathPosition_le {A B v : V} (P : G.Walk A B) (hv : v ∈ P.support) :
    pathPosition P v ≤ P.length := by
  classical
  have h := List.idxOf_lt_length_of_mem hv
  simpa only [pathPosition, Walk.length_support, Nat.lt_succ_iff] using h

/-- Neighbors on a path other than its initial neighbor have proper chord
positions. The finite vertex set and its position image have equal size. -/
theorem exists_path_chord_indices {A B : V} (P : G.Walk A B) (Z : Finset V)
    (hZ : ∀ v ∈ Z, v ∈ P.support ∧ v ≠ P.getVert 1 ∧ G.Adj A v) :
    ∃ D : Finset ℕ, D.card = Z.card ∧
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ P.length ∧ G.Adj A (P.getVert d)) := by
  classical
  refine ⟨Z.image (pathPosition P), ?_, ?_⟩
  · apply Finset.card_image_iff.mpr
    intro u hu v hv hpos
    exact (getVert_pathPosition P (hZ u hu).1).symm.trans
      ((congrArg P.getVert hpos).trans (getVert_pathPosition P (hZ v hv).1))
  · intro d hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hvP, hvone, hAv⟩ := hZ v hv
    have hget := getVert_pathPosition P hvP
    have hnzero : pathPosition P v ≠ 0 := by
      intro hz
      rw [hz, Walk.getVert_zero] at hget
      exact hAv.ne hget
    have hnone : pathPosition P v ≠ 1 := by
      intro hone
      rw [hone] at hget
      exact hvone hget.symm
    refine ⟨by omega, pathPosition_le P hvP, ?_⟩
    simpa only [hget] using hAv

/-- Selected neighbors on an arbitrary longest odd cycle and on an
outside path give the indexed endpoint configuration with unchanged
attachment and chord counts. -/
theorem exists_endpointConfiguration_of_neighbor_sets [Fintype V]
    {c A B y : V} {C : G.Walk c c} {P : G.Walk A B}
    (hC : IsLongestOddCycle C) (hP : P.IsPath) (hAB : A ≠ B)
    (hPC : Disjoint {v | v ∈ P.support} {v | v ∈ C.support})
    (hy : y ∈ C.support) (hBy : G.Adj B y) (X Z : Finset V)
    (hXne : X.Nonempty)
    (hX : ∀ v ∈ X, v ∈ C.support ∧ v ≠ y ∧ G.Adj A v)
    (hZ : ∀ v ∈ Z, v ∈ P.support ∧ v ≠ P.getVert 1 ∧ G.Adj A v) :
    ∃ E : EndpointConfiguration G,
      E.attachments.card = X.card ∧ E.chords.card = Z.card := by
  classical
  let R := C.rotate y hy
  have hR : IsLongestOddCycle R := hC.rotate hy
  have hXR : ∀ v ∈ X, v ∈ R.support ∧ v ≠ y ∧ G.Adj A v := by
    intro v hv
    obtain ⟨hvC, hvy, hAv⟩ := hX v hv
    exact ⟨(C.mem_support_rotate_iff y hy).mpr hvC, hvy, hAv⟩
  obtain ⟨T, hTcard, hT⟩ := exists_cycle_attachment_indices hR.1 X hXR
  obtain ⟨D, hDcard, hD⟩ := exists_path_chord_indices P Z hZ
  have hTne : T.Nonempty := Finset.card_pos.mp (hTcard ▸ Finset.card_pos.mpr hXne)
  let E : EndpointConfiguration G := {
    cycleBase := y
    cycle := R
    longest := hR
    first := A
    last := B
    outside := P
    outside_path := hP
    ends_ne := hAB
    disjoint := by
      apply Set.disjoint_left.mpr
      intro v hvP hvR
      exact Set.disjoint_left.mp hPC hvP ((C.mem_support_rotate_iff y hy).mp hvR)
    last_attachment := hBy
    attachments := T
    attachments_nonempty := hTne
    attachment_bounds := fun t ht ↦ ⟨(hT t ht).1, (hT t ht).2.1⟩
    first_attachments := fun t ht ↦ (hT t ht).2.2
    chords := D
    chord_bounds := fun d hd ↦ ⟨(hD d hd).1, (hD d hd).2.1⟩
    chord_adj := fun d hd ↦ (hD d hd).2.2
  }
  exact ⟨E, hTcard, hDcard⟩

end JSP000078
